use crate::lookup_range_check::LookupRangeCheckConfig;

use ff::PrimeFieldBits;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Value},
    plonk::*,
    poly::Rotation,
};
use std::{marker::PhantomData, vec};

#[derive(Clone)]
/// (selector, poly, eval)
pub(crate) struct Config<const K: usize, F: PrimeFieldBits> {
    selector: Selector,
    pub(crate) poly: Column<Advice>,
    pub(crate) eval: Column<Advice>,
    pub(crate) range_check: LookupRangeCheckConfig<F, K>,
    _marker: PhantomData<F>,
}

impl<const K: usize, F: PrimeFieldBits> Config<K, F> {
    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        poly: Column<Advice>,
        eval: Column<Advice>,
        x: Challenge,
        range_check: Column<Advice>,
        table: TableColumn,
    ) -> Self {
        let selector = meta.selector();
        let constants = meta.fixed_column();
        meta.enable_constant(constants);

        meta.create_gate("poly eval", |meta| {
            let selector = meta.query_selector(selector);
            let coeff = meta.query_advice(poly, Rotation::cur());
            let eval_prev = meta.query_advice(eval, Rotation::prev());
            let eval_cur = meta.query_advice(eval, Rotation::cur());

            let x = meta.query_challenge(x);

            /*
              selector    poly       eval
                 0         a2         a2
                 1         a1         a2 * x + a1
                 1         a0         a2 * x^2 + a1x + a0
            */
            vec![selector * (eval_prev * x + coeff - eval_cur)]
        });

        let range_check = LookupRangeCheckConfig::<F, K>::configure(meta, range_check, table);

        Self {
            selector,
            poly,
            eval,
            range_check,
            _marker: PhantomData,
        }
    }

    // Loads the values [0..2^K) into `table_idx`.
    pub fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "table_idx",
            |mut table| {
                // We generate the row values lazily (we only need them during keygen).
                for index in 0..(1 << K) {
                    table.assign_cell(
                        || "table_idx",
                        self.range_check.table_idx,
                        index,
                        || Value::known(F::from(index as u64)),
                    )?;
                }
                Ok(())
            },
        )
    }

    pub(crate) fn witness_carry(
        &self,
        mut layouter: impl Layouter<F>,
        carry_val: Value<F>,
        num_bits: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        let witnessed = self.range_check.witness_check(
            layouter.namespace(|| "carry_val"),
            carry_val,
            K,
            false,
        )?;

        // Range-constrain remaining chunk (if any).
        if num_bits % K != 0 {
            self.range_check.copy_short_check(
                layouter.namespace(|| "leftover"),
                witnessed[num_bits / K].clone(),
                num_bits % K,
            )?;
        }

        Ok(witnessed[0].clone())
    }

    pub(crate) fn witness_poly(
        &self,
        mut layouter: impl Layouter<F>,
        coeff_vals: Vec<Value<F>>,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        let mut coeffs = vec![];

        // Witness and range-check each limb of poly_a to be 64 bits
        for (i, coeff) in coeff_vals.iter().enumerate() {
            let coeff = self.range_check.witness_check(
                layouter.namespace(|| format!("coeff {}", i)),
                *coeff,
                4,
                true,
            )?[0]
                .clone();
            coeffs.push(coeff);
        }

        Ok(coeffs)
    }

    pub(crate) fn evaluate(
        &self,
        mut layouter: impl Layouter<F>,
        coeffs: &[AssignedCell<F, F>],
        x: Value<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "poly_a",
            |mut region| {
                coeffs[0].copy_advice(|| "coeff 0", &mut region, self.poly, 0)?;
                let mut eval = coeffs[0].value().copied();
                let mut eval_cell =
                    coeffs[0].copy_advice(|| "eval 0", &mut region, self.eval, 0)?;

                for (i, coeff) in coeffs.iter().skip(1).enumerate() {
                    self.selector.enable(&mut region, i + 1)?;
                    coeff.copy_advice(
                        || format!("coeff {}", i + 1),
                        &mut region,
                        self.poly,
                        i + 1,
                    )?;
                    eval = eval * x + coeff.value().copied();
                    eval_cell = region.assign_advice(
                        || format!("eval {}", i + 1),
                        self.eval,
                        i + 1,
                        || eval,
                    )?;
                }

                Ok(eval_cell)
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use ff::{FromUniformBytes, WithSmallOrderMulGroup};
    use halo2_proofs::circuit::floor_planner::V1;
    use halo2_proofs::poly::commitment::{CommitmentScheme, Verifier};
    use halo2_proofs::transcript::EncodedChallenge;
    use halo2_proofs::{
        dev::{metadata, FailureLocation, MockProver, VerifyFailure},
        poly::{commitment::ParamsProver, VerificationStrategy},
        transcript::{
            Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
        },
    };
    use halo2curves::bn256::Bn256;
    use halo2curves::pairing::Engine;
    use rand_core::OsRng;

    #[derive(Clone)]
    pub(crate) struct Config<F: PrimeFieldBits> {
        poly_a: super::Config<4, F>,
        x: Challenge,
    }

    impl<F: PrimeFieldBits> Config<F> {
        fn configure(meta: &mut ConstraintSystem<F>) -> Self {
            let poly = meta.advice_column_in(FirstPhase);
            meta.enable_equality(poly);
            let eval = meta.advice_column_in(SecondPhase);
            meta.enable_equality(eval);
            let x = meta.challenge_usable_after(FirstPhase);
            let range_check = meta.advice_column();
            let table = meta.lookup_table_column();

            let poly_a = super::Config::configure(meta, poly, eval, x, range_check, table);

            Config { poly_a, x }
        }
    }

    // Polynomial coeffs are witnessed in big endian notation
    // to make it more compatible with horners rule
    #[derive(Clone, Default)]
    struct MyCircuit<F: PrimeFieldBits> {
        poly_a: [Value<F>; 4],
    }

    impl<F: PrimeFieldBits> Circuit<F> for MyCircuit<F> {
        type Config = Config<F>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            Config::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            config.poly_a.range_check.load(&mut layouter)?;
            let x = layouter.get_challenge(config.x);

            let poly_a = config.poly_a.witness_poly(
                layouter.namespace(|| "witness poly_a"),
                self.poly_a.to_vec(),
            )?;

            // poly_a evaluation
            let _poly_a_eval =
                config
                    .poly_a
                    .evaluate(layouter.namespace(|| "eval poly_a"), &poly_a, x)?;

            let _ = config.poly_a.witness_carry(
                layouter.namespace(|| ""),
                Value::known(F::from(256)),
                9,
            );

            Ok(())
        }
    }

    fn test_mock_prover<F: Ord + FromUniformBytes<64> + PrimeFieldBits>(
        k: u32,
        circuit: MyCircuit<F>,
        expected: Result<(), Vec<(metadata::Constraint, FailureLocation)>>,
    ) {
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        match (prover.verify(), expected) {
            (Ok(_), Ok(_)) => {}
            (Err(err), Err(expected)) => {
                assert_eq!(
                    err.into_iter()
                        .map(|failure| match failure {
                            VerifyFailure::ConstraintNotSatisfied {
                                constraint,
                                location,
                                ..
                            } => (constraint, location),
                            _ => panic!("MockProver::verify has result unmatching expected"),
                        })
                        .collect::<Vec<_>>(),
                    expected
                )
            }
            (_, _) => panic!("MockProver::verify has result unmatching expected"),
        };
    }

    fn test_prover(k: u32, circuit: MyCircuit<<Bn256 as Engine>::Scalar>, expected: bool) {
        use halo2_proofs::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
        use halo2_proofs::poly::kzg::multiopen::{ProverGWC, VerifierGWC};
        use halo2_proofs::poly::kzg::strategy::AccumulatorStrategy;

        let params = ParamsKZG::<Bn256>::new(k);
        let _rng = OsRng;

        let vk = keygen_vk(&params, &circuit).unwrap();
        let pk = keygen_pk(&params, vk, &circuit).unwrap();

        let proof = {
            let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

            create_proof::<KZGCommitmentScheme<_>, ProverGWC<'_, _>, _, _, _, _>(
                &params,
                &pk,
                &[circuit],
                &[&[]],
                OsRng,
                &mut transcript,
            )
            .expect("proof generation should not fail");

            transcript.finalize()
        };

        fn verify_proof_helper<
            'a,
            'params,
            Scheme: CommitmentScheme,
            V: Verifier<'params, Scheme>,
            E: EncodedChallenge<Scheme::Curve>,
            T: TranscriptReadBuffer<&'a [u8], Scheme::Curve, E>,
            Strategy: VerificationStrategy<'params, Scheme, V, Output = Strategy>,
        >(
            params_verifier: &'params Scheme::ParamsVerifier,
            vk: &VerifyingKey<Scheme::Curve>,
            proof: &'a [u8],
        ) -> bool
        where
            Scheme::Scalar: Ord + WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
        {
            let mut transcript = T::init(proof);

            let strategy = Strategy::new(params_verifier);
            verify_proof(params_verifier, vk, strategy, &[&[]], &mut transcript)
                .unwrap()
                .finalize()
        }

        let accepted = {
            let verifier_params = params.verifier_params();

            verify_proof_helper::<
                _,
                VerifierGWC<_>,
                _,
                Blake2bRead<_, _, Challenge255<_>>,
                AccumulatorStrategy<_>,
            >(verifier_params, pk.get_vk(), &proof[..])
        };

        assert_eq!(accepted, expected);
    }

    #[test]
    fn poly_eval_test() {
        use halo2curves::bn256::Fr;

        const K: u32 = 5;

        let circuit = MyCircuit::<Fr> {
            poly_a: [4u64, 3, 2, 1]
                .iter()
                .map(|coeff| Value::known(Fr::from(*coeff)))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        };

        {
            test_mock_prover(K, circuit.clone(), Ok(()));
            test_prover(K, circuit.clone(), true);
        }
    }
}