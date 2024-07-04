use ff::{Field, PrimeFieldBits};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, Value},
    plonk::*,
    poly::Rotation,
};
use std::vec;

use crate::lookup_range_check::LookupRangeCheckConfig;

pub(crate) struct LoadedPoly<const COEFFS: usize, F: Field> {
    pub(crate) coeffs: [AssignedCell<F, F>; COEFFS],
    pub(crate) eval: AssignedCell<F, F>,
}

#[derive(Clone)]
/// (selector, poly, eval)
pub(crate) struct Config<const K: usize, F: PrimeFieldBits> {
    selector: Selector,
    pub(crate) poly: Column<Advice>,
    pub(crate) eval: Column<Advice>,
    pub(crate) range_check: LookupRangeCheckConfig<F, K>,
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
            let eval_cur = meta.query_advice(eval, Rotation::cur());
            let eval_next = meta.query_advice(eval, Rotation::next());

            let x = meta.query_challenge(x);

            /*
              selector    poly       eval
                1         a0         a2 * x^2 + a1x + a0
                1         a1         a2 * x + a1
                0         a2         a2
            */

            // eval_cur = coeff + challenge * eval_next
            let expected_eval = coeff + x * eval_next;
            vec![selector * (eval_cur - expected_eval)]
        });

        let range_check = LookupRangeCheckConfig::<F, K>::configure(meta, range_check, table);

        Self {
            selector,
            poly,
            eval,
            range_check,
        }
    }

    // Loads the values [0..2^K) into the range check table.
    pub(crate) fn load_range_check(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.range_check.load(layouter)
    }

    pub(crate) fn witness_carry(
        &self,
        mut layouter: impl Layouter<F>,
        carry_val: Value<F>,
        num_bits: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        let witnessed = layouter.assign_region(
            || "witness carry",
            |mut region| region.assign_advice(|| "", self.poly, 0, || carry_val),
        )?;

        let witnessed = self.range_check.witness_check(
            layouter.namespace(|| "carry_val"),
            carry_val,
            num_bits,
        )?;

        Ok(witnessed[0].clone())
    }

    pub(crate) fn witness_poly(
        &self,
        mut layouter: impl Layouter<F>,
        coeff_vals: Vec<Value<F>>,
        num_bits: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        let mut coeffs = vec![];

        // Witness and range-check each limb of poly_a to be 64 bits
        for (i, coeff) in coeff_vals.iter().enumerate() {
            let coeff = self.range_check.witness_check(
                layouter.namespace(|| format!("coeff {}", i)),
                *coeff,
                num_bits,
            )?[0]
                .clone();
            coeffs.push(coeff);
        }

        Ok(coeffs)
    }

    pub(crate) fn witness_and_evaluate_inner<const COEFFS: usize>(
        &self,
        mut region: &mut Region<'_, F>,
        offset: usize,
        coeff_vals: &[Value<F>; COEFFS],
        x: Value<F>,
    ) -> Result<LoadedPoly<COEFFS, F>, Error> {
        let n = COEFFS;
        let mut coeffs = vec![];

        let mut eval = coeff_vals[n - 1];
        let mut eval_cell = region.assign_advice(
            || format!("coeff {}", n - 1),
            self.eval,
            offset + n - 1,
            || eval,
        )?;
        let last_coeff_cell = region.assign_advice(
            || format!("coeff {}", n - 1),
            self.poly,
            offset + n - 1,
            || eval,
        )?;
        coeffs.push(last_coeff_cell);

        for i in (0..=(n - 2)).rev() {
            self.selector.enable(&mut region, i)?;
            let coeff = region.assign_advice(
                || format!("eval {}", i),
                self.poly,
                offset + i,
                || coeff_vals[i],
            )?;

            eval = eval * x + coeff.value().copied();
            eval_cell =
                region.assign_advice(|| format!("eval {}", i), self.eval, offset + i, || eval)?;
            coeffs.push(coeff);
        }

        coeffs.reverse();

        Ok(LoadedPoly {
            coeffs: coeffs.clone().try_into().unwrap(),
            eval: eval_cell,
        })
    }

    pub(crate) fn witness_and_evaluate<const COEFFS: usize>(
        &self,
        mut layouter: impl Layouter<F>,
        // little-endian
        coeff_vals: [Value<F>; COEFFS],
        x: Value<F>,
    ) -> Result<LoadedPoly<COEFFS, F>, Error> {
        layouter.assign_region(
            || "poly_a",
            |mut region| self.witness_and_evaluate_inner(&mut region, 0, &coeff_vals, x),
        )
    }

    pub(crate) fn witness_and_evaluate_and_range_check<const COEFFS: usize>(
        &self,
        mut layouter: impl Layouter<F>,
        // little-endian
        coeff_vals: [Value<F>; COEFFS],
        num_bits: usize,
        x: Value<F>,
    ) -> Result<LoadedPoly<COEFFS, F>, Error> {
        let poly = layouter.assign_region(
            || "poly_a",
            |mut region| self.witness_and_evaluate_inner(&mut region, 0, &coeff_vals, x),
        )?;
        for coeff in poly.coeffs.iter() {
            self.range_check
                .copy_check(layouter.namespace(|| ""), coeff, num_bits)?;
        }

        Ok(poly)
    }

    pub(crate) fn evaluate(
        &self,
        mut layouter: impl Layouter<F>,
        // little-endian
        coeffs: &[AssignedCell<F, F>],
        x: Value<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "poly_a",
            |mut region| {
                let n = coeffs.len();

                let mut eval = coeffs[n - 1].value().copied();
                let mut eval_cell = coeffs[n - 1].copy_advice(
                    || format!("coeff {}", n - 1),
                    &mut region,
                    self.eval,
                    n - 1,
                )?;

                for i in (0..=n - 2).rev() {
                    self.selector.enable(&mut region, i)?;
                    coeffs[i].copy_advice(|| format!("coeff {}", i), &mut region, self.poly, i)?;

                    eval = eval * x + coeffs[i].value().copied();
                    eval_cell =
                        region.assign_advice(|| format!("eval {}", i), self.eval, i, || eval)?;
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
    use halo2_proofs::{
        circuit::floor_planner::V1,
        dev::{metadata, FailureLocation, MockProver, VerifyFailure},
        poly::{
            commitment::{CommitmentScheme, ParamsProver, Verifier},
            VerificationStrategy,
        },
        transcript::{
            Blake2bRead, Blake2bWrite, Challenge255, EncodedChallenge, TranscriptReadBuffer,
            TranscriptWriterBuffer,
        },
    };
    use halo2curves::{bn256::Bn256, pairing::Engine};
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

    // Polynomial coeffs are witnessed in little-endian
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
                64,
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

        // 4 + 30 + 200 + 1000
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
