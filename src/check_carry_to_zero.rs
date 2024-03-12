use crate::{
    mul_cfgs::{MulAddConfig, MulConfig},
    poly_eval::{self, LoadedPoly},
};
use ff::{Field, PrimeField, PrimeFieldBits};

use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector, VirtualCells},
    poly::Rotation,
};

#[derive(Clone)]
pub(crate) struct Config<const BASE: u8, const N: usize, const K: usize, F: PrimeFieldBits> {
    poly: poly_eval::Config<K, F>,
    carry: Column<Advice>,
    init_selector: Selector,
    selector: Selector,
}

impl<const BASE: u8, const N: usize, const K: usize, F: PrimeFieldBits> Config<BASE, N, K, F> {
    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        poly: poly_eval::Config<K, F>,
        carry: Column<Advice>,
    ) -> Self {
        let base = F::from_u128(1 << BASE);
        let init_selector = meta.selector();
        let selector = meta.selector();

        let constants = meta.fixed_column();
        meta.enable_constant(constants);

        /* */

        /*
            given array of coeffs in little-endian

            init_selector    selector       coeffs          carry
                1                0            a0      c0 | a0 = c0 * B
                0                1            a1      c1 | (a1 + c0) = c1 * B
                0                1            a2      c2 | (a2 + c1) = c2 * B
                0                1            a3      c3 | (a3 + c2) = c3 * B
                0                1            a4      c4 | (a4 + c3) = c4 * B | c4 == 0
        */

        meta.create_gate("check init carry", |meta| {
            let init_selector = meta.query_selector(init_selector);
            let coeff = meta.query_advice(poly.poly, Rotation::cur());
            let carry = meta.query_advice(carry, Rotation::cur());

            vec![init_selector * (carry * base - coeff)]
        });

        meta.create_gate("check carry", |meta| {
            let selector = meta.query_selector(selector);
            let coeff = meta.query_advice(poly.poly, Rotation::cur());
            let carry_prev = meta.query_advice(carry, Rotation::prev());
            let carry_cur = meta.query_advice(carry, Rotation::cur());
            vec![selector * (coeff + carry_prev - carry_cur * base)]
        });

        Self {
            poly,
            carry,
            selector,
            init_selector,
        }
    }

    pub(crate) fn synthesize(
        &self,
        mut layouter: impl Layouter<F>,
        f: &[Value<F>; N],
        x: Value<F>,
    ) -> Result<LoadedPoly<N, F>, Error> {
        let base_inv = Value::known(F::from_u128(1 << BASE).invert().unwrap());

        /*
           init_selector    selector       coeffs          carry
               1                0            a0      c0 | a0 = c0 * B
               0                1            a1      c1 | (a1 + c0) = c1 * B
               0                1            a2      c2 | (a2 + c1) = c2 * B
               0                1            a3      c3 | (a3 + c2) = c3 * B
               0                1            a4      c4 | (a4 + c3) = c4 * B | c4 == 0
        */
        layouter.assign_region(
            || "check carry to zero",
            |mut region| {
                // assign f
                let f_loaded = self.poly.witness_and_evaluate_inner(&mut region, 0, f, x)?;

                // enable init selector
                self.init_selector.enable(&mut region, 0)?;

                let mut carry = f[0] * base_inv;
                let mut carry_cell = region.assign_advice(|| "carry 0", self.carry, 0, || carry)?;

                for i in 1..N {
                    self.selector.enable(&mut region, i)?;

                    carry = (carry + f[i]) * base_inv;
                    carry_cell = region.assign_advice(|| "carry", self.carry, i, || carry)?;
                }

                region.constrain_constant(carry_cell.cell(), F::ZERO)?;

                Ok(f_loaded)
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::{
        arithmetic::CurveAffine,
        circuit::floor_planner::V1,
        plonk::{
            create_proof, keygen_pk, keygen_vk, verify_proof, Challenge, Circuit, FirstPhase,
            SecondPhase, VerifyingKey,
        },
        poly::commitment::{CommitmentScheme, Verifier},
        transcript::EncodedChallenge,
    };
    use halo2curves::{bn256::Bn256, pairing::Engine};

    use super::*;

    use crate::poly_eval;
    use ff::{FromUniformBytes, PrimeFieldBits, WithSmallOrderMulGroup};
    use halo2_proofs::{
        dev::{metadata, FailureLocation, MockProver, VerifyFailure},
        poly::{commitment::ParamsProver, VerificationStrategy},
        transcript::{
            Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
        },
    };
    use rand_core::OsRng;

    #[derive(Clone, Debug, Default)]
    struct MyCircuit<F: PrimeField> {
        f: [Value<F>; 4],
    }

    impl<F: PrimeFieldBits> Circuit<F> for MyCircuit<F> {
        type Config = (super::Config<10, 4, 10, F>, Challenge);

        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let f = meta.advice_column();
            let eval = meta.advice_column_in(SecondPhase);
            let x = meta.challenge_usable_after(FirstPhase);
            let range_check = meta.advice_column();
            let table = meta.lookup_table_column();

            let poly = poly_eval::Config::configure(meta, f, eval, x, range_check, table);
            let carry = meta.advice_column();

            meta.enable_equality(f);
            meta.enable_equality(carry);

            (super::Config::configure(meta, poly, carry), x)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let x = config.1;
            let config = config.0;

            let mut witness_poly = |poly: Vec<Value<F>>,
                                    column: Column<Advice>|
             -> Result<Vec<AssignedCell<F, F>>, Error> {
                layouter.assign_region(
                    || "",
                    |mut region| {
                        let mut coeffs = vec![];
                        for (i, coeff) in poly.iter().enumerate() {
                            let coeff = region.assign_advice(|| "", column, i, || *coeff)?;
                            coeffs.push(coeff);
                        }
                        Ok(coeffs)
                    },
                )
            };

            let x = layouter.get_challenge(x);
            // check carry to zero on f
            config.synthesize(layouter.namespace(|| "f"), &self.f, x)?;

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
    fn fpmul_test() {
        use halo2curves::bn256::Fr;

        const K: u32 = 11;

        fn array_value<const L: usize>(array: [i64; L]) -> [Value<Fr>; L] {
            array
                .iter()
                .map(|&coeff| {
                    let fi = if coeff < 0 {
                        -Fr::from(-coeff as u64)
                    } else {
                        Fr::from(coeff as u64)
                    };

                    Value::known(fi)
                })
                .collect::<Vec<_>>()
                .try_into()
                .unwrap()
        }

        let circuit = MyCircuit::<Fr> {
            f: array_value([-10, -9, -9, 1]),
        };

        {
            test_mock_prover(K, circuit.clone(), Ok(()));
            test_prover(K, circuit.clone(), true);
        }
    }
}
