use halo2_proofs::{
    arithmetic::Field,
    circuit::{AssignedCell, Layouter, Value},
    plonk::*,
    poly::Rotation,
};
use std::vec;

#[derive(Clone)]
/// (selector, poly, eval)
pub(crate) struct PolyEval(
    pub(crate) Selector,
    pub(crate) Column<Advice>,
    pub(crate) Column<Advice>,
);
impl PolyEval {
    pub(crate) fn configure<F: Field>(
        meta: &mut ConstraintSystem<F>,
        poly: Column<Advice>,
        eval: Column<Advice>,
        x: Challenge,
    ) -> Self {
        let selector = meta.selector();

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

        Self(selector, poly, eval)
    }

    pub(crate) fn witness<F: Field>(
        &self,
        mut layouter: impl Layouter<F>,
        column: Column<Advice>,
        coeff_vals: Vec<Value<F>>,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        layouter.assign_region(
            || "witness coeffs",
            |mut region| {
                let mut coeffs = vec![];
                for (i, coeff) in coeff_vals.iter().enumerate() {
                    coeffs.push(region.assign_advice(
                        || format!("coeff {}", i),
                        column,
                        i,
                        || *coeff,
                    )?);
                }
                Ok(coeffs)
            },
        )
    }

    pub(crate) fn evaluate<F: Field>(
        &self,
        mut layouter: impl Layouter<F>,
        coeffs: &[AssignedCell<F, F>],
        x: Value<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "poly_a",
            |mut region| {
                coeffs[0].copy_advice(|| "coeff 0", &mut region, self.1, 0)?;
                let mut eval = coeffs[0].value().copied();
                let mut eval_cell = coeffs[0].copy_advice(|| "eval 0", &mut region, self.2, 0)?;

                for (i, coeff) in coeffs.iter().skip(1).enumerate() {
                    self.0.enable(&mut region, i + 1)?;
                    coeff.copy_advice(|| format!("coeff {}", i + 1), &mut region, self.1, i + 1)?;
                    eval = eval * x + coeff.value().copied();
                    eval_cell = region.assign_advice(
                        || format!("eval {}", i + 1),
                        self.2,
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

    use ff::FromUniformBytes;
    use halo2_proofs::{arithmetic::CurveAffine, circuit::floor_planner::V1};
    use halo2_proofs::{
        dev::{metadata, FailureLocation, MockProver, VerifyFailure},
        poly::{
            commitment::ParamsProver,
            ipa::{
                commitment::{IPACommitmentScheme, ParamsIPA},
                multiopen::{ProverIPA, VerifierIPA},
                strategy::AccumulatorStrategy,
            },
            VerificationStrategy,
        },
        transcript::{
            Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
        },
    };
    use rand_core::OsRng;

    #[derive(Clone)]
    pub(crate) struct Config {
        poly_a: PolyEval,
        x: Challenge,
    }

    impl Config {
        fn configure<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
            let poly = meta.advice_column_in(FirstPhase);
            meta.enable_equality(poly);
            let eval = meta.advice_column_in(SecondPhase);
            meta.enable_equality(eval);
            let x = meta.challenge_usable_after(FirstPhase);

            let poly_a = PolyEval::configure(meta, poly, eval, x);

            Config { poly_a, x }
        }
    }

    // Polynomial coeffs are witnessed in big endian notation
    // to make it more compatible with horners rule
    #[derive(Clone, Default)]
    struct MyCircuit<F: Field> {
        poly_a: [Value<F>; 4],
    }

    impl<F: Field> Circuit<F> for MyCircuit<F> {
        type Config = Config;
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
            let x = layouter.get_challenge(config.x);

            // Witness poly_a
            let poly_a = config.poly_a.witness(
                layouter.namespace(|| "witness poly_a"),
                config.poly_a.1,
                self.poly_a.to_vec(),
            )?;
            // poly_a evaluation
            let poly_a_eval =
                config
                    .poly_a
                    .evaluate(layouter.namespace(|| "eval poly_a"), &poly_a, x)?;

            Ok(())
        }
    }

    fn test_mock_prover<F: Ord + FromUniformBytes<64>>(
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

    fn test_prover<C: CurveAffine>(k: u32, circuit: MyCircuit<C::Scalar>, expected: bool)
    where
        C::Scalar: FromUniformBytes<64>,
    {
        let params = ParamsIPA::<C>::new(k);
        let vk = keygen_vk(&params, &circuit).unwrap();
        let pk = keygen_pk(&params, vk, &circuit).unwrap();

        let proof = {
            let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

            create_proof::<IPACommitmentScheme<C>, ProverIPA<C>, _, _, _, _>(
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

        let accepted = {
            let strategy = AccumulatorStrategy::new(&params);
            let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);

            verify_proof::<IPACommitmentScheme<C>, VerifierIPA<C>, _, _, _>(
                &params,
                pk.get_vk(),
                strategy,
                &[&[]],
                &mut transcript,
            )
            .map(|strategy| strategy.finalize())
            .unwrap_or_default()
        };

        assert_eq!(accepted, expected);
    }

    #[test]
    fn poly_eval_test() {
        use halo2curves::pasta::{EqAffine, Fp};

        const K: u32 = 5;

        let circuit = MyCircuit::<Fp> {
            poly_a: vec![4u64, 3, 2, 1]
                .iter()
                .map(|coeff| Value::known(Fp::from(*coeff)))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        };

        {
            test_mock_prover(K, circuit.clone(), Ok(()));
            test_prover::<EqAffine>(K, circuit.clone(), true);
        }
    }
}
