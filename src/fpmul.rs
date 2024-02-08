use crate::mul_cfgs::{MulAddConfig, MulConfig};
use ff::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Selector, VirtualCells},
    poly::Rotation,
};

#[derive(Clone)]
struct CheckCarryToZeroConfig<const BASE: u64> {
    ab: Column<Advice>,
    qn_r: Column<Advice>,
    carry: Column<Advice>,
    init_selector: Selector,
    selector: Selector,
}

impl<const BASE: u64> CheckCarryToZeroConfig<BASE> {
    fn configure<F: Field + From<u64>>(
        meta: &mut ConstraintSystem<F>,
        ab: Column<Advice>,
        qn_r: Column<Advice>,
        carry: Column<Advice>,
    ) -> Self {
        let base = F::from(BASE);
        let init_selector = meta.selector();
        let selector = meta.selector();

        let constants = meta.fixed_column();
        meta.enable_constant(constants);

        /*
            given array of coeffs in big-endian

            init_selector   selector    coeffs   carry
                  0            1         a4       c4 == 0 : (a4 + c3) == 0 * B
                  0            1         a3       c3   : (a3 + c2) = c3 * B
                  0            1         a2       c2   : (a2 + c1) = c2 * B
                  0            1         a1       c1   : (a1 + c0) = c1 * B
                  1            0         a0       c0   : a0 = c0 * B

            n: num of coeffs
            for i = 0 to n - 1
                if i == n - 1:
                    carry[i] = coeffs[i] / B => coeffs[i] = carry * B
                else:
                    carry[i] = (carry[i + 1] + coeffs[i]) / B

            assert: carry[0] := (carry[1] + coeffs[0]) / B == 0
        */

        let coeff = |meta: &mut VirtualCells<F>| {
            let ab = meta.query_advice(ab, Rotation::cur());
            let qn_r = meta.query_advice(qn_r, Rotation::cur());
            ab - qn_r
        };

        meta.create_gate("check init carry", |meta| {
            let init_selector = meta.query_selector(init_selector);
            let coeff = coeff(meta);
            let carry = meta.query_advice(carry, Rotation::cur());
            vec![init_selector * (carry * base - coeff)]
        });

        meta.create_gate("check carry", |meta| {
            let selector = meta.query_selector(selector);
            let coeff = coeff(meta);
            let carry_cur = meta.query_advice(carry, Rotation::cur());
            let carry_next = meta.query_advice(carry, Rotation::next());
            vec![selector * (carry_cur * base - (carry_next + coeff))]
        });

        Self {
            ab,
            qn_r,
            carry,
            selector,
            init_selector,
        }
    }

    fn synthesize<F: Field + From<u64>>(
        &self,
        mut layouter: impl Layouter<F>,
        ab: &[AssignedCell<F, F>],
        qn_r: &[AssignedCell<F, F>],
    ) -> Result<(), Error> {
        let base_inv = Value::known(F::from(BASE).invert().unwrap());

        /*
           init_selector   selector   coeffs           carry
                0            1         a4       c4 == 0 : (a4 + c3) == 0 * B
                0            1         a3       c3   : (a3 + c2) = c3 * B
                0            1         a2       c2   : (a2 + c1) = c2 * B
                0            1         a1       c1   : (a1 + c0) = c1 * B
                1            0         a0       c0   : a0 = c0 * B
        */

        layouter.assign_region(
            || "check carry to zero",
            |mut region| {
                assert_eq!(ab.len(), qn_r.len());
                let n = ab.len();
                let mut coeff = ab[n - 1].value().copied() - qn_r[n - 1].value().copied();
                let mut carry = coeff * base_inv;

                // enable init
                self.init_selector.enable(&mut region, n - 1)?;

                // assign ab, qn_r, carry
                ab[n - 1].copy_advice(|| "ab[n - 1]", &mut region, self.ab, n - 1)?;
                qn_r[n - 1].copy_advice(|| "qn_r[n - 1]", &mut region, self.qn_r, n - 1)?;
                region.assign_advice(|| "carry", self.carry, n - 1, || carry)?;

                for (i, (ab, qn_r)) in ab.iter().rev().skip(1).zip(qn_r.iter().rev().skip(1)).enumerate() {
                    let offset = n - 2 - i;
                    ab.copy_advice(|| format!("ab coeff {}", i), &mut region, self.ab, offset)?;
                    qn_r.copy_advice(
                        || format!("qn_r coeff {}", i),
                        &mut region,
                        self.qn_r,
                        offset,
                    )?;

                    coeff = ab.value().copied() - qn_r.value().copied();
                    carry = (coeff + carry) * base_inv;
                    
                    let carry_cell =
                        region.assign_advice(|| "carry", self.carry, offset, || carry)?;
                    if offset == 0 {
                        region.constrain_constant(carry_cell.cell(), F::ZERO)?;
                    }
                }
                for offset in 0..(n - 1) {
                    self.selector.enable(&mut region, offset)?;
                }

                Ok(())
            },
        )
    }
}

#[derive(Clone)]
struct MulConfigs {
    mul: MulConfig,
    mul_add: MulAddConfig,
}

// values_1 and values_2 need to be Phase2 columns!
impl MulConfigs {
    fn configure<F: Field>(
        meta: &mut ConstraintSystem<F>,
        values_1: Column<Advice>,
        values_2: Column<Advice>,
    ) -> Self {
        let mul = MulConfig::configure(meta, values_1, values_2);
        let mul_add = MulAddConfig::configure(meta, values_1, values_2);

        Self { mul, mul_add }
    }

    fn synthesize<F: Field>(
        &self,
        mut layouter: impl Layouter<F>,
        a: AssignedCell<F, F>,
        b: AssignedCell<F, F>,
        ab: AssignedCell<F, F>,
        q: AssignedCell<F, F>,
        n: AssignedCell<F, F>,
        r: AssignedCell<F, F>,
        qn_r: AssignedCell<F, F>,
    ) -> Result<(), Error> {
        self.mul
            .synthesize(layouter.namespace(|| "a * b == ab"), a, b, ab)?;
        self.mul_add
            .synthesize(layouter.namespace(|| "q * n + r == qn_r"), q, n, r, qn_r)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::{
        arithmetic::CurveAffine,
        circuit::floor_planner::V1,
        plonk::{
            create_proof, keygen_pk, keygen_vk, verify_proof, Challenge, Circuit, FirstPhase,
            SecondPhase,
        },
    };

    use crate::poly_eval::PolyEval;

    use super::*;

    use ff::FromUniformBytes;
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
    struct MyConfig {
        a: PolyEval,
        b: PolyEval,
        q: PolyEval,
        n: PolyEval,
        r: PolyEval,
        ab: PolyEval,
        qn_r: PolyEval,
        mul_cfgs: MulConfigs,
        x: Challenge,
        check_carry_to_zero_cfg: CheckCarryToZeroConfig<10>,
    }

    // tuples of (first_phase_col, second_phase_col)
    impl MyConfig {
        fn configure<F: Field + From<u64>>(
            meta: &mut ConstraintSystem<F>,
            a_cols: (Column<Advice>, Column<Advice>),
            b_cols: (Column<Advice>, Column<Advice>),
            q_cols: (Column<Advice>, Column<Advice>),
            n_cols: (Column<Advice>, Column<Advice>),
            r_cols: (Column<Advice>, Column<Advice>),
            ab_cols: (Column<Advice>, Column<Advice>),
            qn_r_cols: (Column<Advice>, Column<Advice>),
            evals: (Column<Advice>, Column<Advice>),
            check_carry_to_zero: (Column<Advice>, Column<Advice>, Column<Advice>),
        ) -> Self {
            let x = meta.challenge_usable_after(FirstPhase);

            let a = PolyEval::configure(meta, a_cols.0, a_cols.1, x);

            let b = PolyEval::configure(meta, b_cols.0, b_cols.1, x);

            let q = PolyEval::configure(meta, q_cols.0, q_cols.1, x);

            let n = PolyEval::configure(meta, n_cols.0, n_cols.1, x);

            let r = PolyEval::configure(meta, r_cols.0, r_cols.1, x);

            let ab = PolyEval::configure(meta, ab_cols.0, ab_cols.1, x);

            let qn_r = PolyEval::configure(meta, qn_r_cols.0, qn_r_cols.1, x);

            let mul_cfgs = MulConfigs::configure(meta, evals.0, evals.1);

            let check_carry_to_zero_cfg = CheckCarryToZeroConfig::configure(
                meta,
                check_carry_to_zero.0,
                check_carry_to_zero.1,
                check_carry_to_zero.2,
            );

            Self {
                a,
                b,
                q,
                n,
                r,
                ab,
                qn_r,
                mul_cfgs,
                x,
                check_carry_to_zero_cfg,
            }
        }
    }

    #[derive(Clone, Debug, Default)]
    struct MyCircuit<F: Field> {
        a: [Value<F>; 4],
        b: [Value<F>; 4],
        q: [Value<F>; 4],
        n: [Value<F>; 4],
        r: [Value<F>; 4],
        ab: [Value<F>; 7],
        qn_r: [Value<F>; 7],
    }

    impl<F: Field + From<u64>> Circuit<F> for MyCircuit<F> {
        type Config = MyConfig;

        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let poly_eval_cols = (
                meta.advice_column_in(FirstPhase),
                meta.advice_column_in(SecondPhase),
            );
            meta.enable_equality(poly_eval_cols.0);
            meta.enable_equality(poly_eval_cols.1);
            let eval_cols = (
                meta.advice_column_in(SecondPhase),
                meta.advice_column_in(SecondPhase),
            );
            meta.enable_equality(eval_cols.0);
            meta.enable_equality(eval_cols.1);
            let check_carry_to_zero = (
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
            );
            meta.enable_equality(check_carry_to_zero.0);
            meta.enable_equality(check_carry_to_zero.1);
            meta.enable_equality(check_carry_to_zero.2);

            Self::Config::configure(
                meta,
                poly_eval_cols,
                poly_eval_cols,
                poly_eval_cols,
                poly_eval_cols,
                poly_eval_cols,
                poly_eval_cols,
                poly_eval_cols,
                eval_cols,
                check_carry_to_zero,
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let x = layouter.get_challenge(config.x);

            // Witness poly_a
            let poly_a = config.a.witness(
                layouter.namespace(|| "witness poly_a"),
                config.a.1,
                self.a.to_vec(),
            )?;

            // poly_a evaluation
            let poly_a_eval =
                config
                    .a
                    .evaluate(layouter.namespace(|| "eval poly_a"), &poly_a, x)?;

            let poly_b = config.b.witness(
                layouter.namespace(|| "witness poly_b"),
                config.b.1,
                self.b.to_vec(),
            )?;

            // poly_b evaluation
            let poly_b_eval =
                config
                    .b
                    .evaluate(layouter.namespace(|| "eval poly_b"), &poly_b, x)?;

            let poly_q = config.q.witness(
                layouter.namespace(|| "witness poly_q"),
                config.q.1,
                self.q.to_vec(),
            )?;

            // poly_q evaluation
            let poly_q_eval =
                config
                    .q
                    .evaluate(layouter.namespace(|| "eval poly_q"), &poly_q, x)?;

            let poly_n = config.n.witness(
                layouter.namespace(|| "witness poly_n"),
                config.n.1,
                self.n.to_vec(),
            )?;

            // poly_n evaluation
            let poly_n_eval =
                config
                    .n
                    .evaluate(layouter.namespace(|| "eval poly_n"), &poly_n, x)?;

            let poly_r = config.r.witness(
                layouter.namespace(|| "witness poly_r"),
                config.r.1,
                self.r.to_vec(),
            )?;

            // poly_r evaluation
            let poly_r_eval =
                config
                    .r
                    .evaluate(layouter.namespace(|| "eval poly_r"), &poly_r, x)?;

            let poly_ab = config.ab.witness(
                layouter.namespace(|| "witness poly_ab"),
                config.ab.1,
                self.ab.to_vec(),
            )?;

            // poly_ab evaluation
            let poly_ab_eval =
                config
                    .ab
                    .evaluate(layouter.namespace(|| "eval poly_ab"), &poly_ab, x)?;

            let poly_qn_r = config.qn_r.witness(
                layouter.namespace(|| "witness poly_qn_r"),
                config.qn_r.1,
                self.qn_r.to_vec(),
            )?;

            // poly_qn_r evaluation
            let poly_qn_r_eval =
                config
                    .qn_r
                    .evaluate(layouter.namespace(|| "eval poly_qn_r"), &poly_qn_r, x)?;

            config.mul_cfgs.mul.synthesize(
                layouter.namespace(|| "a * b == ab"),
                poly_a_eval,
                poly_b_eval,
                poly_ab_eval,
            )?;

            config.mul_cfgs.mul_add.synthesize(
                layouter.namespace(|| "q * n + r = qn_r"),
                poly_q_eval,
                poly_n_eval,
                poly_r_eval,
                poly_qn_r_eval,
            )?;

            // check carry to zero on ab - qn_r
            config.check_carry_to_zero_cfg.synthesize(
                layouter.namespace(|| "ab - qn_r"),
                &poly_ab,
                &poly_qn_r,
            )?;

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
    fn fpmul_test() {
        use halo2curves::pasta::{EqAffine, Fp};

        const K: u32 = 7;

        fn array_value<const L: usize>(array: [u64; L]) -> [Value<Fp>; L] {
            array
                .iter()
                .rev()
                .map(|coeff| Value::known(Fp::from(*coeff)))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap()
        }

        let circuit = MyCircuit::<Fp> {
            a: array_value([3, 3, 3, 1]),
            b: array_value([3, 3, 3, 1]),
            q: array_value([4, 9, 2, 1]),
            n: array_value([3, 7, 3, 1]),
            r: array_value([7, 2, 2, 0]),
            ab: array_value([9, 18, 27, 24, 15, 6, 1]),
            qn_r: array_value([19, 57, 83, 48, 22, 5, 1]),
        };

        {
            test_mock_prover(K, circuit.clone(), Ok(()));
            test_prover::<EqAffine>(K, circuit.clone(), true);
        }
    }
}
