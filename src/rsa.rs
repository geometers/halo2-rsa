use ff::{Field, PrimeField, PrimeFieldBits};
use halo2_proofs::circuit::{AssignedCell, Value};
use halo2_proofs::plonk::{
    create_proof, keygen_pk, keygen_vk, verify_proof, Advice, Challenge, Circuit, Column,
    ConstraintSystem, FirstPhase, SecondPhase, Selector, ThirdPhase, VerifyingKey,
};
use halo2_proofs::poly::Rotation;
use halo2_proofs::{circuit::Layouter, plonk::Error};
use num_bigint::BigUint;

use crate::poly_eval::LoadedPoly;
use crate::witness_gen::signature::sign;
use crate::witness_gen::trace_gen::FpMulWitness;
use crate::witness_gen::utils::array_value;
use crate::{
    check_carry_to_zero, poly_eval,
    witness_gen::{trace_gen::Trace, utils::biguint_to_field},
};

const BASE: u8 = 64;
const N: usize = 32;
const TWO_N_M1: usize = 63;

// e = 65537
#[derive(Clone, Debug, Default)]
pub struct PKCSV15Witness<F: PrimeField> {
    sig: [Value<F>; N],
    n: [Value<F>; N],
    trace: [FpMulWitness<F>; 17],
}

// ab, a, b, q, n, qn_r
// check_c2z: ab - qn_r
// ab.eval = a.eval * b.eval
// qn_r.eval = q.eval * n.eval + r.eval
#[derive(Clone)]
pub struct Config<F: PrimeFieldBits> {
    poly: poly_eval::Config<16, F>,
    check_carry_to_zero_cfg: check_carry_to_zero::Config<BASE, TWO_N_M1, 16, F>,
    x: Challenge,
    mul_selector: Selector,
    minus_selector: Selector,
}

impl<F: PrimeFieldBits> Config<F> {
    pub fn generate_witness(sig: BigUint, n: BigUint) -> PKCSV15Witness<F> {
        let trace = Trace::<F>::new(n.clone());
        let trace = trace.compute_trace(sig.clone());

        PKCSV15Witness {
            sig: array_value(biguint_to_field::<F>(&sig).try_into().unwrap()),
            n: array_value(biguint_to_field::<F>(&n).try_into().unwrap()),
            trace: trace.try_into().unwrap(),
        }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        poly: Column<Advice>,
        eval: Column<Advice>,
        carry: Column<Advice>,
    ) -> Self {
        let mul_selector = meta.selector();
        let minus_selector = meta.selector();

        meta.create_gate("a * b = ab", |meta| {
            let selector = meta.query_selector(mul_selector);
            let a = meta.query_advice(eval, Rotation::prev());
            let b = meta.query_advice(eval, Rotation::cur());
            let ab = meta.query_advice(eval, Rotation::next());

            vec![selector * (a * b - ab)]
        });

        meta.create_gate("a - b = s", |meta| {
            let selector = meta.query_selector(minus_selector);
            let a = meta.query_advice(eval, Rotation::prev());
            let b = meta.query_advice(eval, Rotation::cur());
            let s = meta.query_advice(eval, Rotation::next());

            vec![selector * (a - b - s)]
        });

        // dummy for now
        let range_check = meta.advice_column();
        let table = meta.lookup_table_column();

        let x = meta.challenge_usable_after(FirstPhase);
        let poly = poly_eval::Config::configure(meta, poly, eval, x, range_check, table);
        let check_carry_to_zero_cfg =
            check_carry_to_zero::Config::configure(meta, poly.clone(), carry);

        Self {
            poly,
            check_carry_to_zero_cfg,
            x,
            mul_selector,
            minus_selector,
        }
    }

    // now we check evaluations: a * b - q*n - r = f
    fn check_evals(
        &self,
        mut layouter: impl Layouter<F>,
        a_eval: &AssignedCell<F, F>,
        b_eval: &AssignedCell<F, F>,
        q_eval: &AssignedCell<F, F>,
        r_eval: &AssignedCell<F, F>,
        f_eval: &AssignedCell<F, F>,
        n_eval: &AssignedCell<F, F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "a * b - q * n - r = f",
            |mut region| {
                self.mul_selector.enable(&mut region, 1)?;
                self.mul_selector.enable(&mut region, 4)?;

                self.minus_selector.enable(&mut region, 7)?;
                self.minus_selector.enable(&mut region, 10)?;

                a_eval.copy_advice(|| "a_eval", &mut region, self.poly.eval, 0)?;
                b_eval.copy_advice(|| "b_eval", &mut region, self.poly.eval, 1)?;
                let ab_eval = region.assign_advice(
                    || "ab",
                    self.poly.eval,
                    2,
                    || a_eval.value().copied() * b_eval.value().copied(),
                )?;

                q_eval.copy_advice(|| "q_eval", &mut region, self.poly.eval, 3)?;
                n_eval.copy_advice(|| "n_eval", &mut region, self.poly.eval, 4)?;
                let qn_eval = region.assign_advice(
                    || "qn",
                    self.poly.eval,
                    5,
                    || q_eval.value().copied() * n_eval.value().copied(),
                )?;

                ab_eval.copy_advice(|| "ab_eval", &mut region, self.poly.eval, 6)?;
                qn_eval.copy_advice(|| "qn_eval", &mut region, self.poly.eval, 7)?;
                let abqn_eval = region.assign_advice(
                    || "ab - qn",
                    self.poly.eval,
                    8,
                    || ab_eval.value().copied() - qn_eval.value().copied(),
                )?;

                abqn_eval.copy_advice(|| "ab_qn", &mut region, self.poly.eval, 9)?;
                r_eval.copy_advice(|| "r_eval", &mut region, self.poly.eval, 10)?;
                f_eval.copy_advice(|| "f_eval", &mut region, self.poly.eval, 11)?;

                Ok(())
            },
        )
    }

    // TODO: add more coments about this
    fn check_encoded_message(
        &self,
        mut layouter: impl Layouter<F>,
        r: &LoadedPoly<N, F>,
        digest: &[AssignedCell<F, F>; 4],
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "check encoded message",
            |mut region| {
                // check that first 4 limbs are mathcing digest
                for (coeff, digest) in r.coeffs[..4].iter().zip(digest.iter()) {
                    region.constrain_equal(coeff.cell(), digest.cell())?;
                }

                region.constrain_constant(r.coeffs[4].cell(), F::from(217300885422736416u64))?;
                region.constrain_constant(r.coeffs[5].cell(), F::from(938447882527703397u64))?;
                region.constrain_constant(r.coeffs[6].cell(), F::from(18446744069417742640u64))?;

                // then it has 24 2^u64 - 1
                for i in 0..24 {
                    region.constrain_constant(r.coeffs[7 + i].cell(), F::from(u64::MAX))?;
                }

                // last one is 2^49 - 1
                region.constrain_constant(r.coeffs[31].cell(), F::from(562949953421311u64))?;
                Ok(())
            },
        )
    }

    pub fn synthesize(
        &self,
        mut layouter: impl Layouter<F>,
        witness: &PKCSV15Witness<F>,
        digest: &[AssignedCell<F, F>; 4],
    ) -> Result<(), Error> {
        let x = layouter.get_challenge(self.x);

        // TODO: witness n into public column
        let n = self
            .poly
            .witness_and_evaluate::<N>(layouter.namespace(|| "n"), witness.n, x)?;
        let n_eval = n.eval;

        // Init
        let a = self
            .poly
            .witness_and_evaluate::<N>(layouter.namespace(|| "a"), witness.sig, x)?;
        let sig_eval = a.eval;

        let q = self.poly.witness_and_evaluate::<N>(
            layouter.namespace(|| "q"),
            witness.trace[0].q,
            x,
        )?;
        let mut r = self.poly.witness_and_evaluate::<N>(
            layouter.namespace(|| "r"),
            witness.trace[0].r,
            x,
        )?;
        let f = self.check_carry_to_zero_cfg.synthesize(
            layouter.namespace(|| "check f"),
            &witness.trace[0].f,
            x,
        )?;

        self.check_evals(
            layouter.namespace(|| "check evals"),
            &sig_eval,
            &sig_eval,
            &q.eval,
            &r.eval,
            &f.eval,
            &n_eval,
        )?;

        for i in 1..16 {
            let a_eval = r.eval.clone();
            let q = self.poly.witness_and_evaluate::<N>(
                layouter.namespace(|| "q"),
                witness.trace[i].q,
                x,
            )?;
            r = self.poly.witness_and_evaluate::<N>(
                layouter.namespace(|| "r"),
                witness.trace[i].r,
                x,
            )?;
            let f = self.check_carry_to_zero_cfg.synthesize(
                layouter.namespace(|| "check f"),
                &witness.trace[i].f,
                x,
            )?;

            self.check_evals(
                layouter.namespace(|| "check evals"),
                &a_eval,
                &a_eval,
                &q.eval,
                &r.eval,
                &f.eval,
                &n_eval,
            )?;
        }

        // Final mul
        let a_eval = r.eval;
        let q = self.poly.witness_and_evaluate::<N>(
            layouter.namespace(|| "q"),
            witness.trace[16].q,
            x,
        )?;
        let r = self.poly.witness_and_evaluate::<N>(
            layouter.namespace(|| "r"),
            witness.trace[16].r,
            x,
        )?;
        let f = self.poly.witness_and_evaluate::<TWO_N_M1>(
            layouter.namespace(|| "f"),
            witness.trace[16].f,
            x,
        )?;

        self.check_encoded_message(layouter.namespace(|| "check encoded message"), &r, &digest)?;

        self.check_evals(
            layouter.namespace(|| "check evals"),
            &a_eval,
            &sig_eval,
            &q.eval,
            &r.eval,
            &f.eval,
            &n_eval,
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod test_rsa {
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

    // Polynomial coeffs are witnessed in little-endian
    #[derive(Clone, Default)]
    struct MyCircuit<F: PrimeFieldBits> {
        witness: PKCSV15Witness<F>,
        digest: [Value<F>; 4],
    }

    impl<F: PrimeFieldBits> Circuit<F> for MyCircuit<F> {
        type Config = Config<F>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let poly = meta.advice_column();
            let eval = meta.advice_column_in(SecondPhase);
            let carry = meta.advice_column();
            meta.enable_equality(poly);
            meta.enable_equality(eval);
            meta.enable_equality(carry);
            Config::configure(meta, poly, eval, carry)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let mut digest = vec![];
            layouter.assign_region(
                || "witness digest",
                |mut region| {
                    for (i, &limb) in self.digest.iter().enumerate() {
                        let limb = region.assign_advice(|| "", config.poly.poly, i, || limb)?;
                        digest.push(limb);
                    }
                    Ok(())
                },
            )?;
            config.synthesize(layouter, &self.witness, &digest.try_into().unwrap())
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
    fn rsa_test() {
        use halo2curves::bn256::Fr;

        const K: u32 = 12;

        let data = b"hello";
        let (n, sig) = sign(data);
        let witness =
            Config::generate_witness(BigUint::from_bytes_be(&sig), BigUint::from_bytes_be(&n));
        let digest = [
            Value::known(Fr::from(8287805712743766052)),
            Value::known(Fr::from(1951780869528568414)),
            Value::known(Fr::from(2803555822930092702)),
            Value::known(Fr::from(3238736544897475342)),
        ];
        let circuit = MyCircuit::<Fr> { witness, digest };

        {
            test_mock_prover(K, circuit.clone(), Ok(()));
            test_prover(K, circuit.clone(), true);
        }
    }
}
