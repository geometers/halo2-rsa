use ff::{Field, PrimeFieldBits};
use halo2_proofs::{
    circuit::{floor_planner::V1, Layouter, SimpleFloorPlanner, Value},
    plonk::{
        create_proof, keygen_pk, keygen_vk, verify_proof, Advice, Circuit, Column,
        ConstraintSystem, Error, Instance, SecondPhase,
    },
    poly::{
        commitment::ParamsProver,
        ipa::{
            commitment::{IPACommitmentScheme, ParamsIPA},
            multiopen::ProverIPA,
            strategy::SingleStrategy,
        },
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::ProverGWC,
        },
        VerificationStrategy,
    },
    transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
    },
};
use halo2curves::{
    bn256::{Bn256, Fr},
    pasta::{pallas, vesta, EqAffine, Fp},
};

use halo2_gadgets::poseidon::{
    primitives::{self as poseidon, ConstantLength, Spec},
    Hash, Pow5Chip, Pow5Config,
};
use num_bigint::BigUint;
use rand_core::OsRng;
use scroll_zkid::rsa::{Config, PKCSV15Witness};
use scroll_zkid::witness_gen::signature::sign;

use std::convert::TryInto;
use std::marker::PhantomData;

use criterion::{criterion_group, criterion_main, Criterion};

#[derive(Clone, Default)]
struct RsaCircuit<F: PrimeFieldBits> {
    witness: PKCSV15Witness<F>,
    digest: [Value<F>; 4],
}

impl<F: PrimeFieldBits> Circuit<F> for RsaCircuit<F> {
    type Config = (Config<F>, Column<Advice>);
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
        (Config::configure(meta, poly, eval, carry), poly)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let column = config.1;
        let config = config.0;
        let mut digest = vec![];
        layouter.assign_region(
            || "witness digest",
            |mut region| {
                for (i, &limb) in self.digest.iter().enumerate() {
                    let limb = region.assign_advice(|| "", column, i, || limb)?;
                    digest.push(limb);
                }
                Ok(())
            },
        )?;
        config.synthesize(layouter, &self.witness, &digest.try_into().unwrap())
    }
}

const K: u32 = 13;

fn bench_rsa(name: &str, c: &mut Criterion) {
    let params = ParamsKZG::<Bn256>::new(K);

    let empty_circuit = RsaCircuit::default();

    // Initialize the proving key
    let vk = keygen_vk(&params, &empty_circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &empty_circuit).expect("keygen_pk should not fail");

    let prover_name = name.to_string() + "-prover";

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
    let circuit = RsaCircuit::<Fr> { witness, digest };

    c.bench_function(&prover_name, |b| {
        // Create a proof
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        b.iter(|| {
            create_proof::<KZGCommitmentScheme<_>, ProverGWC<'_, _>, _, _, _, _>(
                &params,
                &pk,
                &[circuit.clone()],
                &[&[]],
                OsRng,
                &mut transcript,
            )
            .expect("proof generation should not fail");
            // let _ = transcript.finalize();
        });
    });
}

fn criterion_benchmark(c: &mut Criterion) {
    bench_rsa("hello", c);
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);