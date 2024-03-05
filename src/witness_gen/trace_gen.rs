use crate::witness_gen::utils::biguint_to_field;
use ff::PrimeField;
use num_bigint::BigUint;
use num_integer::Integer;

use super::poly_mul::poly_mul;

#[derive(Debug)]
struct FpMulWitness<F: PrimeField> {
    ab: [F; 63],
    qn: [F; 63],
    q: [F; 32],
    r: [F; 32],
}

pub(super) struct Trace<F: PrimeField> {
    n: BigUint,
    n_poly: Vec<F>,
}

impl<F: PrimeField> Trace<F> {
    pub(super) fn new(n: BigUint) -> Self {
        let n_poly = biguint_to_field(&n);
        Self { n, n_poly }
    }

    fn register_mul(&self, a: &[u32; 64], b: &[u32; 64]) -> (FpMulWitness<F>, BigUint) {
        let aa = BigUint::new(a.to_vec());
        let bb = BigUint::new(b.to_vec());

        let ab = &aa * &bb;
        let (q, r) = ab.div_rem(&self.n);

        let q_poly = biguint_to_field(&q);
        let ab_poly = poly_mul(&biguint_to_field(&aa), &biguint_to_field(&bb));
        let qn_poly = poly_mul(&q_poly, &self.n_poly);
        let r_poly = biguint_to_field(&r);

        (
            FpMulWitness::<F> {
                ab: ab_poly.try_into().unwrap(),
                qn: qn_poly.try_into().unwrap(),
                q: q_poly.try_into().unwrap(),
                r: r_poly.try_into().unwrap(),
            },
            r,
        )
    }

    pub(super) fn compute_trace(&self, sig: &[u8]) -> BigUint {
        let sig = BigUint::from_bytes_be(&sig);

        let sig_digits: [u32; 64] = sig.to_u32_digits().try_into().unwrap();

        let (_, mut r) = self.register_mul(&sig_digits, &sig_digits);

        for _ in 1..16 {
            let r_digits: [u32; 64] = r.to_u32_digits().try_into().unwrap();
            (_, r) = self.register_mul(&r_digits, &r_digits);
        }

        let (_, r) = self.register_mul(&r.to_u32_digits().try_into().unwrap(), &sig_digits);

        for limb in r.to_u64_digits() {
            println!("r_i: {}", limb);
        }

        r
    }
}

#[test]
fn test_register_mul() {
    use halo2curves::pasta::Fp;
    let data = b"hello";
    let (n, sig) = super::signature::sign(data);

    let trace = Trace::<Fp>::new(BigUint::from_bytes_be(&n));
    trace.compute_trace(&sig);
}
