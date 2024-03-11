use crate::witness_gen::utils::biguint_to_field;
use ff::PrimeField;
use halo2_proofs::circuit::Value;
use num_bigint::BigUint;
use num_integer::Integer;

use super::{poly_mul::poly_mul, utils::array_value};

#[derive(Clone, Debug)]
pub(crate) struct FpMulWitness<F: PrimeField> {
    pub(crate) q: [Value<F>; 32],
    pub(crate) r: [Value<F>; 32],
    // a*b - q*n - r
    pub(crate) f: [Value<F>; 63],
}

impl<F: PrimeField> Default for FpMulWitness<F> {
    fn default() -> Self {
        Self {
            q: [Value::unknown(); 32],
            r: [Value::unknown(); 32],
            f: [Value::unknown(); 63],
        }
    }
}

pub(crate) struct Trace<F: PrimeField> {
    n: BigUint,
    n_poly: Vec<F>,
}

impl<F: PrimeField> Trace<F> {
    pub(crate) fn new(n: BigUint) -> Self {
        let n_poly = biguint_to_field(&n);
        Self { n, n_poly }
    }

    fn zero_as_bigint(coeffs: &[F]) {
        let b = F::from_u128(1 << 64);
        let b_inv = b.invert().unwrap();

        let n = coeffs.len();

        let mut c_prev = coeffs[0] * b_inv;
        assert_eq!(c_prev * b, coeffs[0]);

        let mut c_next;
        for i in 1..=(n - 2) {
            c_next = (c_prev + coeffs[i]) * b_inv;
            assert_eq!(c_next * b, c_prev + coeffs[i]);
            c_prev = c_next;
        }

        assert_eq!(coeffs[n - 1] + c_prev, F::from(0));
    }

    fn register_mul(&self, a: &[u32; 64], b: &[u32; 64]) -> (FpMulWitness<F>, BigUint) {
        let aa = BigUint::new(a.to_vec());
        let bb = BigUint::new(b.to_vec());

        let ab = &aa * &bb;
        let (q, r) = ab.div_rem(&self.n);

        let q_poly = biguint_to_field(&q);
        let ab_poly = poly_mul(&biguint_to_field::<F>(&aa), &biguint_to_field(&bb));
        let qn_poly = poly_mul(&q_poly, &self.n_poly);
        let r_poly = biguint_to_field(&r);

        let mut f_poly = [F::ZERO; 63];
        for i in 0..63 {
            if i < 32 {
                f_poly[i] = ab_poly[i] - qn_poly[i] - r_poly[i];
            } else {
                f_poly[i] = ab_poly[i] - qn_poly[i];
            }
        }

        Self::zero_as_bigint(&f_poly);

        (
            FpMulWitness::<F> {
                q: array_value(q_poly.try_into().unwrap()),
                r: array_value(r_poly.try_into().unwrap()),
                f: array_value(f_poly.try_into().unwrap()),
            },
            r,
        )
    }

    pub(crate) fn compute_trace(&self, sig: BigUint) -> Vec<FpMulWitness<F>> {
        let mut witnesses = vec![];

        let sig_digits: [u32; 64] = sig.to_u32_digits().try_into().unwrap();

        let (witness, mut r) = self.register_mul(&sig_digits, &sig_digits);
        witnesses.push(witness);

        for _ in 1..16 {
            let r_digits: [u32; 64] = r.to_u32_digits().try_into().unwrap();
            let (witness, new_r) = self.register_mul(&r_digits, &r_digits);
            witnesses.push(witness);
            r = new_r;
        }

        let (witness, _) = self.register_mul(&r.to_u32_digits().try_into().unwrap(), &sig_digits);
        witnesses.push(witness);

        witnesses
    }
}

#[test]
fn test_register_mul() {
    use halo2curves::pasta::Fp;
    let data = b"hello";
    let (n, sig) = super::signature::sign(data);

    let trace = Trace::<Fp>::new(BigUint::from_bytes_be(&n));
    trace.compute_trace(BigUint::from_bytes_be(&sig));
}
