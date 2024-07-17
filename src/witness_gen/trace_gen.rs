use ff::PrimeField;
use halo2_proofs::circuit::Value;
use num_bigint::BigUint;
use num_integer::Integer;

use crate::witness_gen::{
    poly_mul::poly_mul,
    utils::{array_value, biguint_to_field},
};

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
        for &coeffs_i in coeffs.iter().take(n - 1).skip(1) {
            c_next = (c_prev + coeffs_i) * b_inv;
            assert_eq!(c_next * b, c_prev + coeffs_i);
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
                f: array_value(f_poly),
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

#[cfg(test)]
mod tests {
    use super::Trace;
    use crate::witness_gen::signature;
    use ff::{Field, PrimeField};
    use halo2curves::pasta::Fp;
    use num_bigint::BigUint;

    /// EM = 0x00 || 0x01 || PS || 0x00 || T
    fn check_trace<F: PrimeField>(r_limbs: &[F], digest: &[F; 4]) {
        // let r_limbs = r.to_u64_digits();
        assert_eq!(r_limbs.len(), 32);

        // first 4 limbs are equal to digest
        for i in 0..4 {
            assert_eq!(r_limbs[i], digest[i]);
        }

        /*
           Digest INFO for sha256 - 152 bits
           - 00110000001100010011000000001101000001100000100101100000100001100100100000000001011001010000001100000100000000100000000100000101000000000000010000100000

           we append 40 more bits to make it multiple of 64
           EMSA_PKCS1_V1_5_ENCODE outputs: b'\x00\x01' + PS + b'\x00' + digestInfo

           so our 192 bits are values 32 `1` from PS, then 0 octet and then fixed 152 bits (digest info)

           this 192 as 64 limbs give:
           [
               217300885422736416
               938447882527703397
               18446744069417742640
           ]

        */
        assert_eq!(r_limbs[4], F::from(217300885422736416u64));
        assert_eq!(r_limbs[5], F::from(938447882527703397u64));
        assert_eq!(r_limbs[6], F::from(18446744069417742640u64));

        // then it has 24 2^u64 - 1
        for i in 0..24 {
            assert_eq!(r_limbs[7 + i], F::from(u64::MAX));
        }

        // last one is 2^49 - 1
        assert_eq!(r_limbs[31], F::from(562949953421311u64));
    }

    #[test]
    fn test_check_trace() {
        let data = b"hello";
        let digest: [Fp; 4] = [
            Fp::from(8287805712743766052),
            Fp::from(1951780869528568414),
            Fp::from(2803555822930092702),
            Fp::from(3238736544897475342),
        ];
        let (n, sig) = signature::sign(data);

        let trace = Trace::<Fp>::new(BigUint::from_bytes_be(&n));
        let r = trace
            .compute_trace(BigUint::from_bytes_be(&sig))
            .last()
            .unwrap()
            .r;
        let mut r_values = [Fp::ZERO; 32];
        for (r, r_val) in r.iter().zip(r_values.iter_mut()) {
            r.map(|r| *r_val = r);
        }

        check_trace::<Fp>(&r_values, &digest);
    }
}
