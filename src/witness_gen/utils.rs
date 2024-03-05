use ff::{Field, PrimeField};
use num_bigint::BigUint;

pub fn biguint_to_field<F: PrimeField>(x: &BigUint) -> Vec<F> {
    x.to_u64_digits().iter().map(|&xi| F::from(xi)).collect()
}

pub fn field_to_biguint<F: PrimeField>(x: F) -> BigUint {
    let bytes_to_u32 = |chunk_le: &[u8]| -> u32 {
        assert!(chunk_le.len() <= 4);
        assert!(chunk_le.len() > 0);

        let mut result: u32 = 0;
        result |= chunk_le[0] as u32;

        if chunk_le.len() == 2 {
            result |= (chunk_le[1] as u32) << 8;
        } else if chunk_le.len() == 3 {
            result |= (chunk_le[1] as u32) << 8;
            result |= (chunk_le[2] as u32) << 16;
        } else {
            // len = 4
            result |= (chunk_le[1] as u32) << 8;
            result |= (chunk_le[2] as u32) << 16;
            result |= (chunk_le[3] as u32) << 24;
        }

        result
    };

    let repr = x.to_repr(); // this gives a vector of u8
    let slice: &[u8] = repr.as_ref();

    let chunks: Vec<u32> = slice.chunks(4).map(|chunk| bytes_to_u32(chunk)).collect();

    BigUint::new(chunks)
}

#[test]
fn test_biguint_field() {
    use halo2curves::pasta::Fp;

    let bigint = BigUint::from(u64::MAX);
    let field_elem = biguint_to_field::<Fp>(&bigint)[0];

    assert_eq!(bigint, field_to_biguint(field_elem));
}
