use num_bigint::BigUint;

/// EM = 0x00 || 0x01 || PS || 0x00 || T
pub fn check_trace(r: BigUint, digest: [u64; 4]) {
    let r_limbs = r.to_u64_digits();
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

    assert_eq!(r_limbs[4], 217300885422736416u64);
    assert_eq!(r_limbs[5], 938447882527703397u64);
    assert_eq!(r_limbs[6], 18446744069417742640u64);

    // then it has 24 2^u64 - 1
    for i in 0..24 {
        assert_eq!(r_limbs[7 + i], u64::MAX);
    }

    // last one is 2^49 - 1
    assert_eq!(r_limbs[31], 562949953421311u64);
}

#[test]
fn test_check_trace() {
    use super::trace_gen::Trace;
    use halo2curves::pasta::Fp;

    let data = b"hello";
    let digest: [u64; 4] = [
        8287805712743766052,
        1951780869528568414,
        2803555822930092702,
        3238736544897475342,
    ];
    let (n, sig) = super::signature::sign(data);

    let trace = Trace::<Fp>::new(BigUint::from_bytes_be(&n));
    let r = trace.compute_trace(&sig);

    check_trace(r, digest);
}
