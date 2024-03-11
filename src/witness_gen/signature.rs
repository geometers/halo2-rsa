use rsa::pkcs1v15::SigningKey;
use rsa::sha2::Sha256;
use rsa::signature::{RandomizedSigner, SignatureEncoding};
use rsa::traits::PublicKeyParts;
use rsa::RsaPrivateKey;

const KEY_BITS: usize = 2048;

pub fn sign(data: &[u8]) -> (Vec<u8>, Vec<u8>) {
    let mut rng = rand_core::OsRng;

    let private_key = RsaPrivateKey::new(&mut rng, KEY_BITS).expect("failed to generate a key");
    let signing_key = SigningKey::<Sha256>::new(private_key.clone());

    let sig = signing_key.sign_with_rng(&mut rng, data);
    let pk = private_key.to_public_key();

    (pk.n().to_bytes_be(), sig.to_bytes().to_vec())
}

#[test]
fn test_rsa_signature() {
    let data = b"hello";
    println!("{:?}", sign(data));
}
