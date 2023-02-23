mod mimc;
mod sha256;

pub use self::{
    mimc::{mimc, MiMCDemo}, 
    sha256::{sha256, sha256_block_no_padding, get_sha256_iv, sha256_compression_function}
};

#[cfg(test)]
mod test {
    use bls12_381::Scalar;
    use hex_literal::hex;
    use rand_core::{RngCore, SeedableRng};
    use rand_xorshift::XorShiftRng;
    use crate::{
        types::{Bit, Boolean},
        functions::{sha256, get_sha256_iv, sha256_compression_function}
    };
    use bellman::{
        ConstraintSystem,
        gadgets::test::{TestConstraintSystem}
    };

    #[test]
    fn test_blank_hash() {
        let iv = get_sha256_iv();

        let mut cs = TestConstraintSystem::<Scalar>::new();
        let mut input_bits: Vec<_> = (0..512).map(|_| Boolean::Constant(false)).collect();
        input_bits[0] = Boolean::Constant(true);
        let out = sha256_compression_function(&mut cs, &input_bits, &iv).unwrap();
        let mut out = out.into_iter().flat_map(|e| e.into_bits_be());

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 0);

        let expected = hex!("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");

        for b in expected.iter() {
            for i in (0..8).rev() {
                let c = out.next().unwrap().get_value().unwrap();

                assert_eq!(c, (b >> i) & 1u8 == 1u8);
            }
        }
    }

    #[test]
    fn test_full_block() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let iv = get_sha256_iv();

        let mut cs = TestConstraintSystem::<Scalar>::new();
        let input_bits: Vec<_> = (0..512)
            .map(|i| {
                Boolean::from(
                    Bit::alloc(
                        cs.namespace(|| format!("input bit {}", i)),
                        Some(rng.next_u32() % 2 != 0),
                    )
                    .unwrap(),
                )
            })
            .collect();

        sha256_compression_function(cs.namespace(|| "sha256"), &input_bits, &iv).unwrap();

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints() - 512, 25840);
    }

    #[test]
    fn test_against_vectors() {
        use sha2::{Digest, Sha256};

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for input_len in (0..32).chain((32..256).filter(|a| a % 8 == 0)) {
            let mut h = Sha256::new();
            let data: Vec<u8> = (0..input_len).map(|_| rng.next_u32() as u8).collect();
            h.update(&data);
            let hash_result = h.finalize();

            let mut cs = TestConstraintSystem::<Scalar>::new();
            let mut input_bits = vec![];

            for (byte_i, input_byte) in data.into_iter().enumerate() {
                for bit_i in (0..8).rev() {
                    let cs = cs.namespace(|| format!("input bit {} {}", byte_i, bit_i));

                    input_bits.push(
                        Bit::alloc(cs, Some((input_byte >> bit_i) & 1u8 == 1u8))
                            .unwrap()
                            .into(),
                    );
                }
            }

            let r = sha256(&mut cs, &input_bits).unwrap();

            assert!(cs.is_satisfied());

            let mut s = hash_result
                .iter()
                .flat_map(|&byte| (0..8).rev().map(move |i| (byte >> i) & 1u8 == 1u8));

            for b in r {
                match b {
                    Boolean::Is(b) => {
                        assert!(s.next().unwrap() == b.get_value().unwrap());
                    }
                    Boolean::Not(b) => {
                        assert!(s.next().unwrap() != b.get_value().unwrap());
                    }
                    Boolean::Constant(b) => {
                        assert!(input_len == 0);
                        assert!(s.next().unwrap() == b);
                    }
                }
            }
        }
    }
}
