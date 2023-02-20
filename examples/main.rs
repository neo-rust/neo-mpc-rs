// For randomness (during paramgen and proof generation)
use rand::thread_rng;

// Bring in some tools for using finite fields
use ff::Field;

// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use bls12_381::{Scalar};

use phase2::{
    circuit::{
        and::{and, AndDemo}, 
        mimc::{mimc, MiMCDemo}, 
        range::{range, RangeDemo},
    },
    evaluate::Evaluator
};

fn main() {
    let mut rng = thread_rng();
    // And
    let constants = None;
    let c = AndDemo::<Scalar> {
        xl: None,
        xr: None,
        constants: &constants,
    };
    let evaluator = Evaluator::new(c, &mut rng).unwrap();
    evaluator.verify_contribution(AndDemo::<Scalar> {
        xl: None,
        xr: None,
        constants: &constants,
    });
    let flag = false;
    let image = and::<Scalar>(flag, true);
    evaluator.evaluate_circuit(AndDemo {
        xl: Some(flag),
        xr: Some(true),
        constants: &Some(image),
    }, &[image], &mut rng);

    // Mimc
    const MIMC_ROUNDS: usize = 322;
    let constants = (0..MIMC_ROUNDS)
        .map(|_| Scalar::random(&mut rng))
        .collect::<Vec<_>>();
    let c = MiMCDemo::<Scalar> {
        xl: None,
        xr: None,
        constants: &constants
    };
    let evaluator = Evaluator::new(c, &mut rng).unwrap();
    evaluator.verify_contribution(MiMCDemo::<Scalar> {
        xl: None,
        xr: None,
        constants: &constants,
    });

    let xl = Scalar::random(&mut rng);
    let xr = Scalar::random(&mut rng);
    let image = mimc(xl, xr, &constants);
    evaluator.evaluate_circuit(MiMCDemo {
        xl: Some(xl),
        xr: Some(xr),
        constants: &constants,
    }, &[image], &mut rng);

    // Range
    let constants = Some([0u64.into(), 0u64.into(), 0u64.into()]);
    let c = RangeDemo::<Scalar> {
        a: Some(1u64.into()),
        w: Some(8u64.into()),
        w_array: Some(vec![0u64.into(), 0u64.into(), 0u64.into(), 1u64.into()]),
        not_all_zeros: Some(0u64.into()),
        cr_array: Some(vec![0u64.into(), 0u64.into(), 0u64.into()]),
        constants: &constants,
    };

    let evaluator = Evaluator::new(c, &mut rng).unwrap();
    evaluator.verify_contribution(RangeDemo::<Scalar> {
        a: Some(1u64.into()),
        w: Some(8u64.into()),
        w_array: Some(vec![0u64.into(), 0u64.into(), 0u64.into(), 1u64.into()]),
        not_all_zeros: Some(0u64.into()),
        cr_array: Some(vec![0u64.into(), 0u64.into(), 0u64.into()]),
        constants: &constants,
    });

    let image = range::<Scalar>(2u64.into(), 1u64.into(), 1u64.into());
    evaluator.evaluate_circuit(RangeDemo {
        a: Some(1u64.into()),
        w: Some(9u64.into()),
        w_array: Some(vec![1u64.into(), 0u64.into(), 0u64.into(), 1u64.into()]),
        not_all_zeros: Some(1u64.into()),
        cr_array: Some(vec![1u64.into(), 1u64.into(), 1u64.into()]),
        constants: &Some(image)
    }, &image, &mut rng);
}