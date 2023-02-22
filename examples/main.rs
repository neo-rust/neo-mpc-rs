// For randomness (during paramgen and proof generation)
use rand::thread_rng;

// Bring in some tools for using finite fields
use ff::Field;

// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use bls12_381::{Scalar};

use phase2::{
    functions::{MiMCDemo},
    mpc::{MPCWork}
};

fn main() {
    let mut rng = thread_rng();
    // Prepare circuit
    const MIMC_ROUNDS: usize = 322;
    let constants = (0..MIMC_ROUNDS)
        .map(|_| Scalar::random(&mut rng))
        .collect::<Vec<_>>();
    let c = MiMCDemo::<Scalar> {
        xl: None,
        xr: None,
        constants: &constants
    };
    // Init MPC
    let mut mpc = MPCWork::new(c).unwrap();
    // Contribute
    let mut contrib = mpc.contribute(&mut rng);
    mpc.write_params_to("parameters_0");
    for i in 0..3 {
        let mut mpc = MPCWork::read_params_from(format!("parameters_{}", i).as_str()).unwrap();
        let c = MiMCDemo::<Scalar> {
            xl: None,
            xr: None,
            constants: &constants
        };
        mpc.verify_contribution(c, contrib);
        contrib = mpc.contribute(&mut rng);
        mpc.write_params_to(format!("parameters_{}", i + 1).as_str());
    }
}