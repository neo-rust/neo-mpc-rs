extern crate rand;
extern crate pairing;
extern crate bellman;

use std::time::{Duration, Instant};
use bellman::groth16::{create_random_proof, prepare_verifying_key, Proof, verify_proof};
use pairing::bls12_381::Bls12;
use rand::thread_rng;
use and::AndDemo;

fn main() {
    // This may not be cryptographically safe, use
    // `OsRng` (for example) in production software.
    let rng = &mut thread_rng();

    // Generate the MiMC round constants
    let constants = None;

    println!("Creating parameters...");

    // Create parameters for our circuit
    let mut params = {
        let c = AndDemo::<Bls12> {
            xl: None,
            xr: None,
            constants: &constants,
        };

        phase2::MPCParameters::new(c).unwrap()
    };

    let old_params = params.clone();
    params.contribute(rng);

    let first_contrib = phase2::verify_contribution(&old_params, &params).expect("should verify");

    let old_params = params.clone();
    params.contribute(rng);

    let second_contrib = phase2::verify_contribution(&old_params, &params).expect("should verify");

    let verification_result = params.verify(AndDemo::<Bls12> {
        xl: None,
        xr: None,
        constants: &constants,
    }).unwrap();

    assert!(phase2::contains_contribution(&verification_result, &first_contrib));
    assert!(phase2::contains_contribution(&verification_result, &second_contrib));

    let params = params.get_params();

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);

    println!("Creating proofs...");

    // Let's benchmark stuff!
    const SAMPLES: u32 = 50;
    let mut total_proving = Duration::new(0, 0);
    let mut total_verifying = Duration::new(0, 0);

    // Just a place to put the proof data, so we can
    // benchmark deserialization.
    let mut proof_vec = vec![];

    for i in 0..SAMPLES {
        // Generate a random preimage and compute the image
        let flag = i % 2 == 0;
        // let xl = if flag { Scalar::from(1) } else { Scalar::from(0) };
        let image = and::<Bls12>(flag, true);

        proof_vec.truncate(0);

        let start = Instant::now();
        {
            // Create an instance of our circuit (with the
            // witness)
            let c = AndDemo {
                xl: Some(flag),
                xr: Some(true),
                constants: &Some(image),
            };

            // Create a groth16 proof with our parameters.
            let proof = create_random_proof(c, params, rng).unwrap();

            proof.write(&mut proof_vec).unwrap();
        }

        total_proving += start.elapsed();

        let start = Instant::now();
        let proof = Proof::read(&proof_vec[..]).unwrap();
        // Check the proof
        assert!(verify_proof(
            &pvk,
            &proof,
            &[image],
        ).unwrap());
        total_verifying += start.elapsed();
    }
    let proving_avg = total_proving / SAMPLES;
    let proving_avg = proving_avg.subsec_nanos() as f64 / 1_000_000_000f64
        + (proving_avg.as_secs() as f64);

    let verifying_avg = total_verifying / SAMPLES;
    let verifying_avg = verifying_avg.subsec_nanos() as f64 / 1_000_000_000f64
        + (verifying_avg.as_secs() as f64);

    println!("Average proving time: {:?} seconds", proving_avg);
    println!("Average verifying time: {:?} seconds", verifying_avg);
}