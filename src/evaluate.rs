// For randomness (during paramgen and proof generation)
use rand::RngCore;

// For benchmarking
use std::{
    time::{Duration, Instant}
};

// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use bls12_381::{Scalar};

// We're going to use the Groth16 proving system.
use bellman::{
    Circuit,
    SynthesisError,
    groth16::{
        Proof,
        prepare_verifying_key,
        create_random_proof,
        verify_proof
    }
};

use crate::mpc::{
    MPCParameters,
    read_params,
    writer_params,
    verify_contribution,
    contains_contribution
};

pub struct Evaluator {
    params: MPCParameters,
    my_contribution: Vec<[u8; 64]>
}

impl Evaluator {
    pub fn mpc_new<C: Circuit<Scalar>, R: RngCore>(circuit: C, rng: &mut R) -> Result<Evaluator, SynthesisError> {
        // MPC process
        println!("Creating parameters...");
        // Create parameters for our circuit
        let mut params = MPCParameters::new(circuit).unwrap();
        // File path
        let fp_phase2_paramters = [
            "init_old_phase2_paramter",
            "init_new_phase2_paramter",
            "first_phase2_paramter",
            "second_phase2_paramter"];
        let mut my_contribution = Vec::new();

        let fp_old_params = fp_phase2_paramters[0];
        let old_params = params.clone();
        writer_params(&old_params, fp_old_params);

        for index in 0..(fp_phase2_paramters.len() - 1) {
            // Before contribute create
            let fp_old_params = fp_phase2_paramters[index];
            let fp_new_params = fp_phase2_paramters[index + 1];
            params.contribute(rng);
            writer_params(&params, fp_new_params);
            // Next contribute verify
            let old_params = read_params(fp_old_params);
            let new_params = read_params(fp_new_params);
            let contrib = verify_contribution(&old_params, &new_params).expect("should verify");
            my_contribution.push(contrib);
        }

        Ok(Evaluator {
            params: params,
            my_contribution: my_contribution
        })
    }

    pub fn verify_contribution<C: Circuit<Scalar>>(&self, circuit: C) {
        let verification_result = self.params.verify(circuit).unwrap();

        for (_, item) in self.my_contribution.iter().enumerate() {
            assert!(contains_contribution(&verification_result, &item));
        }
    }

    pub fn evaluate_circuit<C: Circuit<Scalar>, R: RngCore>(&self, circuit: C, image: &[Scalar], rng: &mut R) {
        // Proof process
        let params = self.params.get_params();
        // Prepare the verification key (for proof verification)
        let pvk = prepare_verifying_key(&params.vk);
        println!("Creating proofs...");
        // Let's benchmark stuff!
        let mut proving = Duration::new(0, 0);
        let mut verifying = Duration::new(0, 0);
        // Just a place to put the proof data, so we can
        // benchmark deserialization.
        let mut proof_vec = vec![];

        // Compute the proof
        proof_vec.truncate(0);
        let start = Instant::now();
        {
            // Create a groth16 proof with our parameters.
            let proof = create_random_proof(circuit, params, rng).unwrap();
            proof.write(&mut proof_vec).unwrap();
        }
        proving += start.elapsed();

        let start = Instant::now();
        let proof = Proof::read(&proof_vec[..]).unwrap();
        // Check the proof
        assert!(verify_proof(&pvk, &proof, &image).is_ok());
        verifying += start.elapsed();

        let proving = proving.subsec_nanos() as f64 / 1_000_000_000f64
            + (proving.as_secs() as f64);
        let verifying = verifying.subsec_nanos() as f64 / 1_000_000_000f64
            + (verifying.as_secs() as f64);
        println!("Proving time: {:?} seconds", proving);
        println!("Verifying time: {:?} seconds", verifying);
    }
}