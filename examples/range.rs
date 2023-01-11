extern crate bellman;
extern crate bls12_381;
extern crate ff;
extern crate rand;
extern crate phase2;

// For randomness (during paramgen and proof generation)
use rand::thread_rng;

// For benchmarking
use std::{
    time::{Duration, Instant},
    fs::File,
};

// Bring in some tools for using finite fiels
use ff::{PrimeField};

// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use bls12_381::{Bls12, Scalar};

// We'll use these interfaces to construct our circuit.
use bellman::{Circuit, ConstraintSystem, LinearCombination, SynthesisError};

// We're going to use the Groth16 proving system.
use bellman::groth16::{
    Proof,
    prepare_verifying_key,
    create_random_proof,
    verify_proof,
};

use phase2::MPCParameters;

/// This is an implementation of Range-circuit
fn range<S: PrimeField>(b: S, less_or_equal: S, less: S) -> [S; 3] {
    let mut result = [S::zero(); 3];
    result[0] = b.into();
    result[1] = less_or_equal.into();
    result[2] = less.into();
    result
}

/// This is our demo circuit for proving knowledge of the
/// preimage of Range invocation.
struct RangeDemo<'a, S: PrimeField> {
    a: Option<S>,
    w: Option<S>,
    wArray: Option<[S; 4]>,
    not_all_zeros: Option<S>,
    crArray: Option<[S; 3]>,
    constants: &'a Option<[S; 3]>
}

/// Our demo circuit implements this `Circuit` trait which
/// is used during paramgen and proving in order to
/// synthesize the constraint system.
impl<'a, S: PrimeField> Circuit<S> for RangeDemo<'a, S> {
    fn synthesize<CS: ConstraintSystem<S>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let a_value = self.a;
        let mut a = cs.alloc(
            || "a",
            || a_value.ok_or(SynthesisError::AssignmentMissing),
        )?;
        let w_value = self.w;
        let mut w = cs.alloc(
            || "w",
            || w_value.ok_or(SynthesisError::AssignmentMissing),
        )?;
        let not_all_zeros_value = self.not_all_zeros;
        let mut not_all_zeros = cs.alloc(
            || "not_all_zeros",
            || not_all_zeros_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        let mut wArray_value = vec![];
        let wArray = self.wArray.unwrap();
        for i in 0..wArray.len(){
            let wArray_v = cs.alloc(
                || "",
                || wArray.get(i).ok_or(SynthesisError::AssignmentMissing).copied(),
            );
            wArray_value.push(wArray_v.unwrap());
        }
        let mut crArray_value = vec![];
        let crArray = self.crArray.unwrap();
        for i in 0..crArray.len() {
            let crArray_v = cs.alloc(
                || "",
                || crArray.get(i).ok_or(SynthesisError::AssignmentMissing).copied(),
            );
            crArray_value.push(crArray_v.unwrap());
        }
        let n_var = wArray_value.len() as u64;

        let constants_value = self.constants.unwrap();
        let b_value = constants_value.get(0);
        let mut b = cs.alloc_input(
            || "b",
            || b_value.ok_or(SynthesisError::AssignmentMissing).copied(),
        )?;
        let less_or_equal_value = constants_value.get(1);
        let mut less_or_equal = cs.alloc_input(
            || "less_or_equal",
            || less_or_equal_value.ok_or(SynthesisError::AssignmentMissing).copied(),
        )?;
        let less_value = constants_value.get(2);
        let mut less = cs.alloc_input(
            || "less",
            || less_value.ok_or(SynthesisError::AssignmentMissing).copied(),
        )?;

        let mv = 1 << (n_var - 1u64);
        cs.enforce(
            || "w=2^(n-1)+b-a",
            |lc| lc + w,
            |lc| lc + CS::one(),
            |lc| lc + (S::from(mv), CS::one()) + b - a,
        );

        let mut lc1 = LinearCombination::<S>::zero();
        for i in 0..wArray_value.len(){
            lc1 = lc1 + (S::from(1 << i), wArray_value[i]);
        }
        lc1 = lc1 - w;
        cs.enforce(
            || "2^0*w_0+.......-w=0",
            |_| lc1,
            |lc| lc + CS::one(),
            |lc| lc,
        );

        for i in 0..wArray_value.len() {
            cs.enforce(
                || "w_0(1-w_0)=0",
                |lc| lc + wArray_value[i],
                |lc| lc + CS::one() - wArray_value[i],
                |lc| lc,
            );
        }

        cs.enforce(
            || "w_0*1=cr_0",
            |lc| lc + wArray_value[0],
            |lc| lc + CS::one(),
            |lc| lc + crArray_value[0],
        );

        for i in 1..crArray_value.len() {
            cs.enforce(
                || "(cr_(i-1)-1)(w_i-1)=1-cr_i",
                |lc| lc + crArray_value[i - 1] - CS::one(),
                |lc| lc + wArray_value[i] - CS::one(),
                |lc| lc + CS::one() - crArray_value[i],
            );
        }

        cs.enforce(
            || "not_all_zeros*1=cr_n",
            |lc| lc + not_all_zeros,
            |lc| lc + CS::one(),
            |lc| lc + crArray_value[crArray_value.len() - 1],
        );

        cs.enforce(
            || "less_or_equal*wn=w_n",
            |lc| lc + wArray_value[wArray_value.len() - 1],
            |lc| lc + less_or_equal,
            |lc| lc + wArray_value[wArray_value.len() - 1],
        );

        cs.enforce(
            || "w_n*not_all_zeros=less",
            |lc| lc + wArray_value[wArray_value.len() - 1],
            |lc| lc + not_all_zeros,
            |lc| lc + less,
        );
        Ok(())
    }
}


fn main() {
    // MPC process
    let mut rng = thread_rng();
    let constants = Some([0u64.into(), 0u64.into(), 0u64.into()]);
    println!("Creating parameters...");
    // Create parameters for our circuit
    let mut params = {
        let c = RangeDemo::<Scalar> {
            a: Some(1u64.into()),
            w: Some(8u64.into()),
            wArray: Some([0u64.into(), 0u64.into(), 0u64.into(), 1u64.into()]),
            not_all_zeros: Some(0u64.into()),
            crArray: Some([0u64.into(), 0u64.into(), 0u64.into()]),
            constants: &constants,
        };
        //generate_random_parameters::<Bls12, _, _>(c, &mut rng).unwrap()
        phase2::MPCParameters::new(c).unwrap()
    };

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
        params.contribute(&mut rng);
        writer_params(&params, fp_new_params);
        // Next contribute verify
        let old_params = read_params(fp_old_params);
        let new_params = read_params(fp_new_params);
        let contrib = phase2::verify_contribution(&old_params, &new_params).expect("should verify");
        my_contribution.push(contrib);
    }

    let verification_result = params
        .verify(RangeDemo::<Scalar> {
            a: Some(1u64.into()),
            w: Some(8u64.into()),
            wArray: Some([0u64.into(), 0u64.into(), 0u64.into(), 1u64.into()]),
            not_all_zeros: Some(0u64.into()),
            crArray: Some([0u64.into(), 0u64.into(), 0u64.into()]),
            constants: &constants,
        }).unwrap();

    for (index,item) in my_contribution.iter().enumerate(){
        assert!(phase2::contains_contribution(&verification_result, &item));
    }

    // Proof process
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
        let image = range::<Scalar>(2u64.into(), 1u64.into(), 1u64.into());
        proof_vec.truncate(0);
        let start = Instant::now();
        {
            // Create an instance of our circuit
            let c = RangeDemo {
                a: Some(1u64.into()),
                w: Some(9u64.into()),
                wArray: Some([1u64.into(), 0u64.into(), 0u64.into(), 1u64.into()]),
                not_all_zeros: Some(1u64.into()),
                crArray: Some([1u64.into(), 1u64.into(), 1u64.into()]),
                constants: &Some(image)
            };
            // Create a groth16 proof with our parameters.
            let proof = create_random_proof(c, params, &mut rng).unwrap();
            proof.write(&mut proof_vec).unwrap();
        }
        total_proving += start.elapsed();
        let start = Instant::now();
        let proof = Proof::read(&proof_vec[..]).unwrap();
        // Check the proof
        assert!(verify_proof(&pvk, &proof, &image).is_ok());
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

fn read_params(file_path:&str)->MPCParameters{
    let mut reader = File::open(file_path).expect(format!("file:{} open failed", file_path).as_str());
    return MPCParameters::read(reader, false).expect("params read failed");
}

fn writer_params(params:&MPCParameters, file_path:&str){
    let writer = File::create(file_path).expect(format!("file:{} create failed", file_path).as_str());
    assert!(params.write(writer).is_ok());
}
