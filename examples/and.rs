extern crate bellman;
extern crate pairing;
extern crate rand;
extern crate phase2;

// For randomness (during paramgen and proof generation)
use rand::{thread_rng, Rng};

// For benchmarking
use std::time::{Duration, Instant};

// Bring in some tools for using pairing-friendly curves
use pairing::{
    Engine,
    Field,
};

// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use pairing::bls12_381::{
    Bls12
};

// We'll use these interfaces to construct our circuit.
use bellman::{
    Circuit,
    ConstraintSystem,
    SynthesisError
};
use bellman::domain::Scalar;

// We're going to use the Groth16 proving system.
use bellman::groth16::{
    Proof,
    prepare_verifying_key,
    create_random_proof,
    verify_proof,
};


/// This is an implementation of And-circuit, specifically a
/// variant named `LongsightF322p3` for BLS12-381.
/// See http://eprint.iacr.org/2016/492 for more
/// information about this construction.
///
/// ```
/// function LongsightF322p3(xL ⦂ Fp, xR ⦂ Fp) {
///     for i from 0 up to 321 {
///         xL, xR := xR + (xL + Ci)^3, xL
///     }
///     return xL
/// }
/// ```
fn and<E: Engine>(
    xl: bool,
    xr: bool,
) -> E::Fr
{
    if xl&&xr == true {
        E::Fr::one()
    }
    else{
        E::Fr::zero()
    }

}

/// This is our demo circuit for proving knowledge of the
/// preimage of a MiMC hash invocation.
struct AndDemo<'a, E: Engine> {
    xl: Option<bool>,
    xr: Option<bool>,
    constants: &'a Option<E::Fr>
}

/// Our demo circuit implements this `Circuit` trait which
/// is used during paramgen and proving in order to
/// synthesize the constraint system.
impl<'a, E: Engine> Circuit<E> for AndDemo<'a, E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError>
    {
        print!("xl:{:?}  , xr:{:?}  ", self.xl, self.xr);
        //format check: whether xl is a boolean value
        let xl_var = cs.alloc(
            || "xl",
            || {
                if self.xl.is_some() {
                    if self.xl.unwrap() {
                        Ok(E::Fr::one())
                    } else {
                        Ok(E::Fr::zero())
                    }
                } else {
                    Err(SynthesisError::AssignmentMissing)
                }
            },
        )?;
        //check whether xl is a boolean value
        cs.enforce(
            || "xl_boolean_constraint",
            |lc| lc + CS::one() - xl_var,
            |lc| lc + xl_var,
            |lc| lc,
        );

        //format check: whether xr is a boolean value
        let xr_var = cs.alloc(
            || "xr",
            || {
                if self.xr.is_some() {
                    if self.xr.unwrap() {
                        Ok(E::Fr::one())
                    } else {
                        Ok(E::Fr::zero())
                    }
                } else {
                    Err(SynthesisError::AssignmentMissing)
                }
            },
        )?;

        //check whether xr is a boolean value
        cs.enforce(
            || "xr_boolean_constraint",
            |lc| lc + CS::one() - xr_var,
            |lc| lc + xr_var,
            |lc| lc,
        );

        //format check: whether constant is a boolean value
        let c_var = cs.alloc_input(
            || "c",
            || {
                if self.xl.is_some() && self.xr.is_some() {
                    if self.xl.unwrap() && self.xr.unwrap() {
                        Ok(E::Fr::one())
                    } else {
                        Ok(E::Fr::zero())
                    }
                } else {
                    Err(SynthesisError::AssignmentMissing)
                }
            },
        )?;

        //check whether a is same to b
        cs.enforce(
            || "c_and_constraint",
            |lc| lc + xl_var,
            |lc| lc + xr_var,
            |lc| lc + c_var,
        );
        Ok(())
    }
}

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
            constants: &constants
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
        constants: &constants
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
        let flag=i%2==0;
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
                constants: &Some(image)
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
            &[image]
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
