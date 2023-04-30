mod parameters;
mod work;

pub use self::{
	parameters::{contains_contribution, verify_contribution, MPCParameters},
	work::{clean_params, MPCWork},
};

#[cfg(test)]
mod test {
	use crate::{
		helpers::range::{less, range_pub},
		mpc::{clean_params, MPCWork},
	};
	use bellman::{
		groth16::{create_proof, prepare_verifying_key, verify_proof},
		Circuit, ConstraintSystem, SynthesisError,
	};
	use bls12_381::Scalar;
	use ff::PrimeField;
	use rand::thread_rng;
	use rand_core::RngCore;

	struct TestDemo {
		//private inputs
		a: Option<u8>,
		//public inputs
		b: Option<u8>,
	}

	impl<'a, S: PrimeField> Circuit<S> for TestDemo {
		fn synthesize<CS: ConstraintSystem<S>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
			let a = self.a.unwrap();
			let b = self.b.unwrap();
			less(cs, (a, false), (b, true))
		}
	}

	#[test]
	fn test_mpc_work() {
		let mut rng = thread_rng();
		// Prepare circuit
		let constants = Some(2);
		let c = TestDemo { a: Some(1), b: constants };
		// Init MPC
		let mut mpc = MPCWork::new(c).unwrap();
		// players contribute and verify
		let mut contrib = mpc.contribute(&mut rng);
		mpc.write_params_to("parameters_0");
		for i in 0..3 {
			let mut mpc_inner =
				MPCWork::read_params_from(format!("parameters_{}", i).as_str()).unwrap();
			let c = TestDemo { a: Some(1), b: constants };
			mpc_inner.verify_contribution(c, contrib);
			contrib = mpc_inner.contribute(&mut rng);
			mpc_inner.write_params_to(format!("parameters_{}", i + 1).as_str());
		}
		//use params to create proof
		let mpc = MPCWork::read_params_from(format!("parameters_{}", 3).as_str()).unwrap();
		let params = mpc.params.get_params();
		let pvk = prepare_verifying_key(&params.vk);

		println!("Creating proofs...");
		let r = Scalar::from(rng.next_u64());
		let s = Scalar::from(rng.next_u64());
		let proof = {
			let c = TestDemo { a: Some(1), b: constants };
			//create_random_proof(c, &params, &mut rng).unwrap()
			create_proof(c, &*params, r, s).unwrap()
		};
		//verify proof
		let pub_inputs_v: Vec<Scalar> = range_pub((1u8, false), (2u8, true));
		assert!(verify_proof(&pvk, &proof, &pub_inputs_v).is_ok());
		let proof_a = proof.a.to_uncompressed();
		let proof_b = proof.b.to_uncompressed();
		let proof_c = proof.c.to_uncompressed();
		println!("A Point: {:?}", proof_a);
		println!("B Point: {:?}", proof_b);
		println!("C Point: {:?}", proof_c);

		for i in 0..4 {
			clean_params(format!("parameters_{}", i).as_str());
		}
	}
}
