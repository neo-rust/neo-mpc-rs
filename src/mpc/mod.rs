mod keypair;
mod mpc;
mod parameters;
mod work;

pub use self::{
	keypair::*,
	mpc::MPCParameters,
	parameters::{contains_contribution, verify_contribution},
	work::{clean_params, MPCWork},
};
use bellman::multicore::Worker;
use bls12_381::{G1Affine, G1Projective, G2Affine, G2Projective, Scalar};
use ff::Field;
use group::{prime::PrimeCurveAffine, Group, Wnaf};
use pairing::PairingCurveAffine;
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;
use std::sync::Arc;

/// Checks if pairs have the same ratio.
pub fn same_ratio<G: PairingCurveAffine>(g1: (G, G), g2: (G::Pair, G::Pair)) -> bool {
	g1.0.pairing_with(&g2.1) == g1.1.pairing_with(&g2.0)
}

/// Hashes to G2 using the first 32 bytes of `digest`. Panics if `digest` is less
/// than 32 bytes.
pub fn hash_to_g2(digest: &[u8]) -> G2Projective {
	assert!(digest.len() >= 32);

	let mut seed = [0u8; 32];

	for i in 0..8 {
		seed[i] = digest[i];
	}

	G2Projective::random(ChaCha20Rng::from_seed(seed))
}

/// Computes a random linear combination over v1/v2.
///
/// Checking that many pairs of elements are exponentiated by
/// the same `x` can be achieved (with high probability) with
/// the following technique:
///
/// Given v1 = [a, b, c] and v2 = [as, bs, cs], compute
/// (a*r1 + b*r2 + c*r3, (as)*r1 + (bs)*r2 + (cs)*r3) for some
/// random r1, r2, r3. Given (g, g^s)...
///
/// e(g, (as)*r1 + (bs)*r2 + (cs)*r3) = e(g^s, a*r1 + b*r2 + c*r3)
///
/// ... with high probability.
pub fn merge_pairs(v1: &[G1Affine], v2: &[G1Affine]) -> (G1Affine, G1Affine) {
	use rand::thread_rng;
	use std::sync::Mutex;

	assert_eq!(v1.len(), v2.len());

	let chunk = (v1.len() / num_cpus::get()) + 1;

	let s = Arc::new(Mutex::new(G1Projective::identity()));
	let sx = Arc::new(Mutex::new(G1Projective::identity()));

	crossbeam::scope(|scope| {
		for (v1, v2) in v1.chunks(chunk).zip(v2.chunks(chunk)) {
			let s = s.clone();
			let sx = sx.clone();

			scope.spawn(move |_| {
				// We do not need to be overly cautious of the RNG
				// used for this check.
				let rng = &mut thread_rng();

				let mut wnaf = Wnaf::new();
				let mut local_s = G1Projective::identity();
				let mut local_sx = G1Projective::identity();

				for (v1, v2) in v1.iter().zip(v2.iter()) {
					let rho = Scalar::random(&mut *rng);
					let mut wnaf = wnaf.scalar(&rho);
					let v1 = wnaf.base(v1.to_curve());
					let v2 = wnaf.base(v2.to_curve());

					local_s += &v1;
					local_sx += &v2;
				}

				let mut ss = s.lock().unwrap();
				*ss += &local_s;
				let mut ssx = sx.lock().unwrap();
				*ssx += &local_sx;
			});
		}
	})
	.expect("TODO: panic message");

	let s = s.lock().unwrap().to_owned().into();
	let sx = sx.lock().unwrap().to_owned().into();

	(s, sx)
}

fn eval(
	// Lagrange coefficients for tau
	coeffs_g1: Arc<Vec<G1Affine>>,
	coeffs_g2: Arc<Vec<G2Affine>>,
	alpha_coeffs_g1: Arc<Vec<G1Affine>>,
	beta_coeffs_g1: Arc<Vec<G1Affine>>,

	// QAP polynomials
	at: &[Vec<(Scalar, usize)>],
	bt: &[Vec<(Scalar, usize)>],
	ct: &[Vec<(Scalar, usize)>],

	// Resulting evaluated QAP polynomials
	a_g1: &mut [G1Projective],
	b_g1: &mut [G1Projective],
	b_g2: &mut [G2Projective],
	ext: &mut [G1Projective],

	// Worker
	worker: &Worker,
) {
	// Sanity check
	assert_eq!(a_g1.len(), at.len());
	assert_eq!(a_g1.len(), bt.len());
	assert_eq!(a_g1.len(), ct.len());
	assert_eq!(a_g1.len(), b_g1.len());
	assert_eq!(a_g1.len(), b_g2.len());
	assert_eq!(a_g1.len(), ext.len());

	// Evaluate polynomials in multiple threads
	worker.scope(a_g1.len(), |scope, chunk| {
		for ((((((a_g1, b_g1), b_g2), ext), at), bt), ct) in a_g1
			.chunks_mut(chunk)
			.zip(b_g1.chunks_mut(chunk))
			.zip(b_g2.chunks_mut(chunk))
			.zip(ext.chunks_mut(chunk))
			.zip(at.chunks(chunk))
			.zip(bt.chunks(chunk))
			.zip(ct.chunks(chunk))
		{
			let coeffs_g1 = coeffs_g1.clone();
			let coeffs_g2 = coeffs_g2.clone();
			let alpha_coeffs_g1 = alpha_coeffs_g1.clone();
			let beta_coeffs_g1 = beta_coeffs_g1.clone();

			scope.spawn(move |_| {
				for ((((((a_g1, b_g1), b_g2), ext), at), bt), ct) in a_g1
					.iter_mut()
					.zip(b_g1.iter_mut())
					.zip(b_g2.iter_mut())
					.zip(ext.iter_mut())
					.zip(at.iter())
					.zip(bt.iter())
					.zip(ct.iter())
				{
					for &(coeff, lag) in at {
						*a_g1 = a_g1.add(&(coeffs_g1[lag] * coeff));
						*ext = ext.add(&(beta_coeffs_g1[lag] * coeff));
					}

					for &(coeff, lag) in bt {
						*b_g1 = b_g1.add(&(coeffs_g1[lag] * coeff));
						*b_g2 = b_g2.add(&(coeffs_g2[lag] * coeff));
						*ext = ext.add(&(alpha_coeffs_g1[lag] * coeff));
					}

					for &(coeff, lag) in ct {
						*ext = ext.add(&(coeffs_g1[lag] * coeff));
					}
				}

				// Batch normalize
				let mut na_g1 = vec![G1Affine::identity(); a_g1.len()];
				G1Projective::batch_normalize(a_g1, &mut na_g1[..]);
				a_g1.copy_from_slice(
					na_g1
						.iter()
						.map(|g| G1Projective::from(g))
						.collect::<Vec<G1Projective>>()
						.as_slice(),
				);
				let mut nb_g1 = vec![G1Affine::identity(); b_g1.len()];
				G1Projective::batch_normalize(b_g1, &mut nb_g1[..]);
				b_g1.copy_from_slice(
					nb_g1
						.iter()
						.map(|g| G1Projective::from(g))
						.collect::<Vec<G1Projective>>()
						.as_slice(),
				);
				let mut nb_g2 = vec![G2Affine::identity(); b_g2.len()];
				G2Projective::batch_normalize(b_g2, &mut nb_g2[..]);
				b_g2.copy_from_slice(
					nb_g2
						.iter()
						.map(|g| G2Projective::from(g))
						.collect::<Vec<G2Projective>>()
						.as_slice(),
				);
				let mut next = vec![G1Affine::identity(); ext.len()];
				G1Projective::batch_normalize(ext, &mut next[..]);
				ext.copy_from_slice(
					next.iter()
						.map(|g| G1Projective::from(g))
						.collect::<Vec<G1Projective>>()
						.as_slice(),
				);
			});
		}
	});
}

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
