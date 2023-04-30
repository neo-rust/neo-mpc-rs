use crate::mpc::{
	hash_to_g2, merge_pairs, same_ratio, HashWriter, KeypairAssembly, PrivateKey, PublicKey,
};
use bellman::{
	groth16::{Parameters, VerifyingKey},
	multicore::Worker,
	Circuit, ConstraintSystem, Index, SynthesisError, Variable,
};
use bls12_381::{Bls12, G1Affine, G1Projective, G2Affine, G2Projective, Scalar};
use byteorder::{BigEndian, ReadBytesExt, WriteBytesExt};
use ff::Field;
use group::{prime::PrimeCurveAffine, Group, Wnaf};
use rand_core::RngCore;
use std::{
	env,
	fs::File,
	io,
	io::{BufReader, Read, Write},
	sync::Arc,
};

/// MPC parameters are just like bellman `Parameters` except, when serialized,
/// they contain a transcript of contributions at the end, which can be verified.
#[derive(Clone)]
pub struct MPCParameters {
	pub(crate) params: Parameters<Bls12>,
	pub(crate) cs_hash: [u8; 64],
	pub(crate) contributions: Vec<PublicKey>,
}

impl PartialEq for MPCParameters {
	fn eq(&self, other: &MPCParameters) -> bool {
		self.params == other.params
			&& &self.cs_hash[..] == &other.cs_hash[..]
			&& self.contributions == other.contributions
	}
}

impl MPCParameters {
	/// Create new Groth16 parameters (compatible with bellman) for a
	/// given circuit. The resulting parameters are unsafe to use
	/// until there are contributions (see `contribute()`).
	pub fn new<C>(circuit: C) -> Result<MPCParameters, SynthesisError>
	where
		C: Circuit<Scalar>,
	{
		let mut assembly = KeypairAssembly {
			num_inputs: 0,
			num_aux: 0,
			num_constraints: 0,
			at_inputs: vec![],
			bt_inputs: vec![],
			ct_inputs: vec![],
			at_aux: vec![],
			bt_aux: vec![],
			ct_aux: vec![],
		};

		// Allocate the "one" input variable
		assembly.alloc_input(|| "", || Ok(Scalar::one()))?;

		// Synthesize the circuit.
		circuit.synthesize(&mut assembly)?;

		// Input constraints to ensure full density of IC query
		// x * 0 = 0
		for i in 0..assembly.num_inputs {
			assembly.enforce(
				|| "",
				|lc| lc + Variable::new_unchecked(Index::Input(i)),
				|lc| lc,
				|lc| lc,
			);
		}

		// Compute the size of our evaluation domain
		let mut m = 1;
		let mut exp = 0;
		while m < assembly.num_constraints {
			m *= 2;
			exp += 1;

			// Powers of Tau ceremony can't support more than 2^21
			if exp > 21 {
				return Err(SynthesisError::PolynomialDegreeTooLarge)
			}
		}

		// Try to load "phase1radix2m{}"
		let parameters = env::var("PARAMETERS_PATH").unwrap_or_else(|_e| {
			if cfg!(test) {
				format!("src/parameters/test/phase1radix2m{}", exp)
			} else {
				format!("src/parameters/production/phase1radix2m{}", exp)
			}
		});

		let f = match File::open(parameters) {
			Ok(f) => f,
			Err(e) => {
				panic!("Couldn't load phase1radix2m{}: {:?}", exp, e);
			},
		};
		let f = &mut BufReader::with_capacity(1024 * 1024, f);

		let read_g1 = |reader: &mut BufReader<File>| -> io::Result<G1Affine> {
			let mut repr = [0; 96];
			reader.read_exact(repr.as_mut())?;

			match Option::<G1Affine>::from(G1Affine::from_uncompressed_unchecked(&repr)) {
				None =>
					Err(io::Error::new(io::ErrorKind::InvalidData, "can't deserialize element")),
				Some(e) =>
					if e.is_identity().into() {
						Err(io::Error::new(io::ErrorKind::InvalidData, "point at infinity"))
					} else {
						Ok(e)
					},
			}
		};

		let read_g2 = |reader: &mut BufReader<File>| -> io::Result<G2Affine> {
			let mut repr = [0; 192];
			reader.read_exact(repr.as_mut())?;

			match Option::<G2Affine>::from(G2Affine::from_uncompressed_unchecked(&repr)) {
				None =>
					Err(io::Error::new(io::ErrorKind::InvalidData, "can't deserialize element")),
				Some(e) =>
					if e.is_identity().into() {
						Err(io::Error::new(io::ErrorKind::InvalidData, "point at infinity"))
					} else {
						Ok(e)
					},
			}
		};

		let alpha = read_g1(f)?;
		let beta_g1 = read_g1(f)?;
		let beta_g2 = read_g2(f)?;

		let mut coeffs_g1 = Vec::with_capacity(m);
		for _ in 0..m {
			coeffs_g1.push(read_g1(f)?);
		}

		let mut coeffs_g2 = Vec::with_capacity(m);
		for _ in 0..m {
			coeffs_g2.push(read_g2(f)?);
		}

		let mut alpha_coeffs_g1 = Vec::with_capacity(m);
		for _ in 0..m {
			alpha_coeffs_g1.push(read_g1(f)?);
		}

		let mut beta_coeffs_g1 = Vec::with_capacity(m);
		for _ in 0..m {
			beta_coeffs_g1.push(read_g1(f)?);
		}

		// These are `Arc` so that later it'll be easier
		// to use multiexp during QAP evaluation (which
		// requires a futures-based API)
		let coeffs_g1 = Arc::new(coeffs_g1);
		let coeffs_g2 = Arc::new(coeffs_g2);
		let alpha_coeffs_g1 = Arc::new(alpha_coeffs_g1);
		let beta_coeffs_g1 = Arc::new(beta_coeffs_g1);

		let mut h = Vec::with_capacity(m - 1);
		for _ in 0..(m - 1) {
			h.push(read_g1(f)?);
		}

		let mut ic = vec![G1Projective::identity(); assembly.num_inputs];
		let mut l = vec![G1Projective::identity(); assembly.num_aux];
		let mut a_g1 = vec![G1Projective::identity(); assembly.num_inputs + assembly.num_aux];
		let mut b_g1 = vec![G1Projective::identity(); assembly.num_inputs + assembly.num_aux];
		let mut b_g2 = vec![G2Projective::identity(); assembly.num_inputs + assembly.num_aux];

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

		let worker = Worker::new();

		// Evaluate for inputs.
		eval(
			coeffs_g1.clone(),
			coeffs_g2.clone(),
			alpha_coeffs_g1.clone(),
			beta_coeffs_g1.clone(),
			&assembly.at_inputs,
			&assembly.bt_inputs,
			&assembly.ct_inputs,
			&mut a_g1[0..assembly.num_inputs],
			&mut b_g1[0..assembly.num_inputs],
			&mut b_g2[0..assembly.num_inputs],
			&mut ic,
			&worker,
		);

		// Evaluate for auxiliary variables.
		eval(
			coeffs_g1.clone(),
			coeffs_g2.clone(),
			alpha_coeffs_g1.clone(),
			beta_coeffs_g1.clone(),
			&assembly.at_aux,
			&assembly.bt_aux,
			&assembly.ct_aux,
			&mut a_g1[assembly.num_inputs..],
			&mut b_g1[assembly.num_inputs..],
			&mut b_g2[assembly.num_inputs..],
			&mut l,
			&worker,
		);

		// Don't allow any elements be unconstrained, so that
		// the L query is always fully dense.
		for e in l.iter() {
			if e.is_identity().into() {
				return Err(SynthesisError::UnconstrainedVariable)
			}
		}

		let vk = VerifyingKey {
			alpha_g1: alpha,
			beta_g1,
			beta_g2,
			gamma_g2: G2Affine::generator(),
			delta_g1: G1Affine::generator(),
			delta_g2: G2Affine::generator(),
			ic: ic.into_iter().map(|e| e.into()).collect(),
		};

		let params = Parameters {
			vk,
			h: Arc::new(h),
			l: Arc::new(l.into_iter().map(|e| e.into()).collect()),

			// Filter points at infinity away from A/B queries
			a: Arc::new(
				a_g1.into_iter()
					.filter(|e| !bool::from(e.is_identity()))
					.map(|e| e.into())
					.collect(),
			),
			b_g1: Arc::new(
				b_g1.into_iter()
					.filter(|e| !bool::from(e.is_identity()))
					.map(|e| e.into())
					.collect(),
			),
			b_g2: Arc::new(
				b_g2.into_iter()
					.filter(|e| !bool::from(e.is_identity()))
					.map(|e| e.into())
					.collect(),
			),
		};

		let h = {
			let sink = io::sink();
			let mut sink = HashWriter::new(sink);

			params.write(&mut sink).unwrap();

			sink.into_hash()
		};

		let mut cs_hash = [0; 64];
		cs_hash.copy_from_slice(h.as_ref());

		Ok(MPCParameters { params, cs_hash, contributions: vec![] })
	}

	/// Get the underlying Groth16 `Parameters`
	pub fn get_params(&self) -> &Parameters<Bls12> {
		&self.params
	}

	/// Compute a keypair, given the current parameters. Keypairs
	/// cannot be reused for multiple contributions or contributions
	/// in different parameters.
	fn keypair<R: RngCore>(&self, rng: &mut R, current: &MPCParameters) -> (PublicKey, PrivateKey) {
		// Sample random delta
		let delta: Scalar = Scalar::random(&mut *rng);

		// Compute delta s-pair in G1
		let s: G1Affine = G1Projective::random(&mut *rng).into();
		let s_delta: G1Affine = (s * delta).into();

		// H(cs_hash | <previous pubkeys> | s | s_delta)
		let h = {
			let sink = io::sink();
			let mut sink = HashWriter::new(sink);

			sink.write_all(&current.cs_hash[..]).unwrap();
			for pubkey in &current.contributions {
				pubkey.write(&mut sink).unwrap();
			}
			sink.write_all(s.to_uncompressed().as_ref()).unwrap();
			sink.write_all(s_delta.to_uncompressed().as_ref()).unwrap();

			sink.into_hash()
		};

		// This avoids making a weird assumption about the hash into the
		// group.
		let mut transcript = [0; 64];
		transcript.copy_from_slice(h.as_ref());

		// Compute delta s-pair in G2
		let r: G2Affine = hash_to_g2(h.as_ref()).into();
		let r_delta = (r * delta).into();

		(
			PublicKey {
				delta_after: (current.params.vk.delta_g1 * delta).into(),
				s,
				s_delta,
				r_delta,
				transcript,
			},
			PrivateKey { delta },
		)
	}

	/// Contributes some randomness to the parameters. Only one
	/// contributor needs to be honest for the parameters to be
	/// secure.
	///
	/// This function returns a "hash" that is bound to the
	/// contribution. Contributors can use this hash to make
	/// sure their contribution is in the final parameters, by
	/// checking to see if it appears in the output of
	/// `MPCParameters::verify`.
	pub fn contribute<R: RngCore>(&mut self, rng: &mut R) -> [u8; 64] {
		// Generate a keypair
		let (pubkey, privkey) = self.keypair(rng, self);

		fn batch_exp(bases: &mut [G1Affine], coeff: Scalar) {
			let mut projective = vec![G1Projective::identity(); bases.len()];
			let cpus = num_cpus::get();
			let chunk_size = if bases.len() < cpus { 1 } else { bases.len() / cpus };

			// Perform wNAF over multiple cores, placing results into `projective`.
			let _ = crossbeam::scope(|scope| {
				for (bases, projective) in
					bases.chunks_mut(chunk_size).zip(projective.chunks_mut(chunk_size))
				{
					scope.spawn(move |_| {
						let mut wnaf = Wnaf::new();

						for (base, projective) in bases.iter_mut().zip(projective.iter_mut()) {
							*projective = wnaf.base(base.to_curve(), 1).scalar(&coeff);
						}
					});
				}
			});

			// Perform batch normalization
			crossbeam::scope(|scope| {
				for projective in projective.chunks_mut(chunk_size) {
					scope.spawn(move |_| {
						let mut affine = vec![G1Affine::identity(); projective.len()];
						G1Projective::batch_normalize(projective, &mut affine);
						projective.copy_from_slice(
							affine
								.iter()
								.map(|g| G1Projective::from(g))
								.collect::<Vec<G1Projective>>()
								.as_slice(),
						);
					});
				}
			})
			.expect("TODO: panic message");

			// Turn it all back into affine points
			for (projective, affine) in projective.iter().zip(bases.iter_mut()) {
				*affine = projective.into();
			}
		}

		let delta_inv = Option::<Scalar>::from(privkey.delta.invert()).expect("nonzero");
		let mut l = (&self.params.l[..]).to_vec();
		let mut h = (&self.params.h[..]).to_vec();
		batch_exp(&mut l, delta_inv);
		batch_exp(&mut h, delta_inv);
		self.params.l = Arc::new(l);
		self.params.h = Arc::new(h);

		self.params.vk.delta_g1 = (self.params.vk.delta_g1 * privkey.delta).into();
		self.params.vk.delta_g2 = (self.params.vk.delta_g2 * privkey.delta).into();

		self.contributions.push(pubkey.clone());

		// Calculate the hash of the public key and return it
		let sink = io::sink();
		let mut sink = HashWriter::new(sink);
		pubkey.write(&mut sink).unwrap();
		let h = sink.into_hash();
		let mut response = [0u8; 64];
		response.copy_from_slice(h.as_ref());
		response
	}

	/// Verify the correctness of the parameters, given a circuit
	/// instance. This will return all of the hashes that
	/// contributors obtained when they ran
	/// `MPCParameters::contribute`, for ensuring that contributions
	/// exist in the final parameters.
	pub fn verify<C: Circuit<Scalar>>(&self, circuit: C) -> Result<Vec<[u8; 64]>, ()> {
		let initial_params = MPCParameters::new(circuit).map_err(|_| ())?;

		// H/L will change, but should have the same length
		if initial_params.params.h.len() != self.params.h.len()
			|| initial_params.params.l.len() != self.params.l.len()
		{
			return Err(())
		}

		// A/B_G1/B_G2, alpha/beta/gamma, and IC don't change at all
		if initial_params.params.a != self.params.a
			|| initial_params.params.b_g1 != self.params.b_g1
			|| initial_params.params.b_g2 != self.params.b_g2
			|| initial_params.params.vk.alpha_g1 != self.params.vk.alpha_g1
			|| initial_params.params.vk.beta_g1 != self.params.vk.beta_g1
			|| initial_params.params.vk.beta_g2 != self.params.vk.beta_g2
			|| initial_params.params.vk.gamma_g2 != self.params.vk.gamma_g2
			|| initial_params.params.vk.ic != self.params.vk.ic
		{
			return Err(())
		}

		// cs_hash should be the same
		if &initial_params.cs_hash[..] != &self.cs_hash[..] {
			return Err(())
		}

		let sink = io::sink();
		let mut sink = HashWriter::new(sink);
		sink.write_all(&initial_params.cs_hash[..]).unwrap();

		let mut current_delta = G1Affine::generator();
		let mut result = vec![];

		for pubkey in &self.contributions {
			let mut our_sink = sink.clone();
			our_sink.write_all(pubkey.s.to_uncompressed().as_ref()).unwrap();
			our_sink.write_all(pubkey.s_delta.to_uncompressed().as_ref()).unwrap();

			pubkey.write(&mut sink).unwrap();

			let h = our_sink.into_hash();

			// The transcript must be consistent
			if &pubkey.transcript[..] != h.as_ref() {
				return Err(())
			}

			let r = hash_to_g2(h.as_ref()).into();

			// Check the signature of knowledge
			if !same_ratio((r, pubkey.r_delta), (pubkey.s, pubkey.s_delta)) {
				return Err(())
			}

			// Check the change from the old delta is consistent
			if !same_ratio((current_delta, pubkey.delta_after), (r, pubkey.r_delta)) {
				return Err(())
			}

			current_delta = pubkey.delta_after;

			let sink = io::sink();
			let mut sink = HashWriter::new(sink);
			pubkey.write(&mut sink).unwrap();
			let h = sink.into_hash();
			let mut response = [0u8; 64];
			response.copy_from_slice(h.as_ref());
			result.push(response);
		}

		// Current parameters should have consistent delta in G1
		if current_delta != self.params.vk.delta_g1 {
			return Err(())
		}

		// Current parameters should have consistent delta in G2
		if !same_ratio(
			(G1Affine::generator(), current_delta),
			(G2Affine::generator(), self.params.vk.delta_g2),
		) {
			return Err(())
		}

		// H and L queries should be updated with delta^-1
		if !same_ratio(
			merge_pairs(&initial_params.params.h, &self.params.h),
			(self.params.vk.delta_g2, G2Affine::generator()), // reversed for inverse
		) {
			return Err(())
		}

		if !same_ratio(
			merge_pairs(&initial_params.params.l, &self.params.l),
			(self.params.vk.delta_g2, G2Affine::generator()), // reversed for inverse
		) {
			return Err(())
		}

		Ok(result)
	}

	/// Serialize these parameters. The serialized parameters
	/// can be read by bellman as Groth16 `Parameters`.
	pub fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
		self.params.write(&mut writer)?;
		writer.write_all(&self.cs_hash)?;

		writer.write_u32::<BigEndian>(self.contributions.len() as u32)?;
		for pubkey in &self.contributions {
			pubkey.write(&mut writer)?;
		}

		Ok(())
	}

	/// Deserialize these parameters. If `checked` is false,
	/// we won't perform curve validity and group order
	/// checks.
	pub fn read<R: Read>(mut reader: R, checked: bool) -> io::Result<MPCParameters> {
		let params = Parameters::read(&mut reader, checked)?;

		let mut cs_hash = [0u8; 64];
		reader.read_exact(&mut cs_hash)?;

		let contributions_len = reader.read_u32::<BigEndian>()? as usize;

		let mut contributions = vec![];
		for _ in 0..contributions_len {
			contributions.push(PublicKey::read(&mut reader)?);
		}

		Ok(MPCParameters { params, cs_hash, contributions })
	}
}
