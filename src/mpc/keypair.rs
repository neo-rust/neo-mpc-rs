use bellman::{ConstraintSystem, Index, LinearCombination, SynthesisError, Variable};
use blake2_rfc::blake2b::Blake2b;
use bls12_381::{G1Affine, G2Affine, Scalar};
use ff::PrimeField;
use std::{
	io,
	io::{Read, Write},
};

/// This is our assembly structure that we'll use to synthesize the
/// circuit into a QAP.
pub struct KeypairAssembly<Scalar: PrimeField> {
	pub(crate) num_inputs: usize,
	pub(crate) num_aux: usize,
	pub(crate) num_constraints: usize,
	pub(crate) at_inputs: Vec<Vec<(Scalar, usize)>>,
	pub(crate) bt_inputs: Vec<Vec<(Scalar, usize)>>,
	pub(crate) ct_inputs: Vec<Vec<(Scalar, usize)>>,
	pub(crate) at_aux: Vec<Vec<(Scalar, usize)>>,
	pub(crate) bt_aux: Vec<Vec<(Scalar, usize)>>,
	pub(crate) ct_aux: Vec<Vec<(Scalar, usize)>>,
}

impl<Scalar: PrimeField> ConstraintSystem<Scalar> for KeypairAssembly<Scalar> {
	type Root = Self;

	fn alloc<F, A, AR>(&mut self, _: A, _: F) -> Result<Variable, SynthesisError>
	where
		F: FnOnce() -> Result<Scalar, SynthesisError>,
		A: FnOnce() -> AR,
		AR: Into<String>,
	{
		// There is no assignment, so we don't even invoke the
		// function for obtaining one.

		let index = self.num_aux;
		self.num_aux += 1;

		self.at_aux.push(vec![]);
		self.bt_aux.push(vec![]);
		self.ct_aux.push(vec![]);

		Ok(Variable::new_unchecked(Index::Aux(index)))
	}

	fn alloc_input<F, A, AR>(&mut self, _: A, _: F) -> Result<Variable, SynthesisError>
	where
		F: FnOnce() -> Result<Scalar, SynthesisError>,
		A: FnOnce() -> AR,
		AR: Into<String>,
	{
		// There is no assignment, so we don't even invoke the
		// function for obtaining one.

		let index = self.num_inputs;
		self.num_inputs += 1;

		self.at_inputs.push(vec![]);
		self.bt_inputs.push(vec![]);
		self.ct_inputs.push(vec![]);

		Ok(Variable::new_unchecked(Index::Input(index)))
	}

	fn enforce<A, AR, LA, LB, LC>(&mut self, _: A, a: LA, b: LB, c: LC)
	where
		A: FnOnce() -> AR,
		AR: Into<String>,
		LA: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
		LB: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
		LC: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
	{
		fn eval<Scalar: PrimeField>(
			l: LinearCombination<Scalar>,
			inputs: &mut [Vec<(Scalar, usize)>],
			aux: &mut [Vec<(Scalar, usize)>],
			this_constraint: usize,
		) {
			for &(var, coeff) in l.as_ref() {
				match var.get_unchecked() {
					Index::Input(id) => inputs[id].push((coeff, this_constraint)),
					Index::Aux(id) => aux[id].push((coeff, this_constraint)),
				}
			}
		}

		eval(
			a(LinearCombination::zero()),
			&mut self.at_inputs,
			&mut self.at_aux,
			self.num_constraints,
		);
		eval(
			b(LinearCombination::zero()),
			&mut self.bt_inputs,
			&mut self.bt_aux,
			self.num_constraints,
		);
		eval(
			c(LinearCombination::zero()),
			&mut self.ct_inputs,
			&mut self.ct_aux,
			self.num_constraints,
		);

		self.num_constraints += 1;
	}

	fn push_namespace<NR, N>(&mut self, _: N)
	where
		NR: Into<String>,
		N: FnOnce() -> NR,
	{
		// Do nothing; we don't care about namespaces in this context.
	}

	fn pop_namespace(&mut self) {
		// Do nothing; we don't care about namespaces in this context.
	}

	fn get_root(&mut self) -> &mut Self::Root {
		self
	}
}

/// This allows others to verify that you contributed. The hash produced
/// by `MPCParameters::contribute` is just a BLAKE2b hash of this object.
#[derive(Clone)]
pub struct PublicKey {
	/// This is the delta (in G1) after the transformation, kept so that we
	/// can check correctness of the public keys without having the entire
	/// interstitial parameters for each contribution.
	pub(crate) delta_after: G1Affine,

	/// Random element chosen by the contributor.
	pub(crate) s: G1Affine,

	/// That element, taken to the contributor's secret delta.
	pub(crate) s_delta: G1Affine,

	/// r is H(last_pubkey | s | s_delta), r_delta proves knowledge of delta
	pub(crate) r_delta: G2Affine,

	/// Hash of the transcript (used for mapping to r)
	pub(crate) transcript: [u8; 64],
}

impl PublicKey {
	pub(crate) fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
		writer.write_all(self.delta_after.to_uncompressed().as_ref())?;
		writer.write_all(self.s.to_uncompressed().as_ref())?;
		writer.write_all(self.s_delta.to_uncompressed().as_ref())?;
		writer.write_all(self.r_delta.to_uncompressed().as_ref())?;
		writer.write_all(&self.transcript)?;

		Ok(())
	}

	pub(crate) fn read<R: Read>(mut reader: R) -> io::Result<PublicKey> {
		let mut g1_repr = [0; 96];
		let mut g2_repr = [0; 192];

		reader.read_exact(g1_repr.as_mut())?;
		let delta_after = G1Affine::from_uncompressed(&g1_repr).unwrap();

		if delta_after.is_identity().into() {
			return Err(io::Error::new(io::ErrorKind::InvalidData, "point at infinity"))
		}

		reader.read_exact(g1_repr.as_mut())?;
		let s = G1Affine::from_uncompressed(&g1_repr).unwrap();

		if s.is_identity().into() {
			return Err(io::Error::new(io::ErrorKind::InvalidData, "point at infinity"))
		}

		reader.read_exact(g1_repr.as_mut())?;
		let s_delta = G1Affine::from_uncompressed(&g1_repr).unwrap();

		if s_delta.is_identity().into() {
			return Err(io::Error::new(io::ErrorKind::InvalidData, "point at infinity"))
		}

		reader.read_exact(g2_repr.as_mut())?;
		let r_delta = G2Affine::from_uncompressed(&g2_repr).unwrap();

		if r_delta.is_identity().into() {
			return Err(io::Error::new(io::ErrorKind::InvalidData, "point at infinity"))
		}

		let mut transcript = [0u8; 64];
		reader.read_exact(&mut transcript)?;

		Ok(PublicKey { delta_after, s, s_delta, r_delta, transcript })
	}
}

impl PartialEq for PublicKey {
	fn eq(&self, other: &PublicKey) -> bool {
		self.delta_after == other.delta_after
			&& self.s == other.s
			&& self.s_delta == other.s_delta
			&& self.r_delta == other.r_delta
			&& &self.transcript[..] == &other.transcript[..]
	}
}

/// This needs to be destroyed by at least one participant
/// for the final parameters to be secure.
pub struct PrivateKey {
	pub(crate) delta: Scalar,
}

/// Abstraction over a writer which hashes the data being written.
pub struct HashWriter<W: Write> {
	writer: W,
	hasher: Blake2b,
}

impl Clone for HashWriter<io::Sink> {
	fn clone(&self) -> HashWriter<io::Sink> {
		HashWriter { writer: io::sink(), hasher: self.hasher.clone() }
	}
}

impl<W: Write> HashWriter<W> {
	/// Construct a new `HashWriter` given an existing `writer` by value.
	pub fn new(writer: W) -> Self {
		HashWriter { writer, hasher: Blake2b::new(64) }
	}

	/// Destroy this writer and return the hash of what was written.
	pub fn into_hash(self) -> [u8; 64] {
		let mut tmp = [0u8; 64];
		tmp.copy_from_slice(self.hasher.finalize().as_ref());
		tmp
	}
}

impl<W: Write> Write for HashWriter<W> {
	fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
		let bytes = self.writer.write(buf)?;

		if bytes > 0 {
			self.hasher.update(&buf[0..bytes]);
		}

		Ok(bytes)
	}

	fn flush(&mut self) -> io::Result<()> {
		self.writer.flush()
	}
}
