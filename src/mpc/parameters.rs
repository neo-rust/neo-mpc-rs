//! # zk-SNARK MPCs, made easy.
use std::io::{self, Write};

use bls12_381::{G1Affine, G2Affine};

use crate::mpc::{hash_to_g2, merge_pairs, same_ratio, HashWriter, MPCParameters};

/// Verify a contribution, given the old parameters and
/// the new parameters. Returns the hash of the contribution.
pub fn verify_contribution(before: &MPCParameters, after: &MPCParameters) -> Result<[u8; 64], ()> {
	// Transformation involves a single new object
	if after.contributions.len() != (before.contributions.len() + 1) {
		return Err(())
	}

	// None of the previous transformations should change
	if &before.contributions[..] != &after.contributions[0..before.contributions.len()] {
		return Err(())
	}

	// H/L, A/B_G1/B_G2, alpha/beta/gamma, IC, and cs_hash checks
	if before.params.h.len() != after.params.h.len()
		|| before.params.l.len() != after.params.l.len()
		|| before.params.a != after.params.a
		|| before.params.b_g1 != after.params.b_g1
		|| before.params.b_g2 != after.params.b_g2
		|| before.params.vk.alpha_g1 != after.params.vk.alpha_g1
		|| before.params.vk.beta_g1 != after.params.vk.beta_g1
		|| before.params.vk.beta_g2 != after.params.vk.beta_g2
		|| before.params.vk.gamma_g2 != after.params.vk.gamma_g2
		|| before.params.vk.ic != after.params.vk.ic
		|| &before.cs_hash[..] != &after.cs_hash[..]
	{
		return Err(())
	}

	let sink = io::sink();
	let mut sink = HashWriter::new(sink);
	sink.write_all(&before.cs_hash[..]).unwrap();

	for pubkey in &before.contributions {
		pubkey.write(&mut sink).unwrap();
	}

	let pubkey = after.contributions.last().unwrap();
	sink.write_all(pubkey.s.to_uncompressed().as_ref()).unwrap();
	sink.write_all(pubkey.s_delta.to_uncompressed().as_ref()).unwrap();

	let h = sink.into_hash();

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
	if !same_ratio((before.params.vk.delta_g1, pubkey.delta_after), (r, pubkey.r_delta)) {
		return Err(())
	}

	// Current parameters should have consistent delta in G1
	if pubkey.delta_after != after.params.vk.delta_g1 {
		return Err(())
	}

	// Current parameters should have consistent delta in G2
	if !same_ratio(
		(G1Affine::generator(), pubkey.delta_after),
		(G2Affine::generator(), after.params.vk.delta_g2),
	) {
		return Err(())
	}

	// H and L queries should be updated with delta^-1
	if !same_ratio(
		merge_pairs(&before.params.h, &after.params.h),
		(after.params.vk.delta_g2, before.params.vk.delta_g2), // reversed for inverse
	) {
		return Err(())
	}

	if !same_ratio(
		merge_pairs(&before.params.l, &after.params.l),
		(after.params.vk.delta_g2, before.params.vk.delta_g2), // reversed for inverse
	) {
		return Err(())
	}

	let sink = io::sink();
	let mut sink = HashWriter::new(sink);
	pubkey.write(&mut sink).unwrap();
	let h = sink.into_hash();
	let mut response = [0u8; 64];
	response.copy_from_slice(h.as_ref());

	Ok(response)
}

/// This is a cheap helper utility that exists purely
/// because Rust still doesn't have type-level integers
/// and so doesn't implement `PartialEq` for `[T; 64]`
pub fn contains_contribution(contributions: &[[u8; 64]], my_contribution: &[u8; 64]) -> bool {
	for contrib in contributions {
		if &contrib[..] == &my_contribution[..] {
			return true
		}
	}
	false
}
