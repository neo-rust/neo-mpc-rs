//! Gadgets for performing boolean logic.
use ff::{PrimeField, PrimeFieldBits};

use bellman::{gadgets::Assignment, ConstraintSystem, LinearCombination, SynthesisError, Variable};

use super::{field_into_bits_le, Bit};

/// This is a boolean value which may be either a constant or
/// an interpretation of an `Bit`.
#[derive(Clone)]
pub enum Boolean {
	/// Existential view of the boolean variable
	Is(Bit),
	/// Negated view of the boolean variable
	Not(Bit),
	/// Constant (not an allocated variable)
	Constant(bool),
}

impl Boolean {
	pub fn is_constant(&self) -> bool {
		matches!(*self, Boolean::Constant(_))
	}

	pub fn enforce_equal<Scalar, CS>(mut cs: CS, a: &Self, b: &Self) -> Result<(), SynthesisError>
	where
		Scalar: PrimeField,
		CS: ConstraintSystem<Scalar>,
	{
		match (a, b) {
			(&Boolean::Constant(a), &Boolean::Constant(b)) =>
				if a == b {
					Ok(())
				} else {
					Err(SynthesisError::Unsatisfiable)
				},
			(&Boolean::Constant(true), a) | (a, &Boolean::Constant(true)) => {
				cs.enforce(
					|| "enforce equal to one",
					|lc| lc,
					|lc| lc,
					|lc| lc + CS::one() - &a.lc(CS::one(), Scalar::one()),
				);

				Ok(())
			},
			(&Boolean::Constant(false), a) | (a, &Boolean::Constant(false)) => {
				cs.enforce(
					|| "enforce equal to zero",
					|lc| lc,
					|lc| lc,
					|_| a.lc(CS::one(), Scalar::one()),
				);

				Ok(())
			},
			(a, b) => {
				cs.enforce(
					|| "enforce equal",
					|lc| lc,
					|lc| lc,
					|_| a.lc(CS::one(), Scalar::one()) - &b.lc(CS::one(), Scalar::one()),
				);

				Ok(())
			},
		}
	}

	pub fn get_value(&self) -> Option<bool> {
		match *self {
			Boolean::Constant(c) => Some(c),
			Boolean::Is(ref v) => v.get_value(),
			Boolean::Not(ref v) => v.get_value().map(|b| !b),
		}
	}

	pub fn lc<Scalar: PrimeField>(
		&self,
		one: Variable,
		coeff: Scalar,
	) -> LinearCombination<Scalar> {
		match *self {
			Boolean::Constant(c) =>
				if c {
					LinearCombination::<Scalar>::zero() + (coeff, one)
				} else {
					LinearCombination::<Scalar>::zero()
				},
			Boolean::Is(ref v) => LinearCombination::<Scalar>::zero() + (coeff, v.get_variable()),
			Boolean::Not(ref v) =>
				LinearCombination::<Scalar>::zero() + (coeff, one) - (coeff, v.get_variable()),
		}
	}

	/// Construct a boolean from a known constant
	pub fn constant(b: bool) -> Self {
		Boolean::Constant(b)
	}

	/// Return a negated interpretation of this boolean.
	pub fn not(&self) -> Self {
		match *self {
			Boolean::Constant(c) => Boolean::Constant(!c),
			Boolean::Is(ref v) => Boolean::Not(v.clone()),
			Boolean::Not(ref v) => Boolean::Is(v.clone()),
		}
	}

	/// Perform XOR over two boolean operands
	pub fn xor<'a, Scalar, CS>(cs: CS, a: &'a Self, b: &'a Self) -> Result<Self, SynthesisError>
	where
		Scalar: PrimeField,
		CS: ConstraintSystem<Scalar>,
	{
		match (a, b) {
			(&Boolean::Constant(false), x) | (x, &Boolean::Constant(false)) => Ok(x.clone()),
			(&Boolean::Constant(true), x) | (x, &Boolean::Constant(true)) => Ok(x.not()),
			// a XOR (NOT b) = NOT(a XOR b)
			(is @ &Boolean::Is(_), not @ &Boolean::Not(_))
			| (not @ &Boolean::Not(_), is @ &Boolean::Is(_)) => Ok(Boolean::xor(cs, is, &not.not())?.not()),
			// a XOR b = (NOT a) XOR (NOT b)
			(&Boolean::Is(ref a), &Boolean::Is(ref b))
			| (&Boolean::Not(ref a), &Boolean::Not(ref b)) => Ok(Boolean::Is(Bit::xor(cs, a, b)?)),
		}
	}

	/// Perform AND over two boolean operands
	pub fn and<'a, Scalar, CS>(cs: CS, a: &'a Self, b: &'a Self) -> Result<Self, SynthesisError>
	where
		Scalar: PrimeField,
		CS: ConstraintSystem<Scalar>,
	{
		match (a, b) {
			// false AND x is always false
			(&Boolean::Constant(false), _) | (_, &Boolean::Constant(false)) =>
				Ok(Boolean::Constant(false)),
			// true AND x is always x
			(&Boolean::Constant(true), x) | (x, &Boolean::Constant(true)) => Ok(x.clone()),
			// a AND (NOT b)
			(&Boolean::Is(ref is), &Boolean::Not(ref not))
			| (&Boolean::Not(ref not), &Boolean::Is(ref is)) => Ok(Boolean::Is(Bit::and_not(cs, is, not)?)),
			// (NOT a) AND (NOT b) = a NOR b
			(&Boolean::Not(ref a), &Boolean::Not(ref b)) => Ok(Boolean::Is(Bit::nor(cs, a, b)?)),
			// a AND b
			(&Boolean::Is(ref a), &Boolean::Is(ref b)) => Ok(Boolean::Is(Bit::and(cs, a, b)?)),
		}
	}

	/// Computes (a and b) xor ((not a) and c)
	pub fn sha256_ch<'a, Scalar, CS>(
		mut cs: CS,
		a: &'a Self,
		b: &'a Self,
		c: &'a Self,
	) -> Result<Self, SynthesisError>
	where
		Scalar: PrimeField,
		CS: ConstraintSystem<Scalar>,
	{
		let ch_value = match (a.get_value(), b.get_value(), c.get_value()) {
			(Some(a), Some(b), Some(c)) => {
				// (a and b) xor ((not a) and c)
				Some((a & b) ^ ((!a) & c))
			},
			_ => None,
		};

		match (a, b, c) {
			(&Boolean::Constant(_), &Boolean::Constant(_), &Boolean::Constant(_)) => {
				// They're all constants, so we can just compute the value.

				return Ok(Boolean::Constant(ch_value.expect("they're all constants")))
			},
			(&Boolean::Constant(false), _, c) => {
				// If a is false
				// (a and b) xor ((not a) and c)
				// equals
				// (false) xor (c)
				// equals
				// c
				return Ok(c.clone())
			},
			(a, &Boolean::Constant(false), c) => {
				// If b is false
				// (a and b) xor ((not a) and c)
				// equals
				// ((not a) and c)
				return Boolean::and(cs, &a.not(), c)
			},
			(a, b, &Boolean::Constant(false)) => {
				// If c is false
				// (a and b) xor ((not a) and c)
				// equals
				// (a and b)
				return Boolean::and(cs, a, b)
			},
			(a, b, &Boolean::Constant(true)) => {
				// If c is true
				// (a and b) xor ((not a) and c)
				// equals
				// (a and b) xor (not a)
				// equals
				// not (a and (not b))
				return Ok(Boolean::and(cs, a, &b.not())?.not())
			},
			(a, &Boolean::Constant(true), c) => {
				// If b is true
				// (a and b) xor ((not a) and c)
				// equals
				// a xor ((not a) and c)
				// equals
				// not ((not a) and (not c))
				return Ok(Boolean::and(cs, &a.not(), &c.not())?.not())
			},
			(&Boolean::Constant(true), _, _) => {
				// If a is true
				// (a and b) xor ((not a) and c)
				// equals
				// b xor ((not a) and c)
				// So we just continue!
			},
			(&Boolean::Is(_), &Boolean::Is(_), &Boolean::Is(_))
			| (&Boolean::Is(_), &Boolean::Is(_), &Boolean::Not(_))
			| (&Boolean::Is(_), &Boolean::Not(_), &Boolean::Is(_))
			| (&Boolean::Is(_), &Boolean::Not(_), &Boolean::Not(_))
			| (&Boolean::Not(_), &Boolean::Is(_), &Boolean::Is(_))
			| (&Boolean::Not(_), &Boolean::Is(_), &Boolean::Not(_))
			| (&Boolean::Not(_), &Boolean::Not(_), &Boolean::Is(_))
			| (&Boolean::Not(_), &Boolean::Not(_), &Boolean::Not(_)) => {},
		}

		let ch = cs.alloc(
			|| "ch",
			|| ch_value.get().map(|v| if *v { Scalar::one() } else { Scalar::zero() }),
		)?;

		// a(b - c) = ch - c
		cs.enforce(
			|| "ch computation",
			|_| b.lc(CS::one(), Scalar::one()) - &c.lc(CS::one(), Scalar::one()),
			|_| a.lc(CS::one(), Scalar::one()),
			|lc| lc + ch - &c.lc(CS::one(), Scalar::one()),
		);

		Ok(Bit { value: ch_value, variable: ch }.into())
	}

	/// Computes (a and b) xor (a and c) xor (b and c)
	pub fn sha256_maj<'a, Scalar, CS>(
		mut cs: CS,
		a: &'a Self,
		b: &'a Self,
		c: &'a Self,
	) -> Result<Self, SynthesisError>
	where
		Scalar: PrimeField,
		CS: ConstraintSystem<Scalar>,
	{
		let maj_value = match (a.get_value(), b.get_value(), c.get_value()) {
			(Some(a), Some(b), Some(c)) => {
				// (a and b) xor (a and c) xor (b and c)
				Some((a & b) ^ (a & c) ^ (b & c))
			},
			_ => None,
		};

		match (a, b, c) {
			(&Boolean::Constant(_), &Boolean::Constant(_), &Boolean::Constant(_)) => {
				// They're all constants, so we can just compute the value.

				return Ok(Boolean::Constant(maj_value.expect("they're all constants")))
			},
			(&Boolean::Constant(false), b, c) => {
				// If a is false,
				// (a and b) xor (a and c) xor (b and c)
				// equals
				// (b and c)
				return Boolean::and(cs, b, c)
			},
			(a, &Boolean::Constant(false), c) => {
				// If b is false,
				// (a and b) xor (a and c) xor (b and c)
				// equals
				// (a and c)
				return Boolean::and(cs, a, c)
			},
			(a, b, &Boolean::Constant(false)) => {
				// If c is false,
				// (a and b) xor (a and c) xor (b and c)
				// equals
				// (a and b)
				return Boolean::and(cs, a, b)
			},
			(a, b, &Boolean::Constant(true)) => {
				// If c is true,
				// (a and b) xor (a and c) xor (b and c)
				// equals
				// (a and b) xor (a) xor (b)
				// equals
				// not ((not a) and (not b))
				return Ok(Boolean::and(cs, &a.not(), &b.not())?.not())
			},
			(a, &Boolean::Constant(true), c) => {
				// If b is true,
				// (a and b) xor (a and c) xor (b and c)
				// equals
				// (a) xor (a and c) xor (c)
				return Ok(Boolean::and(cs, &a.not(), &c.not())?.not())
			},
			(&Boolean::Constant(true), b, c) => {
				// If a is true,
				// (a and b) xor (a and c) xor (b and c)
				// equals
				// (b) xor (c) xor (b and c)
				return Ok(Boolean::and(cs, &b.not(), &c.not())?.not())
			},
			(&Boolean::Is(_), &Boolean::Is(_), &Boolean::Is(_))
			| (&Boolean::Is(_), &Boolean::Is(_), &Boolean::Not(_))
			| (&Boolean::Is(_), &Boolean::Not(_), &Boolean::Is(_))
			| (&Boolean::Is(_), &Boolean::Not(_), &Boolean::Not(_))
			| (&Boolean::Not(_), &Boolean::Is(_), &Boolean::Is(_))
			| (&Boolean::Not(_), &Boolean::Is(_), &Boolean::Not(_))
			| (&Boolean::Not(_), &Boolean::Not(_), &Boolean::Is(_))
			| (&Boolean::Not(_), &Boolean::Not(_), &Boolean::Not(_)) => {},
		}

		let maj = cs.alloc(
			|| "maj",
			|| maj_value.get().map(|v| if *v { Scalar::one() } else { Scalar::zero() }),
		)?;

		// ¬(¬a ∧ ¬b) ∧ ¬(¬a ∧ ¬c) ∧ ¬(¬b ∧ ¬c)
		// (1 - ((1 - a) * (1 - b))) * (1 - ((1 - a) * (1 - c))) * (1 - ((1 - b) * (1 - c)))
		// (a + b - ab) * (a + c - ac) * (b + c - bc)
		// -2abc + ab + ac + bc
		// a (-2bc + b + c) + bc
		//
		// (b) * (c) = (bc)
		// (2bc - b - c) * (a) = bc - maj

		let bc = Self::and(cs.namespace(|| "b and c"), b, c)?;

		cs.enforce(
			|| "maj computation",
			|_| {
				bc.lc(CS::one(), Scalar::one()) + &bc.lc(CS::one(), Scalar::one())
					- &b.lc(CS::one(), Scalar::one())
					- &c.lc(CS::one(), Scalar::one())
			},
			|_| a.lc(CS::one(), Scalar::one()),
			|_| bc.lc(CS::one(), Scalar::one()) - maj,
		);

		Ok(Bit { value: maj_value, variable: maj }.into())
	}
}

impl From<Bit> for Boolean {
	fn from(b: Bit) -> Boolean {
		Boolean::Is(b)
	}
}

pub fn u64_into_boolean_vec_le<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
	mut cs: CS,
	value: Option<u64>,
) -> Result<Vec<Boolean>, SynthesisError> {
	let values = match value {
		Some(ref value) => {
			let mut tmp = Vec::with_capacity(64);

			for i in 0..64 {
				tmp.push(Some(*value >> i & 1 == 1));
			}

			tmp
		},
		None => vec![None; 64],
	};

	let bits = values
		.into_iter()
		.enumerate()
		.map(|(i, b)| Ok(Boolean::from(Bit::alloc(cs.namespace(|| format!("bit {}", i)), b)?)))
		.collect::<Result<Vec<_>, SynthesisError>>()?;

	Ok(bits)
}

pub fn field_into_boolean_vec_le<
	Scalar: PrimeField,
	CS: ConstraintSystem<Scalar>,
	F: PrimeFieldBits,
>(
	cs: CS,
	value: Option<F>,
) -> Result<Vec<Boolean>, SynthesisError> {
	let v = field_into_bits_le::<Scalar, CS, F>(cs, value)?;

	Ok(v.into_iter().map(Boolean::from).collect())
}

#[cfg(test)]
mod test {
	use super::{u64_into_boolean_vec_le, Boolean};
	use crate::types::Bit;
	use bellman::{gadgets::test::TestConstraintSystem, ConstraintSystem};
	use bls12_381::Scalar;
	use ff::Field;

	#[test]
	fn test_enforce_equal() {
		for a_bool in [false, true].iter().cloned() {
			for b_bool in [false, true].iter().cloned() {
				for a_neg in [false, true].iter().cloned() {
					for b_neg in [false, true].iter().cloned() {
						{
							let mut cs = TestConstraintSystem::<Scalar>::new();

							let mut a = Boolean::from(
								Bit::alloc(cs.namespace(|| "a"), Some(a_bool)).unwrap(),
							);
							let mut b = Boolean::from(
								Bit::alloc(cs.namespace(|| "b"), Some(b_bool)).unwrap(),
							);

							if a_neg {
								a = a.not();
							}
							if b_neg {
								b = b.not();
							}

							Boolean::enforce_equal(&mut cs, &a, &b).unwrap();

							assert_eq!(cs.is_satisfied(), (a_bool ^ a_neg) == (b_bool ^ b_neg));
						}
						{
							let mut cs = TestConstraintSystem::<Scalar>::new();

							let mut a = Boolean::Constant(a_bool);
							let mut b = Boolean::from(
								Bit::alloc(cs.namespace(|| "b"), Some(b_bool)).unwrap(),
							);

							if a_neg {
								a = a.not();
							}
							if b_neg {
								b = b.not();
							}

							Boolean::enforce_equal(&mut cs, &a, &b).unwrap();

							assert_eq!(cs.is_satisfied(), (a_bool ^ a_neg) == (b_bool ^ b_neg));
						}
						{
							let mut cs = TestConstraintSystem::<Scalar>::new();

							let mut a = Boolean::from(
								Bit::alloc(cs.namespace(|| "a"), Some(a_bool)).unwrap(),
							);
							let mut b = Boolean::Constant(b_bool);

							if a_neg {
								a = a.not();
							}
							if b_neg {
								b = b.not();
							}

							Boolean::enforce_equal(&mut cs, &a, &b).unwrap();

							assert_eq!(cs.is_satisfied(), (a_bool ^ a_neg) == (b_bool ^ b_neg));
						}
						{
							let mut cs = TestConstraintSystem::<Scalar>::new();

							let mut a = Boolean::Constant(a_bool);
							let mut b = Boolean::Constant(b_bool);

							if a_neg {
								a = a.not();
							}
							if b_neg {
								b = b.not();
							}

							let result = Boolean::enforce_equal(&mut cs, &a, &b);

							if (a_bool ^ a_neg) == (b_bool ^ b_neg) {
								assert!(result.is_ok());
								assert!(cs.is_satisfied());
							} else {
								assert!(result.is_err());
							}
						}
					}
				}
			}
		}
	}

	#[test]
	fn test_boolean_negation() {
		let mut cs = TestConstraintSystem::<Scalar>::new();

		let mut b = Boolean::from(Bit::alloc(&mut cs, Some(true)).unwrap());

		match b {
			Boolean::Is(_) => {},
			_ => panic!("unexpected value"),
		}

		b = b.not();

		match b {
			Boolean::Not(_) => {},
			_ => panic!("unexpected value"),
		}

		b = b.not();

		match b {
			Boolean::Is(_) => {},
			_ => panic!("unexpected value"),
		}

		b = Boolean::constant(true);

		match b {
			Boolean::Constant(true) => {},
			_ => panic!("unexpected value"),
		}

		b = b.not();

		match b {
			Boolean::Constant(false) => {},
			_ => panic!("unexpected value"),
		}

		b = b.not();

		match b {
			Boolean::Constant(true) => {},
			_ => panic!("unexpected value"),
		}
	}

	#[derive(Copy, Clone, Debug)]
	enum OperandType {
		True,
		False,
		AllocatedTrue,
		AllocatedFalse,
		NegatedAllocatedTrue,
		NegatedAllocatedFalse,
	}

	impl OperandType {
		fn is_constant(&self) -> bool {
			match *self {
				OperandType::True => true,
				OperandType::False => true,
				OperandType::AllocatedTrue => false,
				OperandType::AllocatedFalse => false,
				OperandType::NegatedAllocatedTrue => false,
				OperandType::NegatedAllocatedFalse => false,
			}
		}

		fn val(&self) -> bool {
			match *self {
				OperandType::True => true,
				OperandType::False => false,
				OperandType::AllocatedTrue => true,
				OperandType::AllocatedFalse => false,
				OperandType::NegatedAllocatedTrue => false,
				OperandType::NegatedAllocatedFalse => true,
			}
		}
	}

	#[test]
	fn test_boolean_xor() {
		let variants = [
			OperandType::True,
			OperandType::False,
			OperandType::AllocatedTrue,
			OperandType::AllocatedFalse,
			OperandType::NegatedAllocatedTrue,
			OperandType::NegatedAllocatedFalse,
		];

		for first_operand in variants.iter().cloned() {
			for second_operand in variants.iter().cloned() {
				let mut cs = TestConstraintSystem::<Scalar>::new();

				let a;
				let b;

				{
					let mut dyn_construct = |operand, name| {
						let cs = cs.namespace(|| name);

						match operand {
							OperandType::True => Boolean::constant(true),
							OperandType::False => Boolean::constant(false),
							OperandType::AllocatedTrue =>
								Boolean::from(Bit::alloc(cs, Some(true)).unwrap()),
							OperandType::AllocatedFalse =>
								Boolean::from(Bit::alloc(cs, Some(false)).unwrap()),
							OperandType::NegatedAllocatedTrue =>
								Boolean::from(Bit::alloc(cs, Some(true)).unwrap()).not(),
							OperandType::NegatedAllocatedFalse =>
								Boolean::from(Bit::alloc(cs, Some(false)).unwrap()).not(),
						}
					};

					a = dyn_construct(first_operand, "a");
					b = dyn_construct(second_operand, "b");
				}

				let c = Boolean::xor(&mut cs, &a, &b).unwrap();

				assert!(cs.is_satisfied());

				match (first_operand, second_operand, c) {
					(OperandType::True, OperandType::True, Boolean::Constant(false)) => {},
					(OperandType::True, OperandType::False, Boolean::Constant(true)) => {},
					(OperandType::True, OperandType::AllocatedTrue, Boolean::Not(_)) => {},
					(OperandType::True, OperandType::AllocatedFalse, Boolean::Not(_)) => {},
					(OperandType::True, OperandType::NegatedAllocatedTrue, Boolean::Is(_)) => {},
					(OperandType::True, OperandType::NegatedAllocatedFalse, Boolean::Is(_)) => {},

					(OperandType::False, OperandType::True, Boolean::Constant(true)) => {},
					(OperandType::False, OperandType::False, Boolean::Constant(false)) => {},
					(OperandType::False, OperandType::AllocatedTrue, Boolean::Is(_)) => {},
					(OperandType::False, OperandType::AllocatedFalse, Boolean::Is(_)) => {},
					(OperandType::False, OperandType::NegatedAllocatedTrue, Boolean::Not(_)) => {},
					(OperandType::False, OperandType::NegatedAllocatedFalse, Boolean::Not(_)) => {},

					(OperandType::AllocatedTrue, OperandType::True, Boolean::Not(_)) => {},
					(OperandType::AllocatedTrue, OperandType::False, Boolean::Is(_)) => {},
					(
						OperandType::AllocatedTrue,
						OperandType::AllocatedTrue,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("xor result") == Field::zero());
						assert_eq!(v.value, Some(false));
					},
					(
						OperandType::AllocatedTrue,
						OperandType::AllocatedFalse,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("xor result") == Field::one());
						assert_eq!(v.value, Some(true));
					},
					(
						OperandType::AllocatedTrue,
						OperandType::NegatedAllocatedTrue,
						Boolean::Not(ref v),
					) => {
						assert!(cs.get("xor result") == Field::zero());
						assert_eq!(v.value, Some(false));
					},
					(
						OperandType::AllocatedTrue,
						OperandType::NegatedAllocatedFalse,
						Boolean::Not(ref v),
					) => {
						assert!(cs.get("xor result") == Field::one());
						assert_eq!(v.value, Some(true));
					},

					(OperandType::AllocatedFalse, OperandType::True, Boolean::Not(_)) => {},
					(OperandType::AllocatedFalse, OperandType::False, Boolean::Is(_)) => {},
					(
						OperandType::AllocatedFalse,
						OperandType::AllocatedTrue,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("xor result") == Field::one());
						assert_eq!(v.value, Some(true));
					},
					(
						OperandType::AllocatedFalse,
						OperandType::AllocatedFalse,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("xor result") == Field::zero());
						assert_eq!(v.value, Some(false));
					},
					(
						OperandType::AllocatedFalse,
						OperandType::NegatedAllocatedTrue,
						Boolean::Not(ref v),
					) => {
						assert!(cs.get("xor result") == Field::one());
						assert_eq!(v.value, Some(true));
					},
					(
						OperandType::AllocatedFalse,
						OperandType::NegatedAllocatedFalse,
						Boolean::Not(ref v),
					) => {
						assert!(cs.get("xor result") == Field::zero());
						assert_eq!(v.value, Some(false));
					},

					(OperandType::NegatedAllocatedTrue, OperandType::True, Boolean::Is(_)) => {},
					(OperandType::NegatedAllocatedTrue, OperandType::False, Boolean::Not(_)) => {},
					(
						OperandType::NegatedAllocatedTrue,
						OperandType::AllocatedTrue,
						Boolean::Not(ref v),
					) => {
						assert!(cs.get("xor result") == Field::zero());
						assert_eq!(v.value, Some(false));
					},
					(
						OperandType::NegatedAllocatedTrue,
						OperandType::AllocatedFalse,
						Boolean::Not(ref v),
					) => {
						assert!(cs.get("xor result") == Field::one());
						assert_eq!(v.value, Some(true));
					},
					(
						OperandType::NegatedAllocatedTrue,
						OperandType::NegatedAllocatedTrue,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("xor result") == Field::zero());
						assert_eq!(v.value, Some(false));
					},
					(
						OperandType::NegatedAllocatedTrue,
						OperandType::NegatedAllocatedFalse,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("xor result") == Field::one());
						assert_eq!(v.value, Some(true));
					},

					(OperandType::NegatedAllocatedFalse, OperandType::True, Boolean::Is(_)) => {},
					(OperandType::NegatedAllocatedFalse, OperandType::False, Boolean::Not(_)) => {},
					(
						OperandType::NegatedAllocatedFalse,
						OperandType::AllocatedTrue,
						Boolean::Not(ref v),
					) => {
						assert!(cs.get("xor result") == Field::one());
						assert_eq!(v.value, Some(true));
					},
					(
						OperandType::NegatedAllocatedFalse,
						OperandType::AllocatedFalse,
						Boolean::Not(ref v),
					) => {
						assert!(cs.get("xor result") == Field::zero());
						assert_eq!(v.value, Some(false));
					},
					(
						OperandType::NegatedAllocatedFalse,
						OperandType::NegatedAllocatedTrue,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("xor result") == Field::one());
						assert_eq!(v.value, Some(true));
					},
					(
						OperandType::NegatedAllocatedFalse,
						OperandType::NegatedAllocatedFalse,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("xor result") == Field::zero());
						assert_eq!(v.value, Some(false));
					},

					_ => panic!("this should never be encountered"),
				}
			}
		}
	}

	#[test]
	fn test_boolean_and() {
		let variants = [
			OperandType::True,
			OperandType::False,
			OperandType::AllocatedTrue,
			OperandType::AllocatedFalse,
			OperandType::NegatedAllocatedTrue,
			OperandType::NegatedAllocatedFalse,
		];

		for first_operand in variants.iter().cloned() {
			for second_operand in variants.iter().cloned() {
				let mut cs = TestConstraintSystem::<Scalar>::new();

				let a;
				let b;

				{
					let mut dyn_construct = |operand, name| {
						let cs = cs.namespace(|| name);

						match operand {
							OperandType::True => Boolean::constant(true),
							OperandType::False => Boolean::constant(false),
							OperandType::AllocatedTrue =>
								Boolean::from(Bit::alloc(cs, Some(true)).unwrap()),
							OperandType::AllocatedFalse =>
								Boolean::from(Bit::alloc(cs, Some(false)).unwrap()),
							OperandType::NegatedAllocatedTrue =>
								Boolean::from(Bit::alloc(cs, Some(true)).unwrap()).not(),
							OperandType::NegatedAllocatedFalse =>
								Boolean::from(Bit::alloc(cs, Some(false)).unwrap()).not(),
						}
					};

					a = dyn_construct(first_operand, "a");
					b = dyn_construct(second_operand, "b");
				}

				let c = Boolean::and(&mut cs, &a, &b).unwrap();

				assert!(cs.is_satisfied());

				match (first_operand, second_operand, c) {
					(OperandType::True, OperandType::True, Boolean::Constant(true)) => {},
					(OperandType::True, OperandType::False, Boolean::Constant(false)) => {},
					(OperandType::True, OperandType::AllocatedTrue, Boolean::Is(_)) => {},
					(OperandType::True, OperandType::AllocatedFalse, Boolean::Is(_)) => {},
					(OperandType::True, OperandType::NegatedAllocatedTrue, Boolean::Not(_)) => {},
					(OperandType::True, OperandType::NegatedAllocatedFalse, Boolean::Not(_)) => {},

					(OperandType::False, OperandType::True, Boolean::Constant(false)) => {},
					(OperandType::False, OperandType::False, Boolean::Constant(false)) => {},
					(OperandType::False, OperandType::AllocatedTrue, Boolean::Constant(false)) => {
					},
					(OperandType::False, OperandType::AllocatedFalse, Boolean::Constant(false)) => {
					},
					(
						OperandType::False,
						OperandType::NegatedAllocatedTrue,
						Boolean::Constant(false),
					) => {},
					(
						OperandType::False,
						OperandType::NegatedAllocatedFalse,
						Boolean::Constant(false),
					) => {},

					(OperandType::AllocatedTrue, OperandType::True, Boolean::Is(_)) => {},
					(OperandType::AllocatedTrue, OperandType::False, Boolean::Constant(false)) => {
					},
					(
						OperandType::AllocatedTrue,
						OperandType::AllocatedTrue,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("and result") == Field::one());
						assert_eq!(v.value, Some(true));
					},
					(
						OperandType::AllocatedTrue,
						OperandType::AllocatedFalse,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("and result") == Field::zero());
						assert_eq!(v.value, Some(false));
					},
					(
						OperandType::AllocatedTrue,
						OperandType::NegatedAllocatedTrue,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("and not result") == Field::zero());
						assert_eq!(v.value, Some(false));
					},
					(
						OperandType::AllocatedTrue,
						OperandType::NegatedAllocatedFalse,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("and not result") == Field::one());
						assert_eq!(v.value, Some(true));
					},

					(OperandType::AllocatedFalse, OperandType::True, Boolean::Is(_)) => {},
					(OperandType::AllocatedFalse, OperandType::False, Boolean::Constant(false)) => {
					},
					(
						OperandType::AllocatedFalse,
						OperandType::AllocatedTrue,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("and result") == Field::zero());
						assert_eq!(v.value, Some(false));
					},
					(
						OperandType::AllocatedFalse,
						OperandType::AllocatedFalse,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("and result") == Field::zero());
						assert_eq!(v.value, Some(false));
					},
					(
						OperandType::AllocatedFalse,
						OperandType::NegatedAllocatedTrue,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("and not result") == Field::zero());
						assert_eq!(v.value, Some(false));
					},
					(
						OperandType::AllocatedFalse,
						OperandType::NegatedAllocatedFalse,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("and not result") == Field::zero());
						assert_eq!(v.value, Some(false));
					},

					(OperandType::NegatedAllocatedTrue, OperandType::True, Boolean::Not(_)) => {},
					(
						OperandType::NegatedAllocatedTrue,
						OperandType::False,
						Boolean::Constant(false),
					) => {},
					(
						OperandType::NegatedAllocatedTrue,
						OperandType::AllocatedTrue,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("and not result") == Field::zero());
						assert_eq!(v.value, Some(false));
					},
					(
						OperandType::NegatedAllocatedTrue,
						OperandType::AllocatedFalse,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("and not result") == Field::zero());
						assert_eq!(v.value, Some(false));
					},
					(
						OperandType::NegatedAllocatedTrue,
						OperandType::NegatedAllocatedTrue,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("nor result") == Field::zero());
						assert_eq!(v.value, Some(false));
					},
					(
						OperandType::NegatedAllocatedTrue,
						OperandType::NegatedAllocatedFalse,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("nor result") == Field::zero());
						assert_eq!(v.value, Some(false));
					},

					(OperandType::NegatedAllocatedFalse, OperandType::True, Boolean::Not(_)) => {},
					(
						OperandType::NegatedAllocatedFalse,
						OperandType::False,
						Boolean::Constant(false),
					) => {},
					(
						OperandType::NegatedAllocatedFalse,
						OperandType::AllocatedTrue,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("and not result") == Field::one());
						assert_eq!(v.value, Some(true));
					},
					(
						OperandType::NegatedAllocatedFalse,
						OperandType::AllocatedFalse,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("and not result") == Field::zero());
						assert_eq!(v.value, Some(false));
					},
					(
						OperandType::NegatedAllocatedFalse,
						OperandType::NegatedAllocatedTrue,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("nor result") == Field::zero());
						assert_eq!(v.value, Some(false));
					},
					(
						OperandType::NegatedAllocatedFalse,
						OperandType::NegatedAllocatedFalse,
						Boolean::Is(ref v),
					) => {
						assert!(cs.get("nor result") == Field::one());
						assert_eq!(v.value, Some(true));
					},

					_ => {
						panic!(
							"unexpected behavior at {:?} AND {:?}",
							first_operand, second_operand
						);
					},
				}
			}
		}
	}

	#[test]
	fn test_u64_into_boolean_vec_le() {
		let mut cs = TestConstraintSystem::<Scalar>::new();

		let bits = u64_into_boolean_vec_le(&mut cs, Some(17234652694787248421)).unwrap();

		assert!(cs.is_satisfied());

		assert_eq!(bits.len(), 64);

		assert!(bits[63].get_value().unwrap());
		assert!(bits[63 - 1].get_value().unwrap());
		assert!(bits[63 - 2].get_value().unwrap());
		assert!(!bits[63 - 3].get_value().unwrap());
		assert!(bits[63 - 4].get_value().unwrap());
		assert!(bits[63 - 5].get_value().unwrap());
		assert!(bits[63 - 20].get_value().unwrap());
		assert!(!bits[63 - 21].get_value().unwrap());
		assert!(!bits[63 - 22].get_value().unwrap());
	}

	#[test]
	fn test_boolean_sha256_ch() {
		let variants = [
			OperandType::True,
			OperandType::False,
			OperandType::AllocatedTrue,
			OperandType::AllocatedFalse,
			OperandType::NegatedAllocatedTrue,
			OperandType::NegatedAllocatedFalse,
		];

		for first_operand in variants.iter().cloned() {
			for second_operand in variants.iter().cloned() {
				for third_operand in variants.iter().cloned() {
					let mut cs = TestConstraintSystem::new();

					let a;
					let b;
					let c;

					// ch = (a and b) xor ((not a) and c)
					let expected = (first_operand.val() & second_operand.val())
						^ ((!first_operand.val()) & third_operand.val());

					{
						let mut dyn_construct = |operand, name| {
							let cs = cs.namespace(|| name);

							match operand {
								OperandType::True => Boolean::constant(true),
								OperandType::False => Boolean::constant(false),
								OperandType::AllocatedTrue =>
									Boolean::from(Bit::alloc(cs, Some(true)).unwrap()),
								OperandType::AllocatedFalse =>
									Boolean::from(Bit::alloc(cs, Some(false)).unwrap()),
								OperandType::NegatedAllocatedTrue =>
									Boolean::from(Bit::alloc(cs, Some(true)).unwrap()).not(),
								OperandType::NegatedAllocatedFalse =>
									Boolean::from(Bit::alloc(cs, Some(false)).unwrap()).not(),
							}
						};

						a = dyn_construct(first_operand, "a");
						b = dyn_construct(second_operand, "b");
						c = dyn_construct(third_operand, "c");
					}

					let maj = Boolean::sha256_ch(&mut cs, &a, &b, &c).unwrap();

					assert!(cs.is_satisfied());

					assert_eq!(maj.get_value().unwrap(), expected);

					if first_operand.is_constant()
						|| second_operand.is_constant()
						|| third_operand.is_constant()
					{
						if first_operand.is_constant()
							&& second_operand.is_constant()
							&& third_operand.is_constant()
						{
							assert_eq!(cs.num_constraints(), 0);
						}
					} else {
						assert_eq!(cs.get("ch"), {
							if expected {
								Scalar::one()
							} else {
								Scalar::zero()
							}
						});
						cs.set("ch", {
							if expected {
								Scalar::zero()
							} else {
								Scalar::one()
							}
						});
						assert_eq!(cs.which_is_unsatisfied().unwrap(), "ch computation");
					}
				}
			}
		}
	}

	#[test]
	fn test_boolean_sha256_maj() {
		let variants = [
			OperandType::True,
			OperandType::False,
			OperandType::AllocatedTrue,
			OperandType::AllocatedFalse,
			OperandType::NegatedAllocatedTrue,
			OperandType::NegatedAllocatedFalse,
		];

		for first_operand in variants.iter().cloned() {
			for second_operand in variants.iter().cloned() {
				for third_operand in variants.iter().cloned() {
					let mut cs = TestConstraintSystem::new();

					let a;
					let b;
					let c;

					// maj = (a and b) xor (a and c) xor (b and c)
					let expected = (first_operand.val() & second_operand.val())
						^ (first_operand.val() & third_operand.val())
						^ (second_operand.val() & third_operand.val());

					{
						let mut dyn_construct = |operand, name| {
							let cs = cs.namespace(|| name);

							match operand {
								OperandType::True => Boolean::constant(true),
								OperandType::False => Boolean::constant(false),
								OperandType::AllocatedTrue =>
									Boolean::from(Bit::alloc(cs, Some(true)).unwrap()),
								OperandType::AllocatedFalse =>
									Boolean::from(Bit::alloc(cs, Some(false)).unwrap()),
								OperandType::NegatedAllocatedTrue =>
									Boolean::from(Bit::alloc(cs, Some(true)).unwrap()).not(),
								OperandType::NegatedAllocatedFalse =>
									Boolean::from(Bit::alloc(cs, Some(false)).unwrap()).not(),
							}
						};

						a = dyn_construct(first_operand, "a");
						b = dyn_construct(second_operand, "b");
						c = dyn_construct(third_operand, "c");
					}

					let maj = Boolean::sha256_maj(&mut cs, &a, &b, &c).unwrap();

					assert!(cs.is_satisfied());

					assert_eq!(maj.get_value().unwrap(), expected);

					if first_operand.is_constant()
						|| second_operand.is_constant()
						|| third_operand.is_constant()
					{
						if first_operand.is_constant()
							&& second_operand.is_constant()
							&& third_operand.is_constant()
						{
							assert_eq!(cs.num_constraints(), 0);
						}
					} else {
						assert_eq!(cs.get("maj"), {
							if expected {
								Scalar::one()
							} else {
								Scalar::zero()
							}
						});
						cs.set("maj", {
							if expected {
								Scalar::zero()
							} else {
								Scalar::one()
							}
						});
						assert_eq!(cs.which_is_unsatisfied().unwrap(), "maj computation");
					}
				}
			}
		}
	}
}
