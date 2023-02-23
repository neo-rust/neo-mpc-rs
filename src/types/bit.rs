//! Gadgets for allocating bits in the circuit.
use ff::{PrimeField, PrimeFieldBits};

use bellman::{
    ConstraintSystem, SynthesisError, Variable,
    gadgets::{Assignment}
};

/// Represents a variable in the constraint system which is guaranteed
/// to be either zero or one.
#[derive(Clone)]
pub struct Bit {
    pub variable: Variable,
    pub value: Option<bool>,
}

impl Bit {
    pub fn get_value(&self) -> Option<bool> {
        self.value
    }

    pub fn get_variable(&self) -> Variable {
        self.variable
    }

    /// Allocate a variable in the constraint system which can only be a
    /// boolean value.
    pub fn alloc<Scalar, CS>(mut cs: CS, value: Option<bool>) -> Result<Self, SynthesisError>
    where
        Scalar: PrimeField,
        CS: ConstraintSystem<Scalar>,
    {
        let var = cs.alloc(
            || "boolean",
            || {
                if *value.get()? {
                    Ok(Scalar::one())
                } else {
                    Ok(Scalar::zero())
                }
            },
        )?;

        // Constrain: (1 - a) * a = 0
        // This constrains a to be either 0 or 1.
        cs.enforce(
            || "boolean constraint",
            |lc| lc + CS::one() - var,
            |lc| lc + var,
            |lc| lc,
        );

        Ok(Bit {
            variable: var,
            value,
        })
    }

    /// Performs an XOR operation over the two operands, returning
    /// an `Bit`.
    pub fn xor<Scalar, CS>(mut cs: CS, a: &Self, b: &Self) -> Result<Self, SynthesisError>
    where
        Scalar: PrimeField,
        CS: ConstraintSystem<Scalar>,
    {
        let mut result_value = None;

        let result_var = cs.alloc(
            || "xor result",
            || {
                if *a.value.get()? ^ *b.value.get()? {
                    result_value = Some(true);

                    Ok(Scalar::one())
                } else {
                    result_value = Some(false);

                    Ok(Scalar::zero())
                }
            },
        )?;

        // Constrain (a + a) * (b) = (a + b - c)
        // Given that a and b are boolean constrained, if they
        // are equal, the only solution for c is 0, and if they
        // are different, the only solution for c is 1.
        //
        // ¬(a ∧ b) ∧ ¬(¬a ∧ ¬b) = c
        // (1 - (a * b)) * (1 - ((1 - a) * (1 - b))) = c
        // (1 - ab) * (1 - (1 - a - b + ab)) = c
        // (1 - ab) * (a + b - ab) = c
        // a + b - ab - (a^2)b - (b^2)a + (a^2)(b^2) = c
        // a + b - ab - ab - ab + ab = c
        // a + b - 2ab = c
        // -2a * b = c - a - b
        // 2a * b = a + b - c
        // (a + a) * b = a + b - c
        cs.enforce(
            || "xor constraint",
            |lc| lc + a.variable + a.variable,
            |lc| lc + b.variable,
            |lc| lc + a.variable + b.variable - result_var,
        );

        Ok(Bit {
            variable: result_var,
            value: result_value,
        })
    }

    /// Performs an AND operation over the two operands, returning
    /// an `Bit`.
    pub fn and<Scalar, CS>(mut cs: CS, a: &Self, b: &Self) -> Result<Self, SynthesisError>
    where
        Scalar: PrimeField,
        CS: ConstraintSystem<Scalar>,
    {
        let mut result_value = None;

        let result_var = cs.alloc(
            || "and result",
            || {
                if *a.value.get()? & *b.value.get()? {
                    result_value = Some(true);

                    Ok(Scalar::one())
                } else {
                    result_value = Some(false);

                    Ok(Scalar::zero())
                }
            },
        )?;

        // Constrain (a) * (b) = (c), ensuring c is 1 iff
        // a AND b are both 1.
        cs.enforce(
            || "and constraint",
            |lc| lc + a.variable,
            |lc| lc + b.variable,
            |lc| lc + result_var,
        );

        Ok(Bit {
            variable: result_var,
            value: result_value,
        })
    }

    /// Calculates `a AND (NOT b)`.
    pub fn and_not<Scalar, CS>(mut cs: CS, a: &Self, b: &Self) -> Result<Self, SynthesisError>
    where
        Scalar: PrimeField,
        CS: ConstraintSystem<Scalar>,
    {
        let mut result_value = None;

        let result_var = cs.alloc(
            || "and not result",
            || {
                if *a.value.get()? & !*b.value.get()? {
                    result_value = Some(true);

                    Ok(Scalar::one())
                } else {
                    result_value = Some(false);

                    Ok(Scalar::zero())
                }
            },
        )?;

        // Constrain (a) * (1 - b) = (c), ensuring c is 1 iff
        // a is true and b is false, and otherwise c is 0.
        cs.enforce(
            || "and not constraint",
            |lc| lc + a.variable,
            |lc| lc + CS::one() - b.variable,
            |lc| lc + result_var,
        );

        Ok(Bit {
            variable: result_var,
            value: result_value,
        })
    }

    /// Calculates `(NOT a) AND (NOT b)`.
    pub fn nor<Scalar, CS>(mut cs: CS, a: &Self, b: &Self) -> Result<Self, SynthesisError>
    where
        Scalar: PrimeField,
        CS: ConstraintSystem<Scalar>,
    {
        let mut result_value = None;

        let result_var = cs.alloc(
            || "nor result",
            || {
                if !*a.value.get()? & !*b.value.get()? {
                    result_value = Some(true);

                    Ok(Scalar::one())
                } else {
                    result_value = Some(false);

                    Ok(Scalar::zero())
                }
            },
        )?;

        // Constrain (1 - a) * (1 - b) = (c), ensuring c is 1 iff
        // a and b are both false, and otherwise c is 0.
        cs.enforce(
            || "nor constraint",
            |lc| lc + CS::one() - a.variable,
            |lc| lc + CS::one() - b.variable,
            |lc| lc + result_var,
        );

        Ok(Bit {
            variable: result_var,
            value: result_value,
        })
    }
}

pub fn field_into_bits_le<
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
    F: PrimeFieldBits,
>(
    mut cs: CS,
    value: Option<F>,
) -> Result<Vec<Bit>, SynthesisError> {
    // Deconstruct in big-endian bit order
    let values = match value {
        Some(ref value) => {
            let field_char = F::char_le_bits();
            let mut field_char = field_char.iter().by_refs().rev();

            let mut tmp = Vec::with_capacity(F::NUM_BITS as usize);

            let mut found_one = false;
            for b in value.to_le_bits().iter().by_vals().rev() {
                // Skip leading bits
                found_one |= field_char.next().unwrap();
                if !found_one {
                    continue;
                }

                tmp.push(Some(b));
            }

            assert_eq!(tmp.len(), F::NUM_BITS as usize);

            tmp
        }
        None => vec![None; F::NUM_BITS as usize],
    };

    // Allocate in little-endian order
    let bits = values
        .into_iter()
        .rev()
        .enumerate()
        .map(|(i, b)| Bit::alloc(cs.namespace(|| format!("bit {}", i)), b))
        .collect::<Result<Vec<_>, SynthesisError>>()?;

    Ok(bits)
}