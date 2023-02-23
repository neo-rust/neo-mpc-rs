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
    /// boolean value. Further, constrain that the boolean is false
    /// unless the condition is false.
    pub fn alloc_conditionally<Scalar, CS>(
        mut cs: CS,
        value: Option<bool>,
        must_be_false: &Bit,
    ) -> Result<Self, SynthesisError>
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

        // Constrain: (1 - must_be_false - a) * a = 0
        // if must_be_false is true, the equation
        // reduces to -a * a = 0, which implies a = 0.
        // if must_be_false is false, the equation
        // reduces to (1 - a) * a = 0, which is a
        // traditional boolean constraint.
        cs.enforce(
            || "boolean constraint",
            |lc| lc + CS::one() - must_be_false.variable - var,
            |lc| lc + var,
            |lc| lc,
        );

        Ok(Bit {
            variable: var,
            value,
        })
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

#[cfg(test)]
mod test {
    use super::{field_into_bits_le, Bit};
    use bellman::gadgets::test::TestConstraintSystem;
    use bellman::ConstraintSystem;
    use bls12_381::Scalar;
    use ff::{Field, PrimeField};

    #[test]
    fn test_bit_alloc() {
        let mut cs = TestConstraintSystem::new();

        Bit::alloc(&mut cs, Some(true)).unwrap();
        assert!(cs.get("boolean") == Scalar::one());
        assert!(cs.is_satisfied());
        cs.set("boolean", Scalar::zero());
        assert!(cs.is_satisfied());
        cs.set("boolean", Scalar::from(2));
        assert!(!cs.is_satisfied());
        assert!(cs.which_is_unsatisfied() == Some("boolean constraint"));
    }

    #[test]
    fn test_alloc_conditionally() {
        {
            let mut cs = TestConstraintSystem::<Scalar>::new();
            let b = Bit::alloc(&mut cs, Some(false)).unwrap();

            let value = None;
            // if value is none, fail with SynthesisError
            let is_err = Bit::alloc_conditionally(
                cs.namespace(|| "alloc_conditionally"),
                value,
                &b,
            )
            .is_err();
            assert!(is_err);
        }

        {
            // since value is true, b must be false, so it should succeed
            let mut cs = TestConstraintSystem::<Scalar>::new();

            let value = Some(true);
            let b = Bit::alloc(&mut cs, Some(false)).unwrap();
            let allocated_value = Bit::alloc_conditionally(
                cs.namespace(|| "alloc_conditionally"),
                value,
                &b,
            )
            .unwrap();

            assert!(allocated_value.get_value().unwrap());
            assert!(cs.is_satisfied());
        }

        {
            // since value is true, b must be false, so it should fail
            let mut cs = TestConstraintSystem::<Scalar>::new();

            let value = Some(true);
            let b = Bit::alloc(&mut cs, Some(true)).unwrap();
            Bit::alloc_conditionally(cs.namespace(|| "alloc_conditionally"), value, &b)
                .unwrap();

            assert!(!cs.is_satisfied());
        }

        {
            // since value is false, we don't care about the value of the bit

            let value = Some(false);
            //check with false bit
            let mut cs = TestConstraintSystem::<Scalar>::new();
            let b1 = Bit::alloc(&mut cs, Some(false)).unwrap();
            Bit::alloc_conditionally(cs.namespace(|| "alloc_conditionally"), value, &b1)
                .unwrap();

            assert!(cs.is_satisfied());

            //check with true bit
            let mut cs = TestConstraintSystem::<Scalar>::new();
            let b2 = Bit::alloc(&mut cs, Some(true)).unwrap();
            Bit::alloc_conditionally(cs.namespace(|| "alloc_conditionally"), value, &b2)
                .unwrap();

            assert!(cs.is_satisfied());
        }
    }

    #[test]
    fn test_bit_xor() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TestConstraintSystem::<Scalar>::new();
                let a = Bit::alloc(cs.namespace(|| "a"), Some(*a_val)).unwrap();
                let b = Bit::alloc(cs.namespace(|| "b"), Some(*b_val)).unwrap();
                let c = Bit::xor(&mut cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), *a_val ^ *b_val);

                assert!(cs.is_satisfied());
                assert!(cs.get("a/boolean") == if *a_val { Field::one() } else { Field::zero() });
                assert!(cs.get("b/boolean") == if *b_val { Field::one() } else { Field::zero() });
                assert!(
                    cs.get("xor result")
                        == if *a_val ^ *b_val {
                            Field::one()
                        } else {
                            Field::zero()
                        }
                );

                // Invert the result and check if the constraint system is still satisfied
                cs.set(
                    "xor result",
                    if *a_val ^ *b_val {
                        Field::zero()
                    } else {
                        Field::one()
                    },
                );
                assert!(!cs.is_satisfied());
            }
        }
    }

    #[test]
    fn test_bit_and() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TestConstraintSystem::<Scalar>::new();
                let a = Bit::alloc(cs.namespace(|| "a"), Some(*a_val)).unwrap();
                let b = Bit::alloc(cs.namespace(|| "b"), Some(*b_val)).unwrap();
                let c = Bit::and(&mut cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), *a_val & *b_val);

                assert!(cs.is_satisfied());
                assert!(cs.get("a/boolean") == if *a_val { Field::one() } else { Field::zero() });
                assert!(cs.get("b/boolean") == if *b_val { Field::one() } else { Field::zero() });
                assert!(
                    cs.get("and result")
                        == if *a_val & *b_val {
                            Field::one()
                        } else {
                            Field::zero()
                        }
                );

                // Invert the result and check if the constraint system is still satisfied
                cs.set(
                    "and result",
                    if *a_val & *b_val {
                        Field::zero()
                    } else {
                        Field::one()
                    },
                );
                assert!(!cs.is_satisfied());
            }
        }
    }

    #[test]
    fn test_bit_and_not() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TestConstraintSystem::<Scalar>::new();
                let a = Bit::alloc(cs.namespace(|| "a"), Some(*a_val)).unwrap();
                let b = Bit::alloc(cs.namespace(|| "b"), Some(*b_val)).unwrap();
                let c = Bit::and_not(&mut cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), *a_val & !*b_val);

                assert!(cs.is_satisfied());
                assert!(cs.get("a/boolean") == if *a_val { Field::one() } else { Field::zero() });
                assert!(cs.get("b/boolean") == if *b_val { Field::one() } else { Field::zero() });
                assert!(
                    cs.get("and not result")
                        == if *a_val & !*b_val {
                            Field::one()
                        } else {
                            Field::zero()
                        }
                );

                // Invert the result and check if the constraint system is still satisfied
                cs.set(
                    "and not result",
                    if *a_val & !*b_val {
                        Field::zero()
                    } else {
                        Field::one()
                    },
                );
                assert!(!cs.is_satisfied());
            }
        }
    }

    #[test]
    fn test_bit_nor() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TestConstraintSystem::<Scalar>::new();
                let a = Bit::alloc(cs.namespace(|| "a"), Some(*a_val)).unwrap();
                let b = Bit::alloc(cs.namespace(|| "b"), Some(*b_val)).unwrap();
                let c = Bit::nor(&mut cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), !*a_val & !*b_val);

                assert!(cs.is_satisfied());
                assert!(cs.get("a/boolean") == if *a_val { Field::one() } else { Field::zero() });
                assert!(cs.get("b/boolean") == if *b_val { Field::one() } else { Field::zero() });
                assert!(
                    cs.get("nor result")
                        == if !*a_val & !*b_val {
                            Field::one()
                        } else {
                            Field::zero()
                        }
                );

                // Invert the result and check if the constraint system is still satisfied
                cs.set(
                    "nor result",
                    if !*a_val & !*b_val {
                        Field::zero()
                    } else {
                        Field::one()
                    },
                );
                assert!(!cs.is_satisfied());
            }
        }
    }

    #[test]
    fn test_field_into_bits_le() {
        let mut cs = TestConstraintSystem::<Scalar>::new();

        let r = Scalar::from_str_vartime(
            "9147677615426976802526883532204139322118074541891858454835346926874644257775",
        )
        .unwrap();

        let bits = field_into_bits_le(&mut cs, Some(r)).unwrap();

        assert!(cs.is_satisfied());

        assert_eq!(bits.len(), 255);

        assert!(!bits[254].value.unwrap());
        assert!(!bits[254 - 1].value.unwrap());
        assert!(bits[254 - 2].value.unwrap());
        assert!(!bits[254 - 3].value.unwrap());
        assert!(bits[254 - 4].value.unwrap());
        assert!(!bits[254 - 5].value.unwrap());
        assert!(bits[254 - 20].value.unwrap());
        assert!(bits[254 - 23].value.unwrap());
    }
}