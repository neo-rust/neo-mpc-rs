// Bring in some tools for using finite fields
use ff::{PrimeField};

// We'll use these interfaces to construct our circuit.
use bellman::{Circuit, ConstraintSystem, SynthesisError};

/// This is an implementation of And-circuit
pub fn and<S: PrimeField>(xl: bool, xr: bool) -> S {
    if xl && xr == true {
        S::one()
    } else {
        S::zero()
    }
}

/// This is our demo circuit for proving knowledge of the
/// preimage of And invocation.
pub struct AndDemo<'a, S: PrimeField> {
    pub xl: Option<bool>,
    pub xr: Option<bool>,
    pub constants: &'a Option<S>,
}

/// Our demo circuit implements this `Circuit` trait which
/// is used during paramgen and proving in order to
/// synthesize the constraint system.
impl<'a, S: PrimeField> Circuit<S> for AndDemo<'a, S> {
    fn synthesize<CS: ConstraintSystem<S>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        //print!("xl:{:?}  , xr:{:?}  ", self.xl, self.xr);
        //format check: whether xl is a boolean value
        let xl_var = cs.alloc(
            || "xl",
            || {
                if self.xl.is_some() {
                    if self.xl.unwrap() {
                        Ok(S::one())
                    } else {
                        Ok(S::zero())
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
                        Ok(S::one())
                    } else {
                        Ok(S::zero())
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
                let mut constants_var = false;
                if self.constants.unwrap() == S::zero() {
                    constants_var = false;
                } else if self.constants.unwrap() == S::one() {
                    constants_var = true;
                } else {
                    return Err(SynthesisError::AssignmentMissing);
                }
                if self.xl.is_some() && self.xr.is_some() {
                    if self.xl.unwrap() && self.xr.unwrap() {
                        Ok(S::one())
                    } else {
                        Ok(S::zero())
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
