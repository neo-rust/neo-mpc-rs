mod parameters;
mod work;

pub use self::{
    parameters::{MPCParameters, verify_contribution, contains_contribution},
    work::{MPCWork, clean_params}
};

#[cfg(test)]
mod test {
    use crate::mpc::{MPCWork, clean_params};
    use rand::thread_rng;
    use ff::{PrimeField};
    use bls12_381::{Scalar};
    use bellman::{Circuit, ConstraintSystem, SynthesisError};

    struct AndDemo<'a, S: PrimeField> {
        xl: Option<bool>,
        xr: Option<bool>,
        constants: &'a Option<S>,
    }

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
                    if self.constants.unwrap() != S::zero() && self.constants.unwrap() != S::one() {
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

    #[test]
    fn test_mpc_work() {
        let mut rng = thread_rng();
        // Prepare circuit
        let constants = None;
        let c = AndDemo::<Scalar> {
            xl: None,
            xr: None,
            constants: &constants,
        };
        // Init MPC
        let mut mpc = MPCWork::new(c).unwrap();
        // Contribute
        let mut contrib = mpc.contribute(&mut rng);
        mpc.write_params_to("parameters_0");
        for i in 0..3 {
            let mut mpc = MPCWork::read_params_from(format!("parameters_{}", i).as_str()).unwrap();
            let c = AndDemo::<Scalar> {
                xl: None,
                xr: None,
                constants: &constants,
            };
            mpc.verify_contribution(c, contrib);
            contrib = mpc.contribute(&mut rng);
            mpc.write_params_to(format!("parameters_{}", i + 1).as_str());
        }

        for i in 0..4 {
            clean_params(format!("parameters_{}", i).as_str());
        }
    }
}
