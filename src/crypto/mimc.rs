// Bring in some tools for using finite fields
// We'll use these interfaces to construct our circuit.
use bellman::{Circuit, ConstraintSystem, SynthesisError};
use ff::PrimeField;
use pairing::Engine;

const MIMC_ROUNDS: usize = 322;

/// This is an implementation of MiMC, specifically a
/// variant named `LongsightF322p3` for BLS12-381.
/// See http://eprint.iacr.org/2016/492 for more
/// information about this construction.
pub fn mimc_pub<S: PrimeField>(mut xl: S, mut xr: S, constants: &[S]) -> S {
    assert_eq!(constants.len(), MIMC_ROUNDS);
    for c in constants {
        let mut tmp1 = xl;
        tmp1.add_assign(c);
        let mut tmp2 = tmp1.square();
        tmp2.mul_assign(&tmp1);
        tmp2.add_assign(&xr);
        xr = xl;
        xl = tmp2;
    }
    xl
}

/// Our demo circuit implements this `Circuit` trait which
/// is used during paramgen and proving in order to
/// synthesize the constraint system.
pub fn mimc<S, CS>(
    mut cs: CS,
    xl_in: Option<S>,
    xr_in: Option<S>,
    constants: &[S],
) -> Result<(), SynthesisError>
where
    S: PrimeField,
    CS: ConstraintSystem<S>,
{
    assert_eq!(constants.len(), MIMC_ROUNDS);
    // Allocate the first component of the preimage.
    let mut xl_value = xl_in;
    let mut xl = cs.alloc(
        || "preimage xl",
        || xl_value.ok_or(SynthesisError::AssignmentMissing),
    )?;
    // Allocate the second component of the preimage.
    let mut xr_value = xr_in;
    let mut xr = cs.alloc(
        || "preimage xr",
        || xr_value.ok_or(SynthesisError::AssignmentMissing),
    )?;
    for i in 0..MIMC_ROUNDS {
        // xL, xR := xR + (xL + Ci)^3, xL
        let cs = &mut cs.namespace(|| format!("round {}", i));
        // tmp = (xL + Ci)^2
        let tmp_value = xl_value.map(|mut e| {
            e.add_assign(&constants[i]);
            e.square()
        });
        let tmp = cs.alloc(
            || "tmp",
            || tmp_value.ok_or(SynthesisError::AssignmentMissing),
        )?;
        cs.enforce(
            || "tmp = (xL + Ci)^2",
            |lc| lc + xl + (constants[i], CS::one()),
            |lc| lc + xl + (constants[i], CS::one()),
            |lc| lc + tmp,
        );
        // new_xL = xR + (xL + Ci)^3
        // new_xL = xR + tmp * (xL + Ci)
        // new_xL - xR = tmp * (xL + Ci)
        let new_xl_value = xl_value.map(|mut e| {
            e.add_assign(&constants[i]);
            e.mul_assign(&tmp_value.unwrap());
            e.add_assign(&xr_value.unwrap());
            e
        });
        let new_xl = if i == (MIMC_ROUNDS - 1) {
            // This is the last round, xL is our image and so
            // we allocate a public input.
            cs.alloc_input(
                || "image",
                || new_xl_value.ok_or(SynthesisError::AssignmentMissing),
            )?
        } else {
            cs.alloc(
                || "new_xl",
                || new_xl_value.ok_or(SynthesisError::AssignmentMissing),
            )?
        };
        cs.enforce(
            || "new_xL = xR + (xL + Ci)^3",
            |lc| lc + tmp,
            |lc| lc + xl + (constants[i], CS::one()),
            |lc| lc + new_xl - xr,
        );
        // xR = xL
        xr = xl;
        xr_value = xl_value;
        // xL = new_xL
        xl = new_xl;
        xl_value = new_xl_value;
    }
    Ok(())
}

#[cfg(test)]
mod test {
    use crate::crypto::mimc::MIMC_ROUNDS;
    use crate::crypto::mimc::{mimc, mimc_pub};
    use bellman::{gadgets::test::TestConstraintSystem, ConstraintSystem};
    use bls12_381::Scalar;
    use ff::Field;
    use rand::{thread_rng, Rng};

    #[test]
    fn test_mimc() {
        let mut cs = TestConstraintSystem::<Scalar>::new();
        let mut rng = &mut thread_rng();
        let constants = (0..MIMC_ROUNDS)
            .map(|_| Scalar::random(&mut rng))
            .collect::<Vec<_>>();
        let xl = Scalar::random(&mut rng);
        let xr = Scalar::random(&mut rng);
        let image = mimc_pub(xl, xr, &constants);

        let mut result = mimc(cs.namespace(|| "mimc"), Some(xl), Some(xr), &constants);
        assert!(result.is_ok());
        assert!(cs.is_satisfied());
        assert!(cs.verify(&[image]));
    }
}
