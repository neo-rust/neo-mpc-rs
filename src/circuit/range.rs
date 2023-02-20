// Bring in some tools for using finite fiels
use ff::{PrimeField};

// We'll use these interfaces to construct our circuit.
use bellman::{Circuit, ConstraintSystem, LinearCombination, SynthesisError};

/// This is an implementation of Range-circuit
pub fn range<S: PrimeField>(b: S, less_or_equal: S, less: S) -> [S; 3] {
    let mut result = [S::zero(); 3];
    result[0] = b;
    result[1] = less_or_equal;
    result[2] = less;
    result
}

/// This is our demo circuit for proving knowledge of the
/// preimage of Range invocation.
pub struct RangeDemo<'a, S: PrimeField> {
    pub a: Option<S>,
    pub w: Option<S>,
    pub w_array: Option<Vec<S>>,
    pub not_all_zeros: Option<S>,
    pub cr_array: Option<Vec<S>>,
    pub constants: &'a Option<[S; 3]>
}

/// Our demo circuit implements this `Circuit` trait which
/// is used during paramgen and proving in order to
/// synthesize the constraint system.
impl<'a, S: PrimeField> Circuit<S> for RangeDemo<'a, S> {
    fn synthesize<CS: ConstraintSystem<S>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let a_value = self.a;
        let a = cs.alloc(
            || "a",
            || a_value.ok_or(SynthesisError::AssignmentMissing),
        )?;
        let w_value = self.w;
        let w = cs.alloc(
            || "w",
            || w_value.ok_or(SynthesisError::AssignmentMissing),
        )?;
        let not_all_zeros_value = self.not_all_zeros;
        let not_all_zeros = cs.alloc(
            || "not_all_zeros",
            || not_all_zeros_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        let mut w_array_value = vec![];
        let w_array = self.w_array.unwrap();
        for i in 0..w_array.len(){
            let w_array_v = cs.alloc(
                || format!("w_array {}", i),
                || w_array.get(i).ok_or(SynthesisError::AssignmentMissing).copied(),
            );
            w_array_value.push(w_array_v.unwrap());
        }
        let mut cr_array_value = vec![];
        let cr_array = self.cr_array.unwrap();
        for i in 0..cr_array.len() {
            let cr_array_v = cs.alloc(
                || format!("c_array {}", i),
                || cr_array.get(i).ok_or(SynthesisError::AssignmentMissing).copied(),
            );
            cr_array_value.push(cr_array_v.unwrap());
        }

        let constants_value = self.constants.unwrap();
        let b_value = constants_value.get(0);
        let b = cs.alloc_input(
            || "b",
            || b_value.ok_or(SynthesisError::AssignmentMissing).copied(),
        )?;
        let less_or_equal_value = constants_value.get(1);
        let less_or_equal = cs.alloc_input(
            || "less_or_equal",
            || less_or_equal_value.ok_or(SynthesisError::AssignmentMissing).copied(),
        )?;
        let less_value = constants_value.get(2);
        let less = cs.alloc_input(
            || "less",
            || less_value.ok_or(SynthesisError::AssignmentMissing).copied(),
        )?;

        let n_value = w_array_value.len();
        assert_eq!(cr_array_value.len() + 1, n_value);
        let mv = 1 << (n_value as u64 - 1u64);
        cs.enforce(
            || "w=2^(n-1)+b-a",
            |lc| lc + w,
            |lc| lc + CS::one(),
            |lc| lc + (S::from(mv), CS::one()) + b - a,
        );

        let mut lc1 = LinearCombination::<S>::zero();
        for i in 0..w_array_value.len(){
            lc1 = lc1 + (S::from(1 << i), w_array_value[i]);
        }
        lc1 = lc1 - w;
        cs.enforce(
            || "2^0*w_0+.......-w=0",
            |_| lc1,
            |lc| lc + CS::one(),
            |lc| lc,
        );

        for i in 0..w_array_value.len() {
            cs.enforce(
                || "w_0(1-w_0)=0",
                |lc| lc + w_array_value[i],
                |lc| lc + CS::one() - w_array_value[i],
                |lc| lc,
            );
        }

        cs.enforce(
            || "w_0*1=cr_0",
            |lc| lc + w_array_value[0],
            |lc| lc + CS::one(),
            |lc| lc + cr_array_value[0],
        );

        for i in 1..cr_array_value.len() {
            cs.enforce(
                || "(cr_(i-1)-1)(w_i-1)=1-cr_i",
                |lc| lc + cr_array_value[i - 1] - CS::one(),
                |lc| lc + w_array_value[i] - CS::one(),
                |lc| lc + CS::one() - cr_array_value[i],
            );
        }

        cs.enforce(
            || "not_all_zeros*1=cr_n",
            |lc| lc + not_all_zeros,
            |lc| lc + CS::one(),
            |lc| lc + cr_array_value[cr_array_value.len() - 1],
        );

        cs.enforce(
            || "less_or_equal*wn=w_n",
            |lc| lc + w_array_value[w_array_value.len() - 1],
            |lc| lc + less_or_equal,
            |lc| lc + w_array_value[w_array_value.len() - 1],
        );

        cs.enforce(
            || "w_n*not_all_zeros=less",
            |lc| lc + w_array_value[w_array_value.len() - 1],
            |lc| lc + not_all_zeros,
            |lc| lc + less,
        );
        Ok(())
    }
}
