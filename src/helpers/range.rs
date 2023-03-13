use std::convert::TryInto;

// Bring in some tools for using finite fiels
use ff::{PrimeField};

// We'll use these interfaces to construct our circuit.
use bellman::{ConstraintSystem, LinearCombination, SynthesisError, Variable};

struct Range {
    a: Variable,
    b: Variable,
    w: Variable,
    w_array: Vec<Variable>,
    cr_array: Vec<Variable>,
    not_all_zeros: Variable,
    less_or_equal: u64,
    less: u64,
}

impl Range {
    pub fn alloc<Scalar, CS>(
        mut cs: CS,
        a: (u64, bool),
        b: (u64, bool),
        w: (u64, bool),
        w_array: ([u64; 64], bool),
        cr_array: ([u64; 64], bool),
        less_or_equal: u64,
        less: u64,
        not_all_zeros: (u64, bool)
    ) -> Result<Self, SynthesisError>
        where
            Scalar: PrimeField,
            CS: ConstraintSystem<Scalar>,
    {
        let a_var = Scalar::from(a.0);
        let b_var = Scalar::from(b.0);
        let w_var = Scalar::from(w.0);
        let a_v = match a.1 {
            true => cs.alloc(|| "a", ||  Ok(a_var))?,
            false => cs.alloc_input(|| "a", ||  Ok(a_var))?,
        };
        let b_v = match b.1 {
            true => cs.alloc(|| "b", || Ok(b_var))?,
            false => cs.alloc_input(|| "b", || Ok(b_var))?,
        };
        let w_v = match w.1 {
            true => cs.alloc(|| "w", || Ok(w_var))?,
            false => cs.alloc_input(|| "w", || Ok(w_var))?,
        };

        let not_all_zeros_var = Scalar::from(not_all_zeros.0);
        let not_all_zeros_v = match not_all_zeros.1 {
            true => cs.alloc(|| "not_all_zeros", || Ok(not_all_zeros_var))?,
            false => cs.alloc_input(|| "not_all_zeros", || Ok(not_all_zeros_var))?,
        };
        let mut w_array_var = vec![];
        for i in 0 .. w_array.0.len(){
            let w_array_v = match w_array.1 {
                true => cs.alloc(|| "", || Ok(Scalar::from((w_array.0)[i]))),
                false => cs.alloc_input(|| "", || Ok(Scalar::from(w_array.0[i]))),
            };
            w_array_var.push(w_array_v.unwrap());
        }
        let mut cr_array_var = vec![];
        for i in 0 .. cr_array.0.len() {
            let c_array_v = match cr_array.1 {
                true => cs.alloc(|| "", || Ok(Scalar::from(cr_array.0[i]))),
                false => cs.alloc_input(|| "", || Ok(Scalar::from(cr_array.0[i]))),
            };
            cr_array_var.push(c_array_v.unwrap());
        }

        Ok(Range {
            a: a_v,
            b: b_v,
            w: w_v,
            w_array: w_array_var,
            less_or_equal: less_or_equal,
            less: less,
            not_all_zeros: not_all_zeros_v,
            cr_array: cr_array_var,
        })
    }

    pub fn alloc_u8<Scalar, CS>(
        mut cs: CS,
        a: (u8, bool),
        b: (u8, bool),
        w: (u8, bool),
        w_array: ([u8; 8], bool),
        cr_array: ([u8; 8], bool),
        less_or_equal: u64,
        less: u64,
        not_all_zeros: (u8, bool)
    ) -> Result<Self, SynthesisError>
        where
            Scalar: PrimeField,
            CS: ConstraintSystem<Scalar>,
    {
        let a_var = Scalar::from(a.0.into());
        let b_var = Scalar::from(b.0.into());
        let w_var = Scalar::from(w.0.into());
        let a_v = match a.1 {
            true => cs.alloc(|| "a", ||  Ok(a_var))?,
            false => cs.alloc_input(|| "a", ||  Ok(a_var))?,
        };
        let b_v = match b.1 {
            true => cs.alloc(|| "b", || Ok(b_var))?,
            false => cs.alloc_input(|| "b", || Ok(b_var))?,
        };
        let w_v = match w.1 {
            true => cs.alloc(|| "w", || Ok(w_var))?,
            false => cs.alloc_input(|| "w", || Ok(w_var))?,
        };

        let not_all_zeros_var = Scalar::from(not_all_zeros.0.into());
        let not_all_zeros_v = match not_all_zeros.1 {
            true => cs.alloc(|| "not_all_zeros", || Ok(not_all_zeros_var))?,
            false => cs.alloc_input(|| "not_all_zeros", || Ok(not_all_zeros_var))?,
        };
        let mut w_array_var = vec![];
        for i in 0 .. w_array.0.len(){
            let w_array_v = match w_array.1 {
                true => cs.alloc(|| "", || Ok(Scalar::from(u64::from(w_array.0[i])))),
                false => cs.alloc_input(|| "", || Ok(Scalar::from(u64::from(w_array.0[i])))),
            };
            w_array_var.push(w_array_v.unwrap());
        }
        let mut cr_array_var = vec![];
        for i in 0 .. cr_array.0.len() {
            let c_array_v = match cr_array.1 {
                true => cs.alloc(|| "", || Ok(Scalar::from(u64::from(cr_array.0[i])))),
                false => cs.alloc_input(|| "", || Ok(Scalar::from(u64::from(cr_array.0[i])))),
            };
            cr_array_var.push(c_array_v.unwrap());
        }

        Ok(Range {
            a: a_v,
            b: b_v,
            w: w_v,
            w_array: w_array_var,
            less_or_equal: less_or_equal,
            less: less,
            not_all_zeros: not_all_zeros_v,
            cr_array: cr_array_var,
        })
    }

    pub fn execute<Scalar, CS>(mut cs: CS, input: &Range) -> Result<(), SynthesisError> 
    where 
        Scalar: PrimeField,
        CS: ConstraintSystem<Scalar>,
    {
        let a = input.a;
        let b = input.b;
        let n = input.w_array.len();
        let w = input.w;
        let exp2n = 1 << (n - 1);
        let w_array = &input.w_array;
        let cr_array = &input.cr_array;
        let not_all_zeros = input.not_all_zeros;
        let less_or_equal = input.less_or_equal;
        let less = input.less;
        cs.enforce(
            || "w=2^n+b-a",
            |lc| lc + w,
            |lc| lc + CS::one(),
            |lc| lc + (Scalar::from(exp2n), CS::one()) + b - a,
        );
    
        let mut lct = LinearCombination::<Scalar>::zero();
        for i in 0..w_array.len(){
            lct = lct + (Scalar::from(1 << i), w_array[i]);
        }
        lct = lct - w;
        cs.enforce(
            || "2^0*w0+.......-w=0",
            |_| lct,
            |lc| lc + CS::one(),
            |lc| lc,
        );
    
        for i in 0..w_array.len() {
            cs.enforce(
                || "w0(1-w0)=0",
                |lc| lc + w_array[i],
                |lc| lc + CS::one() - w_array[i],
                |lc| lc,
            );
        }
    
        cs.enforce(
            || "w0=cr0",
            |lc| lc + w_array[0],
            |lc| lc + CS::one(),
            |lc| lc + cr_array[0],
        );
    
        for i in 1..cr_array.len() {
            cs.enforce(
                || "(cr_(i-1)-1)(wi-1)=1-cr_i",
                |lc| lc + cr_array[i-1] - CS::one(),
                |lc| lc + w_array[i] - CS::one(),
                |lc| lc + CS::one() - cr_array[i],
            );
        }
    
        cs.enforce(
            || "not_all_zeros=cr_n",
            |lc| lc + not_all_zeros,
            |lc| lc + CS::one(),
            |lc| lc + cr_array[cr_array.len() - 1],
        );
    
        cs.enforce(
            || "wn=less_or_equal*wn",
            |lc| lc + w_array[w_array.len() - 1],
            |lc| lc + (Scalar::from(less_or_equal), CS::one()),
            |lc| lc + w_array[w_array.len() - 1],
        );
    
        cs.enforce(
            || "wn*less_or_equal=less",
            |lc| lc + w_array[w_array.len() - 1],
            |lc| lc + not_all_zeros,
            |lc| lc + (Scalar::from(less), CS::one()),
        );
        Ok(())
    }
}

pub fn less_or_equal_u64<Scalar, CS>(
    mut cs: CS,
    a: (u64, bool),
    b: (u64, bool)
) -> Result<(), SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    let w = ((1 << (64 - 1u64)) + (b.0 - a.0)) as u64;
    let mut w_array = [0].repeat(64);
    let mut i = 0;
    let mut values = w.clone();
    while i < w_array.len() {
        w_array[i] = values & 1;
        values >>= 1;
        i += 1;
    }
    let mut c_array = [0].repeat(64);
    c_array[0] = w_array[0];
    let j = 1;
    while j < w_array.len(){
        c_array[j] = u64::from(w_array[j] | c_array[j-1]);
    }
    let not_all_zeros = c_array.last().unwrap().clone();
    let r = Range::alloc(
        cs.namespace(|| "less_or_equal_alloc"),
        a,
        b,
        (w, a.1 & b.1),
        (w_array.try_into().unwrap(), a.1 & b.1),
        (c_array.try_into().unwrap(), a.1 & b.1),
        1,
        0,
        (not_all_zeros, a.1 & b.1)
    ).expect("range alloc error");
    return Range::execute(cs.namespace(|| "less_or_equal"), &r);
}

pub fn less_or_equal_u8<Scalar, CS>(
    mut cs: CS,
    a: (u8, bool),
    b: (u8, bool)
) -> Result<(), SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    let w = ((1 << (8 - 1u8)) + (b.0 - a.0)) as u8;
    let mut w_array = [0u8].repeat(8);
    let mut i = 0;
    let mut values = w.clone();
    while i < w_array.len() {
        w_array[i] = values & 1u8;
        values >>= 1;
        i += 1;
    }
    let mut c_array = [0].repeat(8);
    c_array[0] = w_array[0];
    let j = 1;
    while j < w_array.len(){
        c_array[j] = u8::from(w_array[j] | c_array[j-1]);
    }
    let not_all_zeros = c_array.last().unwrap().clone();
    let r = Range::alloc_u8(
        cs.namespace(|| "less_or_equal_alloc"),
        a,
        b,
        (w, a.1 & b.1),
        (w_array.try_into().unwrap(), a.1 & b.1),
        (c_array.try_into().unwrap(), a.1 & b.1),
        1,
        0,
        (not_all_zeros, a.1 & b.1)
    ).expect("range alloc error");
    return Range::execute(cs.namespace(|| "less_or_equal"), &r);
}

pub fn less_u64<Scalar, CS>(
    mut cs: CS,
    a: (u64, bool),
    b: (u64, bool)
) -> Result<(), SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    let w = ((1 << (64 - 1u64)) + (b.0 - a.0)) as u64;
    let mut w_array = [0].repeat(64);
    let mut i = 0;
    let mut values = w.clone();
    while i < w_array.len() {
        w_array[i] = values & 1;
        values >>= 1;
        i += 1;
    }
    let mut c_array = [0].repeat(64);
    c_array[0] = w_array[0];
    let j = 1;
    while j < w_array.len(){
        c_array[j] = u64::from(w_array[j] | c_array[j-1]);
    }
    let not_all_zeros = c_array.last().unwrap().clone();
    let r = Range::alloc(
        cs.namespace(|| "less_or_equal_alloc"),
        a,
        b,
        (w, a.1 & b.1),
        (w_array.try_into().unwrap(), a.1 & b.1),
        (c_array.try_into().unwrap(), a.1 & b.1),
        1,
        1,
        (not_all_zeros, a.1 & b.1)
    ).expect("range alloc error");
    return Range::execute(cs.namespace(|| "less_or_equal_alloc"), &r);
}

pub fn large_or_equal_u64<Scalar, CS>(
    mut cs: CS,
    a: (u64, bool),
    b: (u64, bool)
) -> Result<(), SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    let w = ((1 << (64 - 1u64)) + (a.0 - b.0)) as u64;
    let mut w_array = [0].repeat(64);
    let mut i = 0;
    let mut values = w.clone();
    while i < w_array.len() {
        w_array[i] = values & 1;
        values >>= 1;
        i += 1;
    }
    let mut c_array = [0].repeat(64);
    c_array[0] = w_array[0];
    let j = 1;
    while j < w_array.len(){
        c_array[j] = u64::from(w_array[j] | c_array[j-1]);
    }
    let not_all_zeros = c_array.last().unwrap().clone();
    let r = Range::alloc(
        cs.namespace(|| "large_or_equal_alloc"),
        b,
        a,
        (w, a.1 & b.1),
        (w_array.try_into().unwrap(), a.1 & b.1),
        (c_array.try_into().unwrap(), a.1 & b.1),
        1,
        0,
        (not_all_zeros, a.1 & b.1)
    ).expect("range alloc error");
    return Range::execute(cs.namespace(|| "large_or_equal_alloc"), &r);
}

pub fn large_u64<Scalar, CS>(
    mut cs: CS,
    a: (u64, bool),
    b: (u64, bool)
) -> Result<(), SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    let w = ((1 << (64 - 1u64)) + (a.0 - b.0)) as u64;
    let mut w_array = [0].repeat(64);
    let mut i = 0;
    let mut values = w.clone();
    while i < w_array.len() {
        w_array[i] = values & 1;
        values >>= 1;
        i += 1;
    }
    let mut c_array = [0].repeat(64);
    c_array[0] = w_array[0];
    let j = 1;
    while j < w_array.len(){
        c_array[j] = u64::from(w_array[j] | c_array[j-1]);
    }
    let not_all_zeros = c_array.last().unwrap().clone();
    let r = Range::alloc(
        cs.namespace(|| "large_alloc"),
        b,
        a,
        (w,a.1&b.1),
        (w_array.try_into().unwrap(), a.1 & b.1),
        (c_array.try_into().unwrap(), a.1 & b.1),
        1,
        1,
        (not_all_zeros, a.1 & b.1)
    ).expect("range alloc error");
    return Range::execute(cs.namespace(|| "large_alloc"), &r);
}

#[cfg(test)]
mod test {
    use crate::mpc::{MPCWork, clean_params};
    use rand::thread_rng;
    use ff::{PrimeField};
    use bls12_381::{Scalar};
    use bellman::{
        Circuit, ConstraintSystem, SynthesisError,
        gadgets::test::TestConstraintSystem
    };
    use crate::helpers::range::{
        less_or_equal_u64,
        less_or_equal_u8
    };

    #[test]
    fn test_less_or_equal_u64() {
        let cs = TestConstraintSystem::<Scalar>::new();
        assert!(less_or_equal_u64(cs, (1, true), (2, false)).is_ok());
    }

    #[test]
    fn test_range_mpc() {
        let mut rng = thread_rng();
        // Prepare circuit
        let constants = None;
        let c = TestDemo::<Scalar> {
            xl: Some(5),
            xr: Some(6),
            constants: &constants,
        };
        // Init MPC
        let mut mpc = MPCWork::new(c).unwrap();
        // Contribute
        let mut contrib = mpc.contribute(&mut rng);
        mpc.write_params_to("parameters_0");
        for i in 0..3 {
            let mut mpc = MPCWork::read_params_from(format!("parameters_{}", i).as_str()).unwrap();
            let c = TestDemo::<Scalar> {
                xl: Some(5),
                xr: Some(6),
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

    struct TestDemo<'a, S: PrimeField> {
        xl: Option<u8>,
        xr: Option<u8>,
        constants: &'a Option<S>,
    }

    impl<'a, S: PrimeField> Circuit<S> for TestDemo<'a, S> {
        fn synthesize<CS: ConstraintSystem<S>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
            let a = self.xl.unwrap();
            let b = self.xr.unwrap();

            less_or_equal_u8(cs, (a, true), (b, true))
        }
    }
}
