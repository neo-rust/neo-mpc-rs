use std::convert::TryInto;
use std::ops::BitAnd;
// Bring in some tools for using finite fiels
use ff::{PrimeField};

// We'll use these interfaces to construct our circuit.
use bellman::{Circuit, ConstraintSystem, LinearCombination, SynthesisError, Variable};
use bellman::domain::Scalar;
use rand::thread_rng;
use crate::helpers::range;
use crate::mpc::MPCWork;

/*pub struct RangeA {
    a: Option<u64>,
    b: Option<u64>,
    w:Option<u64>,
    wArray:Option<[u64;4]>,
    less_or_equal:Option<u64>,
    less:Option<u64>,
    not_all_zeros:Option<u64>,
    crArray:Option<[u64;4]>,
}*/

pub struct Range{
    a: Variable,
    b: Variable,
    w:Variable,
    wArray:Vec<Variable>,
    crArray:Vec<Variable>,
    not_all_zeros:Variable,
    less_or_equal:u64,
    less:u64,
}

impl Range{
    pub fn alloc<Scalar, CS>(mut cs: CS, a:Option<(u64,bool)>,b: Option<(u64,bool)>,w:Option<(u64,bool)>,wArray:Option<([u64;64],bool)>,crArray:Option<([u64;64],bool)>,less_or_equal:u64,less:u64,not_all_zeros:Option<(u64,bool)>) -> Result<Self, SynthesisError>
        where
            Scalar: PrimeField,
            CS: ConstraintSystem<Scalar>,
    {
        let a_var = Scalar::from(a.unwrap().0);
        let b_var = Scalar::from(b.unwrap().0);
        let w_var = Scalar::from(w.unwrap().0);
        let mut a_v=match a.unwrap().1 {
            true =>cs.alloc(|| "a", ||  Ok(a_var))?,
            false =>cs.alloc_input(|| "a", ||  Ok(a_var))?,
        };
        let mut b_v=match b.unwrap().1 {
            true =>cs.alloc(|| "b", || Ok(b_var))?,
            false =>cs.alloc_input(|| "b", || Ok(b_var))?,
        };
        let mut w_v=match w.unwrap().1 {
            true =>cs.alloc(|| "w", || Ok(w_var))?,
            false =>cs.alloc_input(|| "w", || Ok(w_var))?,
        };

        let not_all_zeros_var = Scalar::from(not_all_zeros.unwrap().0);
        let mut not_all_zeros_v=match not_all_zeros.unwrap().1 {
            true =>cs.alloc(|| "not_all_zeros", || Ok(not_all_zeros_var))?,
            false =>cs.alloc_input(|| "not_all_zeros", || Ok(not_all_zeros_var))?,
        };
        let mut wArray_var= vec![];
        for i in 0 .. wArray.unwrap().0.len(){
            let mut wArray_v=match wArray.unwrap().1 {
                true =>cs.alloc(||"",||Ok(Scalar::from(*wArray.unwrap().0.get(i).unwrap()))),
                false =>cs.alloc_input(||"",||Ok(Scalar::from(*wArray.unwrap().0.get(i).unwrap()))),
            };
            wArray_var.push(wArray_v.unwrap());
        }
        let mut crArray_var= vec![];
        for i in 0 .. crArray.unwrap().0.len() {
            let mut cArray_v=match crArray.unwrap().1 {
                true =>cs.alloc(||"",||Ok(Scalar::from(*crArray.unwrap().0.get(i).unwrap()))),
                false =>cs.alloc_input(||"",||Ok(Scalar::from(*crArray.unwrap().0.get(i).unwrap()))),
            };
            crArray_var.push(cArray_v.unwrap());
        }

        Ok(Range {
            a: a_v,
            b: b_v,
            w:w_v,
            wArray:wArray_var,
            less_or_equal:less_or_equal,
            less:less,
            not_all_zeros:not_all_zeros_v,
            crArray:crArray_var,
        })
    }

pub fn less_or_equal<Scalar, CS>(mut cs: CS,a:(u64,bool),b:(u64,bool)) -> Result<(), SynthesisError>
    where
        Scalar: PrimeField,
        CS: ConstraintSystem<Scalar>,
{
    let w= ((1<<(64-1u64))+(b.0-a.0)) as u64;
    let mut wArray=[0].repeat(64);
    let mut i=0;
    let mut values=w.clone();
    while i < wArray.len() {
        wArray[i]=values & 1;
        values>>=1;
        i += 1;
    }
    let mut cArray=[0].repeat(64);
    cArray[0]=wArray[0];
    let j=1;
    while j < wArray.len(){
        cArray[j]=u64::from(wArray[j]|cArray[j-1]);
    }
    let not_all_zeros=cArray.last().unwrap().clone();
    let r=Range::alloc(cs.namespace(|| "less_or_equal_alloc"),Some(a),Some(b),Some((w,a.1&b.1)),Some((wArray.try_into().unwrap(),a.1&b.1)),Some((cArray.try_into().unwrap(),a.1&b.1)),1,0,Some((not_all_zeros,a.1&b.1))).expect("range alloc error");
    return Range::range(cs.namespace(|| "less_or_equal"),&r);
}

pub fn less_or_equal_u8<Scalar, CS>(mut cs: CS,a:(u8,bool),b:(u8,bool)) -> Result<(), SynthesisError>
        where
            Scalar: PrimeField,
            CS: ConstraintSystem<Scalar>,
    {
        let w= ((1<<(8-1u8))+(b.0-a.0)) as u8;
        let mut wArray=[0u8].repeat(8);
        let mut i=0;
        let mut values=w.clone();
        while i < wArray.len() {
            wArray[i]=values & 1u8;
            values>>=1;
            i += 1;
        }
        let mut cArray=[0].repeat(8);
        cArray[0]=wArray[0];
        let j=1;
        while j < wArray.len(){
            cArray[j]=u8::from(wArray[j]|cArray[j-1]);
        }
        let not_all_zeros=cArray.last().unwrap().clone();
        let r=Range::alloc_u8(cs.namespace(|| "less_or_equal_alloc"),Some(a),Some(b),Some((w,a.1&b.1)),Some((wArray.try_into().unwrap(),a.1&b.1)),Some((cArray.try_into().unwrap(),a.1&b.1)),1,0,Some((not_all_zeros,a.1&b.1))).expect("range alloc error");
        return Range::range(cs.namespace(|| "less_or_equal"),&r);
    }


    pub fn alloc_u8<Scalar, CS>(mut cs: CS, a:Option<(u8,bool)>,b: Option<(u8,bool)>,w:Option<(u8,bool)>,wArray:Option<([u8;8],bool)>,crArray:Option<([u8;8],bool)>,less_or_equal:u64,less:u64,not_all_zeros:Option<(u8,bool)>) -> Result<Self, SynthesisError>
        where
            Scalar: PrimeField,
            CS: ConstraintSystem<Scalar>,
    {
        let a_var = Scalar::from(a.unwrap().0.into());
        let b_var = Scalar::from(b.unwrap().0.into());
        let w_var = Scalar::from(w.unwrap().0.into());
        let mut a_v=match a.unwrap().1 {
            true =>cs.alloc(|| "a", ||  Ok(a_var))?,
            false =>cs.alloc_input(|| "a", ||  Ok(a_var))?,
        };
        let mut b_v=match b.unwrap().1 {
            true =>cs.alloc(|| "b", || Ok(b_var))?,
            false =>cs.alloc_input(|| "b", || Ok(b_var))?,
        };
        let mut w_v=match w.unwrap().1 {
            true =>cs.alloc(|| "w", || Ok(w_var))?,
            false =>cs.alloc_input(|| "w", || Ok(w_var))?,
        };

        let not_all_zeros_var = Scalar::from(not_all_zeros.unwrap().0.into());
        let mut not_all_zeros_v=match not_all_zeros.unwrap().1 {
            true =>cs.alloc(|| "not_all_zeros", || Ok(not_all_zeros_var))?,
            false =>cs.alloc_input(|| "not_all_zeros", || Ok(not_all_zeros_var))?,
        };
        let mut wArray_var= vec![];
        for i in 0 .. wArray.unwrap().0.len(){
            let mut wArray_v=match wArray.unwrap().1 {
                true =>cs.alloc(||"",||Ok(Scalar::from(u64::from(*wArray.unwrap().0.get(i).unwrap())))),
                false =>cs.alloc_input(||"",||Ok(Scalar::from(u64::from(*wArray.unwrap().0.get(i).unwrap())))),
            };
            wArray_var.push(wArray_v.unwrap());
        }
        let mut crArray_var= vec![];
        for i in 0 .. crArray.unwrap().0.len() {
            let mut cArray_v=match crArray.unwrap().1 {
                true =>cs.alloc(||"",||Ok(Scalar::from(u64::from(*crArray.unwrap().0.get(i).unwrap())))),
                false =>cs.alloc_input(||"",||Ok(Scalar::from(u64::from(*crArray.unwrap().0.get(i).unwrap())))),
            };
            crArray_var.push(cArray_v.unwrap());
        }

        Ok(Range {
            a: a_v,
            b: b_v,
            w:w_v,
            wArray:wArray_var,
            less_or_equal:less_or_equal,
            less:less,
            not_all_zeros:not_all_zeros_v,
            crArray:crArray_var,
        })
    }

    pub fn less<Scalar, CS>(mut cs: CS,a:(u64,bool),b:(u64,bool)) -> Result<(), SynthesisError>
    where
        Scalar: PrimeField,
        CS: ConstraintSystem<Scalar>,
{
    let w= ((1<<(64-1u64))+(b.0-a.0)) as u64;
    let mut wArray=[0].repeat(64);
    let mut i=0;
    let mut values=w.clone();
    while i < wArray.len() {
        wArray[i]=values & 1;
        values>>=1;
        i += 1;
    }
    let mut cArray=[0].repeat(64);
    cArray[0]=wArray[0];
    let j=1;
    while j < wArray.len(){
        cArray[j]=u64::from(wArray[j]|cArray[j-1]);
    }
    let not_all_zeros=cArray.last().unwrap().clone();
    let r=Range::alloc(cs.namespace(|| "less_or_equal_alloc"),Some(a),Some(b),Some((w,a.1&b.1)),Some((wArray.try_into().unwrap(),a.1&b.1)),Some((cArray.try_into().unwrap(),a.1&b.1)),1,1,Some((not_all_zeros,a.1&b.1))).expect("range alloc error");
    return Range::range(cs.namespace(|| "less_or_equal_alloc"),&r);
}

pub fn large_or_equal<Scalar, CS>(mut cs: CS,a:(u64,bool),b:(u64,bool)) -> Result<(), SynthesisError>
    where
        Scalar: PrimeField,
        CS: ConstraintSystem<Scalar>,
{
    let w= ((1<<(64-1u64))+(a.0-b.0)) as u64;
    let mut wArray=[0].repeat(64);
    let mut i=0;
    let mut values=w.clone();
    while i < wArray.len() {
        wArray[i]=values & 1;
        values>>=1;
        i += 1;
    }
    let mut cArray=[0].repeat(64);
    cArray[0]=wArray[0];
    let j=1;
    while j < wArray.len(){
        cArray[j]=u64::from(wArray[j]|cArray[j-1]);
    }
    let not_all_zeros=cArray.last().unwrap().clone();
    let r=Range::alloc(cs.namespace(|| "large_or_equal_alloc"),Some(b),Some(a),Some((w,a.1&b.1)),Some((wArray.try_into().unwrap(),a.1&b.1)),Some((cArray.try_into().unwrap(),a.1&b.1)),1,0,Some((not_all_zeros,a.1&b.1))).expect("range alloc error");
    return Range::range(cs.namespace(|| "large_or_equal_alloc"),&r);
}

pub fn large<Scalar, CS>(mut cs: CS,a:(u64,bool),b:(u64,bool)) -> Result<(), SynthesisError>
    where
        Scalar: PrimeField,
        CS: ConstraintSystem<Scalar>,
{
    let w= ((1<<(64-1u64))+(a.0-b.0)) as u64;
    let mut wArray=[0].repeat(64);
    let mut i=0;
    let mut values=w.clone();
    while i < wArray.len() {
        wArray[i]=values & 1;
        values>>=1;
        i += 1;
    }
    let mut cArray=[0].repeat(64);
    cArray[0]=wArray[0];
    let j=1;
    while j < wArray.len(){
        cArray[j]=u64::from(wArray[j]|cArray[j-1]);
    }
    let not_all_zeros=cArray.last().unwrap().clone();
    let r=Range::alloc(cs.namespace(|| "large_alloc"),Some(b),Some(a),Some((w,a.1&b.1)),Some((wArray.try_into().unwrap(),a.1&b.1)),Some((cArray.try_into().unwrap(),a.1&b.1)),1,1,Some((not_all_zeros,a.1&b.1))).expect("range alloc error");
    return Range::range(cs.namespace(|| "large_alloc"),&r);
}

pub fn range<Scalar, CS>(mut cs: CS, input: &Range) -> Result<(), SynthesisError> where Scalar: PrimeField, CS: ConstraintSystem<Scalar>,
{
    let a=input.a;
    let b=input.b;
    let n=input.wArray.len();
    let w=input.w;
    let exp2n =1<<(n-1);
    let wArray=&input.wArray;
    let crArray=&input.crArray;
    let not_all_zeros=input.not_all_zeros;
    let less_or_equal= input.less_or_equal;
    let less=input.less;
    cs.enforce(
        || "w=2^n+b-a",
        |lc| lc + w,
        |lc| lc + CS::one(),
        |lc| lc+(Scalar::from(exp2n), CS::one())+b-a,
    );

    let mut lct = LinearCombination::<Scalar>::zero();
    for i in 0..wArray.len(){
        lct = lct + (Scalar::from(1<<i), wArray[i]);
    }
    lct = lct -w;
    cs.enforce(
        || "2^0*w0+.......-w=0",
        |_| lct,
        |lc| lc + CS::one(),
        |lc| lc,
    );

    for i in 0..wArray.len() {
        cs.enforce(
            || "w0(1-w0)=0",
            |lc| lc + wArray[i],
            |lc| lc + CS::one()-wArray[i],
            |lc| lc,
        );
    }

    cs.enforce(
        || "w0=cr0",
        |lc| lc + wArray[0],
        |lc| lc + CS::one(),
        |lc| lc+crArray[0],
    );

    for i in 1..crArray.len() {
        cs.enforce(
            || "(cr_(i-1)-1)(wi-1)=1-cr_i",
            |lc| lc + crArray[i-1]-CS::one(),
            |lc| lc + wArray[i]-CS::one(),
            |lc| lc+CS::one()- crArray[i],
        );
    }

    cs.enforce(
        || "not_all_zeros=cr_n",
        |lc| lc + not_all_zeros,
        |lc| lc + CS::one(),
        |lc| lc+crArray[crArray.len()-1],
    );

    cs.enforce(
        || "wn=less_or_equal*wn",
        |lc| lc + wArray[wArray.len()-1],
        |lc| lc + (Scalar::from(less_or_equal), CS::one()),
        |lc| lc+wArray[wArray.len()-1],
    );

    cs.enforce(
        || "wn*less_or_equal=less",
        |lc| lc + wArray[wArray.len()-1],
        |lc| lc + not_all_zeros,
        |lc| lc+(Scalar::from(less), CS::one()),
    );
    Ok(())
}
}


#[cfg(test)]
mod test {
    use crate::mpc::{MPCWork, clean_params};
    use rand::thread_rng;
    use ff::{PrimeField};
    use bls12_381::{Scalar};
    use bellman::{Circuit, ConstraintSystem, SynthesisError};
    use crate::helpers::range::Range;

    #[test]
    fn test_mpc_work() {
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
            Range::less_or_equal_u8(cs,(self.xl.unwrap(),true),(self.xr.unwrap(),true))
        }
    }


}
