mod bit;
mod boolean;
mod bytes4;
mod num;

pub use self::{
    bit::{Bit, field_into_bits_le},
    boolean::{Boolean, field_into_boolean_vec_le, u64_into_boolean_vec_le},
    bytes4::{Bytes4},
    num::{Num, UnallocatedNum}
};
