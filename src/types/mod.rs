mod bit;
mod boolean;
mod bytes4;

pub use self::{
    bit::{Bit, field_into_bits_le},
    boolean::{Boolean, field_into_boolean_vec_le},
    bytes4::{Bytes4}
};