mod mimc;
mod sha256;

pub use self::{
    mimc::{mimc, MiMCDemo}, 
    sha256::{sha256, sha256_block_no_padding, get_sha256_iv, sha256_compression_function}
};
