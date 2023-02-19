//! This crate implements Goldilocks field with modulus 2^64 - 2^32 + 1
//! Credit: the majority of the code is borrowed or inspired from Plonky2 with modifications.

use curves::FieldExt;
use ff::{Field, PrimeField};

pub mod fp;
pub mod fp2;
#[cfg(test)]
mod tests;
mod util;
