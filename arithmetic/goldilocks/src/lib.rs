//! This crate implements Goldilocks field with modulus 2^64 - 2^32 + 1
//! Credit: the majority of the code is borrowed or inspired from Plonky2 with modifications.

use ff::{Field, PrimeField};

pub mod fp;
pub mod fp2;
#[cfg(test)]
mod tests;
mod util;

/// A finite field of order less than 2^64.
pub trait Field64: Field + PrimeField {
    const ORDER: u64;

    /// Returns `x % Self::CHARACTERISTIC`.
    // TODO: Move to `Field`.
    fn from_noncanonical_u64(n: u64) -> Self;

    /// Returns `n` as an element of this field.
    // TODO: Move to `Field`.
    fn from_noncanonical_i64(n: i64) -> Self;

    /// Returns `n` as an element of this field. Assumes that `0 <= n < Self::ORDER`.
    // TODO: Move to `Field`.
    // TODO: Should probably be unsafe.
    #[inline]
    fn from_canonical_i64(n: i64) -> Self {
        Self::from_canonical_u64(n as u64)
    }

    #[inline]
    // TODO: Move to `Field`.
    fn add_one(&self) -> Self {
        unsafe { self.add_canonical_u64(1) }
    }

    #[inline]
    // TODO: Move to `Field`.
    fn sub_one(&self) -> Self {
        unsafe { self.sub_canonical_u64(1) }
    }

    /// # Safety
    /// Equivalent to *self + Self::from_canonical_u64(rhs), but may be cheaper. The caller must
    /// ensure that 0 <= rhs < Self::ORDER. The function may return incorrect results if this
    /// precondition is not met. It is marked unsafe for this reason.
    // TODO: Move to `Field`.
    #[inline]
    unsafe fn add_canonical_u64(&self, rhs: u64) -> Self {
        // Default implementation.
        *self + Self::from_canonical_u64(rhs)
    }

    /// # Safety
    /// Equivalent to *self - Self::from_canonical_u64(rhs), but may be cheaper. The caller must
    /// ensure that 0 <= rhs < Self::ORDER. The function may return incorrect results if this
    /// precondition is not met. It is marked unsafe for this reason.
    // TODO: Move to `Field`.
    #[inline]
    unsafe fn sub_canonical_u64(&self, rhs: u64) -> Self {
        // Default implementation.
        *self - Self::from_canonical_u64(rhs)
    }

    fn from_canonical_u64(n: u64) -> Self;

    fn to_canonical_u64(&self) -> u64;

    fn to_noncanonical_u64(&self) -> u64;

    #[inline(always)]
    fn to_canonical(&self) -> Self {
        Self::from_canonical_u64(self.to_canonical_u64())
    }

    /// Returns `n % Self::characteristic()`.
    fn from_noncanonical_u128(n: u128) -> Self;

    /// Returns `n % Self::characteristic()`. May be cheaper than from_noncanonical_u128 when we know
    /// that `n < 2 ** 96`.
    #[inline]
    fn from_noncanonical_u96((n_lo, n_hi): (u64, u32)) -> Self {
        // Default implementation.
        let n: u128 = ((n_hi as u128) << 64) + (n_lo as u128);
        Self::from_noncanonical_u128(n)
    }

    #[inline]
    fn multiply_accumulate(&self, x: Self, y: Self) -> Self;
}
