use super::fp2::GoldilocksExtension as Fp2; //, Extendable};
use crate::util::{add_no_canonicalize_trashing_input, branch_hint, split};
use crate::util::{assume, try_inverse_u64};
use core::fmt::Debug;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use curves::{Field64, FieldExt, Group};
use ff::{Field, PrimeField};
//use pasta_curves::arithmetic::SqrtRatio;
use pasta_curves::arithmetic::{Extendable, FieldExtension, SqrtRatio};
use rand_core::RngCore;
use std::fmt::{Display, Formatter};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

/// Goldilocks field with modulus 2^64 - 2^32 + 1.
/// A Goldilocks field may store a non-canonical form of the element
/// where the value can be between 0 and 2^64.
/// For unique representation of its form, use `to_canonical_u64`
#[derive(Clone, Copy, Ord, PartialOrd, Default, Eq)]
pub struct Goldilocks(pub u64);

impl PartialEq for Goldilocks {
    fn eq(&self, other: &Goldilocks) -> bool {
        self.to_canonical_u64() == other.to_canonical_u64()
    }
}

impl Display for Goldilocks {
    fn fmt(&self, w: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(w, "{}", self.0)
    }
}

impl Debug for Goldilocks {
    fn fmt(&self, w: &mut Formatter) -> Result<(), std::fmt::Error> {
        write!(w, "{:#x}", self.0)
    }
}

/// 2^64 - 2^32 + 1
pub const MODULUS: u64 = 0xffffffff00000001;
/// 2^32 - 1
pub const EPSILON: u64 = 0xffffffff;
pub const TWO_ADICITY: usize = 32;
pub const INVERSE_TWO_POW_ADICITY: u64 = 18446744065119617026;

impl Field for Goldilocks {
    /// Returns an element chosen uniformly at random using a user-provided RNG.
    /// Note: this sampler is not constant time!
    fn random(mut rng: impl RngCore) -> Self {
        let mut res = rng.next_u64();
        while res >= MODULUS {
            res = rng.next_u64();
        }
        Self(res)
    }

    /// Returns the zero element of the field, the additive identity.
    fn zero() -> Self {
        Self(0)
    }

    /// Returns the one element of the field, the multiplicative identity.
    fn one() -> Self {
        Self(1)
    }

    /// Squares this element.
    #[must_use]
    fn square(&self) -> Self {
        *self * *self
    }

    /// Cubes this element.
    #[must_use]
    fn cube(&self) -> Self {
        self.square() * self
    }

    /// Doubles this element.
    #[must_use]
    fn double(&self) -> Self {
        *self + *self
    }

    /// Computes the multiplicative inverse of this element,
    /// failing if the element is zero.
    fn invert(&self) -> CtOption<Self> {
        match try_inverse_u64(&self.0) {
            Some(p) => CtOption::new(Self(p), Choice::from(1)),
            None => CtOption::new(Self(0), Choice::from(0)),
        }
    }

    /// Returns the square root of the field element, if it is
    /// quadratic residue.
    fn sqrt(&self) -> CtOption<Self> {
        let res = self.pow_vartime(&[0x7fffffff80000001]);
        if res.square() == *self {
            CtOption::new(res, Choice::from(1))
        } else {
            CtOption::new(Self::zero(), Choice::from(0))
        }
    }
}

impl AsRef<u64> for Goldilocks {
    fn as_ref(&self) -> &u64 {
        &self.0
    }
}

impl AsMut<[u8]> for Goldilocks {
    fn as_mut(&mut self) -> &mut [u8] {
        let ptr = self as *const Self as *mut u8;
        unsafe { std::slice::from_raw_parts_mut(ptr, 8) }
    }
}

impl AsRef<[u8]> for Goldilocks {
    fn as_ref(&self) -> &[u8] {
        let ptr = self as *const Self as *const u8;
        // SAFETY Self is repr(transparent) and u64 is 8 bytes wide,
        // with alignment greater than that of u8
        unsafe { std::slice::from_raw_parts(ptr, 8) }
    }
}

/// This represents an element of a prime field.
impl PrimeField for Goldilocks {
    /// The prime field can be converted back and forth into this binary
    /// representation.
    type Repr = Self;

    /// Attempts to convert a byte representation of a field element into an element of
    /// this prime field, failing if the input is not canonical (is not smaller than the
    /// field's modulus).
    ///
    /// The byte representation is interpreted with the same endianness as elements
    /// returned by [`PrimeField::to_repr`].
    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        CtOption::new(repr, Choice::from(1))
    }

    /// Attempts to convert a byte representation of a field element into an element of
    /// this prime field, failing if the input is not canonical (is not smaller than the
    /// field's modulus).
    ///
    /// The byte representation is interpreted with the same endianness as elements
    /// returned by [`PrimeField::to_repr`].
    ///
    /// # Security
    ///
    /// This method provides **no** constant-time guarantees. Implementors of the
    /// `PrimeField` trait **may** optimise this method using non-constant-time logic.
    fn from_repr_vartime(repr: Self::Repr) -> Option<Self> {
        Self::from_repr(repr).into()
    }

    /// Converts an element of the prime field into the standard byte representation for
    /// this field.
    ///
    /// The endianness of the byte representation is implementation-specific. Generic
    /// encodings of field elements should be treated as opaque.
    fn to_repr(&self) -> Self::Repr {
        *self
    }

    /// Returns true iff this element is odd.
    fn is_odd(&self) -> Choice {
        Choice::from((self.0 & 1) as u8)
    }

    /// How many bits are needed to represent an element of this field.
    const NUM_BITS: u32 = 64;

    /// How many bits of information can be reliably stored in the field element.
    ///
    /// This is usually `Self::NUM_BITS - 1`.
    const CAPACITY: u32 = 63;

    /// Returns a fixed multiplicative generator of `modulus - 1` order. This element must
    /// also be a quadratic nonresidue.
    ///
    /// It can be calculated using [SageMath] as `GF(modulus).primitive_element()`.
    ///
    /// Implementations of this method MUST ensure that this is the generator used to
    /// derive `Self::root_of_unity`.
    ///
    /// [SageMath]: https://www.sagemath.org/
    fn multiplicative_generator() -> Self {
        Self(7)
    }

    /// An integer `s` satisfying the equation `2^s * t = modulus - 1` with `t` odd.
    ///
    /// This is the number of leading zero bits in the little-endian bit representation of
    /// `modulus - 1`.
    const S: u32 = TWO_ADICITY as u32;

    /// Returns the `2^s` root of unity.
    ///
    /// It can be calculated by exponentiating `Self::multiplicative_generator` by `t`,
    /// where `t = (modulus - 1) >> Self::S`.
    fn root_of_unity() -> Self {
        Self(1753635133440165772)
    }
}

impl From<u64> for Goldilocks {
    fn from(input: u64) -> Self {
        Self(input)
    }
}

impl From<Goldilocks> for u64 {
    fn from(input: Goldilocks) -> Self {
        input.0
    }
}

impl ConditionallySelectable for Goldilocks {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self(u64::conditional_select(&a.0, &b.0, choice))
    }
}

impl ConstantTimeEq for Goldilocks {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.to_canonical_u64().ct_eq(&other.to_canonical_u64())
    }
}

impl Neg for Goldilocks {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        if self.0 == 0 {
            self
        } else {
            Self(MODULUS - self.to_canonical_u64())
        }
    }
}

impl Add for Goldilocks {
    type Output = Self;

    #[inline]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn add(self, rhs: Self) -> Self::Output {
        let (sum, over) = self.0.overflowing_add(rhs.0);
        let (mut sum, over) = sum.overflowing_add((over as u64) * EPSILON);
        if over {
            // NB: self.0 > Self::ORDER && rhs.0 > Self::ORDER is necessary but not sufficient for
            // double-overflow.
            // This assume does two things:
            //  1. If compiler knows that either self.0 or rhs.0 <= ORDER, then it can skip this
            //     check.
            //  2. Hints to the compiler how rare this double-overflow is (thus handled better with
            //     a branch).
            assume(self.0 > MODULUS && rhs.0 > MODULUS);
            branch_hint();
            sum += EPSILON; // Cannot overflow.
        }
        Self(sum)
    }
}

impl<'a> Add<&'a Goldilocks> for Goldilocks {
    type Output = Self;

    #[inline]
    fn add(self, rhs: &'a Goldilocks) -> Self::Output {
        self + *rhs
    }
}

impl AddAssign for Goldilocks {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<'a> AddAssign<&'a Goldilocks> for Goldilocks {
    #[inline]
    fn add_assign(&mut self, rhs: &'a Goldilocks) {
        *self = *self + *rhs;
    }
}

impl Sub for Goldilocks {
    type Output = Self;

    #[inline]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn sub(self, rhs: Self) -> Self {
        let (diff, under) = self.0.overflowing_sub(rhs.0);
        let (mut diff, under) = diff.overflowing_sub((under as u64) * EPSILON);
        if under {
            // NB: self.0 < EPSILON - 1 && rhs.0 > Self::ORDER is necessary but not sufficient for
            // double-underflow.
            // This assume does two things:
            //  1. If compiler knows that either self.0 >= EPSILON - 1 or rhs.0 <= ORDER, then it
            //     can skip this check.
            //  2. Hints to the compiler how rare this double-underflow is (thus handled better
            //     with a branch).
            assume(self.0 < EPSILON - 1 && rhs.0 > MODULUS);
            branch_hint();
            diff -= EPSILON; // Cannot underflow.
        }
        Self(diff)
    }
}

impl<'a> Sub<&'a Goldilocks> for Goldilocks {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: &'a Goldilocks) -> Self::Output {
        self - *rhs
    }
}

impl SubAssign for Goldilocks {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<'a> SubAssign<&'a Goldilocks> for Goldilocks {
    #[inline]
    fn sub_assign(&mut self, rhs: &'a Goldilocks) {
        *self = *self - *rhs;
    }
}

impl Mul for Goldilocks {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        reduce128((self.0 as u128) * (rhs.0 as u128))
    }
}

impl<'a> Mul<&'a Goldilocks> for Goldilocks {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: &'a Goldilocks) -> Self::Output {
        self * *rhs
    }
}

impl MulAssign for Goldilocks {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<'a> MulAssign<&'a Goldilocks> for Goldilocks {
    #[inline]
    fn mul_assign(&mut self, rhs: &'a Goldilocks) {
        *self = *self * *rhs;
    }
}

/// Reduces to a 64-bit value. The result might not be in canonical form; it could be in between the
/// field order and `2^64`.
#[inline]
pub fn reduce128(x: u128) -> Goldilocks {
    let (x_lo, x_hi) = split(x); // This is a no-op
    let x_hi_hi = x_hi >> 32;
    let x_hi_lo = x_hi & EPSILON;

    let (mut t0, borrow) = x_lo.overflowing_sub(x_hi_hi);
    if borrow {
        branch_hint(); // A borrow is exceedingly rare. It is faster to branch.
        t0 -= EPSILON; // Cannot underflow.
    }
    let t1 = x_hi_lo * EPSILON;
    let t2 = unsafe { add_no_canonicalize_trashing_input(t0, t1) };
    Goldilocks(t2)
}

impl Field64 for Goldilocks {
    const ORDER: u64 = MODULUS;

    #[inline]
    fn from_noncanonical_u64(n: u64) -> Self {
        Self(n)
    }

    #[inline]
    fn from_noncanonical_i64(n: i64) -> Self {
        Self::from_canonical_u64(if n < 0 {
            // If n < 0, then this is guaranteed to overflow since
            // both arguments have their high bit set, so the result
            // is in the canonical range.
            MODULUS.wrapping_add(n as u64)
        } else {
            n as u64
        })
    }

    #[inline]
    unsafe fn add_canonical_u64(&self, rhs: u64) -> Self {
        let (res_wrapped, carry) = self.0.overflowing_add(rhs);
        // Add EPSILON * carry cannot overflow unless rhs is not in canonical form.
        Self(res_wrapped + EPSILON * (carry as u64))
    }

    #[inline]
    unsafe fn sub_canonical_u64(&self, rhs: u64) -> Self {
        let (res_wrapped, borrow) = self.0.overflowing_sub(rhs);
        // Sub EPSILON * carry cannot underflow unless rhs is not in canonical form.
        Self(res_wrapped - EPSILON * (borrow as u64))
    }

    #[inline(always)]
    fn from_canonical_u64(n: u64) -> Self {
        debug_assert!(n < Self::ORDER);
        Self(n)
    }

    #[inline]
    fn to_canonical_u64(&self) -> u64 {
        let mut c = self.0;
        // We only need one condition subtraction, since 2 * ORDER would not fit in a u64.
        if c >= MODULUS {
            c -= MODULUS;
        }
        c
    }

    #[inline(always)]
    fn to_noncanonical_u64(&self) -> u64 {
        self.0
    }

    fn from_noncanonical_u128(n: u128) -> Self {
        reduce128(n)
    }

    #[inline]
    fn multiply_accumulate(&self, x: Self, y: Self) -> Self {
        // u64 + u64 * u64 cannot overflow.
        reduce128((self.0 as u128) + (x.0 as u128) * (y.0 as u128))
    }
}

impl FieldExt for Goldilocks {
    const MODULUS: &'static str = "0xffffffff00000001";
    const TWO_INV: Self = Self(9223372034707292161);
    const ROOT_OF_UNITY_INV: Self = Self(8554224884056360729);
    const DELTA: Self = Self(1); // TODO
    const ZETA: Self = Self(0); // TODO

    fn from_u128(v: u128) -> Self {
        unimplemented!()
    }

    fn from_bytes_wide(bytes: &[u8; 64]) -> Self {
        unimplemented!()
    }

    fn get_lower_128(&self) -> u128 {
        unimplemented!()
    }
}

impl SqrtRatio for Goldilocks {
    const T_MINUS1_OVER2: [u64; 4] = [0, 0, 0, 0];

    fn pow_by_t_minus1_over2(&self) -> Self {
        unimplemented!();
    }

    fn get_lower_32(&self) -> u32 {
        self.0 as u32
    }

    #[cfg(feature = "sqrt-table")]
    fn sqrt_ratio(num: &Self, div: &Self) -> (Choice, Self) {
        unimplemented!();
    }

    #[cfg(feature = "sqrt-table")]
    fn sqrt_alt(&self) -> (Choice, Self) {
        unimplemented!();
    }
}

impl Group for Goldilocks {
    type Scalar = Goldilocks;

    fn group_zero() -> Self {
        Self::zero()
    }
    fn group_add(&mut self, rhs: &Self) {
        *self += *rhs;
    }
    fn group_sub(&mut self, rhs: &Self) {
        *self -= *rhs;
    }
    fn group_scale(&mut self, by: &Self::Scalar) {
        *self *= *by;
    }
}

impl From<bool> for Goldilocks {
    fn from(bit: bool) -> Self {
        if bit {
            Self::one()
        } else {
            Self::zero()
        }
    }
}

impl Goldilocks {
    pub fn from_bytes(bytes: &[u8; 8]) -> CtOption<Self> {
        Self::from_repr(Goldilocks(u64::from_le_bytes(*bytes)))
    }
}

impl Extendable<2> for Goldilocks {
    type BaseField = Self;
    type Extension = Fp2;
}
