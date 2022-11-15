use crate::util::assume;
use crate::util::{add_no_canonicalize_trashing_input, branch_hint, split};
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use ff::{Field, PrimeField};
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

/// Goldilocks field with modulus 2^64 - 2^32 + 1.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Goldilocks(u64);

/// 2^64 - 2^32 + 1
pub const MODULUS: u64 = 0xffffffff00000001;
/// 2^32 - 1
pub const EPSILON: u64 = 0xffffffff;

impl Field for Goldilocks {
    /// Returns an element chosen uniformly at random using a user-provided RNG.
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
        let (res, carry) = self.0.overflowing_shl(1);
        Self(res + EPSILON * (carry as u64))
    }

    /// Computes the multiplicative inverse of this element,
    /// failing if the element is zero.
    fn invert(&self) -> CtOption<Self> {
        todo!()
    }

    /// Returns the square root of the field element, if it is
    /// quadratic residue.
    fn sqrt(&self) -> CtOption<Self> {
        todo!()
    }
}

impl AsMut<[u8]> for Goldilocks {
    fn as_mut(&mut self) -> &mut [u8] {
        todo!()
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

    /// Interpret a string of numbers as a (congruent) prime field element.
    /// Does not accept unnecessary leading zeroes or a blank string.
    ///
    /// # Security
    ///
    /// This method provides **no** constant-time guarantees.
    fn from_str_vartime(s: &str) -> Option<Self> {
        if s.is_empty() {
            return None;
        }

        if s == "0" {
            return Some(Self::zero());
        }

        let mut res = Self::zero();

        let ten = Self::from(10);

        let mut first_digit = true;

        for c in s.chars() {
            match c.to_digit(10) {
                Some(c) => {
                    if first_digit {
                        if c == 0 {
                            return None;
                        }

                        first_digit = false;
                    }

                    res.mul_assign(&ten);
                    res.add_assign(&Self::from(u64::from(c)));
                }
                None => {
                    return None;
                }
            }
        }

        Some(res)
    }

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
        todo!()
    }

    /// Returns true iff this element is even.
    #[inline(always)]
    fn is_even(&self) -> Choice {
        !self.is_odd()
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
    const S: u32 = 32;

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

impl ConditionallySelectable for Goldilocks {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        todo!()
    }
}

impl ConstantTimeEq for Goldilocks {
    fn ct_eq(&self, other: &Self) -> Choice {
        todo!()
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
fn reduce128(x: u128) -> Goldilocks {
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

impl Goldilocks {
    #[inline]
    fn to_canonical_u64(&self) -> u64 {
        let mut c = self.0;
        // We only need one condition subtraction, since 2 * ORDER would not fit in a u64.
        if c >= MODULUS {
            c -= MODULUS;
        }
        c
    }
}
