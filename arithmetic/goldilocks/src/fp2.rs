use crate::fp::Goldilocks as Fp; //, FieldExtension};
use crate::util::{add_no_canonicalize_trashing_input, branch_hint, split};
use crate::util::{assume, try_inverse_u64};
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use curves::{FieldExt, Group};
use ff::{Field, PrimeField};
use pasta_curves::arithmetic::{Extendable, FieldExtension, SqrtRatio};
use rand_core::RngCore;
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

/// Goldilocks extension field
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct GoldilocksExtension([Fp; 2]);

// Verifiable in Sage with
// `R.<x> = GF(p)[]; assert (x^2 - 7).is_irreducible()`.
const W: Fp = Fp(7);

impl Display for GoldilocksExtension {
    fn fmt(&self, w: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(w, "{} {}", self.0[0], self.0[1])
    }
}

impl Field for GoldilocksExtension {
    /// Returns an element chosen uniformly at random using a user-provided RNG.
    /// Note: this sampler is not constant time!
    fn random(mut rng: impl RngCore) -> Self {
        Self([Fp::random(&mut rng), Fp::random(&mut rng)])
    }

    /// Returns the zero element of the field, the additive identity.
    fn zero() -> Self {
        Self([Fp::zero(), Fp::zero()])
    }

    /// Returns the one element of the field, the multiplicative identity.
    fn one() -> Self {
        Self([Fp::one(), Fp::one()])
    }

    /// Squares this element.
    #[must_use]
    fn square(&self) -> Self {
        self.square()
    }

    /// Doubles this element.
    #[must_use]
    fn double(&self) -> Self {
        *self + *self
    }

    /// Computes the multiplicative inverse of this element,
    /// failing if the element is zero.
    fn invert(&self) -> CtOption<Self> {
        self.invert()
    }

    /// Returns the square root of the field element, if it is
    /// quadratic residue.
    fn sqrt(&self) -> CtOption<Self> {
        todo!()
    }
}

/// This represents an element of a prime field.
impl PrimeField for GoldilocksExtension {
    /// The prime field can be converted back and forth into this binary
    /// representation.
    type Repr = Fp2Bytes;

    /// Attempts to convert a byte representation of a field element into an element of
    /// this prime field, failing if the input is not canonical (is not smaller than the
    /// field's modulus).
    ///
    /// The byte representation is interpreted with the same endianness as elements
    /// returned by [`PrimeField::to_repr`].
    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        let c0 = Fp::from_bytes(&repr.0[..8].try_into().unwrap());
        let c1 = Fp::from_bytes(&repr.0[8..].try_into().unwrap());
        // Disallow overflow representation
        CtOption::new(
            GoldilocksExtension::new(c0.unwrap(), c1.unwrap()),
            Choice::from(1),
        )
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
        Fp2Bytes(self.to_bytes())
    }

    /// Returns true iff this element is odd.
    fn is_odd(&self) -> Choice {
        Choice::from(self.to_repr().as_ref()[0] & 1)
    }

    /// How many bits are needed to represent an element of this field.
    const NUM_BITS: u32 = 128;

    /// How many bits of information can be reliably stored in the field element.
    ///
    /// This is usually `Self::NUM_BITS - 1`.
    const CAPACITY: u32 = 127;

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
        // TODO: Confirm correct multiplicative generator
        Self([Fp(18081566051660590251), Fp(16121475356294670766)])
    }

    const S: u32 = 33;

    /// Returns the `2^s` root of unity.
    ///
    /// It can be calculated by exponentiating `Self::multiplicative_generator` by `t`,
    /// where `t = (modulus - 1) >> Self::S`.
    fn root_of_unity() -> Self {
        // TODO: Confirm correct root of unity
        Self([Fp(0), Fp(15659105665374529263)])
    }
}

impl From<bool> for GoldilocksExtension {
    fn from(bit: bool) -> Self {
        if bit {
            Self::one()
        } else {
            Self::zero()
        }
    }
}

impl From<u64> for GoldilocksExtension {
    fn from(val: u64) -> Self {
        Self([Fp::from(val), Fp::zero()])
    }
}

impl Ord for GoldilocksExtension {
    #[inline(always)]
    fn cmp(&self, other: &GoldilocksExtension) -> Ordering {
        match self.0[1].cmp(&other.0[1]) {
            Ordering::Greater => Ordering::Greater,
            Ordering::Less => Ordering::Less,
            Ordering::Equal => self.0[0].cmp(&other.0[0]),
        }
    }
}

impl PartialOrd for GoldilocksExtension {
    #[inline(always)]
    fn partial_cmp(&self, other: &GoldilocksExtension) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl ConditionallySelectable for GoldilocksExtension {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self([
            Fp::conditional_select(&a.0[0], &b.0[0], choice),
            Fp::conditional_select(&a.0[1], &b.0[1], choice),
        ])
    }
}

impl ConstantTimeEq for GoldilocksExtension {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0[0].ct_eq(&other.0[0]) & self.0[1].ct_eq(&other.0[1])
    }
}

impl Add for GoldilocksExtension {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        Self([self.0[0] + rhs.0[0], self.0[1] + rhs.0[1]])
    }
}

impl<'a> Add<&'a GoldilocksExtension> for GoldilocksExtension {
    type Output = Self;

    #[inline]
    fn add(self, rhs: &'a GoldilocksExtension) -> Self::Output {
        self + *rhs
    }
}

impl AddAssign for GoldilocksExtension {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<'a> AddAssign<&'a GoldilocksExtension> for GoldilocksExtension {
    #[inline]
    fn add_assign(&mut self, rhs: &'a GoldilocksExtension) {
        *self = *self + *rhs;
    }
}

impl Neg for GoldilocksExtension {
    type Output = GoldilocksExtension;

    #[inline]
    fn neg(self) -> GoldilocksExtension {
        -&self
    }
}

impl<'a> Neg for &'a GoldilocksExtension {
    type Output = GoldilocksExtension;

    #[inline]
    fn neg(self) -> GoldilocksExtension {
        self.neg()
    }
}

impl Sub for GoldilocksExtension {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self {
        Self([self.0[0] - rhs.0[0], self.0[1] - rhs.0[1]])
    }
}

impl<'a> Sub<&'a GoldilocksExtension> for GoldilocksExtension {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: &'a GoldilocksExtension) -> Self::Output {
        self - *rhs
    }
}

impl SubAssign for GoldilocksExtension {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<'a> SubAssign<&'a GoldilocksExtension> for GoldilocksExtension {
    #[inline]
    fn sub_assign(&mut self, rhs: &'a GoldilocksExtension) {
        *self = *self - *rhs;
    }
}

impl Mul for GoldilocksExtension {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let Self([a0, a1]) = self;
        let Self([b0, b1]) = rhs;

        let c0 = a0 * b0 + W * a1 * b1;
        let c1 = a0 * b1 + a1 * b0;

        Self([c0, c1])
    }
}

impl<'a> Mul<&'a GoldilocksExtension> for GoldilocksExtension {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: &'a GoldilocksExtension) -> Self::Output {
        self * *rhs
    }
}

impl MulAssign for GoldilocksExtension {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<'a> MulAssign<&'a GoldilocksExtension> for GoldilocksExtension {
    #[inline]
    fn mul_assign(&mut self, rhs: &'a GoldilocksExtension) {
        *self = *self * *rhs;
    }
}

impl FieldExt for GoldilocksExtension {
    const MODULUS: &'static str = "0xffffffff00000001";
    const TWO_INV: Self = Self([Fp(9223372034707292160), Fp(0)]);
    const ROOT_OF_UNITY_INV: Self = Self([Fp(0), Fp(15659105665374529263)]);
    const DELTA: Self = Self([Fp(0), Fp(1)]);
    const ZETA: Self = Self([Fp(0), Fp(1)]);

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

impl SqrtRatio for GoldilocksExtension {
    const T_MINUS1_OVER2: [u64; 4] = [0, 0, 0, 0];

    fn pow_by_t_minus1_over2(&self) -> Self {
        unimplemented!();
    }

    fn get_lower_32(&self) -> u32 {
        unimplemented!();
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

impl Group for GoldilocksExtension {
    type Scalar = GoldilocksExtension;

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

#[derive(Copy, Clone)]
pub struct Fp2Bytes([u8; 16]);

impl Default for Fp2Bytes {
    fn default() -> Self {
        Self([0u8; 16])
    }
}

impl AsMut<[u8]> for Fp2Bytes {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.0
    }
}

impl AsRef<[u8]> for Fp2Bytes {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl GoldilocksExtension {
    pub const fn new(c0: Fp, c1: Fp) -> Self {
        Self([c0, c1])
    }

    fn square(&self) -> Self {
        let Self([a0, a1]) = *self;

        let c0 = a0.square() + W * a1.square();
        let c1 = a0 * a1.double();

        Self([c0, c1])
    }

    pub fn from_bytes(bytes: &[u8; 16]) -> CtOption<Self> {
        let c0 = Fp::from_bytes(bytes[0..8].try_into().unwrap());
        let c1 = Fp::from_bytes(bytes[8..16].try_into().unwrap());
        CtOption::new(
            GoldilocksExtension::new(c0.unwrap(), c1.unwrap()),
            c0.is_some() & c1.is_some(),
        )
    }

    pub fn to_bytes(&self) -> [u8; 16] {
        Self::to_repr(self).0
    }
}

impl FieldExtension<2> for GoldilocksExtension {
    type BaseField = Fp;

    fn to_base_elements(&self) -> Vec<Self::BaseField> {
        vec![self.0[0], self.0[1]]
    }
}

impl From<Fp> for GoldilocksExtension {
    fn from(f: Fp) -> Self {
        GoldilocksExtension::new(Fp::zero(), f)
    }
}
