//! Exact arbitrary-precision rational arithmetic for the nonlinear-real
//! certificate search.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Backed by `num_bigint::BigInt` so polynomial multiplication and certificate
//! arithmetic never overflow — a wraparound here would be a *soundness* bug,
//! not just a precision one. Rationals are kept in canonical form: reduced by
//! the gcd of numerator and denominator, with a strictly positive denominator
//! and a unique representation of zero (`0/1`).

use std::cmp::Ordering;

use num_bigint::BigInt;
use num_bigint::Sign;

/// An exact rational number `num / den` in lowest terms with `den > 0`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Rational {
    num: BigInt,
    den: BigInt,
}

impl Rational {
    /// Construct from an `i128` integer.
    pub(super) fn from_int(n: i128) -> Self {
        Self {
            num: BigInt::from(n),
            den: BigInt::from(1),
        }
    }

    /// The rational `0`.
    pub(super) fn zero() -> Self {
        Self::from_int(0)
    }

    /// The rational `1`.
    pub(super) fn one() -> Self {
        Self::from_int(1)
    }

    /// Construct from a numerator/denominator pair, reducing to canonical form.
    /// `den` must be non-zero.
    fn new(num: BigInt, den: BigInt) -> Self {
        debug_assert!(den.sign() != Sign::NoSign, "zero denominator");
        let (num, den) = if den.sign() == Sign::Minus {
            (-num, -den)
        } else {
            (num, den)
        };
        let g = gcd(num.clone(), den.clone());
        if g == BigInt::from(1) || g.sign() == Sign::NoSign {
            Self { num, den }
        } else {
            Self {
                num: num / &g,
                den: den / &g,
            }
        }
    }

    pub(super) fn is_zero(&self) -> bool {
        self.num.sign() == Sign::NoSign
    }

    pub(super) fn is_one(&self) -> bool {
        self.den == BigInt::from(1) && self.num == BigInt::from(1)
    }

    pub(super) fn is_positive(&self) -> bool {
        self.num.sign() == Sign::Plus
    }

    pub(super) fn is_negative(&self) -> bool {
        self.num.sign() == Sign::Minus
    }

    pub(super) fn neg(&self) -> Self {
        Self {
            num: -self.num.clone(),
            den: self.den.clone(),
        }
    }

    pub(super) fn add(&self, other: &Self) -> Self {
        // a/b + c/d = (a*d + c*b) / (b*d)
        let num = &self.num * &other.den + &other.num * &self.den;
        let den = &self.den * &other.den;
        Self::new(num, den)
    }

    pub(super) fn sub(&self, other: &Self) -> Self {
        self.add(&other.neg())
    }

    pub(super) fn mul(&self, other: &Self) -> Self {
        Self::new(&self.num * &other.num, &self.den * &other.den)
    }

    pub(super) fn div(&self, other: &Self) -> Self {
        debug_assert!(!other.is_zero(), "division by zero rational");
        Self::new(&self.num * &other.den, &self.den * &other.num)
    }

    /// Multiplicative inverse. Returns `None` for zero.
    pub(super) fn inv(&self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }
        Some(Self::new(self.den.clone(), self.num.clone()))
    }

    fn cmp(&self, other: &Self) -> Ordering {
        // a/b ? c/d  <=>  a*d ? c*b   (both denominators positive)
        let lhs = &self.num * &other.den;
        let rhs = &other.num * &self.den;
        lhs.cmp(&rhs)
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(Ord::cmp(self, other))
    }
}

impl Ord for Rational {
    fn cmp(&self, other: &Self) -> Ordering {
        Rational::cmp(self, other)
    }
}

/// Euclidean gcd of two `BigInt`s (sign-insensitive, always non-negative).
fn gcd(a: BigInt, b: BigInt) -> BigInt {
    let mut a = abs(a);
    let mut b = abs(b);
    while b.sign() != Sign::NoSign {
        let r = a % &b;
        a = b;
        b = r;
    }
    a
}

fn abs(x: BigInt) -> BigInt {
    if x.sign() == Sign::Minus {
        -x
    } else {
        x
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reduces_to_lowest_terms() {
        let r = Rational::new(BigInt::from(6), BigInt::from(8));
        assert_eq!(r.num, BigInt::from(3));
        assert_eq!(r.den, BigInt::from(4));
    }

    #[test]
    fn normalizes_negative_denominator() {
        let r = Rational::new(BigInt::from(1), BigInt::from(-2));
        assert_eq!(r.num, BigInt::from(-1));
        assert_eq!(r.den, BigInt::from(2));
        assert!(r.is_negative());
    }

    #[test]
    fn add_sub_mul_div_roundtrip() {
        let a = Rational::new(BigInt::from(1), BigInt::from(3));
        let b = Rational::new(BigInt::from(1), BigInt::from(6));
        let sum = a.add(&b); // 1/2
        assert_eq!(sum, Rational::new(BigInt::from(1), BigInt::from(2)));
        let diff = a.sub(&b); // 1/6
        assert_eq!(diff, b);
        let prod = a.mul(&b); // 1/18
        assert_eq!(prod, Rational::new(BigInt::from(1), BigInt::from(18)));
        let quot = a.div(&b); // 2
        assert_eq!(quot, Rational::from_int(2));
    }

    #[test]
    fn zero_one_predicates() {
        assert!(Rational::zero().is_zero());
        assert!(Rational::one().is_one());
        assert!(!Rational::zero().is_positive());
        assert!(!Rational::zero().is_negative());
        assert!(Rational::from_int(3).is_positive());
        assert!(Rational::from_int(-3).is_negative());
    }

    #[test]
    fn inv_of_zero_is_none() {
        assert!(Rational::zero().inv().is_none());
        assert_eq!(
            Rational::from_int(2).inv().unwrap(),
            Rational::new(BigInt::from(1), BigInt::from(2))
        );
    }

    #[test]
    fn ordering_is_exact() {
        let a = Rational::new(BigInt::from(1), BigInt::from(3));
        let b = Rational::new(BigInt::from(1), BigInt::from(2));
        assert!(a < b);
        assert!(b > a);
        assert_eq!(a.cmp(&a), Ordering::Equal);
    }

    #[test]
    fn no_overflow_on_large_products() {
        // Multiply many large rationals; BigInt must not wrap.
        let mut acc = Rational::from_int(1);
        let big = Rational::from_int(1_000_000_000);
        for _ in 0..8 {
            acc = acc.mul(&big);
        }
        // acc = 10^72; assert it is positive and not collapsed to a small int.
        assert!(acc.is_positive());
        assert!(acc > Rational::from_int(i128::MAX));
    }
}
