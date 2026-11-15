//! TRUST-VC-FREM-1: Rust's float `%` is C `fmod`, never the IEEE remainder.
//!
//! `TrustVcExpr::Arith { op: Rem, .. }` at a float type is Rust's `%` on
//! `f32`/`f64`: the TRUNCATING remainder `x - trunc(x / y) * y`, which has the
//! dividend's sign. SMT-LIB `fp.rem` is the IEEE 754 remainder, which rounds
//! the quotient to nearest-even: `fp.rem(5, 3) = -1` while `5.0 % 3.0 == 2.0`.
//! The encoder lowered `%` to bare `fp.rem`, so a VC over a float remainder
//! verified the false `5 % 3 < 0` and refuted the true `5 % 3 == 2` and
//! `x >= 0 => x % 3 >= 0` (measured on the `trust-vc` CLI before the fix, see
//! `tests/float_rem_fmod_soundness.rs`).
//!
//! Every concrete expectation here is computed by Rust's own `%` on the same
//! operands (the semantics of record), and held BIT-EXACT by SMT `=`, so
//! `-0.0` and `+0.0` differ. The symbolic case is kept at f32: a symbolic
//! f64 `fp.rem` plus `fp.add` is far slower in ay (the trust-ir twin of this
//! test measured a memout).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::ir::{ArithOp, TrustVcExpr, TrustVcType};
use ay_dpll::api::{Logic, Solver, Sort, Term};
use std::collections::HashMap;

#[derive(Clone, Copy, Debug)]
enum Fmt {
    F32,
    F64,
}

impl Fmt {
    fn width(self) -> u32 {
        match self {
            Fmt::F32 => 32,
            Fmt::F64 => 64,
        }
    }

    fn eb_sb(self) -> (u32, u32) {
        match self {
            Fmt::F32 => (8, 24),
            Fmt::F64 => (11, 53),
        }
    }

    /// Rust's `%` on the operands' bit patterns: the semantics of record.
    fn rust_rem_bits(self, x_bits: u64, y_bits: u64) -> u64 {
        match self {
            Fmt::F32 => {
                let r = f32::from_bits(x_bits as u32) % f32::from_bits(y_bits as u32);
                u64::from(r.to_bits())
            }
            Fmt::F64 => (f64::from_bits(x_bits) % f64::from_bits(y_bits)).to_bits(),
        }
    }

    fn is_nan(self, bits: u64) -> bool {
        match self {
            Fmt::F32 => f32::from_bits(bits as u32).is_nan(),
            Fmt::F64 => f64::from_bits(bits).is_nan(),
        }
    }

    fn show(self, bits: u64) -> String {
        match self {
            Fmt::F32 => format!("{:?}", f32::from_bits(bits as u32)),
            Fmt::F64 => format!("{:?}", f64::from_bits(bits)),
        }
    }
}

fn f64b(v: f64) -> u64 {
    v.to_bits()
}

fn f32b(v: f32) -> u64 {
    u64::from(v.to_bits())
}

fn fp_const(solver: &mut Solver, fmt: Fmt, bits: u64) -> Term {
    let (eb, sb) = fmt.eb_sb();
    solver
        .try_fp_const_from_bits(bits, eb, sb)
        .expect("an in-envelope FP constant")
}

/// Encode `x % y` through the encoder's `TrustVcExpr` path, with the
/// variables `x` and `y` bound to the given terms.
fn encode_rem(solver: &mut Solver, fmt: Fmt, x: Term, y: Term) -> Term {
    let ty = TrustVcType::Float { width: fmt.width() };
    let mut variables = HashMap::new();
    variables.insert("x".to_string(), x);
    variables.insert("y".to_string(), y);
    let mut var_types = HashMap::new();
    var_types.insert("x".to_string(), ty.clone());
    var_types.insert("y".to_string(), ty.clone());
    let mut collection_lengths = HashMap::new();
    let functions = HashMap::new();
    let mut parser = AstExpressionParser::new(
        solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    let var = |name: &str| TrustVcExpr::Var {
        name: name.to_string(),
        ty: ty.clone(),
    };
    let expr = TrustVcExpr::Arith {
        op: ArithOp::Rem,
        left: Box::new(var("x")),
        right: Box::new(var("y")),
        ty: ty.clone(),
    };
    parser
        .encode_trust_vc_expr(&expr)
        .expect("a float remainder encodes")
}

#[derive(Debug, PartialEq, Eq)]
enum Verdict {
    Unsat,
    Sat,
    Unknown,
}

/// Assert `not(goal(x % y))` over constant operands and check it: `Unsat`
/// means `goal` holds of the encoder's remainder.
fn rem_goal_verdict(
    fmt: Fmt,
    x_bits: u64,
    y_bits: u64,
    goal: impl FnOnce(&mut Solver, Term) -> Term,
) -> Verdict {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let x = fp_const(&mut solver, fmt, x_bits);
    let y = fp_const(&mut solver, fmt, y_bits);
    let r = encode_rem(&mut solver, fmt, x, y);
    let g = goal(&mut solver, r);
    let negated = solver.try_not(g).unwrap();
    solver.try_assert_term(negated).unwrap();
    let result = solver.check_sat();
    if result.is_unsat() {
        Verdict::Unsat
    } else if result.is_sat() {
        Verdict::Sat
    } else {
        Verdict::Unknown
    }
}

/// The encoder's `x % y` is provably Rust's `x % y`, bit for bit (a NaN
/// result only as NaN: SMT-LIB has one NaN, and Rust pins no payload).
fn assert_matches_rust(fmt: Fmt, x_bits: u64, y_bits: u64) {
    let expected = fmt.rust_rem_bits(x_bits, y_bits);
    let verdict = rem_goal_verdict(fmt, x_bits, y_bits, |solver, r| {
        if fmt.is_nan(expected) {
            solver.try_fp_is_nan(r).unwrap()
        } else {
            let e = fp_const(solver, fmt, expected);
            solver.try_eq(r, e).unwrap()
        }
    });
    assert_eq!(
        verdict,
        Verdict::Unsat,
        "{fmt:?} {} % {}: the encoded remainder is not provably Rust's {}",
        fmt.show(x_bits),
        fmt.show(y_bits),
        fmt.show(expected)
    );
}

/// `5.0 % 3.0 == 2.0` is valid, and `5.0 % 3.0 < 0.0` is NOT: under bare
/// `fp.rem` the remainder is `-1.0`, which refuted the first and proved the
/// second.
#[test]
fn f64_5_rem_3_is_2_and_not_negative() {
    assert_eq!(5.0f64 % 3.0, 2.0);
    assert_eq!(
        rem_goal_verdict(Fmt::F64, f64b(5.0), f64b(3.0), |s, r| {
            let two = fp_const(s, Fmt::F64, f64b(2.0));
            s.try_fp_eq(r, two).unwrap()
        }),
        Verdict::Unsat,
        "5.0 % 3.0 == 2.0 must be valid"
    );
    assert_eq!(
        rem_goal_verdict(Fmt::F64, f64b(5.0), f64b(3.0), |s, r| {
            let zero = fp_const(s, Fmt::F64, f64b(0.0));
            s.try_fp_lt(r, zero).unwrap()
        }),
        Verdict::Sat,
        "5.0 % 3.0 < 0.0 is false and must not be valid"
    );
}

/// `-5 % 3 == -2` (dividend's sign; `fp.rem` gives `+1`), the tie
/// `3 % 2 == 1` (`1.5` rounds to even `2`, so `fp.rem` gives `-1`), and the
/// exact multiple `-6 % 3 == -0.0`, a NEGATIVE zero, at f64.
#[test]
fn f64_sign_tie_and_negative_zero() {
    assert_matches_rust(Fmt::F64, f64b(-5.0), f64b(3.0));
    assert_eq!(-5.0f64 % 3.0, -2.0);
    assert_matches_rust(Fmt::F64, f64b(3.0), f64b(2.0));
    assert_eq!(3.0f64 % 2.0, 1.0);

    let minus_zero = -6.0f64 % 3.0;
    assert_eq!(minus_zero.to_bits(), (-0.0f64).to_bits());
    assert_matches_rust(Fmt::F64, f64b(-6.0), f64b(3.0));
    assert_eq!(
        rem_goal_verdict(Fmt::F64, f64b(-6.0), f64b(3.0), |s, r| {
            let zero = s.try_fp_is_zero(r).unwrap();
            let negative = s.try_fp_is_negative(r).unwrap();
            s.try_and(zero, negative).unwrap()
        }),
        Verdict::Unsat,
        "-6.0 % 3.0 must be a NEGATIVE zero"
    );
}

/// The characteristic cases at f32, and the IEEE special operands (NaN,
/// infinities, zero divisors, signed-zero dividends, subnormals, a wide
/// exponent gap), each bit-exact to Rust's `%`. The specials already agreed
/// between `fp.rem` and `fmod`; they are here so the correction never fires
/// where it must not.
#[test]
fn f32_matches_rust_bit_exact_table() {
    let cases: [(f32, f32); 24] = [
        (5.0, 3.0),
        (-5.0, 3.0),
        (5.0, -3.0),
        (-5.0, -3.0),
        (3.0, 2.0),
        (-3.0, 2.0),
        (5.25, 2.0),
        (-6.0, 3.0),
        (6.0, -3.0),
        (7.5, 2.5),
        (1.0, 3.0),
        (-1.0, 3.0),
        (0.0, 3.0),
        (-0.0, 3.0),
        (5.0, f32::INFINITY),
        (-5.0, f32::NEG_INFINITY),
        (f32::INFINITY, 3.0),
        (5.0, 0.0),
        (5.0, -0.0),
        (f32::NAN, 3.0),
        (5.0, f32::NAN),
        (f32::MAX, 3.0),
        (-f32::MAX, 3.0),
        (f32::MAX, f32::from_bits(1)), // largest over the least subnormal
    ];
    for (x, y) in cases {
        assert_matches_rust(Fmt::F32, f32b(x), f32b(y));
    }
    // Subnormal operands. The second pair takes the correction
    // (-7q % 2q: fp.rem is +1q, fmod is -1q), and the add stays exact.
    for (x_bits, y_bits) in [(0x0000_0007u64, 0x0000_0003u64), (0x8000_0007, 0x0000_0002)] {
        assert_matches_rust(Fmt::F32, x_bits, y_bits);
    }
}

/// The remaining f64 rows: a non-integral dividend (`5.25 % 2 == 1.25`;
/// `fp.rem` gives `-0.75`), a negative divisor (its sign is irrelevant), and
/// `+0.0` for a positive exact multiple.
#[test]
fn f64_fraction_negative_divisor_and_positive_zero() {
    for (x, y) in [(5.25f64, 2.0f64), (5.0, -3.0), (6.0, -3.0)] {
        assert_matches_rust(Fmt::F64, f64b(x), f64b(y));
    }
}

/// For EVERY finite f32 `x >= 0`, `x % 3.0 >= 0.0`. The IEEE remainder
/// refutes this (`fp.rem(2, 3) = -1`); `fmod` keeps the dividend's sign.
#[test]
fn f32_symbolic_nonnegative_dividend_gives_nonnegative_remainder() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));
    let three = fp_const(&mut solver, Fmt::F32, f32b(3.0));
    let zero = fp_const(&mut solver, Fmt::F32, f32b(0.0));
    let r = encode_rem(&mut solver, Fmt::F32, x, three);

    let nonneg = solver.try_fp_ge(x, zero).unwrap();
    solver.try_assert_term(nonneg).unwrap();
    let inf = solver.try_fp_is_infinite(x).unwrap();
    let finite = solver.try_not(inf).unwrap();
    solver.try_assert_term(finite).unwrap();
    let goal = solver.try_fp_ge(r, zero).unwrap();
    let negated = solver.try_not(goal).unwrap();
    solver.try_assert_term(negated).unwrap();
    assert!(
        solver.check_sat().is_unsat(),
        "x >= 0 finite must imply x % 3.0 >= 0.0"
    );
}
