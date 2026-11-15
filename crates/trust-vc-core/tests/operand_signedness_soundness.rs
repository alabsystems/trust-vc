//! Signedness is a property of the OPERAND, never of a hash-consed term.
//!
//! ay hash-conses BV constants, so `u64::MAX` and the `i64` literal `-1` are the
//! SAME term (as are `200u8` / `-56i8` and `255u8` / `-1i8`). A side table keyed
//! by term (`term_widths`) cannot tell those occurrences apart: whichever
//! occurrence was encoded last owns the entry, and every other occurrence reads
//! the wrong sign. Two lifts consulted it, or ignored signedness altogether:
//!
//! * the comparison boundary (`compare.rs`, Route A #2779), which lifts a BV
//!   peer of an Int-sorted length to Int with the sign it found in the table —
//!   so `u64::MAX < a.len() + (-1i64)` read its LEFT operand as `-1` after the
//!   right operand's `-1` re-registered the shared term as signed;
//! * the arithmetic boundary (`bv_arith.rs`, Route A), which lifted a BV peer
//!   of an Int-sorted length UNSIGNED unconditionally — so `a.len() + (-3i64)`
//!   was `a.len() + 2^64 - 3`.
//!
//! Together they returned `Verified` for false properties and counterexamples
//! for true ones. Every case below was measured through the same typed seam
//! the rustc-driver front end uses (`VerificationContext::from_typed_parts`,
//! the body of `trust_vc_driver::lower::DriverFn::verify{,_exec}`).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use trust_vc_core::ir::{ArithOp, CompareOp, TrustVcExpr, TrustVcType};
use trust_vc_core::vc::{TypedProofObligation, VariableDecl, VerificationContext};
use trust_vc_core::VerifyResult;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Outcome {
    Verified,
    Refuted,
    Unknown,
}

/// `DriverFn::verify` / `verify_exec`, verbatim: params plus a Bool `result`,
/// each `requires` assumed, the single `ensures` checked.
fn run(
    params: &[(&str, TrustVcType)],
    requires: &[TrustVcExpr],
    ensures: TrustVcExpr,
    exec: bool,
) -> (Outcome, VerifyResult) {
    let mut variables: Vec<VariableDecl> = params
        .iter()
        .map(|(name, ty)| VariableDecl::new((*name).to_string(), ty.clone()))
        .collect();
    variables.push(VariableDecl::new("result".to_string(), TrustVcType::Bool));
    let mut obligations: Vec<TypedProofObligation> = requires
        .iter()
        .enumerate()
        .map(|(i, req)| TypedProofObligation::requires(format!("f_requires_{i}"), req.clone()))
        .collect();
    obligations.push(TypedProofObligation::ensures("f_ensures_0", ensures));
    let mut ctx = VerificationContext::from_typed_parts(variables, obligations);
    if exec {
        ctx.enable_overflow_checks();
    }
    let result = ctx.verify();
    let outcome = match &result {
        VerifyResult::Verified => Outcome::Verified,
        VerifyResult::Counterexample { .. } | VerifyResult::NotProved { .. } => Outcome::Refuted,
        _ => Outcome::Unknown,
    };
    (outcome, result)
}

fn i64_ty() -> TrustVcType {
    TrustVcType::Int { width: 64 }
}

fn lit(value: i128, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::IntLit { value, ty }
}

fn var(name: &str, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty,
    }
}

/// `a.len()` over a `&str` view, typed `i64` exactly as the driver's
/// `strings::str_len` types it. Its TERM is an Int (Route A).
fn str_len(name: &str) -> TrustVcExpr {
    TrustVcExpr::CollectionOp {
        op: trust_vc_core::ir::CollectionOp::Len,
        receiver: Box::new(var(name, TrustVcType::StrSlice)),
        receiver_name: Some(name.to_string()),
        args: vec![],
        ty: i64_ty(),
    }
}

fn arith(op: ArithOp, left: TrustVcExpr, right: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Arith {
        op,
        left: Box::new(left),
        right: Box::new(right),
        ty,
    }
}

fn cmp(op: CompareOp, left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op,
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn len_is(name: &str, value: i128) -> TrustVcExpr {
    cmp(CompareOp::Eq, str_len(name), lit(value, i64_ty()))
}

fn both_modes(
    label: &str,
    params: &[(&str, TrustVcType)],
    requires: &[TrustVcExpr],
    ensures: &TrustVcExpr,
    expected: Outcome,
) {
    for exec in [false, true] {
        let (outcome, raw) = run(params, requires, ensures.clone(), exec);
        assert_eq!(
            outcome, expected,
            "{label} (exec={exec}): expected {expected:?}, raw verdict: {raw:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// The comparison boundary: the LEFT operand shares its bit pattern with a
// literal of the opposite sign inside the RIGHT operand.
// ---------------------------------------------------------------------------

/// requires a.len() == 0; ensures u64::MAX < a.len() + (-1i64)
///
/// FALSE (2^64 - 1 < -1). Measured `Verified` at d4e06963: the right operand's
/// `-1i64` re-registered the shared all-ones BV64 term as signed, and the
/// Route A lift of the left operand then read `u64::MAX` as `-1`.
#[test]
fn u64_max_is_not_below_len_minus_one() {
    both_modes(
        "u64::MAX < a.len() + (-1i64)",
        &[("a", TrustVcType::StrSlice)],
        &[len_is("a", 0)],
        &cmp(
            CompareOp::Lt,
            lit(i128::from(u64::MAX), TrustVcType::Uint { width: 64 }),
            arith(ArithOp::Add, str_len("a"), lit(-1, i64_ty()), i64_ty()),
        ),
        Outcome::Refuted,
    );
}

/// requires a.len() == 0; ensures 200u8 < a.len() + (-56i8)
///
/// FALSE (200 < -56). `200u8` and `-56i8` are the same BV8 term `0xC8`.
#[test]
fn two_hundred_u8_is_not_below_len_minus_56_i8() {
    both_modes(
        "200u8 < a.len() + (-56i8)",
        &[("a", TrustVcType::StrSlice)],
        &[len_is("a", 0)],
        &cmp(
            CompareOp::Lt,
            lit(200, TrustVcType::Uint { width: 8 }),
            // Declared at the type its operands DERIVE (`i64 + i8` is the
            // exact `int`): the `i64` claim is refused (§5b rule 13,
            // `integer_typing_declared_claims.rs`).
            arith(
                ArithOp::Add,
                str_len("a"),
                lit(-56, TrustVcType::Int { width: 8 }),
                TrustVcType::MathInt,
            ),
        ),
        Outcome::Refuted,
    );
}

/// requires a.len() == 0; ensures 255u8 < a.len() + (-1i8)
///
/// FALSE (255 < -1). `255u8` and `-1i8` are the same BV8 term `0xFF`.
#[test]
fn two_fifty_five_u8_is_not_below_len_minus_one_i8() {
    both_modes(
        "255u8 < a.len() + (-1i8)",
        &[("a", TrustVcType::StrSlice)],
        &[len_is("a", 0)],
        &cmp(
            CompareOp::Lt,
            lit(255, TrustVcType::Uint { width: 8 }),
            // Declared at the type its operands DERIVE (`i64 + i8` is the
            // exact `int`): the `i64` claim is refused (§5b rule 13,
            // `integer_typing_declared_claims.rs`).
            arith(
                ArithOp::Add,
                str_len("a"),
                lit(-1, TrustVcType::Int { width: 8 }),
                TrustVcType::MathInt,
            ),
        ),
        Outcome::Refuted,
    );
}

/// The true twin of `u64_max_is_not_below_len_minus_one`, so the pair shows the
/// comparison is decided, not merely refused: requires a.len() == 0;
/// ensures a.len() + (-1i64) < u64::MAX  (-1 < 2^64 - 1).
#[test]
fn len_minus_one_is_below_u64_max() {
    both_modes(
        "a.len() + (-1i64) < u64::MAX",
        &[("a", TrustVcType::StrSlice)],
        &[len_is("a", 0)],
        &cmp(
            CompareOp::Lt,
            arith(ArithOp::Add, str_len("a"), lit(-1, i64_ty()), i64_ty()),
            lit(i128::from(u64::MAX), TrustVcType::Uint { width: 64 }),
        ),
        Outcome::Verified,
    );
}

// ---------------------------------------------------------------------------
// The arithmetic boundary: a SIGNED BV peer of an Int-sorted length.
// ---------------------------------------------------------------------------

/// requires a.len() == 2; ensures a.len() + (-3i64) > 100
///
/// FALSE (-1 > 100). Measured `Verified` at 806b8d3a: `bv_arith.rs` lifted the
/// `-3` peer unsigned, so the sum was `2 + 2^64 - 3`.
#[test]
fn len_plus_negative_literal_is_not_large() {
    both_modes(
        "a.len() + (-3i64) > 100",
        &[("a", TrustVcType::StrSlice)],
        &[len_is("a", 2)],
        &cmp(
            CompareOp::Gt,
            arith(ArithOp::Add, str_len("a"), lit(-3, i64_ty()), i64_ty()),
            lit(100, i64_ty()),
        ),
        Outcome::Refuted,
    );
}

/// requires a.len() == 2, n == -3; ensures a.len() + n > 100  (n: i64)
///
/// FALSE; the same unsigned lift, through a signed VARIABLE peer.
#[test]
fn len_plus_negative_variable_is_not_large() {
    both_modes(
        "a.len() + n > 100, n == -3",
        &[("a", TrustVcType::StrSlice), ("n", i64_ty())],
        &[
            len_is("a", 2),
            cmp(CompareOp::Eq, var("n", i64_ty()), lit(-3, i64_ty())),
        ],
        &cmp(
            CompareOp::Gt,
            arith(ArithOp::Add, str_len("a"), var("n", i64_ty()), i64_ty()),
            lit(100, i64_ty()),
        ),
        Outcome::Refuted,
    );
}

/// requires a.len() == 2; ensures a.len() + (-3i64) < 0
///
/// TRUE (-1 < 0). Measured with a FALSE counterexample at 806b8d3a.
#[test]
fn len_plus_negative_literal_is_negative() {
    both_modes(
        "a.len() + (-3i64) < 0",
        &[("a", TrustVcType::StrSlice)],
        &[len_is("a", 2)],
        &cmp(
            CompareOp::Lt,
            arith(ArithOp::Add, str_len("a"), lit(-3, i64_ty()), i64_ty()),
            lit(0, i64_ty()),
        ),
        Outcome::Verified,
    );
}

/// requires a.len() == 2, n == -3; ensures a.len() - n == 5  (n: i64)
///
/// TRUE (2 - (-3) == 5). Measured with a FALSE counterexample at 806b8d3a.
#[test]
fn len_minus_negative_variable_is_five() {
    both_modes(
        "a.len() - n == 5, n == -3",
        &[("a", TrustVcType::StrSlice), ("n", i64_ty())],
        &[
            len_is("a", 2),
            cmp(CompareOp::Eq, var("n", i64_ty()), lit(-3, i64_ty())),
        ],
        &cmp(
            CompareOp::Eq,
            arith(ArithOp::Sub, str_len("a"), var("n", i64_ty()), i64_ty()),
            lit(5, i64_ty()),
        ),
        Outcome::Verified,
    );
}

// ---------------------------------------------------------------------------
// Found by the property check (`operand_signedness_proptest.rs`) once the two
// boundaries above were fixed: the same class — an operand read with a
// signedness or width that is not its own — at the comparison and the
// arithmetic encoders, and one unsound ASSUMPTION of unchecked arithmetic.
// ---------------------------------------------------------------------------

fn u8_ty() -> TrustVcType {
    TrustVcType::Uint { width: 8 }
}

fn i8_ty() -> TrustVcType {
    TrustVcType::Int { width: 8 }
}

fn i32_ty() -> TrustVcType {
    TrustVcType::Int { width: 32 }
}

fn pinned(name: &str, ty: &TrustVcType, value: i128) -> TrustVcExpr {
    cmp(CompareOp::Eq, var(name, ty.clone()), lit(value, ty.clone()))
}

/// requires x == 255 (u8), y == -1 (i8); ensures x == y. FALSE: one BV8
/// term, two integers. The equal-width BV comparison compared the BITS
/// (`Verified`); a mixed pair is now compared as the integers it denotes.
#[test]
fn same_bits_opposite_sign_values_are_not_equal() {
    both_modes(
        "x: u8 == 255 == y: i8 == -1",
        &[("x", u8_ty()), ("y", i8_ty())],
        &[pinned("x", &u8_ty(), 255), pinned("y", &i8_ty(), -1)],
        &cmp(CompareOp::Eq, var("x", u8_ty()), var("y", i8_ty())),
        Outcome::Refuted,
    );
}

/// requires x == 200 (u8), y == 100 (i8); ensures x < y. FALSE (200 < 100).
/// The equal-width mixed pair went to `bvslt`, which reads `x` as `-56`.
#[test]
fn unsigned_above_signed_range_is_not_below_it() {
    both_modes(
        "x: u8 == 200 < y: i8 == 100",
        &[("x", u8_ty()), ("y", i8_ty())],
        &[pinned("x", &u8_ty(), 200), pinned("y", &i8_ty(), 100)],
        &cmp(CompareOp::Lt, var("x", u8_ty()), var("y", i8_ty())),
        Outcome::Refuted,
    );
}

/// requires x0 == 4294967295 (u32), x1 == -1 (i32); ensures x0 == x1. FALSE.
/// After equality substitution the right operand is the literal `-1` typed
/// `Int{32}` — the unsuffixed placeholder — which the peer hint retyped to
/// `u32`, i.e. `4294967295` (`Verified`). A negative literal is never retyped
/// to an unsigned type.
#[test]
fn u32_max_is_not_minus_one_after_substitution() {
    let u32_ty = TrustVcType::Uint { width: 32 };
    both_modes(
        "x0: u32 == u32::MAX == x1: i32 == -1",
        &[("x0", u32_ty.clone()), ("x1", i32_ty())],
        &[
            pinned("x0", &u32_ty, 4_294_967_295),
            pinned("x1", &i32_ty(), -1),
        ],
        &cmp(CompareOp::Eq, var("x0", u32_ty), var("x1", i32_ty())),
        Outcome::Refuted,
    );
}

/// requires x0 == 0, x1 == 1 (i32), x2 == 0 (u8); ensures x0 - x1 > x2.
/// FALSE (-1 > 0). Substituting the pinned `i32` variables CLOSED a tree of
/// `Int{32}` literals, which the `u8` peer then retyped: `0u8 - 1u8 == 255`
/// (`Verified`). Its true twin (`<`) was refuted.
#[test]
fn i32_difference_is_not_retyped_by_a_u8_peer() {
    let params = [("x0", i32_ty()), ("x1", i32_ty()), ("x2", u8_ty())];
    let requires = [
        pinned("x0", &i32_ty(), 0),
        pinned("x1", &i32_ty(), 1),
        pinned("x2", &u8_ty(), 0),
    ];
    let diff = || {
        arith(
            ArithOp::Sub,
            var("x0", i32_ty()),
            var("x1", i32_ty()),
            i32_ty(),
        )
    };
    both_modes(
        "x0 - x1 > x2",
        &params,
        &requires,
        &cmp(CompareOp::Gt, diff(), var("x2", u8_ty())),
        Outcome::Refuted,
    );
    both_modes(
        "x0 - x1 < x2",
        &params,
        &requires,
        &cmp(CompareOp::Lt, diff(), var("x2", u8_ty())),
        Outcome::Verified,
    );
}

/// requires x0 == i32::MAX, x1 == -1 (i32), x2 == 0 (i64); ensures
/// x0 - x1 >= x2. FALSE: the `i32` difference wraps to `i32::MIN`. The same
/// substitution retyped it to the `i64` peer, where it is `2^31`.
#[test]
fn i32_difference_is_not_widened_by_an_i64_peer() {
    let i64_ty = TrustVcType::Int { width: 64 };
    let (outcome, raw) = run(
        &[("x0", i32_ty()), ("x1", i32_ty()), ("x2", i64_ty.clone())],
        &[
            pinned("x0", &i32_ty(), i128::from(i32::MAX)),
            pinned("x1", &i32_ty(), -1),
            pinned("x2", &i64_ty, 0),
        ],
        cmp(
            CompareOp::Ge,
            arith(
                ArithOp::Sub,
                var("x0", i32_ty()),
                var("x1", i32_ty()),
                i32_ty(),
            ),
            var("x2", i64_ty),
        ),
        false,
    );
    assert_eq!(outcome, Outcome::Refuted, "raw verdict: {raw:?}");
}

/// requires x0 == 3, x1 == 86, x2 == 0 (u8); ensures x0 - x1 == x2, under
/// EXEC semantics. FALSE (the wrapped difference is 173). An `ensures` is spec
/// arithmetic and is never overflow-checked — but the main solve still
/// ASSUMED its no-underflow predicate, which the pinned values contradict, so
/// the goal was vacuously `Verified`. It must be refuted in both modes.
#[test]
fn unchecked_spec_arithmetic_is_not_assumed_overflow_free() {
    let sub = arith(
        ArithOp::Sub,
        var("x0", u8_ty()),
        var("x1", u8_ty()),
        u8_ty(),
    );
    both_modes(
        "x0 - x1 == x2 (u8)",
        &[("x0", u8_ty()), ("x1", u8_ty()), ("x2", u8_ty())],
        &[
            pinned("x0", &u8_ty(), 3),
            pinned("x1", &u8_ty(), 86),
            pinned("x2", &u8_ty(), 0),
        ],
        &cmp(CompareOp::Eq, sub, var("x2", u8_ty())),
        Outcome::Refuted,
    );
}
