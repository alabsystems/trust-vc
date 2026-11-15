//! Shift-by->=bit-width soundness tests (#1868).
//!
//! Unlike arithmetic overflow (which wraps safely in release mode),
//! out-of-range shifts are UB in ALL Rust modes. The shift bounds check
//! must fire even WITHOUT `with_overflow_checks()`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use ay_dpll::api::{Logic, Solver, Sort};

struct DirectShiftEnv {
    solver: Solver,
    variables: std::collections::HashMap<String, Term>,
    collection_lengths: std::collections::HashMap<String, Term>,
    var_types: std::collections::HashMap<String, crate::ir::TrustVcType>,
    functions: std::collections::HashMap<String, FuncDecl>,
}

impl DirectShiftEnv {
    fn new() -> Self {
        Self {
            solver: Solver::try_new(Logic::All).unwrap(),
            variables: std::collections::HashMap::new(),
            collection_lengths: std::collections::HashMap::new(),
            var_types: std::collections::HashMap::new(),
            functions: std::collections::HashMap::new(),
        }
    }

    fn parser(&mut self) -> AstExpressionParser<'_> {
        AstExpressionParser::new(
            &mut self.solver,
            &self.variables,
            &mut self.collection_lengths,
            &self.var_types,
            &self.functions,
        )
    }
}

fn assert_shift_guard_result(
    solver: &mut Solver,
    shift_amount: Term,
    guard: Term,
    rhs_width: u32,
    value: i64,
    should_hold: bool,
    label: &str,
) {
    let value_term = solver.try_bv_const(value, rhs_width).unwrap();
    let eq = solver.try_eq(shift_amount, value_term).unwrap();
    let contradiction = if should_hold {
        solver.try_not(guard).unwrap()
    } else {
        guard
    };

    solver.try_push().unwrap();
    solver.try_assert_term(eq).unwrap();
    solver.try_assert_term(contradiction).unwrap();
    let sat_result = solver.try_check_sat().unwrap();
    let sat = sat_result.result();
    solver.try_pop().unwrap();

    assert!(
        sat.is_unsat(),
        "{} guard for shift {} with rhs width {} should {}hold, got {:?}",
        label,
        value,
        rhs_width,
        if should_hold { "" } else { "not " },
        sat
    );
}

/// DISCRIMINATING: Left shift by a valid amount should verify even without
/// overflow checks. 1u32 << 5 = 32 is fine — the shift amount is in range.
#[test]
fn test_shl_valid_shift_no_overflow_checks_verifies() {
    let mut ctx = VerificationContext::new(); // no with_overflow_checks()
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("val", "x == 1"));
    ctx.push_obligation(ProofObligation::assert("shifted", "(x << 5) == 32"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "1u32 << 5 == 32 should verify without overflow checks",
    );
}

/// DISCRIMINATING: Left shift by >= bit width must NOT verify even without
/// overflow checks. 1u32 << 32 is UB in Rust regardless of overflow mode.
#[test]
fn test_shl_by_bitwidth_no_overflow_checks_not_verified() {
    let mut ctx = VerificationContext::new(); // no with_overflow_checks()
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("val", "x == 1"));
    ctx.push_obligation(ProofObligation::assert("shifted", "(x << 32) == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "1u32 << 32 must NOT verify without overflow checks — shift >= width is UB",
    );
}

/// DISCRIMINATING: Right shift by >= bit width must NOT verify even without
/// overflow checks. 100u32 >> 32 is UB in Rust regardless of overflow mode.
#[test]
fn test_shr_by_bitwidth_no_overflow_checks_not_verified() {
    let mut ctx = VerificationContext::new(); // no with_overflow_checks()
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("val", "x == 100"));
    ctx.push_obligation(ProofObligation::assert("shifted", "(x >> 32) == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "100u32 >> 32 must NOT verify without overflow checks — shift >= width is UB",
    );
}

/// DISCRIMINATING: Variable shift amount that could overflow must NOT verify
/// even without overflow checks. If n is unconstrained, it could be >= 32.
#[test]
fn test_shl_variable_unbounded_no_overflow_checks_not_verified() {
    let mut ctx = VerificationContext::new(); // no with_overflow_checks()
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 1"));
    // n is unconstrained — could be >= 32, triggering shift bounds check
    ctx.push_obligation(ProofObligation::assert("result", "(x << n) >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "x << n with unbounded n must NOT verify without overflow checks — UB",
    );
}

/// DISCRIMINATING: Mixed-width shift must use LHS width for bounds.
/// For `u32 << u64`, n=40 is out-of-range for u32 and must NOT verify.
#[test]
fn test_shl_mixed_width_rhs_uses_lhs_width_bound() {
    let mut ctx = VerificationContext::new(); // no with_overflow_checks()
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 1"));
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 40"));
    // Tautology: only shift-bound checks can make this fail.
    ctx.push_obligation(ProofObligation::assert("tautology", "(x << n) == (x << n)"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "u32 << u64 with n=40 must NOT verify — LHS width bound is 32",
    );
}

/// CONTROL: Mixed-width shift with in-range RHS should verify.
#[test]
fn test_shl_mixed_width_rhs_in_range_verifies() {
    let mut ctx = VerificationContext::new(); // no with_overflow_checks()
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 1"));
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 5"));
    ctx.push_obligation(ProofObligation::assert("tautology", "(x << n) == (x << n)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "u32 << u64 with n=5 should verify — shift amount in range",
    );
}

/// DISCRIMINATING: Mixed-width shift result keeps the LHS width.
/// `0x8000_0000u32 << 1u64` wraps in u32 to 0; it must not be encoded as a
/// widened 64-bit shift that produces 0x1_0000_0000.
#[test]
fn test_shl_mixed_width_rhs_keeps_lhs_width_result() {
    let mut ctx = VerificationContext::new(); // no with_overflow_checks()
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 2147483648"));
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 1"));
    ctx.push_obligation(ProofObligation::assert("u32_wrap", "(x << n) == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "u32 << u64 should keep u32 result width and wrap high bit out",
    );
}

/// DISCRIMINATING: The same shift must not expose a widened 64-bit result
/// through a cast after the shift.
#[test]
fn test_shl_mixed_width_rhs_does_not_widen_lhs_result() {
    let mut ctx = VerificationContext::new(); // no with_overflow_checks()
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 2147483648"));
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "not_widened",
        "(x << n) as u64 == 4294967296",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "u32 << u64 must not verify as a widened 64-bit shift result",
    );
}

/// DISCRIMINATING: Mixed-width right shift must use LHS width for bounds.
/// For `u32 >> u64`, n=40 is out-of-range for u32 and must NOT verify.
#[test]
fn test_shr_mixed_width_rhs_uses_lhs_width_bound() {
    let mut ctx = VerificationContext::new(); // no with_overflow_checks()
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 40"));
    // Tautology: only shift-bound checks can make this fail.
    ctx.push_obligation(ProofObligation::assert("tautology", "(x >> n) == (x >> n)"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "u32 >> u64 with n=40 must NOT verify — LHS width bound is 32",
    );
}

/// CONTROL: Mixed-width right shift with in-range RHS should verify.
#[test]
fn test_shr_mixed_width_rhs_in_range_verifies() {
    let mut ctx = VerificationContext::new(); // no with_overflow_checks()
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 5"));
    ctx.push_obligation(ProofObligation::assert("tautology", "(x >> n) == (x >> n)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "u32 >> u64 with n=5 should verify — shift amount in range",
    );
}

// ========================================================================
// Direct helper contract regression (#2297)
// ========================================================================

/// DISCRIMINATING: `check_shift_overflow` must honor an explicit 64-bit bound
/// even when the raw BV64 shift term has no `term_widths` metadata entry.
#[test]
fn test_shl_direct_guard_uses_explicit_u64_bound_without_metadata() {
    let mut env = DirectShiftEnv::new();
    let shift_amount = env.solver.declare_const("n", Sort::bitvec(64));
    let guard = {
        let mut parser = env.parser();
        parser
            .check_shift_overflow(shift_amount, 64, "left shift")
            .expect("raw BV64 left shift should accept an explicit lhs width");
        let checks = parser.take_overflow_checks();
        assert_eq!(checks.len(), 1, "expected one left-shift overflow guard");
        checks.into_iter().next().unwrap().1
    };

    assert_shift_guard_result(
        &mut env.solver,
        shift_amount,
        guard,
        64,
        40,
        true,
        "left shift",
    );
    assert_shift_guard_result(
        &mut env.solver,
        shift_amount,
        guard,
        64,
        64,
        false,
        "left shift",
    );
}

/// DISCRIMINATING: Mixed-width shifts must still use the explicit 64-bit LHS
/// bound even when the shift amount itself is only a BV32 term.
#[test]
fn test_shr_direct_guard_uses_explicit_lhs_bound_for_mixed_width_rhs() {
    let mut env = DirectShiftEnv::new();
    let shift_amount = env.solver.declare_const("n", Sort::bitvec(32));
    let guard = {
        let mut parser = env.parser();
        parser.term_widths.insert(shift_amount, (32, false));
        parser
            .check_shift_overflow(shift_amount, 64, "right shift")
            .expect("mixed-width right shift should accept an explicit lhs width");
        let checks = parser.take_overflow_checks();
        assert_eq!(checks.len(), 1, "expected one right-shift overflow guard");
        checks.into_iter().next().unwrap().1
    };

    assert_shift_guard_result(
        &mut env.solver,
        shift_amount,
        guard,
        32,
        40,
        true,
        "right shift",
    );
    assert_shift_guard_result(
        &mut env.solver,
        shift_amount,
        guard,
        32,
        64,
        false,
        "right shift",
    );
}

// ========================================================================
// `global size_of usize == N` architecture directive (#2778)
//
// The directive binds usize/isize bit width for verification. Because
// `declare_var_typed` resolves the width via `pointer_width()` at declaration
// time, the `PointerWidthGuard` must be installed BEFORE declaring usize vars.
// ========================================================================

/// Under `global size_of usize == 4`, `usize << 32` shifts by the bit width and
/// must fail closed (UB), mirroring upstream `bit_shift_overflow_arch32`.
#[test]
fn test_usize_shl_by_32_fails_under_arch32() {
    let _guard = crate::ir::PointerWidthGuard::install(32);
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("usize"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("usize"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 32"));
    ctx.push_obligation(ProofObligation::assert("tautology", "(x << y) == (x << y)"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "usize << 32 must NOT verify under 32-bit usize — shift >= width is UB",
    );
}

/// Under `global size_of usize == 4`, `usize << 31` is in range and verifies,
/// mirroring upstream `bit_shift_overflow_arch32::test_usize_overflow2`.
#[test]
fn test_usize_shl_by_31_ok_under_arch32() {
    let _guard = crate::ir::PointerWidthGuard::install(32);
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("usize"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("usize"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 31"));
    ctx.push_obligation(ProofObligation::assert("tautology", "(x << y) == (x << y)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "usize << 31 should verify under 32-bit usize — shift amount in range",
    );
}

/// Under `global size_of usize == 8`, `usize << 63` is in range and verifies,
/// mirroring upstream `bit_shift_overflow_arch64::test_usize_overflow2`.
#[test]
fn test_usize_shl_by_63_ok_under_arch64() {
    let _guard = crate::ir::PointerWidthGuard::install(64);
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("usize"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("usize"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 63"));
    ctx.push_obligation(ProofObligation::assert("tautology", "(x << y) == (x << y)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "usize << 63 should verify under 64-bit usize — shift amount in range",
    );
}

/// Under `global size_of usize == 8`, `usize << 64` shifts by the bit width and
/// must fail closed (UB), mirroring upstream `bit_shift_overflow_arch64`.
#[test]
fn test_usize_shl_by_64_fails_under_arch64() {
    let _guard = crate::ir::PointerWidthGuard::install(64);
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("usize"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("usize"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 64"));
    ctx.push_obligation(ProofObligation::assert("tautology", "(x << y) == (x << y)"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "usize << 64 must NOT verify under 64-bit usize — shift >= width is UB",
    );
}

/// CONTROL: the same `usize << 32` that fails under 32-bit usize is IN RANGE
/// under 64-bit usize. This proves the directive actually changes the width
/// the shift-bound check uses, rather than the result being a host-width
/// coincidence.
#[test]
fn test_usize_shl_by_32_ok_under_arch64() {
    let _guard = crate::ir::PointerWidthGuard::install(64);
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("usize"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("usize"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 32"));
    ctx.push_obligation(ProofObligation::assert("tautology", "(x << y) == (x << y)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "usize << 32 should verify under 64-bit usize — 32 < 64 is in range",
    );
}

/// Width-specific bit-vector fact: under 32-bit usize, `(y >> 32) == 0` is the
/// upper bound of the type and holds for the unsigned shift width. We model the
/// width-bounded fact as: shifting a 32-bit value right by 31 yields a value
/// `< 2`. Under 64-bit usize the same expression is unconstrained, proving the
/// directive drives width-specific reasoning (mirrors upstream
/// `bit_vector_usize_as_32bit`/`64bit` intent).
#[test]
fn test_usize_high_bit_shift_fact_is_width_specific() {
    // 32-bit: y >> 31 keeps only the top bit, so it is always 0 or 1, hence < 2.
    {
        let _guard = crate::ir::PointerWidthGuard::install(32);
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("usize"));
        ctx.push_obligation(ProofObligation::assert("top_bit", "(y >> 31) < 2"));
        let result = AYEncoder::verify(&ctx);
        expect_verified(
            &result,
            "32-bit usize: (y >> 31) keeps only the top bit, so it is < 2",
        );
    }
    // 64-bit: y >> 31 still has 33 live bits, so it is NOT bounded below 2.
    {
        let _guard = crate::ir::PointerWidthGuard::install(64);
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("usize"));
        ctx.push_obligation(ProofObligation::assert("top_bit", "(y >> 31) < 2"));
        let result = AYEncoder::verify(&ctx);
        expect_fail_closed(
            &result,
            "64-bit usize: (y >> 31) has 33 live bits and is NOT bounded below 2",
        );
    }
}

// ========================================================================
// Normal-mode signed-shift `possible bit shift underflow/overflow` parity
// (#2778)
//
// Upstream Verus (`vir/src/ast_to_sst.rs`, `BitshiftBehavior::Error`) emits
// `possible bit shift underflow/overflow` for an exec bit-shift whose shift
// amount is not provably in `[0, width)`. A *signed* shift amount is possibly
// negative, so the bound cannot be discharged without a proof that it is
// nonnegative — exactly the upstream tests `bit_shift_underflow` (i16 << i16)
// and `bit_shift_unsigned_shift_signed` (u16 << i16).
//
// Both upstream cases report via `assert_vir_error_msg` (an error with no
// diagnostic code), which the trust-vc evidence gate maps to
// `VerusExpectedVerdict::Error` — NOT `VerusExpectedVerdict::Counterexample`
// (the `assert_fails` mapping used by the unsigned over-shift cases). trust-vc
// therefore routes an out-of-range *signed* shift failure to
// `VerifyResult::Error` instead of a model-bearing `VerifyResult::Counterexample`,
// reproducing the upstream verdict distinction byte-for-byte.
//
// Soundness: the underlying `bvult` obligation is identical to the
// counterexample path. Only the *out-of-range* SAT failure is reclassified;
// a provably-in-range nonnegative signed amount still solves UNSAT and verifies
// (see `test_signed_shift_amount_in_range_still_verifies`). The reclassification
// rejects exactly the programs the counterexample path rejected — strictly the
// same programs Verus rejects — so it cannot accept anything new and cannot
// reject a legitimate in-range signed shift.
// ========================================================================

/// Pull the `obligation_name` out of a [`VerifyResult::Counterexample`], failing
/// the test if the result is anything else.
#[track_caller]
fn counterexample_obligation_name(result: &crate::encoder::VerifyResult, context: &str) -> String {
    match result {
        crate::encoder::VerifyResult::Counterexample {
            obligation_name, ..
        } => obligation_name.clone(),
        other => panic!("{context} should be a Counterexample, got: {other:?}"),
    }
}

/// Upstream `overflow.rs::bit_shift_underflow`: `let z = (x: i16) << (y: i16)`
/// with `y == -1` must fail closed as a VIR-level `VerifyResult::Error`, and the
/// diagnostic must carry the byte-exact upstream substring
/// `possible bit shift underflow/overflow` (a signed shift amount is possibly
/// negative). `expect_error_containing` asserts both the `Error` shape (upstream
/// `assert_vir_error_msg`, not `assert_fails`) and the message substring.
#[test]
fn test_signed_shift_amount_fails_with_bit_shift_underflow_overflow_message() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i16"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i16"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == -1"));
    // Tautology: only the shift-bounds check can make this fail.
    ctx.push_obligation(ProofObligation::assert("taut", "(x << y) == (x << y)"));

    let result = AYEncoder::verify(&ctx);
    expect_error_containing(
        &result,
        "possible bit shift underflow/overflow",
        "i16 << i16 with y == -1 must fail closed as a VIR-level error \
         (possibly-negative shift amount)",
    );
}

/// Upstream `overflow.rs::bit_shift_unsigned_shift_signed`:
/// `let z = (x: u16) << (y: i16)` with `y == -1`. The LHS is *unsigned* but the
/// shift amount is *signed*; the message keys off the RHS type, so this also
/// fails closed as a `VerifyResult::Error` carrying
/// `possible bit shift underflow/overflow`.
#[test]
fn test_unsigned_lhs_signed_shift_amount_fails_with_bit_shift_underflow_overflow_message() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u16"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i16"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == -1"));
    ctx.push_obligation(ProofObligation::assert("taut", "(x << y) == (x << y)"));

    let result = AYEncoder::verify(&ctx);
    expect_error_containing(
        &result,
        "possible bit shift underflow/overflow",
        "u16 << i16 with y == -1 must fail closed as a VIR-level error \
         (possibly-negative shift amount)",
    );
}

/// SHOULD-VERIFY control for `bit_shift_unsigned_shift_signed`
/// (`let z = (x: u16) << (y: i16)`): a *signed* shift amount that is provably
/// nonnegative and in `[0, 16)` must still verify, even though the LHS is
/// unsigned and the RHS is signed. This is the missing positive direction for
/// the unsigned-LHS/signed-RHS shape — its fail direction is pinned by
/// `test_unsigned_lhs_signed_shift_amount_fails_with_bit_shift_underflow_overflow_message`.
/// It proves the `bit shift underflow/overflow` reclassification fires ONLY on
/// the out-of-range branch and never rejects a legitimate in-range signed shift
/// of an unsigned value. The obligation is identical to every other shift bound
/// check; the assert is a tautology, so only the shift-bounds check can fail.
/// Part of #2778.
#[test]
fn test_unsigned_lhs_signed_shift_amount_in_range_still_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u16"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i16"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    // 0 <= 3 < 16: a provably-nonnegative, in-range signed i16 shift amount.
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 3"));
    ctx.push_obligation(ProofObligation::assert("taut", "(x << y) == (x << y)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "u16 << i16 with a provably-in-range nonnegative amount (y == 3) must still verify",
    );
}

/// SHOULD-FAIL direction for `bit_shift_underflow` matching the upstream
/// `// FAILS` shape literally: `(x: i16) << 16i16`. The shift amount is a
/// *signed literal equal to the bit width* (16 == width 16), so it is out of
/// range. Because the RHS type is signed, this routes through the
/// `possible bit shift underflow/overflow` VIR-error path (`assert_vir_error_msg`,
/// not `assert_fails`), so we assert both the `Error` shape and the byte-exact
/// upstream message. Complements the `y == -1` assumption-driven variant by
/// exercising the literal-amount path on the over-shift (not the negative)
/// branch. Part of #2778.
#[test]
fn test_signed_shift_by_width_literal_fails_with_bit_shift_underflow_overflow_message() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i16"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    // `16i16` is a signed literal equal to the i16 bit width — out of `[0, 16)`.
    ctx.push_obligation(ProofObligation::assert(
        "taut",
        "(x << 16i16) == (x << 16i16)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_error_containing(
        &result,
        "possible bit shift underflow/overflow",
        "i16 << 16i16 (signed literal == width) must fail closed as a VIR-level error \
         (out-of-range signed shift amount)",
    );
}

/// Right shift with a signed amount must carry the same parity message — the
/// diagnostic keys off the RHS type, not the shift direction.
#[test]
fn test_signed_right_shift_amount_fails_with_bit_shift_underflow_overflow_message() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i16"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i16"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == -1"));
    ctx.push_obligation(ProofObligation::assert("taut", "(x >> y) == (x >> y)"));

    let result = AYEncoder::verify(&ctx);
    expect_error_containing(
        &result,
        "possible bit shift underflow/overflow",
        "i16 >> i16 with y == -1 must fail closed as a VIR-level error \
         (possibly-negative shift amount)",
    );
}

/// SHOULD-VERIFY direction: a signed shift amount that is *provably* in
/// `[0, width)` must still verify. The diagnostic-parity wiring changes only
/// the failure label, never the underlying obligation, so a nonnegative,
/// in-range signed amount is accepted exactly as upstream accepts it. This is
/// the control that proves the change does not unsoundly reject (nor falsely
/// fail) a legitimate signed shift.
#[test]
fn test_signed_shift_amount_in_range_still_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i16"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i16"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    // 0 <= 3 < 16: provably in range for an i16 shift amount.
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 3"));
    ctx.push_obligation(ProofObligation::assert("taut", "(x << y) == (x << y)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "i16 << i16 with a provably-in-range nonnegative amount must still verify",
    );
}

/// REGRESSION GUARD: an *unsigned* over-shift keeps its existing
/// `left shift overflow` diagnostic and must NOT be relabeled as the signed
/// bit-shift-underflow message. Confirms the parity label keys strictly on a
/// signed RHS type.
#[test]
fn test_unsigned_overshift_keeps_left_shift_overflow_message() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 1"));
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 40"));
    ctx.push_obligation(ProofObligation::assert("taut", "(x << n) == (x << n)"));

    let result = AYEncoder::verify(&ctx);
    let name = counterexample_obligation_name(
        &result,
        "u32 << u32 with n == 40 must fail closed (shift amount >= width)",
    );
    assert!(
        name.contains("possible left shift overflow"),
        "unsigned over-shift must keep its `left shift overflow` diagnostic, got: {name}"
    );
    assert!(
        !name.contains("bit shift underflow/overflow"),
        "unsigned over-shift must NOT be relabeled as the signed parity message, got: {name}"
    );
}

/// SHOULD-FAIL (verdict-shape) direction: an out-of-range signed shift must
/// surface as a `VerifyResult::Error`, and explicitly NOT as a
/// `VerifyResult::Counterexample`. This is the verdict-shape guard for the
/// upstream `assert_vir_error_msg` -> `VerusExpectedVerdict::Error` mapping;
/// a regression that reverted to a counterexample would silently mis-match the
/// gate's expected verdict and is caught here. Part of #2778.
#[test]
fn test_signed_out_of_range_shift_is_error_not_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i16"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i16"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == -1"));
    ctx.push_obligation(ProofObligation::assert("taut", "(x << y) == (x << y)"));

    let result = AYEncoder::verify(&ctx);
    // `expect_error` asserts the `Error` shape and panics on `Counterexample`,
    // pinning both directions of the verdict-shape boundary at once.
    expect_error(
        &result,
        "a possibly-negative signed shift amount must surface as VerifyResult::Error \
         (upstream `assert_vir_error_msg`), never a model-bearing Counterexample",
    );
}

/// SHOULD-VERIFY direction (positive literal amount): a signed shift by a
/// provably-in-range *literal* must verify, exercising the literal-amount path
/// distinctly from the assumption-constrained variable case. Confirms the
/// Error reclassification only fires on the out-of-range branch and never
/// rejects a legitimate in-range signed shift. Part of #2778.
#[test]
fn test_signed_shift_by_in_range_literal_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i16"));
    // `3i16` is a nonnegative literal provably in `[0, 16)`.
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "taut",
        "(x << 3i16) == (x << 3i16)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "i16 << 3i16 (in-range nonnegative literal amount) must verify",
    );
}

/// REGRESSION GUARD (verdict shape): the unsigned over-shift failure must keep
/// `VerifyResult::Counterexample` and must NOT be reclassified to
/// `VerifyResult::Error`. Pairs with
/// `test_signed_out_of_range_shift_is_error_not_counterexample` to pin the exact
/// signed-vs-unsigned verdict-shape boundary. Part of #2778.
#[test]
fn test_unsigned_overshift_is_counterexample_not_error() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 1"));
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 40"));
    ctx.push_obligation(ProofObligation::assert("taut", "(x << n) == (x << n)"));

    let result = AYEncoder::verify(&ctx);
    // `expect_counterexample` asserts the `Counterexample` shape and panics on
    // `Error`, so it pins that the unsigned over-shift is NOT reclassified.
    expect_counterexample(
        &result,
        "an unsigned over-shift (>= width) must stay a Counterexample \
         (upstream `assert_fails`), never reclassified to VerifyResult::Error",
    );
}

// ========================================================================
// `.shl()` / `.shr()` primitive-integer method-call lowering (#2779)
//
// Upstream Verus `operators.rs::test_arith` exercises the `core::ops::Shl::shl`
// / `core::ops::Shr::shr` method-call forms on primitive integers:
//
//     fn test_shl(u: u16) { let _ = u.shl(15u16); let _ = u.shl(16u16); /*FAILS*/ }
//     fn test_shr(u: i16) { let _ = u.shr(15i16); let _ = u.shr(16i16); /*FAILS*/ }
//
// trust-vc lowers these method calls to the same `SpecialArith { op: Shl/Shr }`
// IR as the binary `<<`/`>>` operators (`dispatch::methods::
// lower_primitive_integer_trait_method_call`), so they reuse the already-verified
// sound shift-overflow checker (`encode_bv_shift`, which fails closed when the
// amount `>= width`). The obligation-string path routes through
// `syn::parse_str` -> `lower_syn_expr` -> the same method dispatch, so these
// asserts exercise the method-call lowering exactly as source would.
//
// The asserts below are tautologies (`(e) == (e)`); only the shift-bounds check
// can make them fail, so an in-range amount verifies and an out-of-range amount
// fails closed — byte-matching upstream `test_shl`/`test_shr` (15 Ok, 16 FAILS).
// ========================================================================

/// SHOULD-VERIFY: `u.shl(15u16)` with `u: u16` — amount 15 < 16 is in range, so
/// the method-call form verifies, mirroring upstream `test_shl`'s first line.
#[test]
fn test_shl_method_call_in_range_amount_verifies() {
    let mut ctx = VerificationContext::new();
    // The source imports `std::ops::{Shl, Shr}`.
    ctx.set_std_operator_methods(["shl", "shr"]);
    ctx.declare_var_typed("u", crate::ir::TrustVcType::parse_or_opaque("u16"));
    // Tautology: only the shift-bounds check can make this fail.
    ctx.push_obligation(ProofObligation::assert(
        "taut",
        "u.shl(15u16) == u.shl(15u16)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "u16.shl(15u16) must verify — amount 15 < 16 is in range (upstream test_shl line 1)",
    );
}

/// SHOULD-FAIL: `u.shl(16u16)` with `u: u16` — amount 16 == width is UB, so the
/// method-call form fails closed as a counterexample, mirroring upstream
/// `test_shl`'s second line (`// FAILS`). This is the soundness witness: the
/// method lowering does NOT bypass the shift-overflow obligation.
#[test]
fn test_shl_method_call_by_bitwidth_amount_is_counterexample() {
    let mut ctx = VerificationContext::new();
    // The source imports `std::ops::{Shl, Shr}`.
    ctx.set_std_operator_methods(["shl", "shr"]);
    ctx.declare_var_typed("u", crate::ir::TrustVcType::parse_or_opaque("u16"));
    ctx.push_obligation(ProofObligation::assert(
        "taut",
        "u.shl(16u16) == u.shl(16u16)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "u16.shl(16u16) must fail closed — amount 16 >= width 16 is UB (upstream test_shl line 2 FAILS)",
    );
}

/// SHOULD-VERIFY: `u.shr(15i16)` with `u: i16` — a nonnegative, in-range signed
/// amount (15 < 16) verifies via the method-call form, mirroring upstream
/// `test_shr`'s first line.
#[test]
fn test_shr_method_call_in_range_amount_verifies() {
    let mut ctx = VerificationContext::new();
    // The source imports `std::ops::{Shl, Shr}`.
    ctx.set_std_operator_methods(["shl", "shr"]);
    ctx.declare_var_typed("u", crate::ir::TrustVcType::parse_or_opaque("i16"));
    ctx.push_obligation(ProofObligation::assert(
        "taut",
        "u.shr(15i16) == u.shr(15i16)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "i16.shr(15i16) must verify — amount 15 is nonnegative and < 16 (upstream test_shr line 1)",
    );
}

/// SHOULD-FAIL: `u.shr(16i16)` with `u: i16` — amount 16 == width is out of
/// range, so the method-call form fails closed, mirroring upstream `test_shr`'s
/// second line (`// FAILS`). The shift amount is *signed* (`i16`), so — exactly
/// like the binary `>>` path — it routes through the `bit shift
/// underflow/overflow` VIR-error path (a signed amount is possibly negative,
/// matching upstream `assert_vir_error_msg`). We therefore assert the `Error`
/// shape AND the byte-exact upstream message via `expect_error_containing`,
/// identical to the existing signed-shift parity tests above. This is the
/// soundness witness: the method lowering does NOT bypass the shift obligation.
#[test]
fn test_shr_method_call_by_bitwidth_signed_amount_is_vir_error() {
    let mut ctx = VerificationContext::new();
    // The source imports `std::ops::{Shl, Shr}`.
    ctx.set_std_operator_methods(["shl", "shr"]);
    ctx.declare_var_typed("u", crate::ir::TrustVcType::parse_or_opaque("i16"));
    ctx.push_obligation(ProofObligation::assert(
        "taut",
        "u.shr(16i16) == u.shr(16i16)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_error_containing(
        &result,
        "possible bit shift underflow/overflow",
        "i16.shr(16i16) must fail closed as a VIR-level error — signed amount 16 \
         is out of range (upstream test_shr line 2 FAILS)",
    );
}

// ========================================================================
// Constant unsigned over-shift counterexample parity (FEATURE A)
//
// A fully *constant* unsigned over-shift (e.g. `1u8 << 9`, `255u8 >> 9`) has no
// free variable, so ay-dpll's CEGQI returns SAT with an EMPTY model when the
// negated shift-bound obligation (`shift_amount < width`, a `bvult`) is
// refuted. Previously the empty-model guard in
// `verification/overflow.rs` demoted this validated-SAT result to
// `Unknown(EmptyModel)` for the unsigned `left shift overflow` /
// `right shift overflow` labels (only the *signed*
// `bit shift underflow/overflow` label was reclassified above the guard).
//
// Upstream Verus FAILS these (`assert_fails`), so the validated-SAT empty model
// is now reported as a model-less `Counterexample` — the constant shift amount
// is provably `>= width`, a genuine over-shift UB witness. Soundness rests on
// the same invariant the signed path relies on: a provably-in-range shift is
// UNSAT -> Verified ABOVE the guard and never reaches this branch, so the
// reclassification fires ONLY on a genuine over-shift, never on a valid shift.
// ========================================================================

/// POSITIVE (was `Unknown(EmptyModel)`, now a definite FAILURE): a constant
/// unsigned left over-shift `1u8 << 9` (amount 9 >= width 8) must surface as a
/// model-less `Counterexample` carrying the byte-exact `possible left shift
/// overflow` label — matching upstream `assert_fails`. The assert is a
/// tautology, so only the shift-bound check can fail; there is no free variable,
/// which is exactly the empty-model path being exercised.
#[test]
fn test_const_unsigned_overshift_shl_is_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "taut",
        "(1u8 << 9u8) == (1u8 << 9u8)",
    ));

    let result = AYEncoder::verify(&ctx);
    let name = counterexample_obligation_name(
        &result,
        "1u8 << 9u8 (constant amount 9 >= width 8) must fail closed as a counterexample",
    );
    assert!(
        name.contains("possible left shift overflow"),
        "constant unsigned over-shift must carry the `left shift overflow` label, got: {name}"
    );
}

/// POSITIVE: same as above for an unsuffixed amount (`1u8 << 9`). The shift
/// amount keys off the LHS unsigned type, so the unsuffixed literal still routes
/// to the unsigned `left shift overflow` label (not the signed VIR-error path).
#[test]
fn test_const_unsigned_overshift_shl_unsuffixed_is_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("taut", "(1u8 << 9) == (1u8 << 9)"));

    let result = AYEncoder::verify(&ctx);
    let name = counterexample_obligation_name(
        &result,
        "1u8 << 9 (unsuffixed amount 9 >= width 8) must fail closed as a counterexample",
    );
    assert!(
        name.contains("possible left shift overflow"),
        "constant unsigned over-shift must carry the `left shift overflow` label, got: {name}"
    );
    assert!(
        !name.contains("bit shift underflow/overflow"),
        "unsigned-LHS over-shift must NOT route through the signed VIR-error label, got: {name}"
    );
}

/// POSITIVE: a constant unsigned right over-shift `255u8 >> 9` (amount 9 >=
/// width 8) must surface as a model-less `Counterexample` carrying the
/// `possible right shift overflow` label.
#[test]
fn test_const_unsigned_overshift_shr_is_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "taut",
        "(255u8 >> 9u8) == (255u8 >> 9u8)",
    ));

    let result = AYEncoder::verify(&ctx);
    let name = counterexample_obligation_name(
        &result,
        "255u8 >> 9u8 (constant amount 9 >= width 8) must fail closed as a counterexample",
    );
    assert!(
        name.contains("possible right shift overflow"),
        "constant unsigned over-shift must carry the `right shift overflow` label, got: {name}"
    );
}

/// ADVERSARIAL (must stay VERIFIED — NO false failure): a constant unsigned
/// IN-RANGE shift `1u8 << 3` (amount 3 < width 8) is UNSAT -> Verified ABOVE the
/// empty-model guard and must NOT be reclassified to a failure by the new
/// over-shift counterexample branch. This is the soundness witness that the
/// reclassification fires ONLY on a genuine over-shift.
#[test]
fn test_const_unsigned_inrange_shl_still_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "taut",
        "(1u8 << 3u8) == (1u8 << 3u8)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "1u8 << 3u8 (constant amount 3 < width 8) must stay Verified — a valid shift \
         must never be reclassified to a failure",
    );
}

/// ADVERSARIAL (must stay VERIFIED): the matching in-range right shift
/// `255u8 >> 3` must also stay Verified.
#[test]
fn test_const_unsigned_inrange_shr_still_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "taut",
        "(255u8 >> 3u8) == (255u8 >> 3u8)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "255u8 >> 3u8 (constant amount 3 < width 8) must stay Verified",
    );
}

/// ADVERSARIAL (must stay VERIFIED): a *variable* shift whose amount is bounded
/// below the bit width by a `requires`/assume is provably in range, so the
/// negated bound is UNSAT and the assertion verifies. This proves the change
/// does not falsely fail a legitimate variable shift constrained to `[0, width)`.
#[test]
fn test_variable_inrange_shl_under_bound_still_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.declare_var_typed("amt", crate::ir::TrustVcType::parse_or_opaque("u8"));
    // requires-style bound: amt is provably in [0, 8) for a u8 shift.
    ctx.push_obligation(ProofObligation::assume("amt_bound", "amt < 8"));
    ctx.push_obligation(ProofObligation::assert("taut", "(x << amt) == (x << amt)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "x << amt with `amt < 8` (provably in range) must stay Verified — the bounded \
         variable shift is UNSAT for the negated bound",
    );
}

/// CONTROL (non-shift overflow check UNAFFECTED): a constant *arithmetic*
/// overflow (`255u8 + 1u8`) is decided by the const-fold path and must still be
/// a `Counterexample` — the over-shift-only empty-model branch does not touch
/// non-shift checks.
#[test]
fn test_non_shift_const_arith_overflow_still_counterexample() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.push_obligation(ProofObligation::assert("arith", "255u8 + 1u8 == 0u8"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "255u8 + 1u8 (non-shift arithmetic overflow) must stay a Counterexample — \
         the shift-specific empty-model branch must not affect non-shift checks",
    );
}

/// CONTROL (non-shift overflow check UNAFFECTED): an in-range constant
/// arithmetic op (`100u8 + 100u8`) must still Verify.
#[test]
fn test_non_shift_const_arith_in_range_still_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.push_obligation(ProofObligation::assert("arith", "100u8 + 100u8 == 200u8"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "100u8 + 100u8 == 200u8 (non-shift, in range) must stay Verified",
    );
}
