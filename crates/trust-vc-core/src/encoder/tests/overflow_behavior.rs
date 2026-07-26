//! Tests for mode-aware overflow behavior (#2516).
//!
//! Validates `OverflowBehavior::Error`, `Truncate`, and `Allow` variants,
//! mode-based derivation from `FunctionMode`, and backward compatibility
//! with the `check_overflow: bool` API.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::mode::FunctionMode;
use crate::vc::{BitshiftBehavior, Div0Behavior, OverflowBehavior, VerificationContext};

// ── Enum derivation from FunctionMode ──

#[test]
fn test_overflow_behavior_from_exec_mode() {
    let behavior = OverflowBehavior::from_mode(FunctionMode::Exec);
    assert_eq!(behavior, OverflowBehavior::Error);
    assert!(behavior.should_check());
    assert!(behavior.should_clip());
}

#[test]
fn test_overflow_behavior_from_proof_mode() {
    let behavior = OverflowBehavior::from_mode(FunctionMode::Proof);
    assert_eq!(behavior, OverflowBehavior::Allow);
    assert!(!behavior.should_check());
    assert!(!behavior.should_clip());
}

#[test]
fn test_overflow_behavior_from_spec_mode() {
    let behavior = OverflowBehavior::from_mode(FunctionMode::Spec);
    assert_eq!(behavior, OverflowBehavior::Allow);
    assert!(!behavior.should_check());
    assert!(!behavior.should_clip());
}

#[test]
fn test_truncate_clips_without_checking() {
    let behavior = OverflowBehavior::Truncate;
    assert!(!behavior.should_check(), "Truncate should not assert");
    assert!(behavior.should_clip(), "Truncate should clip to range");
}

#[test]
fn test_div0_behavior_from_mode() {
    assert_eq!(
        Div0Behavior::from_mode(FunctionMode::Exec),
        Div0Behavior::Error
    );
    assert!(Div0Behavior::Error.should_check());

    assert_eq!(
        Div0Behavior::from_mode(FunctionMode::Proof),
        Div0Behavior::Allow
    );
    assert!(!Div0Behavior::Allow.should_check());

    assert_eq!(
        Div0Behavior::from_mode(FunctionMode::Spec),
        Div0Behavior::Allow
    );
}

#[test]
fn test_bitshift_behavior_from_mode() {
    assert_eq!(
        BitshiftBehavior::from_mode(FunctionMode::Exec),
        BitshiftBehavior::Error
    );
    assert!(BitshiftBehavior::Error.should_check());

    assert_eq!(
        BitshiftBehavior::from_mode(FunctionMode::Proof),
        BitshiftBehavior::Allow
    );
    assert!(!BitshiftBehavior::Allow.should_check());
}

// ── VerificationContext API ──

#[test]
fn test_context_default_is_allow() {
    let ctx = VerificationContext::new();
    assert_eq!(ctx.overflow_behavior(), OverflowBehavior::Allow);
    assert!(!ctx.check_overflow());
}

#[test]
fn test_enable_overflow_checks_sets_error() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    assert_eq!(ctx.overflow_behavior(), OverflowBehavior::Error);
    assert!(ctx.check_overflow());
}

#[test]
fn test_with_overflow_checks_builder() {
    let ctx = VerificationContext::new().with_overflow_checks();
    assert_eq!(ctx.overflow_behavior(), OverflowBehavior::Error);
    assert!(ctx.check_overflow());
}

#[test]
fn test_with_mode_overflow_exec() {
    let ctx = VerificationContext::new().with_mode_overflow(FunctionMode::Exec);
    assert_eq!(ctx.overflow_behavior(), OverflowBehavior::Error);
    assert!(ctx.check_overflow());
}

#[test]
fn test_with_mode_overflow_proof() {
    let ctx = VerificationContext::new().with_mode_overflow(FunctionMode::Proof);
    assert_eq!(ctx.overflow_behavior(), OverflowBehavior::Allow);
    assert!(!ctx.check_overflow());
}

#[test]
fn test_set_overflow_behavior_truncate() {
    let mut ctx = VerificationContext::new();
    ctx.set_overflow_behavior(OverflowBehavior::Truncate);
    assert_eq!(ctx.overflow_behavior(), OverflowBehavior::Truncate);
    assert!(!ctx.check_overflow(), "Truncate should not check");
}

// ── Verification pipeline: Error mode detects overflow ──

#[test]
fn test_error_mode_catches_overflow() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(crate::vc::ProofObligation::assume("at_max", "x == 255"));
    ctx.enable_overflow_checks();
    ctx.push_obligation(crate::vc::ProofObligation::assert("overflows", "x + 1 > 0"));

    let result = crate::encoder::AYEncoder::verify(&ctx);
    // With Error mode, x + 1 on u8 at max should produce a counterexample
    // for the overflow check (not Verified).
    assert!(
        !result.is_verified(),
        "Error mode should detect overflow for u8::MAX + 1, got: {:?}",
        result,
    );
}

#[test]
fn test_allow_mode_no_overflow_check() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(crate::vc::ProofObligation::assume("at_max", "x == 255"));
    // Default is Allow — no overflow checks
    ctx.push_obligation(crate::vc::ProofObligation::assert("wraps", "x + 1 == 0"));

    let result = crate::encoder::AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Allow mode should let u8::MAX + 1 wrap to 0 without overflow error",
    );
}

// ── VerificationContext Div0/Bitshift integration ──

#[test]
fn test_enable_overflow_checks_sets_all_behaviors() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    assert_eq!(ctx.div0_behavior(), Div0Behavior::Error);
    assert_eq!(ctx.bitshift_behavior(), BitshiftBehavior::Error);
}

#[test]
fn test_with_mode_overflow_exec_sets_all_behaviors() {
    let ctx = VerificationContext::new().with_mode_overflow(FunctionMode::Exec);
    assert_eq!(ctx.div0_behavior(), Div0Behavior::Error);
    assert_eq!(ctx.bitshift_behavior(), BitshiftBehavior::Error);
}

#[test]
fn test_with_mode_overflow_spec_sets_all_behaviors_allow() {
    let ctx = VerificationContext::new().with_mode_overflow(FunctionMode::Spec);
    assert_eq!(ctx.overflow_behavior(), OverflowBehavior::Allow);
    assert_eq!(ctx.div0_behavior(), Div0Behavior::Allow);
    assert_eq!(ctx.bitshift_behavior(), BitshiftBehavior::Allow);
}

#[test]
fn test_context_default_div0_allow_bitshift_error() {
    let ctx = VerificationContext::new();
    // Div-by-zero defaults to Allow (matches overflow default).
    assert_eq!(ctx.div0_behavior(), Div0Behavior::Allow);
    // Shift UB defaults to Error — always checked in BV mode.
    assert_eq!(ctx.bitshift_behavior(), BitshiftBehavior::Error);
}

#[test]
fn test_set_function_context_exec_derives_all_behaviors() {
    let mut ctx = VerificationContext::new();
    ctx.set_function_context(crate::vc::FunctionContext {
        name: "test_fn".to_string(),
        params: vec![],
        return_type: crate::ir::TrustVcType::Bool,
        is_recursive: false,
        mode: FunctionMode::Exec,
        trait_bounds: vec![],
    });
    assert_eq!(ctx.overflow_behavior(), OverflowBehavior::Error);
    assert_eq!(ctx.div0_behavior(), Div0Behavior::Error);
    assert_eq!(ctx.bitshift_behavior(), BitshiftBehavior::Error);
}

#[test]
fn test_set_function_context_spec_derives_all_behaviors() {
    let mut ctx = VerificationContext::new();
    ctx.set_function_context(crate::vc::FunctionContext {
        name: "spec_fn".to_string(),
        params: vec![],
        return_type: crate::ir::TrustVcType::Bool,
        is_recursive: false,
        mode: FunctionMode::Spec,
        trait_bounds: vec![],
    });
    assert_eq!(ctx.overflow_behavior(), OverflowBehavior::Allow);
    assert_eq!(ctx.div0_behavior(), Div0Behavior::Allow);
    assert_eq!(ctx.bitshift_behavior(), BitshiftBehavior::Allow);
}

// ── Parser state: overflow_behavior propagation ──

fn make_solver() -> ay_dpll::api::Solver {
    ay_dpll::api::Solver::try_new(ay_dpll::api::Logic::All).expect("solver construction")
}

#[test]
fn test_parser_with_overflow_checking_true() {
    let mut solver = make_solver();
    let variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let parser = crate::encoder::AstExpressionParser::with_overflow_checking(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
        true,
    );
    assert!(parser.overflow_behavior.should_check());
    assert_eq!(parser.overflow_behavior, OverflowBehavior::Error);
}

#[test]
fn test_parser_with_overflow_checking_false() {
    let mut solver = make_solver();
    let variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let parser = crate::encoder::AstExpressionParser::with_overflow_checking(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
        false,
    );
    assert!(!parser.overflow_behavior.should_check());
}

#[test]
fn test_parser_with_overflow_behavior_truncate() {
    let mut solver = make_solver();
    let variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let parser = crate::encoder::AstExpressionParser::with_overflow_behavior(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
        OverflowBehavior::Truncate,
    );
    assert_eq!(parser.overflow_behavior, OverflowBehavior::Truncate);
    assert!(!parser.overflow_behavior.should_check());
    assert!(parser.overflow_behavior.should_clip());
}

#[test]
fn test_parser_derives_div0_bitshift_from_overflow_error() {
    let mut solver = make_solver();
    let variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let parser = crate::encoder::AstExpressionParser::with_overflow_checking(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
        true,
    );
    assert_eq!(parser.div0_behavior, Div0Behavior::Error);
    assert_eq!(parser.bitshift_behavior, BitshiftBehavior::Error);
}

#[test]
fn test_parser_derives_div0_bitshift_from_overflow_allow() {
    let mut solver = make_solver();
    let variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let parser = crate::encoder::AstExpressionParser::with_overflow_checking(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
        false,
    );
    assert_eq!(parser.div0_behavior, Div0Behavior::Allow);
    // Bitshift UB is always Error by default — not derived from overflow.
    assert_eq!(parser.bitshift_behavior, BitshiftBehavior::Error);
}

// ── Pipeline: Div0Behavior Error catches division by symbolic zero ──

#[test]
fn test_div0_error_catches_symbolic_division_by_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(crate::vc::ProofObligation::assume("y_is_zero", "y == 0"));
    ctx.enable_overflow_checks();
    // Division by a variable that's zero should trigger the div0 check.
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "result_ok",
        "x / y < 100",
    ));

    let result = crate::encoder::AYEncoder::verify(&ctx);
    assert!(
        !result.is_verified(),
        "Div0 Error mode should detect division by zero, got: {:?}",
        result,
    );
}

#[test]
fn test_div0_allow_permits_division_by_symbolic_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u32"));
    // y is unconstrained — could be zero. Default: div0 = Allow, so no
    // div0 check is generated. The reflexive assertion verifies because
    // `x / y == x / y` is structurally identical at the SMT level.
    // In Error mode, this would fail because we can't prove y != 0.
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "div_reflexive",
        "x / y == x / y",
    ));

    let result = crate::encoder::AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Div0 Allow mode should permit division by symbolic zero without generating a check",
    );
}

// ── Pipeline: Spec mode suppresses all checking ──

#[test]
fn test_spec_mode_suppresses_overflow_and_div0() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(crate::vc::ProofObligation::assume("at_max", "x == 255"));
    // Configure as spec mode — all checks suppressed.
    let mut ctx = ctx.with_mode_overflow(FunctionMode::Spec);
    // In spec mode, x + 1 wraps to 0 and no overflow check fires.
    ctx.push_obligation(crate::vc::ProofObligation::assert("wraps", "x + 1 == 0"));

    let result = crate::encoder::AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Spec mode should suppress overflow checks — u8::MAX + 1 wraps freely",
    );
}

// ── Pipeline: Bitshift Allow mode (spec) permits over-shift ──

#[test]
fn test_bitshift_allow_permits_over_shift_in_spec_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(crate::vc::ProofObligation::assume("over_shift", "s == 33"));
    // Spec mode sets bitshift_behavior = Allow. Shifting by >= bit width
    // does NOT generate a bounds check. The assertion uses actual shift
    // to exercise the bitshift Allow propagation path.
    let mut ctx = ctx.with_mode_overflow(FunctionMode::Spec);
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "shift_reflexive",
        "(x << s) == (x << s)",
    ));

    let result = crate::encoder::AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Bitshift Allow mode should permit over-shift without bounds check",
    );
}

#[test]
fn test_bitshift_allow_permits_over_shift_right_in_spec_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(crate::vc::ProofObligation::assume("over_shift", "s == 33"));
    let mut ctx = ctx.with_mode_overflow(FunctionMode::Spec);
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "shift_reflexive",
        "(x >> s) == (x >> s)",
    ));

    let result = crate::encoder::AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Bitshift Allow mode should permit over-right-shift without bounds check",
    );
}

// ── Pipeline: Truncate mode clips without asserting ──

#[test]
fn test_truncate_mode_no_overflow_assertion() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(crate::vc::ProofObligation::assume("at_max", "x == 255"));
    ctx.set_overflow_behavior(OverflowBehavior::Truncate);
    // Truncate clips to range but does NOT assert. x + 1 wraps to 0.
    ctx.push_obligation(crate::vc::ProofObligation::assert("wraps", "x + 1 == 0"));

    let result = crate::encoder::AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Truncate mode should let u8::MAX + 1 wrap without overflow assertion",
    );
}

// ── Pipeline: Assert+Assume pattern ──

#[test]
fn test_assert_assume_overflow_result_in_range() {
    // After proving no overflow, the main assertion can rely on the
    // result being in range. This test verifies the assert+assume pattern:
    // in Error mode, if x < 200, then x + 1 <= 200 should verify because
    // the overflow check passes (x + 1 fits in u8) and the main assertion
    // can use the in-range result.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(crate::vc::ProofObligation::assume("bounded", "x < 200"));
    ctx.enable_overflow_checks();
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "in_range",
        "x + 1 <= 200",
    ));

    let result = crate::encoder::AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Assert+assume: after proving no overflow, result should be in range",
    );
}
