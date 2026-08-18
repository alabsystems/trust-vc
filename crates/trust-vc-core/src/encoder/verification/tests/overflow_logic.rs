//! Logic routing regressions for isolated overflow checks.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::Logic;

use crate::encoder::verification::outcome::AssertionOutcome;
use crate::encoder::verification::overflow::check_overflow_predicates;
use crate::encoder::verification::overflow_logic::isolated_overflow_logic;
use crate::encoder::verification::VerificationSlices;
use crate::encoder::AYEncoder;
use crate::ir::TrustVcType;
use crate::prepared_context::{prepare_context, PreparedObligation};
use crate::vc::{ProofObligation, VerificationContext};

fn obligation_refs(
    prepared: &crate::prepared_context::PreparedVerificationContext,
) -> (Vec<&PreparedObligation>, &PreparedObligation) {
    let assumptions = prepared
        .obligations
        .iter()
        .filter(|obligation| {
            matches!(
                obligation.kind,
                crate::vc::ObligationKind::Assume | crate::vc::ObligationKind::Requires
            )
        })
        .collect();
    let assertion = prepared
        .obligations
        .iter()
        .find(|obligation| matches!(obligation.kind, crate::vc::ObligationKind::Assert))
        .expect("prepared context should contain the assertion");
    (assumptions, assertion)
}

#[test]
fn pure_wide_bv_overflow_helper_uses_qf_bv() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_typed("hi", TrustVcType::Int { width: 128 });
    ctx.declare_var_typed("lo", TrustVcType::Int { width: 128 });
    ctx.declare_var_typed("result", TrustVcType::Bool);
    // Extracted function bodies commonly contribute a named tautological fact
    // before the preconditions.  Keep it here so this regression matches the
    // integration query rather than ay's smaller direct API fixture.
    ctx.push_obligation(ProofObligation::assume("body_fact", "true"));
    ctx.push_obligation(ProofObligation::assume("ordered", "hi > lo"));
    ctx.push_obligation(ProofObligation::assume("positive", "lo >= 1"));
    ctx.push_obligation(ProofObligation::assume(
        "body_result",
        "result == (hi - lo > 0)",
    ));
    ctx.push_obligation(ProofObligation::assert("difference", "hi - lo > 0"));

    let prepared = prepare_context(&ctx).expect("pure BV context should prepare");
    let (assumptions, assertion) = obligation_refs(&prepared);
    let empty: [&PreparedObligation; 0] = [];
    let slices = VerificationSlices::new(&prepared, &assumptions, &empty, &empty, &empty, &empty);

    assert_eq!(
        isolated_overflow_logic(&prepared, assertion, false, None, &[]),
        Logic::QfBv,
        "a quantifier-free Bool/BV128 overflow query should use ay's native BV route"
    );
    let mut encoder = AYEncoder::setup_overflow_from_prepared(
        &slices,
        assertion,
        false,
        None,
        &[],
        Some(assertion),
        None,
    )
    .expect("QF_BV overflow setup should succeed");
    assert_eq!(
        encoder.configured_logic,
        Logic::QfBv,
        "the constructed helper must actually carry QF_BV logic"
    );
    let outcome = check_overflow_predicates(&mut encoder, assertion, true)
        .expect("the isolated wide-BV overflow check should run");
    assert!(
        matches!(outcome, AssertionOutcome::Verified),
        "the keep-max-shaped BV128 overflow refutation must certify, got {outcome:?}"
    );
}

#[test]
fn mixed_int_bv_overflow_helper_stays_all_and_fails_closed() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.declare_var_typed("n", TrustVcType::MathInt);
    ctx.push_obligation(ProofObligation::assume("math_nonnegative", "n >= 0"));
    // The equality is tautological, but `x + 1` can overflow.  The only sound
    // result is therefore a counterexample/Unknown, never Verified.
    ctx.push_obligation(ProofObligation::assert(
        "possibly_overflowing",
        "x + 1 == x + 1",
    ));

    let prepared = prepare_context(&ctx).expect("mixed context should prepare");
    let (assumptions, assertion) = obligation_refs(&prepared);
    let empty: [&PreparedObligation; 0] = [];
    let slices = VerificationSlices::new(&prepared, &assumptions, &empty, &empty, &empty, &empty);

    assert_eq!(
        isolated_overflow_logic(&prepared, assertion, false, None, &[]),
        Logic::All,
        "the presence of an unbounded Int must keep the mixed-theory route"
    );
    let encoder = AYEncoder::setup_overflow_from_prepared(
        &slices,
        assertion,
        false,
        None,
        &[],
        Some(assertion),
        None,
    )
    .expect("mixed overflow setup should succeed");
    assert_eq!(
        encoder.configured_logic,
        Logic::All,
        "the constructed mixed helper must actually retain ALL logic"
    );

    let result = AYEncoder::verify(&ctx);
    assert!(
        !matches!(result, crate::VerifyResult::Verified),
        "a possibly-overflowing mixed-sort tautology must fail closed, got {result:?}"
    );
}

#[test]
fn bv_function_context_with_parameters_stays_all() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.set_function_context(crate::vc::FunctionContext::new(
        "f",
        vec![("x".to_string(), TrustVcType::Int { width: 32 })],
        TrustVcType::Int { width: 32 },
        crate::mode::FunctionMode::Spec,
    ));
    ctx.push_obligation(ProofObligation::assert(
        "possibly_overflowing",
        "x + 1 == x + 1",
    ));

    let prepared = prepare_context(&ctx).expect("BV function context should prepare");
    let (_, assertion) = obligation_refs(&prepared);
    assert_eq!(
        isolated_overflow_logic(&prepared, assertion, false, None, &[]),
        Logic::All,
        "a non-zero-arity function context declares a UF and cannot use QF_BV"
    );
}
