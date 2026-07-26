//! End-to-end tests for demand-driven cross-function inlining (#2655).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::encoder::tests::expect_verified;
use crate::encoder::types::VerifyResult;
use crate::encoder::verification::VerificationSlices;
use crate::ir::TrustVcType;
use crate::prepared_context::{prepare_context, PreparedObligation};
use crate::vc::{DemandInlineConfig, ProofObligation, VerificationContext};
use crate::verification_report::VerificationReportOptions;

/// Helper: build a context with a non-inline body axiom for `helper(x) == x + x`
/// and an assertion that depends on knowing the body. The explicit trigger is
/// intentionally unrelated to the assertion, so ordinary broadcast proving keeps
/// the axiom inert while the demand-inline retry can still extract and
/// substitute the body axiom directly.
fn build_direct_demand_inline_context(config: DemandInlineConfig) -> VerificationContext {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.declare_helper_function_typed(
        "helper",
        TrustVcType::Int { width: 32 },
        vec![("x".to_string(), TrustVcType::Int { width: 32 })],
    );
    ctx.declare_helper_function_typed(
        "seed",
        TrustVcType::Int { width: 32 },
        vec![("x".to_string(), TrustVcType::Int { width: 32 })],
    );

    // Deliberately use an unrelated trigger head so the ordinary broadcast path
    // cannot fire from `helper(3)`. The retry-local inline override is what
    // makes the proof go through in this regression.
    ctx.push_obligation(
        ProofObligation::broadcast_assume("__body_axiom_helper", "helper(x) == x + x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["seed(x)".to_string()]]),
    );

    // Demand-inline MVP currently runs on the fresh-encoder lane, not the
    // shared-BV fast path. Use NonlinearArith to force the intended path.
    ctx.push_obligation(
        ProofObligation::assert("check_helper_3", "helper(3) == 6")
            .with_solver_mode(crate::vc::SolverMode::NonlinearArith),
    );

    ctx.set_demand_inline_config(config);
    ctx
}

fn build_chained_demand_inline_context(config: DemandInlineConfig) -> VerificationContext {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.declare_helper_function_typed(
        "f",
        TrustVcType::Int { width: 32 },
        vec![("x".to_string(), TrustVcType::Int { width: 32 })],
    );
    ctx.declare_helper_function_typed(
        "g",
        TrustVcType::Int { width: 32 },
        vec![("x".to_string(), TrustVcType::Int { width: 32 })],
    );
    ctx.declare_helper_function_typed(
        "seed_f",
        TrustVcType::Int { width: 32 },
        vec![("x".to_string(), TrustVcType::Int { width: 32 })],
    );
    ctx.declare_helper_function_typed(
        "seed_g",
        TrustVcType::Int { width: 32 },
        vec![("x".to_string(), TrustVcType::Int { width: 32 })],
    );

    ctx.push_obligation(
        ProofObligation::broadcast_assume("__body_axiom_f", "f(x) == g(x) + 1")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["seed_f(x)".to_string()]]),
    );
    ctx.push_obligation(
        ProofObligation::broadcast_assume("__body_axiom_g", "g(x) == x + x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["seed_g(x)".to_string()]]),
    );
    ctx.push_obligation(
        ProofObligation::assert("check_f_3", "f(3) == 7")
            .with_solver_mode(crate::vc::SolverMode::NonlinearArith),
    );
    ctx.set_demand_inline_config(config);
    ctx
}

fn prepared_assertion_and_broadcasts(
    ctx: &VerificationContext,
) -> (
    crate::prepared_context::PreparedVerificationContext,
    Vec<PreparedObligation>,
    PreparedObligation,
) {
    let prepared = prepare_context(ctx).expect("context should prepare");
    let broadcasts = prepared
        .obligations
        .iter()
        .filter(|obligation| matches!(obligation.kind, crate::vc::ObligationKind::BroadcastAssume))
        .cloned()
        .collect::<Vec<_>>();
    let assertion = prepared
        .obligations
        .iter()
        .find(|obligation| matches!(obligation.kind, crate::vc::ObligationKind::Assert))
        .cloned()
        .expect("prepared context should contain the target assertion");
    (prepared, broadcasts, assertion)
}

/// depth=1 direct recovery: ordinary body-axiom replay is disabled by the
/// unreachable trigger head, so only demand-inline can recover the proof.
#[test]
fn test_demand_inline_depth_1_direct_recovery() {
    let config = DemandInlineConfig::new().with_depth_bound(1);
    let ctx = build_direct_demand_inline_context(config);
    let result = ctx.verify();
    expect_verified(
        &result,
        "helper(3)==6 should verify only after the depth=1 demand-inline retry",
    );
}

/// With the retry disabled, the same unreachable-trigger body axiom must no longer
/// verify. This proves the direct-recovery test is really exercising #2655.
#[test]
fn test_demand_inline_disabled_preserves_baseline_failure() {
    let config = DemandInlineConfig::new().with_enabled(false);
    let ctx = build_direct_demand_inline_context(config);
    let result = ctx.verify();
    assert!(
        !matches!(result, VerifyResult::Verified),
        "without demand-inline, the unreachable-trigger body axiom should stay unproved: {result:?}",
    );
}

/// depth semantics: inlining only the direct callee `f` is insufficient, but
/// depth=2 can also inline `g` from inside `f`'s body and recover the proof.
#[test]
fn test_demand_inline_depth_2_chained_recovery() {
    let depth_1 =
        build_chained_demand_inline_context(DemandInlineConfig::new().with_depth_bound(1));
    let depth_1_result = depth_1.verify();
    assert!(
        !matches!(depth_1_result, VerifyResult::Verified),
        "depth=1 should not recover the chained helper proof: {depth_1_result:?}",
    );

    let depth_2 =
        build_chained_demand_inline_context(DemandInlineConfig::new().with_depth_bound(2));
    let depth_2_result = depth_2.verify();
    expect_verified(
        &depth_2_result,
        "depth=2 should recover the chained helper proof by inlining f and g",
    );
}

#[test]
fn test_demand_inline_report_mentions_contract_strengthening() {
    let ctx = build_direct_demand_inline_context(DemandInlineConfig::new().with_depth_bound(1));
    let report = ctx.verify_with_report(VerificationReportOptions::new().with_verbose(true));

    assert!(
        matches!(report.result(), VerifyResult::Verified),
        "direct recovery should surface as a verified report, got {:?}",
        report.result()
    );

    let assertion_step = report
        .steps()
        .iter()
        .find(|step| step.label() == "check_helper_3")
        .expect("report should include the recovered assertion step");
    let recovery = assertion_step
        .demand_inline_recovery()
        .expect("recovered assertion should record demand-inline metadata");
    assert_eq!(recovery.inlined_functions(), ["helper".to_string()]);
    assert_eq!(recovery.depth_used(), 1);

    let rendered = report.format_with_options(VerificationReportOptions::new().with_verbose(true));
    assert!(rendered.contains("verified after inlining helper"));
    assert!(rendered.contains("consider strengthening helper's contract"));
}

#[test]
fn test_demand_inline_retry_registers_inline_body_override() {
    let ctx = build_direct_demand_inline_context(DemandInlineConfig::new().with_depth_bound(1));
    let (prepared, broadcasts, assertion) = prepared_assertion_and_broadcasts(&ctx);
    let broadcast_refs = broadcasts.iter().collect::<Vec<_>>();
    let empty: [&PreparedObligation; 0] = [];
    let slices =
        VerificationSlices::new(&prepared, &empty, &broadcast_refs, &empty, &empty, &empty);

    let encoder = crate::encoder::AYEncoder::setup_from_prepared_with_inline_overrides(
        &slices,
        false,
        None,
        &[],
        Some(&assertion),
        &["helper".to_string()],
    )
    .expect("retry setup should succeed");

    assert!(
        encoder.state.inline_bodies.contains_key("helper"),
        "retry setup should register helper as an inline body override"
    );

    let substituted = crate::encoder::eval::substitute_inline_calls(
        &assertion.expr,
        &encoder.state.inline_bodies,
    );
    match substituted {
        crate::ir::TrustVcExpr::Compare { left, right, .. } => {
            assert!(
                matches!(
                    (&*left, &*right),
                    (
                        crate::ir::TrustVcExpr::Arith { .. },
                        crate::ir::TrustVcExpr::IntLit { value: 6, .. }
                    )
                ),
                "inline override should substitute helper(3) into arithmetic, got {:?}",
                (&*left, &*right)
            );
        }
        other => panic!("expected substituted comparison assertion, got {:?}", other),
    }
}

#[test]
fn test_demand_inline_retry_omits_redundant_quantified_body_axiom() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.declare_helper_function_typed(
        "helper",
        TrustVcType::Int { width: 32 },
        vec![("x".to_string(), TrustVcType::Int { width: 32 })],
    );
    ctx.push_obligation(
        ProofObligation::broadcast_assume("__body_axiom_helper", "helper(x) == x + x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["helper(x)".to_string()]]),
    );
    ctx.push_obligation(ProofObligation::assert("check_helper_3", "helper(3) == 6"));

    let (prepared, broadcasts, assertion) = prepared_assertion_and_broadcasts(&ctx);
    let broadcast_refs = broadcasts.iter().collect::<Vec<_>>();
    let empty: [&PreparedObligation; 0] = [];
    let slices =
        VerificationSlices::new(&prepared, &empty, &broadcast_refs, &empty, &empty, &empty);

    let baseline = crate::encoder::AYEncoder::setup_from_prepared_with_inline_overrides(
        &slices,
        false,
        None,
        &[],
        Some(&assertion),
        &[],
    )
    .expect("baseline setup should succeed");
    assert_eq!(
        baseline.state.broadcast_count, 1,
        "the reachable defining axiom should be live without an override"
    );

    let retry = crate::encoder::AYEncoder::setup_from_prepared_with_inline_overrides(
        &slices,
        false,
        None,
        &[],
        Some(&assertion),
        &["helper".to_string()],
    )
    .expect("retry setup should succeed");
    assert!(
        retry.state.inline_bodies.contains_key("helper"),
        "the retry must substitute the exact helper body at every call"
    );
    assert_eq!(
        retry.state.broadcast_count, 0,
        "the substituted body must not remain as a redundant quantified axiom"
    );
}

/// Demand-inline recovery with collection context: the confirmation
/// double-check is skipped for demand-inline proofs (#2687), so the
/// assertion should verify despite collection context being present.
#[test]
fn test_demand_inline_recovery_works_with_collection_context() {
    // Same setup as direct recovery, but with a Seq variable to trigger
    // collection confirmation check via has_collection_context.
    let config = DemandInlineConfig::new().with_depth_bound(1);
    let mut ctx = build_direct_demand_inline_context(config);
    ctx.declare_var_typed("s", TrustVcType::parse_or_opaque("Seq<i32>"));

    let result = ctx.verify();

    // Fixed in #2687: confirmation check is skipped when proof was
    // recovered via demand-inline, since the disagreement is expected
    // (normal cascade lacks body axioms) rather than non-deterministic.
    expect_verified(
        &result,
        "demand-inline recovery should succeed even with collection context (#2687)",
    );
}

/// Baseline: WITHOUT collection context, demand-inline recovery works.
/// This proves the collection confirmation check is what defeats it.
#[test]
fn test_demand_inline_recovery_works_without_collection_context() {
    // Same as test_demand_inline_depth_1_direct_recovery — no Seq variable.
    let config = DemandInlineConfig::new().with_depth_bound(1);
    let ctx = build_direct_demand_inline_context(config);
    let result = ctx.verify();
    expect_verified(
        &result,
        "without collection context, demand-inline recovery should succeed",
    );
}

/// Safety boundary: opaque callee must not be auto-inlined even when
/// demand-inline is enabled.
#[test]
fn test_demand_inline_skips_opaque_callee() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.declare_var_typed("y", TrustVcType::Int { width: 32 });
    ctx.declare_helper_function_typed(
        "secret",
        TrustVcType::Int { width: 32 },
        vec![("x".to_string(), TrustVcType::Int { width: 32 })],
    );

    ctx.declare_helper_function_typed(
        "seed",
        TrustVcType::Int { width: 32 },
        vec![("x".to_string(), TrustVcType::Int { width: 32 })],
    );

    // Opaque body axiom — must not be demand-inlined.
    ctx.push_obligation(
        ProofObligation::broadcast_assume("__body_axiom_secret", "secret(x) == x + x")
            .with_opaque(true)
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["seed(x)".to_string()]]),
    );

    // This assertion can ONLY succeed if secret's body is visible.
    // Since it's opaque, neither broadcast NOR demand-inline should reveal it.
    ctx.push_obligation(
        ProofObligation::assert("check_secret_3", "secret(3) == 6")
            .with_solver_mode(crate::vc::SolverMode::NonlinearArith),
    );
    ctx.set_demand_inline_config(DemandInlineConfig::new().with_depth_bound(1));

    let result = ctx.verify();

    // The assertion should NOT be verified (opaque body not inlined).
    assert!(
        !matches!(result, VerifyResult::Verified),
        "opaque callee must not be auto-inlined: {result:?}",
    );
}
