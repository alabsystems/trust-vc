// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ir::TrustVcType;

#[test]
fn test_complex_verification_scenario() {
    let mut ctx = VerificationContext::new();

    // Simulate a function with preconditions, postconditions, and loop invariants
    ctx.declare_var_typed("n", TrustVcType::Uint { width: 64 });
    ctx.declare_var_typed("sum", TrustVcType::Uint { width: 64 });
    ctx.declare_var_typed("i", TrustVcType::Uint { width: 64 });

    // Precondition
    ctx.obligations.push(
        ProofObligation::requires("precondition", "n > 0 && n < 1000").with_location("func.rs:1"),
    );

    // Loop invariant
    ctx.push_obligation(ProofObligation::assume(
        "loop_invariant",
        "i <= n && sum == i * (i + 1) / 2",
    ));

    // Loop body assertion
    ctx.push_obligation(ProofObligation::assert("loop_body", "sum < n * n"));

    // Postcondition
    ctx.obligations.push(
        ProofObligation::ensures("postcondition", "sum == n * (n + 1) / 2")
            .with_location("func.rs:20"),
    );

    assert_eq!(ctx.variables.len(), 3);
    assert_eq!(ctx.obligations.len(), 4);
    assert!(ctx.has_assertions()); // Has Assert and Ensures
}

// === Invariant mask pipeline test (#2427) ===

/// Verifies that invariant_mask set on VerificationContext flows through
/// prepare_context and affects verification outcome. Uses the typed
/// VerificationContext API with InvariantOpen obligations that have namespaces.
#[test]
fn test_invariant_mask_flows_through_prepare_context() {
    use crate::encoder::VerifyResult;
    use crate::prepared_context::prepare_context;

    // Build a VerificationContext with an InvariantOpen obligation namespace 42
    // and a mask that only allows namespace 42.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assert("trivial", "x == x"));

    let open_obligation =
        ProofObligation::invariant_open("inv_open", "__trust_vc_invariant_open(inv, x)")
            .with_invariant_namespace(42);
    let close_obligation =
        ProofObligation::invariant_close("inv_close", "__trust_vc_invariant_close(inv)")
            .with_invariant_namespace(42);

    ctx.push_obligation(open_obligation);
    ctx.push_obligation(close_obligation);
    ctx.set_invariant_mask(InvariantMask::Namespaces(vec![42]));

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");

    // Verify that mask and namespace survived the prepare_context pipeline
    assert_eq!(prepared.invariant_mask, InvariantMask::Namespaces(vec![42]));

    let inv_open_obligation = prepared
        .obligations
        .iter()
        .find(|o| o.kind == ObligationKind::InvariantOpen)
        .expect("should have InvariantOpen obligation");
    assert_eq!(inv_open_obligation.invariant_namespace, Some(42));

    // Verify: mask allows ns 42, so verification should proceed (not error)
    let result = crate::encoder::AYEncoder::verify_prepared(&prepared);
    assert!(
        !matches!(result, VerifyResult::Error { .. }),
        "mask allows ns 42 so verification should not error, got: {:?}",
        result
    );
}

/// Same setup but mask blocks the namespace — should return Error.
#[test]
fn test_invariant_mask_blocks_namespace_through_pipeline() {
    use crate::encoder::VerifyResult;
    use crate::prepared_context::prepare_context;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assert("trivial", "x == x"));

    let open_obligation =
        ProofObligation::invariant_open("inv_open", "__trust_vc_invariant_open(inv, x)")
            .with_invariant_namespace(42);
    ctx.push_obligation(open_obligation);
    ctx.set_invariant_mask(InvariantMask::None);

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
    assert_eq!(prepared.invariant_mask, InvariantMask::None);

    let result = crate::encoder::AYEncoder::verify_prepared(&prepared);
    assert!(
        matches!(result, VerifyResult::Error { .. }),
        "mask None should block namespace 42, got: {:?}",
        result
    );
}
