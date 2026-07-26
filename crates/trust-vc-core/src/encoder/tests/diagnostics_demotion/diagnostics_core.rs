// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ============================================================
// Unit tests for EncodingDiagnostics
// ============================================================

#[test]
fn test_diagnostics_default_no_demoting_categories() {
    let d = EncodingDiagnostics::default();
    assert!(!d.has_demoting());
    assert_eq!(d.summary(), "");
}

#[test]
fn test_diagnostics_function_context_omission_is_demoting() {
    let d = diagnostics_with(&[(EncodingApproximation::FunctionContextReturnTypeOmitted, 1)]);
    assert!(d.has_demoting());
    assert_eq!(d.summary(), "function_context_return_type_omitted(1)");
    assert_eq!(
        d.summary_demoting(),
        "function_context_return_type_omitted(1)"
    );
}

#[test]
fn test_diagnostics_broadcast_cap_is_non_demoting() {
    // broadcast_cap_hit is LOW risk: capping broadcasts removes forall
    // quantification, giving the solver LESS information (conservative).
    // Cannot cause false Verified, only false Unknown.
    let d = diagnostics_with(&[(EncodingApproximation::BroadcastCapHit, 3)]);
    assert!(
        !d.has_demoting(),
        "broadcast_cap_hit is LOW, not HIGH — capping is conservative"
    );
    assert_eq!(d.summary(), "broadcast_cap_hit(3)");
    assert_eq!(d.summary_demoting(), "");
}

#[test]
fn test_diagnostics_bounds_check_skipped_is_non_demoting() {
    let d = diagnostics_with(&[(EncodingApproximation::BoundsCheckSkipped, 5)]);
    assert!(
        !d.has_demoting(),
        "bounds_check_skipped is MEDIUM, not HIGH"
    );
    assert_eq!(d.summary(), "bounds_check_skipped(5)");
}

#[test]
fn test_diagnostics_int_bv_coercion_is_non_demoting() {
    let d = diagnostics_with(&[(EncodingApproximation::IntBvCoercion, 2)]);
    assert!(!d.has_demoting(), "int_bv_coercion is MEDIUM, not HIGH");
}

#[test]
fn test_diagnostics_skolemization_is_non_demoting() {
    let d = diagnostics_with(&[(EncodingApproximation::ForallSkolemization, 1)]);
    assert!(!d.has_demoting(), "skolemization is LOW, not HIGH");
}

#[test]
fn test_diagnostics_ground_fixpoint_non_convergence_is_non_demoting() {
    let d = diagnostics_with(&[(EncodingApproximation::GroundFixpointNonConvergence, 1)]);
    assert!(
        !d.has_demoting(),
        "ground_fixpoint_non_convergence is LOW, not HIGH"
    );
    assert_eq!(d.summary(), "ground_fixpoint_non_convergence(1)");
}

#[test]
fn test_diagnostics_merge() {
    let mut a = diagnostics_with(&[
        (EncodingApproximation::BoundsCheckSkipped, 2),
        (EncodingApproximation::FunctionContextReturnTypeOmitted, 1),
    ]);

    let b = diagnostics_with(&[
        (EncodingApproximation::BoundsCheckSkipped, 3),
        (EncodingApproximation::IntBvCoercion, 4),
    ]);

    a.merge(&b);
    assert_eq!(a.count(EncodingApproximation::BoundsCheckSkipped), 5);
    assert_eq!(
        a.count(EncodingApproximation::FunctionContextReturnTypeOmitted),
        1
    );
    assert_eq!(a.count(EncodingApproximation::IntBvCoercion), 4);
}

#[test]
fn test_diagnostics_summary_multiple_counters() {
    let d = diagnostics_with(&[
        (EncodingApproximation::FunctionContextReturnTypeOmitted, 1),
        (EncodingApproximation::BroadcastCapHit, 2),
        (EncodingApproximation::ForallSkolemization, 3),
    ]);
    let s = d.summary();
    assert!(s.contains("function_context_return_type_omitted(1)"));
    assert!(s.contains("broadcast_cap_hit(2)"));
    assert!(s.contains("forall_skolemization(3)"));
}
