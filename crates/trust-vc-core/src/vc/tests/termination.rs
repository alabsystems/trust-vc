// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ir::TrustVcType;

#[test]
fn test_termination_measure() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", TrustVcType::Uint { width: 64 });
    ctx.add_measure_nonneg("n");
    ctx.add_measure_decreases("n", "n_entry", "n_recursive");

    assert_eq!(ctx.obligations.len(), 2);
    assert_eq!(
        ctx.obligations
            .first()
            .expect("Should have first obligation after length check")
            .kind,
        ObligationKind::MeasureNonNegative
    );
    assert_eq!(
        ctx.obligations
            .get(1)
            .expect("Should have second obligation after length check")
            .kind,
        ObligationKind::MeasureDecreases
    );
}

#[test]
fn test_add_measure_decreases_obligation() {
    let mut ctx = VerificationContext::new();

    // Test adding custom obligation with location
    ctx.add_measure_decreases_obligation(
        "custom_check",
        "x > 0 && y < 100",
        Some("test.rs:42".to_string()),
    );

    assert_eq!(ctx.obligations.len(), 1);
    let first_obligation = ctx
        .obligations
        .first()
        .expect("Should have first obligation after length check");
    assert_eq!(first_obligation.name, "custom_check");
    assert_eq!(first_obligation.condition, "x > 0 && y < 100");
    assert_eq!(first_obligation.location, Some("test.rs:42".to_string()));
    assert_eq!(first_obligation.kind, ObligationKind::MeasureDecreases);

    // Test adding custom obligation without location
    ctx.add_measure_decreases_obligation("another_check", "z != 0", None);

    assert_eq!(ctx.obligations.len(), 2);
    assert_eq!(ctx.obligations[1].location, None);
}

#[test]
fn test_termination_checking_complete() {
    let mut ctx = VerificationContext::new();

    // Simulate recursive function termination checking
    ctx.declare_var_typed("n", TrustVcType::Int { width: 32 });
    ctx.declare_var_typed("m", TrustVcType::Int { width: 32 });

    // Add lexicographic measure
    ctx.add_measure_nonneg("n");
    ctx.add_measure_nonneg("m");

    // Add decrease checks for recursive calls
    ctx.add_measure_decreases("first_call", "n", "n - 1");
    ctx.add_measure_decreases("second_call", "(n, m)", "(n, m - 1)");

    assert_eq!(ctx.obligations.len(), 4);

    // Verify all are termination-related
    let termination_obligations = ctx
        .obligations
        .iter()
        .filter(|o| {
            matches!(
                o.kind,
                ObligationKind::MeasureNonNegative | ObligationKind::MeasureDecreases
            )
        })
        .count();

    assert_eq!(termination_obligations, 4);
}

#[test]
fn test_add_measure_decreases_matches_shared_lex_helper() {
    let mut ctx = VerificationContext::new();
    let old_measure = "(n, m)";
    let new_measure = "(n, m - 1)";
    ctx.add_measure_decreases("tuple_call", old_measure, new_measure);

    let first_obligation = ctx
        .obligations
        .first()
        .expect("Should have first obligation after adding decreases check");
    assert_eq!(
        first_obligation.condition,
        crate::decreases_lex::lexicographic_decreases_condition(old_measure, new_measure)
    );
}
