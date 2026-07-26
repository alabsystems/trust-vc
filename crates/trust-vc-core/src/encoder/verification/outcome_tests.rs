// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_solver_unknown_detail_preserves_quantifier_reason_variants() {
    let cases = [
        UnknownReason::QuantifierRoundLimit,
        UnknownReason::QuantifierDeferred,
        UnknownReason::QuantifierUnhandled,
        UnknownReason::QuantifierCegqiIncomplete,
        UnknownReason::QuantifierEmatchingExistsIncomplete,
    ];

    for reason in cases {
        assert_eq!(
            SolverUnknownDetail::from_unknown_reason(Some(reason)),
            Some(SolverUnknownDetail::AY(reason)),
            "exact detail should preserve {reason:?}"
        );
    }
}

#[test]
fn test_solver_unknown_detail_classifies_budget_pressure_retries() {
    let cases = [
        UnknownReason::QuantifierRoundLimit,
        UnknownReason::QuantifierDeferred,
    ];

    for reason in cases {
        let detail = SolverUnknownDetail::AY(reason);
        assert_eq!(
            detail.adaptive_quantifier_retry_class(),
            AdaptiveQuantifierRetryClass::BudgetPressureRetriable,
            "{reason:?} should be retriable budget pressure"
        );
        assert!(
            detail.is_budget_retriable(),
            "{reason:?} should be marked budget retriable"
        );
    }
}

#[test]
fn test_solver_unknown_detail_classifies_permanent_quantifier_gaps() {
    let cases = [
        UnknownReason::QuantifierUnhandled,
        UnknownReason::QuantifierCegqiIncomplete,
        UnknownReason::QuantifierEmatchingExistsIncomplete,
    ];

    for reason in cases {
        let detail = SolverUnknownDetail::AY(reason);
        assert_eq!(
            detail.adaptive_quantifier_retry_class(),
            AdaptiveQuantifierRetryClass::PermanentlyNonRetriable,
            "{reason:?} should be non-retriable"
        );
        assert!(
            !detail.is_budget_retriable(),
            "{reason:?} should not be marked budget retriable"
        );
    }
}

#[test]
fn test_solver_unknown_detail_classifies_non_quantifier_reasons_as_other() {
    let detail = SolverUnknownDetail::AY(UnknownReason::Timeout);
    assert_eq!(
        detail.adaptive_quantifier_retry_class(),
        AdaptiveQuantifierRetryClass::Other
    );
    assert!(!detail.is_budget_retriable());
}
