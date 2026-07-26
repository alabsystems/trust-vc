//! Regression tests for overflow-guard construction error propagation.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Before #2298, `guard_overflow_checks_since` silently swallowed `try_or`
//! failures via `unwrap_or(check.1)`, leaving overflow checks unguarded when
//! the skip condition had the wrong sort. This module proves the fix: the
//! helper now returns `Err` containing both the check name and the underlying
//! sort-mismatch text, so the existing `Unknown` classification fires.

use super::*;

/// Push a non-Bool overflow predicate (BV8) and call `guard_overflow_checks_since`
/// with a Bool skip condition. Before #2298, this silently kept the unguarded
/// BV predicate. After, it returns `Err` with the check name and sort mismatch.
///
/// DISCRIMINATING: Passes only when `guard_overflow_checks_since` propagates
/// the `try_or` error instead of swallowing it with `unwrap_or`.
#[test]
fn test_guard_overflow_checks_since_returns_sort_mismatch() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::with_overflow_checking(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
        true,
    );

    // Bool skip condition — correct sort for try_or's first argument.
    let skip_cond = parser.solver.bool_const(false);
    // BV8 predicate — wrong sort for try_or (expects Bool, got BV8).
    let bad_pred = parser.solver.try_bv_const(1, 8).unwrap();

    parser
        .overflow_checks
        .push(("bogus_overflow".into(), bad_pred));

    let result = parser.guard_overflow_checks_since(0, skip_cond);

    assert!(
        result.is_err(),
        "Expected Err from sort-mismatched try_or, got Ok"
    );
    let err = result.unwrap_err().to_string();

    // The error must mention the check name so diagnostics can trace it.
    assert!(
        err.contains("bogus_overflow"),
        "Error should contain check name 'bogus_overflow', got: {}",
        err
    );

    // The error must preserve sort-mismatch wording so is_sort_mismatch_error
    // continues to classify it correctly for the Unknown path.
    let err_lower = err.to_lowercase();
    let err_compact: String = err_lower
        .chars()
        .filter(|c: &char| !c.is_ascii_whitespace())
        .collect();
    assert!(
        err_lower.contains("sort mismatch")
            || err_compact.contains("sortmismatch")
            || err_lower.contains("expects bool"),
        "Error should contain sort-mismatch marker for classification, got: {}",
        err
    );
}

/// Verify that `guard_overflow_checks_since` succeeds on well-typed checks.
/// Ensures the fix for #2298 doesn't regress the normal happy path.
#[test]
fn test_guard_overflow_checks_since_ok_on_bool_predicates() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::with_overflow_checking(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
        true,
    );

    let skip_cond = parser.solver.bool_const(false);
    let good_pred = parser.solver.bool_const(true);

    parser
        .overflow_checks
        .push(("valid_overflow".into(), good_pred));

    let result = parser.guard_overflow_checks_since(0, skip_cond);
    assert!(
        result.is_ok(),
        "Expected Ok for well-typed Bool predicate, got: {:?}",
        result.err()
    );
}
