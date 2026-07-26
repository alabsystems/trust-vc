// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ========================================================================
// encode_match: last non-wildcard arm condition silently dropped (#2035)
// ========================================================================

/// DISCRIMINATING: match with all-literal arms (no wildcard) is non-exhaustive
/// and must return an error. Fixes #2035.
#[test]
fn test_match_all_literal_arms_returns_error() {
    let result = try_encode_match_on_x(vec![lit_arm(0, 10), lit_arm(1, 20)]);
    assert!(
        result.is_err(),
        "Non-exhaustive match (all literal arms, no wildcard) must return error. \
         Fixes #2035: previously the last arm's condition was silently dropped."
    );
    let err = match result {
        Err(e) => e,
        Ok(_) => unreachable!("already asserted is_err"),
    };
    assert!(
        err.contains("Non-exhaustive match"),
        "Error message should mention non-exhaustive match, got: {}",
        err
    );
}

/// DISCRIMINATING: match with wildcard last arm should work correctly.
#[test]
fn test_match_wildcard_last_arm_works() {
    let (mut solver, x, match_term) = encode_match_on_x(vec![lit_arm(0, 10), wildcard_arm(20)]);

    assert_match_at(&mut solver, x, match_term, 0, 10);
    assert_match_at(&mut solver, x, match_term, 5, 20);
}

/// DISCRIMINATING: match with three literal arms (no wildcard) is non-exhaustive.
/// Fixes #2035.
#[test]
fn test_match_three_literal_arms_no_wildcard_returns_error() {
    let result = try_encode_match_on_x(vec![lit_arm(0, 100), lit_arm(1, 200), lit_arm(2, 300)]);
    assert!(
        result.is_err(),
        "Non-exhaustive match (three literal arms, no wildcard) must return error. Fixes #2035."
    );
}

/// DISCRIMINATING: match with literal arms AND wildcard encodes correctly.
/// All three literal values match their bodies; non-matching values hit wildcard.
#[test]
fn test_match_three_literal_arms_with_wildcard() {
    let (mut solver, x, match_term) = encode_match_on_x(vec![
        lit_arm(0, 100),
        lit_arm(1, 200),
        lit_arm(2, 300),
        wildcard_arm(999),
    ]);

    assert_match_at(&mut solver, x, match_term, 0, 100);
    assert_match_at(&mut solver, x, match_term, 1, 200);
    assert_match_at(&mut solver, x, match_term, 2, 300);
    assert_match_at(&mut solver, x, match_term, 5, 999);
}
