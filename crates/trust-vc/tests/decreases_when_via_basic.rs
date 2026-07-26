// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for decreases when/via clause parsing and verification.
//!
//! Exercises parsing, runtime expansion, and active verification for
//! `#[decreases(..., when/via = ...)]`. Includes `verify_should_pass` and
//! `verify_and_get_result` lanes for `via_fn`, `decreases(via)`,
//! `decreases(when, via)`, and failing `via` proofs.
//! Lower-level guarded-`when` obligation shape tests live in
//! `test_decreases_integration.rs`.

use trust_vc::{decreases, via_fn};
use trust_vc_core::VerifyResult;
// Test: when clause only
#[decreases(n, when = n > 0)]
fn partial_factorial(n: i64) -> i64 {
    if n <= 0 {
        1
    } else {
        n * partial_factorial(n - 1)
    }
}

mod common;

#[test]
fn test_decreases_when_compiles() {
    common::with_clean_verification(|| {
        // Function with when clause should compile and execute
        assert_eq!(partial_factorial(0), 1);
        assert_eq!(partial_factorial(5), 120);
        assert_eq!(partial_factorial(-1), 1); // Negative handled

        // Note: decreases itself doesn't generate assertions,
        // but we can verify the via_fn proof separately
    })
}

// Test: via clause only
#[via_fn]
fn floor_log2_proof(n: u64) {
    trust_vc::assert!(n <= 1 || (n >> 1) < n);
}

#[decreases(n, via = floor_log2_proof)]
fn floor_log2(n: u64) -> u64 {
    if n <= 1 {
        0
    } else {
        floor_log2(n >> 1) + 1
    }
}

#[test]
fn test_via_fn_direct_invocation_verifies_under_test() {
    let result = common::verify_should_pass(|| {
        floor_log2_proof(16);
    });
    assert!(
        matches!(result, VerifyResult::Verified),
        "via_fn direct call should verify, got: {:?}",
        result
    );
}

#[test]
fn test_decreases_via_verifies() {
    let result = common::verify_should_pass(|| {
        assert_eq!(floor_log2(0), 0);
        assert_eq!(floor_log2(1), 0);
        assert_eq!(floor_log2(2), 1);
        assert_eq!(floor_log2(4), 2);
        assert_eq!(floor_log2(8), 3);
        assert_eq!(floor_log2(16), 4);
    });
    assert!(
        matches!(result, VerifyResult::Verified),
        "decreases(via) should verify, got: {:?}",
        result
    );
}

// Test: both when and via clauses
#[via_fn]
fn bounded_div_proof(n: i64) {
    trust_vc::assert!(n <= 1 || (n / 2) < n);
}

#[decreases(n, when = n > 0, via = bounded_div_proof)]
fn bounded_div(n: i64) -> i64 {
    if n <= 0 {
        0
    } else if n == 1 {
        1
    } else {
        bounded_div(n / 2) + 1
    }
}

#[test]
fn test_decreases_when_via_verifies() {
    let result = common::verify_should_pass(|| {
        assert_eq!(bounded_div(0), 0);
        assert_eq!(bounded_div(-5), 0);
        assert_eq!(bounded_div(1), 1);
        assert_eq!(bounded_div(16), 5); // 16 -> 8 -> 4 -> 2 -> 1 (5 steps)
    });
    assert!(
        matches!(result, VerifyResult::Verified),
        "decreases(when, via) should verify, got: {:?}",
        result
    );
}

#[via_fn]
fn positive_only_div_proof(n: i64) {
    assert!(n > 0, "via proof should only run inside the when guard");
    trust_vc::assert!(n <= 1 || (n / 2) < n);
}

#[decreases(n, when = n > 0, via = positive_only_div_proof)]
fn positive_only_div(n: i64) -> i64 {
    if n <= 0 {
        0
    } else if n == 1 {
        1
    } else {
        positive_only_div(n / 2) + 1
    }
}

#[test]
fn test_decreases_when_via_skips_proof_outside_guard() {
    let result = common::verify_should_pass(|| {
        assert_eq!(positive_only_div(-5), 0);
        assert_eq!(positive_only_div(0), 0);
        assert_eq!(positive_only_div(8), 4);
    });
    assert!(
        matches!(result, VerifyResult::Verified),
        "decreases(when, via) should skip proof outside guard, got: {:?}",
        result
    );
}

// Test: lexicographic with when
// NOTE: Bug #975 - Multi-argument decreases generates unparseable ay conditions
// This function compiles but verification would fail due to tuple parsing issue
#[decreases(m, n, when = m > 0 || n > 0)]
fn bounded_ack_when(m: i64, n: i64) -> i64 {
    if m <= 0 && n <= 0 {
        0
    } else if m <= 0 {
        n + 1
    } else if n <= 0 {
        bounded_ack_when(m - 1, 1)
    } else {
        bounded_ack_when(m - 1, bounded_ack_when(m, n - 1))
    }
}

#[test]
fn test_lexicographic_with_when() {
    common::with_clean_verification(|| {
        assert_eq!(bounded_ack_when(0, 0), 0);
        assert_eq!(bounded_ack_when(0, 5), 6);
        assert_eq!(bounded_ack_when(1, 1), 3);
        assert_eq!(bounded_ack_when(2, 2), 7);
    })
}

#[via_fn]
fn bad_floor_log2_proof(_n: u64) {
    trust_vc::assert!(false);
}

#[decreases(n, via = bad_floor_log2_proof)]
fn bad_floor_log2(n: u64) -> u64 {
    if n <= 1 {
        0
    } else {
        bad_floor_log2(n >> 1) + 1
    }
}

#[test]
fn test_bad_via_proof_fails_verification() {
    let result = common::verify_and_get_result(|| {
        assert_eq!(bad_floor_log2(16), 4);
    });
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "invalid via proof should produce counterexample, got: {:?}",
        result
    );
}
