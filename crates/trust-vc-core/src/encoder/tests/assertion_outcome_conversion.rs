//! Tests for `AssertionOutcome → VerifyResult` conversion (#1690).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Documents that the `From<AssertionOutcome>` conversion intentionally drops
//! the internal `category` and exact `detail` fields from Unknown —
//! VerifyResult is the public API surface and does not carry either.

use super::*;

use crate::encoder::verification::outcome::AssertionOutcome;
use crate::encoder::verification::unknown_category::UnknownCategory;

#[test]
fn test_verified_converts_to_verify_result_verified() {
    let outcome = AssertionOutcome::Verified;
    let result: VerifyResult = outcome.into();
    expect_verified(
        &result,
        "Verified outcome must map to VerifyResult::Verified",
    );
}

#[test]
fn test_counterexample_preserves_obligation_name_and_model() {
    let outcome = AssertionOutcome::Counterexample {
        obligation_name: "assert_x_positive".to_string(),
        location: None,
        model: Some("x = -1".to_string()),
        bindings: Vec::new(),
    };
    let result: VerifyResult = outcome.into();
    match result {
        VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        } => {
            assert_eq!(obligation_name, "assert_x_positive");
            assert_eq!(model, Some("x = -1".to_string()));
        }
        other => panic!("expected Counterexample, got {:?}", other),
    }
}

#[test]
fn test_counterexample_preserves_none_model() {
    let outcome = AssertionOutcome::Counterexample {
        obligation_name: "invariant_loop_0".to_string(),
        location: None,
        model: None,
        bindings: Vec::new(),
    };
    let result: VerifyResult = outcome.into();
    match result {
        VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        } => {
            assert_eq!(obligation_name, "invariant_loop_0");
            assert!(model.is_none(), "None model must be preserved");
        }
        other => panic!("expected Counterexample, got {:?}", other),
    }
}

#[test]
fn test_unknown_preserves_reason_and_drops_category() {
    let outcome = AssertionOutcome::Unknown {
        reason: "solver timeout after 5s".to_string(),
        category: Some(UnknownCategory::Timeout),
        detail: None,
    };
    let result: VerifyResult = outcome.into();
    match result {
        VerifyResult::Unknown { reason, .. } => {
            assert_eq!(reason, "solver timeout after 5s");
            // category/detail are intentionally dropped in conversion —
            // VerifyResult is the public API surface and does not
            // carry the internal classification/plumbing.
        }
        other => panic!("expected Unknown, got {:?}", other),
    }
}

#[test]
fn test_unknown_with_none_category_converts() {
    let outcome = AssertionOutcome::Unknown {
        reason: "unclassified".to_string(),
        category: None,
        detail: None,
    };
    let result: VerifyResult = outcome.into();
    expect_unknown(&result, "Unknown with None category must convert cleanly");
    if let VerifyResult::Unknown { reason, .. } = &result {
        assert_eq!(reason, "unclassified");
    }
}
