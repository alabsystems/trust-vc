// trust-vc-oracle — End-to-end integration tests
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// These tests exercise the full oracle pipeline (propose -> verify -> feedback -> refine)
// using MockBackend so no external LLM service is required.

use trust_vc_oracle::{
    run_oracle, FunctionSignature, MockBackend, OracleConfig, ProofFeedback, ProposedAnnotations,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn make_config(max_iterations: usize) -> OracleConfig {
    OracleConfig {
        max_iterations,
        verbose: false,
    }
}

fn proposal(requires: &[&str], ensures: &[&str]) -> ProposedAnnotations {
    ProposedAnnotations {
        requires: requires.iter().map(|s| s.to_string()).collect(),
        ensures: ensures.iter().map(|s| s.to_string()).collect(),
        invariants: vec![],
        decreases: vec![],
        raw_response: String::new(),
    }
}

// ---------------------------------------------------------------------------
// 1. test_oracle_abs_function
//    Oracle finds specs for abs(x: i32) -> i32.
//    Mock proposes ensures!(result >= 0) — verifies because result is u32.
// ---------------------------------------------------------------------------

#[test]
fn test_oracle_abs_function() {
    // Declare result as u32 so `result >= 0` is trivially provable.
    let func = FunctionSignature::new(
        "abs",
        vec![
            ("x".to_string(), "i32".to_string()),
            ("result".to_string(), "u32".to_string()),
        ],
        Some("u32".to_string()),
        "fn abs(x: i32) -> u32 { if x < 0 { (-x) as u32 } else { x as u32 } }",
    );

    let backend = MockBackend::new(vec![proposal(&[], &["result >= 0"])]);
    let config = make_config(5);

    let result = run_oracle(&func, &backend, &config).unwrap();

    assert!(
        result.is_verified(),
        "abs ensures!(result >= 0) should verify: {:?}",
        result.final_feedback
    );
    assert_eq!(result.iterations, 1);
    assert!(result.annotations.is_some());

    let ann = result.annotations.unwrap();
    assert_eq!(ann.ensures, vec!["result >= 0"]);
    assert!(ann.requires.is_empty());

    // History should contain exactly one entry
    assert_eq!(result.history.len(), 1);
    assert!(result.history[0].1.is_verified());
}

// ---------------------------------------------------------------------------
// 2. test_oracle_max_function
//    Oracle finds specs for max(a: i32, b: i32) -> i32.
//    Mock proposes ensures!(result >= a && result >= b) with matching requires.
// ---------------------------------------------------------------------------

#[test]
fn test_oracle_max_function() {
    let func = FunctionSignature::new(
        "max",
        vec![
            ("a".to_string(), "i32".to_string()),
            ("b".to_string(), "i32".to_string()),
            ("result".to_string(), "i32".to_string()),
        ],
        Some("i32".to_string()),
        "fn max(a: i32, b: i32) -> i32 { if a >= b { a } else { b } }",
    );

    // The verifier treats requires as assumptions — so assuming result >= a
    // and result >= b makes the ensures clause provable.
    let backend = MockBackend::new(vec![proposal(
        &["result >= a", "result >= b"],
        &["result >= a && result >= b"],
    )]);
    let config = make_config(5);

    let result = run_oracle(&func, &backend, &config).unwrap();

    assert!(
        result.is_verified(),
        "max ensures should verify with matching requires: {:?}",
        result.final_feedback
    );
    assert_eq!(result.iterations, 1);

    let ann = result.annotations.unwrap();
    assert_eq!(ann.ensures, vec!["result >= a && result >= b"]);
    assert_eq!(ann.requires.len(), 2);
}

// ---------------------------------------------------------------------------
// 3. test_oracle_with_precondition_refinement
//    First attempt is too strong (ensures x > 0 for unconstrained i32), fails.
//    Second attempt adds a precondition and weakened postcondition, verifies.
// ---------------------------------------------------------------------------

#[test]
fn test_oracle_with_precondition_refinement() {
    let func = FunctionSignature::new(
        "positive",
        vec![("x".to_string(), "i32".to_string())],
        Some("i32".to_string()),
        "fn positive(x: i32) -> i32 { x }",
    );

    let backend = MockBackend::new(vec![
        // Attempt 1: too strong — i32 x can be negative or zero
        proposal(&[], &["x > 0"]),
        // Attempt 2: add precondition, weaken postcondition
        proposal(&["x > 0"], &["x >= 1"]),
    ]);
    let config = make_config(5);

    let result = run_oracle(&func, &backend, &config).unwrap();

    assert!(
        result.is_verified(),
        "x > 0 => x >= 1 should verify: {:?}",
        result.final_feedback
    );
    assert_eq!(result.iterations, 2);
    assert_eq!(result.history.len(), 2);

    // First attempt should have failed (or been unknown)
    let first_feedback = &result.history[0].1;
    assert!(
        first_feedback.is_failed() || first_feedback.is_unknown(),
        "first attempt should fail for unconstrained i32: {:?}",
        first_feedback
    );

    // Second attempt should have succeeded
    let second_feedback = &result.history[1].1;
    assert!(second_feedback.is_verified());

    // Winning annotations should have the precondition
    let ann = result.annotations.unwrap();
    assert_eq!(ann.requires, vec!["x > 0"]);
    assert_eq!(ann.ensures, vec!["x >= 1"]);
}

// ---------------------------------------------------------------------------
// 4. test_oracle_feedback_json_complete
//    Verify JSON output contains all expected fields for a Failed feedback.
// ---------------------------------------------------------------------------

#[test]
fn test_oracle_feedback_json_complete() {
    let func = FunctionSignature::new(
        "check_json",
        vec![("x".to_string(), "i32".to_string())],
        Some("i32".to_string()),
        "fn check_json(x: i32) -> i32 { x }",
    );

    // Propose something that will fail — i32 is not always > 0
    let backend = MockBackend::new(vec![proposal(&[], &["x > 0"])]);
    let config = make_config(1);

    let result = run_oracle(&func, &backend, &config).unwrap();
    assert!(!result.is_verified());

    let feedback = &result.history[0].1;

    // Serialize to JSON
    let json_str = feedback.to_json().unwrap();
    let json: serde_json::Value = serde_json::from_str(&json_str).unwrap();

    match feedback {
        ProofFeedback::Failed {
            counterexamples,
            localization,
            ..
        } => {
            let inner = json
                .get("Failed")
                .expect("JSON should have 'Failed' tag for Failed variant");

            let json_cx = inner["counterexamples"]
                .as_array()
                .expect("Failed should have 'counterexamples' array");
            for (i, cx) in counterexamples.iter().enumerate() {
                let jcx = &json_cx[i];
                assert!(
                    jcx["name"].is_string(),
                    "counterexample should have 'name' field"
                );
                assert!(
                    jcx["ty"].is_string(),
                    "counterexample should have 'ty' field"
                );
                assert!(
                    jcx["value"].is_string(),
                    "counterexample should have 'value' field"
                );
                assert_eq!(jcx["name"].as_str().unwrap(), cx.name);
                assert_eq!(jcx["ty"].as_str().unwrap(), cx.ty);
                assert_eq!(jcx["value"].as_str().unwrap(), cx.value);
            }

            let json_loc = &inner["localization"];
            assert!(
                json_loc["sub_results"].is_array(),
                "localization should have 'sub_results' array"
            );

            let sub_results = json_loc["sub_results"].as_array().unwrap();
            for (i, sr) in localization.sub_results.iter().enumerate() {
                let jsr = &sub_results[i];
                assert!(
                    jsr["label"].is_string(),
                    "sub_result should have 'label' field"
                );
                assert!(
                    jsr["status"].is_string(),
                    "sub_result should have 'status' field"
                );
                assert_eq!(jsr["label"].as_str().unwrap(), sr.label);
            }
        }
        ProofFeedback::Unknown { .. } => {
            let inner = json
                .get("Unknown")
                .expect("JSON should have 'Unknown' tag for Unknown variant");

            assert!(inner["reason"].is_string(), "unknown should have 'reason'");
            assert!(
                inner["category"].is_string(),
                "unknown should have 'category'"
            );
            assert!(
                inner["suggestion"].is_string(),
                "unknown should have 'suggestion'"
            );
        }
        other => panic!(
            "expected Failed or Unknown feedback for i32 x > 0, got: {:?}",
            other
        ),
    }

    // Round-trip: JSON parses back to ProofFeedback
    let roundtrip: ProofFeedback = serde_json::from_str(&json_str).unwrap();
    assert!(
        roundtrip.is_failed() || roundtrip.is_unknown(),
        "round-tripped feedback should preserve variant"
    );
}

// ---------------------------------------------------------------------------
// 5. test_oracle_feedback_llm_summary
//    Verify text summary is well-formed for LLM consumption.
// ---------------------------------------------------------------------------

#[test]
fn test_oracle_feedback_llm_summary() {
    // -- Verified summary --
    let func_pass = FunctionSignature::new(
        "nonneg",
        vec![("x".to_string(), "u32".to_string())],
        Some("u32".to_string()),
        "fn nonneg(x: u32) -> u32 { x }",
    );

    let backend_pass = MockBackend::new(vec![proposal(&[], &["x >= 0"])]);
    let result_pass = run_oracle(&func_pass, &backend_pass, &make_config(1)).unwrap();
    assert!(result_pass.is_verified());

    let summary_pass = result_pass.final_feedback.to_llm_summary();
    assert!(
        summary_pass.starts_with("VERIFIED"),
        "verified summary should start with VERIFIED: got '{}'",
        summary_pass
    );

    // -- Failed summary --
    let func_fail = FunctionSignature::new(
        "check_fail",
        vec![("x".to_string(), "i32".to_string())],
        Some("i32".to_string()),
        "fn check_fail(x: i32) -> i32 { x }",
    );

    let backend_fail = MockBackend::new(vec![proposal(&[], &["x > 0"])]);
    let result_fail = run_oracle(&func_fail, &backend_fail, &make_config(1)).unwrap();
    assert!(!result_fail.is_verified());

    let summary_fail = result_fail.final_feedback.to_llm_summary();
    match &result_fail.final_feedback {
        ProofFeedback::Failed {
            counterexamples, ..
        } => {
            assert!(
                summary_fail.starts_with("FAILED"),
                "failed summary should start with FAILED: got '{}'",
                summary_fail
            );
            for cx in counterexamples {
                assert!(
                    summary_fail.contains(&cx.name),
                    "summary should contain variable name '{}': got '{}'",
                    cx.name,
                    summary_fail
                );
                assert!(
                    summary_fail.contains(&cx.value),
                    "summary should contain variable value '{}': got '{}'",
                    cx.value,
                    summary_fail
                );
            }
        }
        ProofFeedback::Unknown { .. } => {
            assert!(
                summary_fail.starts_with("UNKNOWN"),
                "unknown summary should start with UNKNOWN: got '{}'",
                summary_fail
            );
        }
        other => panic!("expected Failed or Unknown, got: {:?}", other),
    }
}

// ---------------------------------------------------------------------------
// 6. test_oracle_multiple_ensures
//    Oracle handles multiple postconditions proposed simultaneously.
// ---------------------------------------------------------------------------

#[test]
fn test_oracle_multiple_ensures() {
    let func = FunctionSignature::new(
        "multi_post",
        vec![("x".to_string(), "u32".to_string())],
        Some("u32".to_string()),
        "fn multi_post(x: u32) -> u32 { x }",
    );

    // Two ensures clauses that are both trivially true for u32
    let backend = MockBackend::new(vec![proposal(&[], &["x >= 0", "x == x"])]);
    let config = make_config(5);

    let result = run_oracle(&func, &backend, &config).unwrap();

    assert!(
        result.is_verified(),
        "both ensures should verify for u32: {:?}",
        result.final_feedback
    );
    assert_eq!(result.iterations, 1);

    let ann = result.annotations.unwrap();
    assert_eq!(ann.ensures.len(), 2, "should preserve both ensures clauses");
    assert_eq!(ann.ensures[0], "x >= 0");
    assert_eq!(ann.ensures[1], "x == x");
}

// ---------------------------------------------------------------------------
// 7. test_oracle_budget_exhaustion
//    All proposals fail; verify iterations == max_iterations and graceful exit.
// ---------------------------------------------------------------------------

#[test]
fn test_oracle_budget_exhaustion() {
    let func = FunctionSignature::new(
        "impossible",
        vec![("x".to_string(), "i32".to_string())],
        Some("i32".to_string()),
        "fn impossible(x: i32) -> i32 { x }",
    );

    // Three proposals, all too strong for unconstrained i32
    let backend = MockBackend::new(vec![
        proposal(&[], &["x > 100"]),
        proposal(&[], &["x > 50"]),
        proposal(&[], &["x > 0"]),
    ]);
    let config = make_config(3);

    let result = run_oracle(&func, &backend, &config).unwrap();

    assert!(!result.is_verified(), "all proposals should fail");
    assert_eq!(
        result.iterations, 3,
        "should exhaust entire budget of 3 iterations"
    );
    assert!(
        result.annotations.is_none(),
        "no winning annotations when budget exhausted"
    );
    assert_eq!(
        result.history.len(),
        3,
        "history should record all attempts"
    );

    // Every attempt should have failed or been unknown
    for (i, (_, feedback)) in result.history.iter().enumerate() {
        assert!(
            feedback.is_failed() || feedback.is_unknown(),
            "attempt {} should have failed: {:?}",
            i + 1,
            feedback
        );
    }
}

// ---------------------------------------------------------------------------
// 8. test_oracle_empty_ensures_trivial
//    ensures!(true) always verifies.
// ---------------------------------------------------------------------------

#[test]
fn test_oracle_empty_ensures_trivial() {
    let func = FunctionSignature::new(
        "trivial",
        vec![("x".to_string(), "i32".to_string())],
        Some("i32".to_string()),
        "fn trivial(x: i32) -> i32 { x }",
    );

    let backend = MockBackend::new(vec![proposal(&[], &["true"])]);
    let config = make_config(1);

    let result = run_oracle(&func, &backend, &config).unwrap();

    assert!(
        result.is_verified(),
        "ensures!(true) should always verify: {:?}",
        result.final_feedback
    );
    assert_eq!(result.iterations, 1);

    let ann = result.annotations.unwrap();
    assert_eq!(ann.ensures, vec!["true"]);

    // Verify the OracleResult structure
    assert_eq!(result.history.len(), 1);
    assert!(result.history[0].1.is_verified());

    // Verify ProofFeedback structure for Verified variant
    match &result.final_feedback {
        ProofFeedback::Verified {
            steps,
            elapsed,
            certificate_info,
        } => {
            let _ = elapsed.as_millis();
            assert!(
                certificate_info.is_none(),
                "certificate_info should be None without proof-certificates feature"
            );
            for step in steps {
                assert!(!step.label.is_empty(), "step label should be non-empty");
                assert!(!step.result.is_empty(), "step result should be non-empty");
            }
        }
        other => panic!("expected Verified, got: {:?}", other),
    }
}
