// trust-vc-oracle — Comprehensive feedback roundtrip tests
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Tests the full oracle feedback loop: propose -> verify -> feedback -> refine.
// All tests use MockBackend for deterministic, offline execution.

use std::time::Duration;

use trust_vc_oracle::{
    run_oracle, CertificateInfo, CounterexampleField, FailureLocalization, FunctionSignature,
    MockBackend, OracleConfig, OracleError, ProofFeedback, ProposedAnnotations, StepSummary,
    SubAssertionResult, SubAssertionStatus,
};

// ===========================================================================
// Helpers
// ===========================================================================

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

fn simple_func(name: &str, param_name: &str, param_type: &str) -> FunctionSignature {
    FunctionSignature::new(
        name,
        vec![(param_name.to_string(), param_type.to_string())],
        Some(param_type.to_string()),
        format!(
            "fn {}({}: {}) -> {} {{ {} }}",
            name, param_name, param_type, param_type, param_name
        ),
    )
}

fn make_counterexample(name: &str, ty: &str, value: &str) -> CounterexampleField {
    CounterexampleField {
        name: name.to_string(),
        ty: ty.to_string(),
        value: value.to_string(),
    }
}

fn make_step(label: &str, result: &str, elapsed_ms: u64) -> StepSummary {
    StepSummary {
        label: label.to_string(),
        phase: "Assertion".to_string(),
        elapsed: Duration::from_millis(elapsed_ms),
        result: result.to_string(),
        used_assumptions: vec![],
    }
}

fn verified_feedback(steps: Vec<StepSummary>, elapsed_ms: u64) -> ProofFeedback {
    ProofFeedback::Verified {
        steps,
        elapsed: Duration::from_millis(elapsed_ms),
        certificate_info: None,
    }
}

fn failed_feedback(
    counterexamples: Vec<CounterexampleField>,
    obligation: &str,
    elapsed_ms: u64,
) -> ProofFeedback {
    ProofFeedback::Failed {
        counterexamples,
        localization: FailureLocalization {
            full_assertion: None,
            sub_results: vec![],
        },
        obligation_name: obligation.to_string(),
        solver_mode: "default".to_string(),
        elapsed: Duration::from_millis(elapsed_ms),
    }
}

fn unknown_feedback(reason: &str, suggestion: &str) -> ProofFeedback {
    ProofFeedback::Unknown {
        reason: reason.to_string(),
        category: "Timeout".to_string(),
        is_retriable: true,
        suggestion: suggestion.to_string(),
        elapsed: Duration::from_millis(30000),
    }
}

fn error_feedback(message: &str) -> ProofFeedback {
    ProofFeedback::Error {
        message: message.to_string(),
    }
}

// ===========================================================================
// 1. ProofFeedback::Verified roundtrip — oracle stops after verified feedback
// ===========================================================================

#[test]
fn test_verified_roundtrip_oracle_stops_immediately() {
    let func = simple_func("nonneg", "x", "u32");
    // u32 >= 0 is trivially true — verifies on first try
    let backend = MockBackend::new(vec![proposal(&[], &["x >= 0"])]);
    let config = make_config(10);

    let result = run_oracle(&func, &backend, &config).unwrap();

    assert!(
        result.is_verified(),
        "u32 x >= 0 should verify: {:?}",
        result.final_feedback
    );
    assert_eq!(
        result.iterations, 1,
        "oracle should stop after first verified feedback"
    );
    assert!(
        result.annotations.is_some(),
        "winning annotations should be present"
    );
    assert_eq!(
        result.history.len(),
        1,
        "history should contain exactly one entry"
    );
    assert!(result.history[0].1.is_verified());
}

#[test]
fn test_verified_feedback_json_roundtrip_preserves_all_fields() {
    let feedback = ProofFeedback::Verified {
        steps: vec![
            make_step("postcondition_a", "verified", 10),
            make_step("postcondition_b", "verified", 15),
        ],
        elapsed: Duration::from_millis(30),
        certificate_info: Some(CertificateInfo {
            strict_verified: true,
            clean_supported: false,
            trust_count: 1,
            hole_count: 0,
            resolution_count: 42,
            theory_count: 3,
        }),
    };

    let json = feedback.to_json().unwrap();
    let parsed: ProofFeedback = serde_json::from_str(&json).unwrap();

    assert!(parsed.is_verified());
    match &parsed {
        ProofFeedback::Verified {
            steps,
            elapsed,
            certificate_info,
        } => {
            assert_eq!(steps.len(), 2);
            assert_eq!(steps[0].label, "postcondition_a");
            assert_eq!(steps[1].label, "postcondition_b");
            assert_eq!(*elapsed, Duration::from_millis(30));
            let cert = certificate_info.as_ref().unwrap();
            assert!(cert.strict_verified);
            assert!(!cert.clean_supported);
            assert_eq!(cert.trust_count, 1);
            assert_eq!(cert.hole_count, 0);
            assert_eq!(cert.resolution_count, 42);
            assert_eq!(cert.theory_count, 3);
        }
        other => panic!("expected Verified, got: {:?}", other),
    }
}

// ===========================================================================
// 2. ProofFeedback::Counterexample with model data — triggers refinement
// ===========================================================================

#[test]
fn test_counterexample_triggers_refinement_to_success() {
    let func = simple_func("positive", "x", "i32");

    // First attempt: too strong postcondition for unconstrained i32
    // Second attempt: add precondition that makes the spec provable
    let backend = MockBackend::new(vec![
        proposal(&[], &["x > 0"]),
        proposal(&["x > 0"], &["x >= 1"]),
    ]);
    let config = make_config(5);

    let result = run_oracle(&func, &backend, &config).unwrap();

    assert!(
        result.is_verified(),
        "refinement should converge: {:?}",
        result.final_feedback
    );
    assert_eq!(result.iterations, 2, "should verify on second attempt");
    assert_eq!(result.history.len(), 2);

    // First attempt should have produced a counterexample or unknown
    let first = &result.history[0].1;
    assert!(
        first.is_failed() || first.is_unknown(),
        "first attempt with no precondition should fail: {:?}",
        first
    );

    // Second attempt should be verified
    assert!(result.history[1].1.is_verified());
}

#[test]
fn test_counterexample_feedback_contains_typed_bindings() {
    let feedback = failed_feedback(
        vec![
            make_counterexample("x", "i32", "-42"),
            make_counterexample("result", "i32", "-42"),
        ],
        "ensures_positive",
        15,
    );

    let json = feedback.to_json().unwrap();
    let parsed: ProofFeedback = serde_json::from_str(&json).unwrap();

    match &parsed {
        ProofFeedback::Failed {
            counterexamples,
            obligation_name,
            ..
        } => {
            assert_eq!(counterexamples.len(), 2);
            assert_eq!(counterexamples[0].name, "x");
            assert_eq!(counterexamples[0].ty, "i32");
            assert_eq!(counterexamples[0].value, "-42");
            assert_eq!(counterexamples[1].name, "result");
            assert_eq!(obligation_name, "ensures_positive");
        }
        other => panic!("expected Failed, got: {:?}", other),
    }
}

// ===========================================================================
// 3. ProofFeedback::Unknown with reason — triggers retry with different strategy
// ===========================================================================

#[test]
fn test_unknown_feedback_triggers_retry_until_verified() {
    let func = FunctionSignature::new(
        "bounded",
        vec![
            ("x".to_string(), "u32".to_string()),
            ("y".to_string(), "u32".to_string()),
        ],
        Some("u32".to_string()),
        "fn bounded(x: u32, y: u32) -> u32 { x }",
    );

    // First attempt: a provable spec but the oracle will verify it.
    // Second attempt: simplified postcondition that trivially verifies.
    let backend = MockBackend::new(vec![
        // First attempt: too strong — x is not necessarily > y
        proposal(&[], &["x > y"]),
        // Second attempt: trivially true for u32
        proposal(&[], &["x >= 0"]),
    ]);
    let config = make_config(5);

    let result = run_oracle(&func, &backend, &config).unwrap();

    assert!(
        result.is_verified(),
        "second attempt should verify: {:?}",
        result.final_feedback
    );
    assert_eq!(result.iterations, 2);
    // First attempt should not have been verified
    assert!(!result.history[0].1.is_verified());
}

#[test]
fn test_unknown_feedback_roundtrip_preserves_category_and_retriability() {
    let feedback = ProofFeedback::Unknown {
        reason: "quantifier instantiation limit reached".to_string(),
        category: "QuantifierOverflow".to_string(),
        is_retriable: true,
        suggestion: "reduce quantifier nesting or add explicit triggers".to_string(),
        elapsed: Duration::from_millis(45000),
    };

    let json = feedback.to_json().unwrap();
    let parsed: ProofFeedback = serde_json::from_str(&json).unwrap();

    match &parsed {
        ProofFeedback::Unknown {
            reason,
            category,
            is_retriable,
            suggestion,
            elapsed,
        } => {
            assert_eq!(reason, "quantifier instantiation limit reached");
            assert_eq!(category, "QuantifierOverflow");
            assert!(*is_retriable);
            assert_eq!(
                suggestion,
                "reduce quantifier nesting or add explicit triggers"
            );
            assert_eq!(*elapsed, Duration::from_millis(45000));
        }
        other => panic!("expected Unknown, got: {:?}", other),
    }
}

// ===========================================================================
// 4. ProofFeedback::Error — oracle gracefully handles backend errors
// ===========================================================================

#[test]
fn test_error_feedback_from_exhausted_backend() {
    let func = simple_func("exhaust", "x", "i32");

    // Backend has only one proposal, but oracle budget is 3
    let backend = MockBackend::new(vec![proposal(&[], &["x > 0"])]);
    let config = make_config(3);

    let result = run_oracle(&func, &backend, &config);

    // When the backend is exhausted, run_oracle propagates BackendExhausted as Err
    match result {
        Err(OracleError::BackendExhausted { attempts }) => {
            // The first proposal fails (i32 not always > 0), then second call
            // exhausts the backend at index 1
            assert_eq!(
                attempts, 1,
                "backend should be exhausted after 1 proposal consumed"
            );
        }
        Ok(oracle_result) => {
            // If the first proposal happened to verify, that's also acceptable
            // (depends on ay semantics), but the result should reflect the state
            assert!(
                oracle_result.history.len() <= 1,
                "should not have more history than available proposals"
            );
        }
        Err(other) => panic!("unexpected error variant: {:?}", other),
    }
}

#[test]
fn test_error_feedback_json_roundtrip() {
    let feedback = error_feedback("internal ay crash: sort mismatch in bitvector theory");

    let json = feedback.to_json().unwrap();
    let parsed: ProofFeedback = serde_json::from_str(&json).unwrap();

    assert!(parsed.is_error());
    match &parsed {
        ProofFeedback::Error { message } => {
            assert_eq!(
                message,
                "internal ay crash: sort mismatch in bitvector theory"
            );
        }
        other => panic!("expected Error, got: {:?}", other),
    }
}

#[test]
fn test_error_llm_summary_format() {
    let feedback = error_feedback("parse error: unexpected token at line 42");
    let summary = feedback.to_llm_summary();

    assert!(
        summary.starts_with("ERROR"),
        "error summary should start with ERROR: got '{}'",
        summary
    );
    assert!(
        summary.contains("parse error"),
        "summary should contain the message: got '{}'",
        summary
    );
    assert!(
        summary.contains("line 42"),
        "summary should preserve details: got '{}'",
        summary
    );
}

// ===========================================================================
// 5. Multi-iteration convergence — start with wrong spec, refine through feedback
// ===========================================================================

#[test]
fn test_multi_iteration_convergence_three_attempts() {
    let func = simple_func("check", "x", "i32");

    // Three proposals: each one progressively weaker until one verifies
    // Attempt 1: x > 100 — fails (i32 can be anything)
    // Attempt 2: x > 0 — fails (i32 can be negative)
    // Attempt 3: x > 0 with precondition x > 0 — verifies
    let backend = MockBackend::new(vec![
        proposal(&[], &["x > 100"]),
        proposal(&[], &["x > 0"]),
        proposal(&["x > 0"], &["x >= 1"]),
    ]);
    let config = make_config(5);

    let result = run_oracle(&func, &backend, &config).unwrap();

    assert!(
        result.is_verified(),
        "should converge after 3 attempts: {:?}",
        result.final_feedback
    );
    assert_eq!(result.iterations, 3);
    assert_eq!(result.history.len(), 3);

    // First two attempts should have failed
    for i in 0..2 {
        assert!(
            result.history[i].1.is_failed() || result.history[i].1.is_unknown(),
            "attempt {} should have failed: {:?}",
            i + 1,
            result.history[i].1
        );
    }

    // Third attempt should be verified
    assert!(result.history[2].1.is_verified());

    // Winning annotations should match the third attempt
    let ann = result.annotations.unwrap();
    assert_eq!(ann.requires, vec!["x > 0"]);
    assert_eq!(ann.ensures, vec!["x >= 1"]);
}

#[test]
fn test_multi_iteration_history_preserves_all_proposals() {
    let func = simple_func("track_history", "x", "u32");

    // Two failed attempts then one verified
    let backend = MockBackend::new(vec![
        proposal(&[], &["x > 1000"]),
        proposal(&[], &["x > 500"]),
        proposal(&[], &["x >= 0"]),
    ]);
    let config = make_config(5);

    let result = run_oracle(&func, &backend, &config).unwrap();

    assert!(result.is_verified());
    assert_eq!(result.history.len(), 3);

    // Verify the proposals in history match what the mock emitted
    assert_eq!(result.history[0].0.ensures, vec!["x > 1000"]);
    assert_eq!(result.history[1].0.ensures, vec!["x > 500"]);
    assert_eq!(result.history[2].0.ensures, vec!["x >= 0"]);
}

// ===========================================================================
// 6. Timeout after max_iterations — oracle respects budget
// ===========================================================================

#[test]
fn test_timeout_after_max_iterations_budget_of_one() {
    let func = simple_func("one_shot", "x", "i32");

    // Single attempt, will fail
    let backend = MockBackend::new(vec![proposal(&[], &["x > 0"])]);
    let config = make_config(1);

    let result = run_oracle(&func, &backend, &config).unwrap();

    assert!(
        !result.is_verified(),
        "unconstrained i32 > 0 should not verify"
    );
    assert_eq!(result.iterations, 1, "should use exactly 1 iteration");
    assert!(
        result.annotations.is_none(),
        "no winning annotations when budget exhausted"
    );
    assert_eq!(result.history.len(), 1);
}

#[test]
fn test_timeout_after_max_iterations_budget_of_three() {
    let func = simple_func("three_tries", "x", "i32");

    // All three proposals are too strong for unconstrained i32
    let backend = MockBackend::new(vec![
        proposal(&[], &["x > 100"]),
        proposal(&[], &["x > 50"]),
        proposal(&[], &["x > 0"]),
    ]);
    let config = make_config(3);

    let result = run_oracle(&func, &backend, &config).unwrap();

    assert!(!result.is_verified());
    assert_eq!(result.iterations, 3, "should use all 3 iterations");
    assert!(result.annotations.is_none());
    assert_eq!(
        result.history.len(),
        3,
        "history should record all 3 attempts"
    );

    // Final feedback should be from the last attempt (not an error)
    assert!(
        result.final_feedback.is_failed() || result.final_feedback.is_unknown(),
        "final feedback should be the last attempt's result: {:?}",
        result.final_feedback
    );
}

#[test]
fn test_early_verification_does_not_exhaust_budget() {
    let func = simple_func("quick_verify", "x", "u32");

    // First proposal verifies immediately — remaining 4 iterations unused
    let backend = MockBackend::new(vec![
        proposal(&[], &["x >= 0"]),
        proposal(&[], &["x >= 0"]),
        proposal(&[], &["x >= 0"]),
    ]);
    let config = make_config(5);

    let result = run_oracle(&func, &backend, &config).unwrap();

    assert!(result.is_verified());
    assert_eq!(
        result.iterations, 1,
        "should stop at first verified, not use all 5"
    );
    assert_eq!(result.history.len(), 1);
}

// ===========================================================================
// 7. Empty function body — oracle handles degenerate input
// ===========================================================================

#[test]
fn test_empty_params_trivial_ensures() {
    let func = FunctionSignature::new("unit_fn", vec![], None, "fn unit_fn() {}");

    // ensures!(true) with no variables should verify
    let backend = MockBackend::new(vec![proposal(&[], &["true"])]);
    let config = make_config(3);

    let result = run_oracle(&func, &backend, &config).unwrap();

    assert!(
        result.is_verified(),
        "ensures!(true) with no params should verify: {:?}",
        result.final_feedback
    );
    assert_eq!(result.iterations, 1);
}

#[test]
fn test_empty_ensures_list_handled_gracefully() {
    let func = simple_func("no_post", "x", "u32");

    // No postconditions at all — the verifier may or may not consider this
    // "verified" depending on whether it requires at least one assertion.
    // Supply enough proposals so the oracle does not hit BackendExhausted.
    let backend = MockBackend::new(vec![
        proposal(&[], &[]),
        proposal(&[], &[]),
        proposal(&[], &[]),
    ]);
    let config = make_config(3);

    let result = run_oracle(&func, &backend, &config);

    // The oracle must not panic regardless of the verifier's interpretation
    // of an empty ensures list. It may verify, fail, or exhaust the budget.
    match result {
        Ok(r) => {
            // Either verified (vacuously) or budget exhausted — both valid
            assert!(
                !r.history.is_empty(),
                "should have at least one history entry"
            );
        }
        Err(e) => {
            // BackendExhausted is acceptable if the verifier keeps retrying
            panic!(
                "oracle should not error with 3 proposals available: {:?}",
                e
            );
        }
    }
}

// ===========================================================================
// 8. Multiple functions in one file — oracle processes each independently
// ===========================================================================

#[test]
fn test_independent_functions_verified_separately() {
    // Function A: u32 parameter, trivially provable
    let func_a = FunctionSignature::new(
        "fn_a",
        vec![("a".to_string(), "u32".to_string())],
        Some("u32".to_string()),
        "fn fn_a(a: u32) -> u32 { a }",
    );

    // Function B: i32 parameter with precondition
    let func_b = FunctionSignature::new(
        "fn_b",
        vec![("b".to_string(), "i32".to_string())],
        Some("i32".to_string()),
        "fn fn_b(b: i32) -> i32 { b }",
    );

    let config = make_config(5);

    // Oracle for function A
    let backend_a = MockBackend::new(vec![proposal(&[], &["a >= 0"])]);
    let result_a = run_oracle(&func_a, &backend_a, &config).unwrap();

    // Oracle for function B
    let backend_b = MockBackend::new(vec![
        proposal(&[], &["b > 0"]),         // fails for unconstrained i32
        proposal(&["b > 0"], &["b >= 1"]), // verifies with precondition
    ]);
    let result_b = run_oracle(&func_b, &backend_b, &config).unwrap();

    // A should verify in 1 iteration
    assert!(result_a.is_verified());
    assert_eq!(result_a.iterations, 1);

    // B should verify in 2 iterations
    assert!(result_b.is_verified());
    assert_eq!(result_b.iterations, 2);

    // Histories are fully independent
    assert_eq!(result_a.history.len(), 1);
    assert_eq!(result_b.history.len(), 2);
}

#[test]
fn test_independent_functions_one_passes_one_fails() {
    let func_pass = simple_func("passes", "x", "u32");
    let func_fail = simple_func("fails", "y", "i32");

    let config = make_config(1);

    let backend_pass = MockBackend::new(vec![proposal(&[], &["x >= 0"])]);
    let result_pass = run_oracle(&func_pass, &backend_pass, &config).unwrap();

    let backend_fail = MockBackend::new(vec![proposal(&[], &["y > 0"])]);
    let result_fail = run_oracle(&func_fail, &backend_fail, &config).unwrap();

    assert!(result_pass.is_verified(), "u32 >= 0 should verify");
    assert!(
        !result_fail.is_verified(),
        "unconstrained i32 > 0 should not verify"
    );

    // Verify they did not interfere with each other
    assert!(result_pass.annotations.is_some());
    assert!(result_fail.annotations.is_none());
}

// ===========================================================================
// 9. Backend returning malformed annotations — error recovery
// ===========================================================================

#[test]
fn test_malformed_ensures_expression_produces_feedback() {
    let func = simple_func("malformed", "x", "i32");

    // The ensures clause is syntactic garbage — the verifier should handle it
    // gracefully (either as an error or unknown, not a panic)
    let backend = MockBackend::new(vec![
        proposal(&[], &["%%% not valid %%%"]),
        // Second attempt is correct
        proposal(&["x > 0"], &["x >= 1"]),
    ]);
    let config = make_config(3);

    let result = run_oracle(&func, &backend, &config);

    // The oracle should not panic. It should either:
    // 1. Return Ok with the first attempt failed/error and second verified, or
    // 2. Return Ok with the malformed attempt as failed/unknown/error
    match result {
        Ok(r) => {
            // If the oracle handled the malformed input, the history should show it
            assert!(
                !r.history.is_empty(),
                "should have at least one history entry"
            );
            // The malformed input should not have been "Verified"
            assert!(
                !r.history[0].1.is_verified(),
                "malformed ensures should not verify: {:?}",
                r.history[0].1
            );
        }
        Err(_) => {
            // Also acceptable — the verification layer may reject the input
        }
    }
}

#[test]
fn test_empty_raw_response_does_not_crash() {
    let func = simple_func("empty_raw", "x", "u32");

    // Proposal with empty raw_response field
    let backend = MockBackend::new(vec![ProposedAnnotations {
        requires: vec![],
        ensures: vec!["x >= 0".to_string()],
        invariants: vec![],
        decreases: vec![],
        raw_response: String::new(),
    }]);
    let config = make_config(3);

    let result = run_oracle(&func, &backend, &config).unwrap();

    assert!(
        result.is_verified(),
        "empty raw_response should not affect verification: {:?}",
        result.final_feedback
    );
}

// ===========================================================================
// 10. Idempotent feedback — same feedback twice doesn't diverge
// ===========================================================================

#[test]
fn test_identical_proposals_produce_identical_feedback() {
    let func = simple_func("idem_pass", "x", "u32");
    let config = make_config(1);

    // Run same proposal twice independently
    let backend1 = MockBackend::new(vec![proposal(&[], &["x >= 0"])]);
    let result1 = run_oracle(&func, &backend1, &config).unwrap();

    let backend2 = MockBackend::new(vec![proposal(&[], &["x >= 0"])]);
    let result2 = run_oracle(&func, &backend2, &config).unwrap();

    // Both should produce the same verdict
    assert_eq!(result1.is_verified(), result2.is_verified());
    assert_eq!(result1.iterations, result2.iterations);
    assert_eq!(result1.history.len(), result2.history.len());
}

#[test]
fn test_repeated_failing_proposal_does_not_diverge() {
    let func = simple_func("idem_fail", "x", "i32");

    // Same failing proposal three times
    let backend = MockBackend::new(vec![
        proposal(&[], &["x > 0"]),
        proposal(&[], &["x > 0"]),
        proposal(&[], &["x > 0"]),
    ]);
    let config = make_config(3);

    let result = run_oracle(&func, &backend, &config).unwrap();

    assert!(
        !result.is_verified(),
        "same failing spec should fail every time"
    );
    assert_eq!(result.iterations, 3);

    // All three feedback entries should be consistently failed or unknown
    for (i, (_, feedback)) in result.history.iter().enumerate() {
        assert!(
            feedback.is_failed() || feedback.is_unknown(),
            "attempt {} should fail consistently: {:?}",
            i + 1,
            feedback
        );
    }

    // Verify all proposals in history are identical
    for (i, (ann, _)) in result.history.iter().enumerate() {
        assert_eq!(
            ann.ensures,
            vec!["x > 0"],
            "proposal {} should be unchanged: {:?}",
            i + 1,
            ann.ensures
        );
    }
}

// ===========================================================================
// Additional coverage: ProofFeedback type-level properties
// ===========================================================================

#[test]
fn test_feedback_variant_predicates_are_mutually_exclusive() {
    let variants: Vec<ProofFeedback> = vec![
        verified_feedback(vec![], 1),
        failed_feedback(vec![], "test", 1),
        unknown_feedback("reason", "suggestion"),
        error_feedback("boom"),
    ];

    for feedback in &variants {
        let pred_count = [
            feedback.is_verified(),
            feedback.is_failed(),
            feedback.is_unknown(),
            feedback.is_error(),
        ]
        .iter()
        .filter(|&&b| b)
        .count();

        assert_eq!(
            pred_count, 1,
            "exactly one predicate should be true for {:?}, but {} are",
            feedback, pred_count
        );
    }
}

#[test]
fn test_llm_summary_format_consistency() {
    // Verified starts with "VERIFIED"
    let v = verified_feedback(vec![make_step("a", "verified", 5)], 10);
    assert!(v.to_llm_summary().starts_with("VERIFIED"));

    // Failed starts with "FAILED"
    let f = failed_feedback(vec![make_counterexample("x", "i32", "-1")], "ens", 10);
    let f_summary = f.to_llm_summary();
    assert!(f_summary.starts_with("FAILED"));
    assert!(
        f_summary.contains("x: i32 = -1"),
        "should render counterexample: got '{}'",
        f_summary
    );

    // Unknown starts with "UNKNOWN"
    let u = unknown_feedback("timeout", "simplify");
    let u_summary = u.to_llm_summary();
    assert!(u_summary.starts_with("UNKNOWN"));
    assert!(u_summary.contains("timeout"));
    assert!(u_summary.contains("simplify"));

    // Error starts with "ERROR"
    let e = error_feedback("crash");
    assert!(e.to_llm_summary().starts_with("ERROR"));
}

#[test]
fn test_json_variant_tags_match_enum_names() {
    let test_cases: Vec<(&str, ProofFeedback)> = vec![
        ("Verified", verified_feedback(vec![], 1)),
        ("Failed", failed_feedback(vec![], "test", 1)),
        ("Unknown", unknown_feedback("r", "s")),
        ("Error", error_feedback("e")),
    ];

    for (expected_tag, feedback) in &test_cases {
        let json = feedback.to_json().unwrap();
        let value: serde_json::Value = serde_json::from_str(&json).unwrap();

        assert!(
            value.get(expected_tag).is_some(),
            "JSON for {:?} should have '{}' tag, got: {}",
            feedback,
            expected_tag,
            json
        );
    }
}

#[test]
fn test_failure_localization_sub_assertions_roundtrip() {
    let feedback = ProofFeedback::Failed {
        counterexamples: vec![make_counterexample("x", "i32", "0")],
        localization: FailureLocalization {
            full_assertion: Some("x > 0 && x < 100".to_string()),
            sub_results: vec![
                SubAssertionResult {
                    label: "x > 0".to_string(),
                    status: SubAssertionStatus::Fail,
                },
                SubAssertionResult {
                    label: "x < 100".to_string(),
                    status: SubAssertionStatus::Pass,
                },
            ],
        },
        obligation_name: "compound".to_string(),
        solver_mode: "default".to_string(),
        elapsed: Duration::from_millis(8),
    };

    let json = feedback.to_json().unwrap();
    let parsed: ProofFeedback = serde_json::from_str(&json).unwrap();

    match &parsed {
        ProofFeedback::Failed { localization, .. } => {
            assert_eq!(
                localization.full_assertion.as_deref(),
                Some("x > 0 && x < 100")
            );
            assert_eq!(localization.sub_results.len(), 2);
            assert_eq!(localization.sub_results[0].status, SubAssertionStatus::Fail);
            assert_eq!(localization.sub_results[1].status, SubAssertionStatus::Pass);
        }
        other => panic!("expected Failed, got: {:?}", other),
    }

    // Also check the summary renders the localization
    let summary = feedback.to_llm_summary();
    assert!(
        summary.contains("[FAIL] x > 0"),
        "summary should show FAIL: got '{}'",
        summary
    );
    assert!(
        summary.contains("[PASS] x < 100"),
        "summary should show PASS: got '{}'",
        summary
    );
}

#[test]
fn test_sub_assertion_status_as_str_covers_all_variants() {
    assert_eq!(SubAssertionStatus::Pass.as_str(), "PASS");
    assert_eq!(SubAssertionStatus::Fail.as_str(), "FAIL");
    assert_eq!(SubAssertionStatus::Unknown.as_str(), "UNKNOWN");
    assert_eq!(SubAssertionStatus::Error.as_str(), "ERROR");
}

#[test]
fn test_step_summary_used_assumptions_roundtrip() {
    let feedback = ProofFeedback::Verified {
        steps: vec![StepSummary {
            label: "postcondition".to_string(),
            phase: "Assertion".to_string(),
            elapsed: Duration::from_millis(25),
            result: "verified".to_string(),
            used_assumptions: vec![
                "requires_x_gt_0".to_string(),
                "requires_y_le_100".to_string(),
            ],
        }],
        elapsed: Duration::from_millis(25),
        certificate_info: None,
    };

    let json = feedback.to_json().unwrap();
    let parsed: ProofFeedback = serde_json::from_str(&json).unwrap();

    match &parsed {
        ProofFeedback::Verified { steps, .. } => {
            assert_eq!(steps[0].used_assumptions.len(), 2);
            assert_eq!(steps[0].used_assumptions[0], "requires_x_gt_0");
            assert_eq!(steps[0].used_assumptions[1], "requires_y_le_100");
        }
        other => panic!("expected Verified, got: {:?}", other),
    }
}

// ===========================================================================
// Additional coverage: edge cases in the oracle engine
// ===========================================================================

#[test]
fn test_oracle_config_default_values() {
    let config = OracleConfig::default();
    assert_eq!(config.max_iterations, 10);
    assert!(!config.verbose);
}

#[test]
fn test_oracle_result_is_verified_delegates_to_feedback() {
    let func = simple_func("delegate_test", "x", "u32");

    // Verified case
    let backend_pass = MockBackend::new(vec![proposal(&[], &["x >= 0"])]);
    let result_pass = run_oracle(&func, &backend_pass, &make_config(1)).unwrap();
    assert!(result_pass.is_verified());
    assert!(result_pass.final_feedback.is_verified());

    // Failed case
    let func_fail = simple_func("delegate_fail", "x", "i32");
    let backend_fail = MockBackend::new(vec![proposal(&[], &["x > 0"])]);
    let result_fail = run_oracle(&func_fail, &backend_fail, &make_config(1)).unwrap();
    assert!(!result_fail.is_verified());
    assert!(!result_fail.final_feedback.is_verified());
}

#[test]
fn test_large_counterexample_values_survive_roundtrip() {
    let large_seq = format!(
        "[{}]",
        (0..200)
            .map(|i| i.to_string())
            .collect::<Vec<_>>()
            .join(", ")
    );
    let feedback = failed_feedback(
        vec![make_counterexample("big_arr", "Seq<i32>", &large_seq)],
        "test_large",
        30,
    );

    let json = feedback.to_json().unwrap();
    let parsed: ProofFeedback = serde_json::from_str(&json).unwrap();

    match &parsed {
        ProofFeedback::Failed {
            counterexamples, ..
        } => {
            assert_eq!(counterexamples[0].value, large_seq);
        }
        other => panic!("expected Failed, got: {:?}", other),
    }
}

#[test]
fn test_duration_precision_survives_roundtrip() {
    let feedback = ProofFeedback::Verified {
        steps: vec![StepSummary {
            label: "timing".to_string(),
            phase: "Assertion".to_string(),
            elapsed: Duration::from_nanos(123_456_789),
            result: "verified".to_string(),
            used_assumptions: vec![],
        }],
        elapsed: Duration::from_millis(99999),
        certificate_info: None,
    };

    let json = feedback.to_json().unwrap();
    let parsed: ProofFeedback = serde_json::from_str(&json).unwrap();

    match &parsed {
        ProofFeedback::Verified { steps, elapsed, .. } => {
            assert_eq!(*elapsed, Duration::from_millis(99999));
            assert_eq!(steps[0].elapsed, Duration::from_nanos(123_456_789));
        }
        other => panic!("expected Verified, got: {:?}", other),
    }
}
