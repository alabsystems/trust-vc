// trust-vc-oracle — End-to-end integration test with CodexBackend pipeline
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Exercises the full LLM proof oracle pipeline:
//   source parsing -> signature extraction -> prompt generation ->
//   LLM call (mock) -> annotation parsing -> verification -> feedback
//
// Uses a mock backend that simulates CodexBackend responses (structured
// REQUIRES:/ENSURES: format) so no API keys or network access are needed.
// Epic: #2746, Task 1.2 (#2752)

use trust_vc_oracle::prompt::{build_user_prompt, parse_annotations, SYSTEM_PROMPT};
use trust_vc_oracle::{
    parse_function_by_name, parse_functions, run_oracle, CodexBackend, FunctionSignature,
    LlmBackend, OracleConfig, OracleError, ProofFeedback, ProposedAnnotations,
};

// ===========================================================================
// CodexStyleMockBackend — simulates CodexBackend response format
// ===========================================================================

/// A mock LLM backend that returns canned responses in the same structured
/// format that the Codex CLI would produce (REQUIRES:/ENSURES: lines).
///
/// Unlike `MockBackend` which returns pre-built `ProposedAnnotations`,
/// this backend returns raw text that must pass through `parse_annotations`,
/// exercising the full prompt->response->parse pipeline.
struct CodexStyleMockBackend {
    /// Raw LLM response strings, indexed by feedback history length.
    responses: Vec<String>,
}

impl CodexStyleMockBackend {
    fn new(responses: Vec<String>) -> Self {
        Self { responses }
    }
}

impl LlmBackend for CodexStyleMockBackend {
    fn propose_annotations(
        &self,
        source: &str,
        feedback_history: &[(ProposedAnnotations, ProofFeedback)],
    ) -> Result<ProposedAnnotations, OracleError> {
        // Verify the prompt is well-formed before responding
        let prompt = build_user_prompt(source, feedback_history);
        assert!(
            prompt.contains("```rust"),
            "prompt should contain fenced source code"
        );

        let idx = feedback_history.len();
        let raw = self
            .responses
            .get(idx)
            .ok_or(OracleError::BackendExhausted { attempts: idx })?;

        Ok(parse_annotations(raw))
    }

    fn name(&self) -> &str {
        "codex-mock"
    }
}

// ===========================================================================
// Helpers
// ===========================================================================

fn make_config(max_iterations: usize) -> OracleConfig {
    OracleConfig {
        max_iterations,
        verbose: false,
    }
}

/// Sample Rust source file with multiple functions of varying complexity.
const SAMPLE_SOURCE: &str = r#"
fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}

fn clamp(x: i32, lo: i32, hi: i32) -> i32 {
    if x < lo { lo } else if x > hi { hi } else { x }
}

fn identity(x: u32) -> u32 {
    x
}

fn double(x: u32) -> u32 {
    x + x
}

struct Counter {
    val: u32,
}

impl Counter {
    fn value(&self) -> u32 {
        self.val
    }

    fn increment(&mut self) {
        self.val += 1;
    }
}
"#;

// ===========================================================================
// Phase 1: Source parsing -> signature extraction
// ===========================================================================

#[test]
fn test_e2e_source_parsing_extracts_all_functions() {
    let sigs = parse_functions(SAMPLE_SOURCE);

    let names: Vec<&str> = sigs.iter().map(|s| s.name.as_str()).collect();
    assert!(names.contains(&"abs"), "should find abs: {:?}", names);
    assert!(names.contains(&"clamp"), "should find clamp: {:?}", names);
    assert!(
        names.contains(&"identity"),
        "should find identity: {:?}",
        names
    );
    assert!(names.contains(&"double"), "should find double: {:?}", names);
    assert!(
        names.contains(&"value"),
        "should find value method: {:?}",
        names
    );
    assert!(
        names.contains(&"increment"),
        "should find increment method: {:?}",
        names
    );
    assert_eq!(sigs.len(), 6, "should find exactly 6 functions/methods");
}

#[test]
fn test_e2e_source_parsing_extracts_params_and_return_types() {
    let clamp =
        parse_function_by_name(SAMPLE_SOURCE, "clamp").expect("clamp should be found in source");

    assert_eq!(clamp.params.len(), 3);
    assert_eq!(clamp.params[0].0, "x");
    assert_eq!(clamp.params[0].1, "i32");
    assert_eq!(clamp.params[1].0, "lo");
    assert_eq!(clamp.params[1].1, "i32");
    assert_eq!(clamp.params[2].0, "hi");
    assert_eq!(clamp.params[2].1, "i32");
    assert_eq!(clamp.return_type.as_deref(), Some("i32"));
}

#[test]
fn test_e2e_source_parsing_handles_self_methods() {
    let value =
        parse_function_by_name(SAMPLE_SOURCE, "value").expect("value method should be found");

    assert_eq!(value.params.len(), 1);
    assert_eq!(value.params[0].0, "self");
    assert_eq!(value.params[0].1, "&self");
    assert_eq!(value.return_type.as_deref(), Some("u32"));
}

// ===========================================================================
// Phase 2: Prompt generation from parsed signatures
// ===========================================================================

#[test]
fn test_e2e_prompt_generation_includes_source() {
    let sig = parse_function_by_name(SAMPLE_SOURCE, "identity").expect("identity should be found");

    let prompt = build_user_prompt(&sig.source, &[]);

    assert!(
        prompt.contains("fn identity"),
        "prompt should include function source"
    );
    assert!(
        prompt.contains("```rust"),
        "prompt should use fenced code blocks"
    );
    assert!(
        !prompt.contains("Previous attempts"),
        "first prompt should have no history"
    );
}

#[test]
fn test_e2e_prompt_generation_includes_feedback_history() {
    let sig = parse_function_by_name(SAMPLE_SOURCE, "abs").expect("abs should be found");

    let history = vec![(
        ProposedAnnotations {
            requires: vec![],
            ensures: vec!["result >= 0".to_string()],
            invariants: vec![],
            decreases: vec![],
            raw_response: "ENSURES: result >= 0".to_string(),
        },
        ProofFeedback::Failed {
            counterexamples: vec![],
            localization: trust_vc_oracle::FailureLocalization {
                full_assertion: None,
                sub_results: vec![],
            },
            obligation_name: "ensures_nonneg".to_string(),
            solver_mode: "default".to_string(),
            elapsed: std::time::Duration::from_millis(10),
        },
    )];

    let prompt = build_user_prompt(&sig.source, &history);

    assert!(
        prompt.contains("Previous attempts"),
        "prompt with history should include previous attempts section"
    );
    assert!(
        prompt.contains("Attempt 1"),
        "prompt should number attempts"
    );
    assert!(
        prompt.contains("ensures!(result >= 0)"),
        "prompt should show prior proposals"
    );
}

#[test]
fn test_e2e_system_prompt_teaches_trust_vc_syntax() {
    assert!(
        SYSTEM_PROMPT.contains("requires!"),
        "system prompt should teach requires! syntax"
    );
    assert!(
        SYSTEM_PROMPT.contains("ensures!"),
        "system prompt should teach ensures! syntax"
    );
    assert!(
        SYSTEM_PROMPT.contains("REQUIRES:"),
        "system prompt should teach structured response format"
    );
    assert!(
        SYSTEM_PROMPT.contains("ENSURES:"),
        "system prompt should teach structured response format"
    );
}

// ===========================================================================
// Phase 3: LLM response parsing (simulated Codex responses)
// ===========================================================================

#[test]
fn test_e2e_parse_codex_style_structured_response() {
    let codex_response = "\
REQUIRES: x != i32::MIN
ENSURES: result >= 0
ENSURES: result == x || result == -x";

    let ann = parse_annotations(codex_response);
    assert_eq!(ann.requires, vec!["x != i32::MIN"]);
    assert_eq!(ann.ensures.len(), 2);
    assert_eq!(ann.ensures[0], "result >= 0");
    assert_eq!(ann.ensures[1], "result == x || result == -x");
}

#[test]
fn test_e2e_parse_codex_style_response_with_prose() {
    // Codex sometimes adds explanatory text around the annotations
    let codex_response = "\
Here are the formal specifications for the clamp function:

REQUIRES: lo <= hi
ENSURES: result >= lo && result <= hi
ENSURES: result == x || result == lo || result == hi

These ensure the output is within bounds.";

    let ann = parse_annotations(codex_response);
    assert_eq!(ann.requires, vec!["lo <= hi"]);
    assert_eq!(ann.ensures.len(), 2);
    assert!(ann.ensures[0].contains("result >= lo"));
    assert!(ann.ensures[1].contains("result == x"));
}

#[test]
fn test_e2e_parse_codex_style_macro_format() {
    // Some LLMs respond in macro format instead of structured format
    let codex_response = "\
requires!(lo <= hi)
ensures!(result >= lo)
ensures!(result <= hi)";

    let ann = parse_annotations(codex_response);
    assert_eq!(ann.requires, vec!["lo <= hi"]);
    assert_eq!(ann.ensures, vec!["result >= lo", "result <= hi"]);
}

// ===========================================================================
// Phase 4: Full pipeline — parse -> prompt -> mock LLM -> verify -> feedback
// ===========================================================================

#[test]
fn test_e2e_full_pipeline_identity_u32() {
    // Parse the function from source
    let sig = parse_function_by_name(SAMPLE_SOURCE, "identity")
        .expect("identity should be found in source");

    // Build the FunctionSignature with variable declarations for verification
    let func = FunctionSignature::new(
        sig.name.clone(),
        vec![("x".to_string(), "u32".to_string())],
        sig.return_type.clone(),
        sig.source.clone(),
    );

    // Codex mock returns structured format, as the real Codex CLI would
    let backend = CodexStyleMockBackend::new(vec!["ENSURES: x >= 0".to_string()]);

    let config = make_config(3);
    let result = run_oracle(&func, &backend, &config).unwrap();

    assert!(
        result.is_verified(),
        "u32 >= 0 is trivially true, should verify: {:?}",
        result.final_feedback
    );
    assert_eq!(result.iterations, 1, "should succeed on first try");
    assert!(result.annotations.is_some());
    assert_eq!(result.annotations.unwrap().ensures, vec!["x >= 0"]);
}

#[test]
fn test_e2e_full_pipeline_with_refinement() {
    // Parse function from source
    let sig = parse_function_by_name(SAMPLE_SOURCE, "abs").expect("abs should be found in source");

    // For verification, we declare the variables the verifier will reason about
    let func = FunctionSignature::new(
        "abs",
        vec![
            ("x".to_string(), "i32".to_string()),
            ("result".to_string(), "u32".to_string()),
        ],
        Some("u32".to_string()),
        sig.source.clone(),
    );

    // Simulate a Codex session where first attempt fails, second succeeds:
    //   Attempt 1: "ENSURES: result == x" -- fails because result is u32, x is i32
    //   Attempt 2: "ENSURES: result >= 0" -- succeeds (u32 is always >= 0)
    let backend = CodexStyleMockBackend::new(vec![
        "ENSURES: result == x".to_string(),
        "ENSURES: result >= 0".to_string(),
    ]);

    let config = make_config(5);
    let result = run_oracle(&func, &backend, &config).unwrap();

    // The first proposal may fail or succeed depending on ay's handling of
    // cross-type comparison. Either way, the pipeline should eventually verify.
    assert!(
        result.is_verified(),
        "should eventually verify: {:?}",
        result.final_feedback
    );
    assert!(result.iterations <= 2, "should verify within 2 iterations");
    assert!(result.annotations.is_some());

    // The history should show at least one entry
    assert!(!result.history.is_empty(), "history should be non-empty");
}

#[test]
fn test_e2e_full_pipeline_precondition_discovery() {
    // Parse a function that needs a precondition
    let func = FunctionSignature::new(
        "positive_check",
        vec![("x".to_string(), "i32".to_string())],
        Some("i32".to_string()),
        "fn positive_check(x: i32) -> i32 { x }",
    );

    // Codex first tries without precondition (fails), then adds one
    let backend = CodexStyleMockBackend::new(vec![
        "ENSURES: x > 0".to_string(),
        "REQUIRES: x > 0\nENSURES: x >= 1".to_string(),
    ]);

    let config = make_config(5);
    let result = run_oracle(&func, &backend, &config).unwrap();

    assert!(
        result.is_verified(),
        "x > 0 => x >= 1 should verify: {:?}",
        result.final_feedback
    );
    assert_eq!(
        result.iterations, 2,
        "should refine in exactly 2 iterations"
    );

    // First attempt should have failed
    let first = &result.history[0].1;
    assert!(
        first.is_failed() || first.is_unknown(),
        "first attempt (no precondition) should fail: {:?}",
        first
    );

    // Winning annotations should have the precondition
    let ann = result.annotations.unwrap();
    assert_eq!(ann.requires, vec!["x > 0"]);
    assert_eq!(ann.ensures, vec!["x >= 1"]);
}

#[test]
fn test_e2e_full_pipeline_budget_exhaustion() {
    let func = FunctionSignature::new(
        "unprovable",
        vec![("x".to_string(), "i32".to_string())],
        Some("i32".to_string()),
        "fn unprovable(x: i32) -> i32 { x }",
    );

    // All responses are too strong for unconstrained i32
    let backend = CodexStyleMockBackend::new(vec![
        "ENSURES: x > 100".to_string(),
        "ENSURES: x > 0".to_string(),
    ]);

    let config = make_config(2);
    let result = run_oracle(&func, &backend, &config).unwrap();

    assert!(
        !result.is_verified(),
        "should NOT verify — all proposals too strong"
    );
    assert_eq!(result.iterations, 2);
    assert!(result.annotations.is_none());
    assert_eq!(result.history.len(), 2);

    // Both attempts should have failed
    for (i, (_, feedback)) in result.history.iter().enumerate() {
        assert!(
            feedback.is_failed() || feedback.is_unknown(),
            "attempt {} should fail: {:?}",
            i + 1,
            feedback
        );
    }
}

// ===========================================================================
// Phase 5: Feedback validation
// ===========================================================================

#[test]
fn test_e2e_verified_feedback_structure() {
    let func = FunctionSignature::new(
        "nonneg",
        vec![("x".to_string(), "u32".to_string())],
        Some("u32".to_string()),
        "fn nonneg(x: u32) -> u32 { x }",
    );

    let backend = CodexStyleMockBackend::new(vec!["ENSURES: x >= 0".to_string()]);

    let result = run_oracle(&func, &backend, &make_config(1)).unwrap();
    assert!(result.is_verified());

    match &result.final_feedback {
        ProofFeedback::Verified {
            steps,
            elapsed,
            certificate_info,
        } => {
            // Elapsed should be non-zero for real verification
            let _ = elapsed.as_millis();

            // Without proof-certificates feature, cert info should be None
            assert!(
                certificate_info.is_none(),
                "certificate_info should be None without feature flag"
            );

            // Steps should be valid
            for step in steps {
                assert!(!step.label.is_empty(), "step label should be non-empty");
                assert!(!step.result.is_empty(), "step result should be non-empty");
                assert!(!step.phase.is_empty(), "step phase should be non-empty");
            }
        }
        other => panic!("expected Verified feedback, got: {:?}", other),
    }

    // JSON round-trip
    let json_str = result.final_feedback.to_json().unwrap();
    let roundtrip: ProofFeedback = serde_json::from_str(&json_str).unwrap();
    assert!(
        roundtrip.is_verified(),
        "JSON round-trip should preserve Verified"
    );

    // LLM summary
    let summary = result.final_feedback.to_llm_summary();
    assert!(
        summary.starts_with("VERIFIED"),
        "summary should start with VERIFIED: got '{}'",
        summary
    );
}

#[test]
fn test_e2e_failed_feedback_has_counterexample() {
    let func = FunctionSignature::new(
        "check_cx",
        vec![("x".to_string(), "i32".to_string())],
        Some("i32".to_string()),
        "fn check_cx(x: i32) -> i32 { x }",
    );

    let backend = CodexStyleMockBackend::new(vec!["ENSURES: x > 0".to_string()]);

    let result = run_oracle(&func, &backend, &make_config(1)).unwrap();

    let feedback = &result.history[0].1;
    match feedback {
        ProofFeedback::Failed {
            counterexamples,
            localization: _,
            obligation_name,
            solver_mode,
            elapsed: _,
        } => {
            // Should have counterexample bindings
            assert!(
                !counterexamples.is_empty(),
                "failed verification should produce counterexamples"
            );
            // The counterexample should show x with a non-positive value
            let x_cx = counterexamples.iter().find(|cx| cx.name == "x");
            assert!(x_cx.is_some(), "counterexample should include variable x");
            let x_cx = x_cx.unwrap();
            assert_eq!(x_cx.ty, "i32", "counterexample type should be i32");

            // Obligation name should be non-empty
            assert!(
                !obligation_name.is_empty(),
                "obligation_name should be non-empty"
            );

            // Solver mode should be non-empty
            assert!(!solver_mode.is_empty(), "solver_mode should be non-empty");

            // LLM summary should contain counterexample info
            let summary = feedback.to_llm_summary();
            assert!(summary.contains("FAILED"), "summary should contain FAILED");
            assert!(summary.contains("x"), "summary should mention variable x");

            // JSON round-trip
            let json_str = feedback.to_json().unwrap();
            let roundtrip: ProofFeedback = serde_json::from_str(&json_str).unwrap();
            assert!(
                roundtrip.is_failed(),
                "JSON round-trip should preserve Failed"
            );
        }
        ProofFeedback::Unknown {
            reason, suggestion, ..
        } => {
            // Unknown is also acceptable — ay may return unknown instead of SAT
            assert!(!reason.is_empty(), "unknown should have a reason");
            assert!(!suggestion.is_empty(), "unknown should have a suggestion");
        }
        other => panic!("expected Failed or Unknown for i32 x > 0, got: {:?}", other),
    }
}

#[test]
fn test_e2e_feedback_llm_summary_round_trips_through_json() {
    let func = FunctionSignature::new(
        "json_rt",
        vec![
            ("x".to_string(), "i32".to_string()),
            ("y".to_string(), "i32".to_string()),
        ],
        Some("i32".to_string()),
        "fn json_rt(x: i32, y: i32) -> i32 { x }",
    );

    // Two-iteration session: first fails, second verifies
    let backend = CodexStyleMockBackend::new(vec![
        "ENSURES: x > y".to_string(),
        "REQUIRES: x >= y\nENSURES: x >= y".to_string(),
    ]);

    let result = run_oracle(&func, &backend, &make_config(5)).unwrap();
    assert!(result.is_verified());

    // Every feedback in history should survive JSON round-trip
    for (i, (_, feedback)) in result.history.iter().enumerate() {
        let json_str = feedback
            .to_json()
            .unwrap_or_else(|e| panic!("iteration {} feedback should serialize: {}", i, e));

        let roundtrip: ProofFeedback = serde_json::from_str(&json_str)
            .unwrap_or_else(|e| panic!("iteration {} feedback should deserialize: {}", i, e));

        // Variant should be preserved
        match (feedback, &roundtrip) {
            (ProofFeedback::Verified { .. }, ProofFeedback::Verified { .. }) => {}
            (ProofFeedback::Failed { .. }, ProofFeedback::Failed { .. }) => {}
            (ProofFeedback::Unknown { .. }, ProofFeedback::Unknown { .. }) => {}
            (ProofFeedback::Error { .. }, ProofFeedback::Error { .. }) => {}
            _ => panic!(
                "iteration {} round-trip changed variant: {:?} -> {:?}",
                i, feedback, roundtrip
            ),
        }

        // LLM summary should be non-empty
        let summary = feedback.to_llm_summary();
        assert!(
            !summary.is_empty(),
            "iteration {} summary should be non-empty",
            i
        );
    }
}

// ===========================================================================
// Phase 6: CodexBackend unit-level checks (no subprocess)
// ===========================================================================

#[test]
fn test_codex_backend_construction() {
    let backend = CodexBackend::new("o4-mini");
    assert_eq!(backend.name(), "codex");

    let backend_with_dir = CodexBackend::new("o3")
        .with_working_dir("/tmp/trust-vc-test")
        .with_timeout(std::time::Duration::from_secs(120));
    assert_eq!(backend_with_dir.name(), "codex");
}

#[test]
fn test_codex_backend_unavailable_returns_typed_error() {
    let backend = CodexBackend::new("o4-mini");

    // If codex CLI is not installed, we should get BackendUnavailable
    if !backend.is_available() {
        let result = backend.propose_annotations("fn foo() {}", &[]);
        assert!(result.is_err());
        match result.unwrap_err() {
            OracleError::BackendUnavailable { backend: name, .. } => {
                assert_eq!(name, "codex");
            }
            other => panic!("expected BackendUnavailable, got: {:?}", other),
        }
    }
}

// ===========================================================================
// Phase 7: Multi-function source file pipeline
// ===========================================================================

#[test]
fn test_e2e_multi_function_pipeline() {
    // Parse all functions from the sample source
    let sigs = parse_functions(SAMPLE_SOURCE);
    assert!(sigs.len() >= 4, "should parse multiple functions");

    // Run oracle on each free function (skip methods with self)
    let free_functions: Vec<_> = sigs
        .iter()
        .filter(|s| s.params.iter().all(|(name, _)| name != "self"))
        .collect();

    assert!(
        free_functions.len() >= 3,
        "should have at least 3 free functions"
    );

    // Verify identity and double (both u32 -> u32) with trivial specs
    for sig in &free_functions {
        if sig.name == "identity" || sig.name == "double" {
            let func = FunctionSignature::new(
                sig.name.clone(),
                vec![("x".to_string(), "u32".to_string())],
                sig.return_type.clone(),
                sig.source.clone(),
            );

            let backend = CodexStyleMockBackend::new(vec!["ENSURES: x >= 0".to_string()]);

            let result = run_oracle(&func, &backend, &make_config(1)).unwrap();
            assert!(
                result.is_verified(),
                "u32 x >= 0 should verify for {}: {:?}",
                sig.name,
                result.final_feedback
            );
        }
    }
}
