// trust-vc-oracle — Claude backend integration tests
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Tests for ClaudeBackend availability, prompt construction, annotation
// parsing edge cases, "I don't know" LLM responses, and timeout handling.
// Live LLM tests are guarded by the TRUST_VC_LIVE_LLM=1 env var.

use std::time::Duration;

use trust_vc_oracle::prompt::{build_user_prompt, parse_annotations, SYSTEM_PROMPT};
use trust_vc_oracle::{
    run_oracle, ClaudeBackend, CodexBackend, CounterexampleField, FailureLocalization,
    FunctionSignature, LlmBackend, MockBackend, OracleConfig, OracleError, ProofFeedback,
    ProposedAnnotations,
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

fn abs_signature() -> FunctionSignature {
    FunctionSignature::new(
        "abs",
        vec![
            ("x".to_string(), "i32".to_string()),
            ("result".to_string(), "u32".to_string()),
        ],
        Some("u32".to_string()),
        "fn abs(x: i32) -> u32 { if x < 0 { (-x) as u32 } else { x as u32 } }",
    )
}

fn is_live_llm_enabled() -> bool {
    std::env::var("TRUST_VC_LIVE_LLM")
        .map(|v| v == "1")
        .unwrap_or(false)
}

/// A backend that always returns empty annotations (simulates "I don't know").
struct EmptyResponseBackend;

impl LlmBackend for EmptyResponseBackend {
    fn propose_annotations(
        &self,
        _source: &str,
        _feedback_history: &[(ProposedAnnotations, ProofFeedback)],
    ) -> Result<ProposedAnnotations, OracleError> {
        Ok(parse_annotations(
            "I'm not sure what to propose for this function.",
        ))
    }

    fn name(&self) -> &str {
        "empty-response"
    }
}

/// A backend that always times out (simulates an unresponsive LLM).
struct TimeoutBackend;

impl LlmBackend for TimeoutBackend {
    fn propose_annotations(
        &self,
        _source: &str,
        _feedback_history: &[(ProposedAnnotations, ProofFeedback)],
    ) -> Result<ProposedAnnotations, OracleError> {
        Err(OracleError::BackendTimeout { seconds: 30 })
    }

    fn name(&self) -> &str {
        "timeout-backend"
    }
}

/// A backend that returns messy markdown-wrapped responses.
struct MessyMarkdownBackend {
    responses: Vec<String>,
}

impl LlmBackend for MessyMarkdownBackend {
    fn propose_annotations(
        &self,
        _source: &str,
        feedback_history: &[(ProposedAnnotations, ProofFeedback)],
    ) -> Result<ProposedAnnotations, OracleError> {
        let idx = feedback_history.len();
        let response = self
            .responses
            .get(idx)
            .ok_or(OracleError::BackendExhausted { attempts: idx })?;
        Ok(parse_annotations(response))
    }

    fn name(&self) -> &str {
        "messy-markdown"
    }
}

// ===========================================================================
// Test 1: ClaudeBackend is_available checks CLI presence
// ===========================================================================

#[test]
fn test_claude_backend_is_available() {
    let backend = ClaudeBackend::new("sonnet");
    // We just check the method works and returns a bool.
    // On machines with claude installed it returns true, otherwise false.
    // Just verify it returns without panicking.
    let _available = backend.is_available();
}

// ===========================================================================
// Test 2: ClaudeBackend unavailable returns BackendUnavailable error
// ===========================================================================

#[test]
fn test_claude_backend_unavailable_returns_typed_error() {
    let backend = ClaudeBackend::new("sonnet");
    if !backend.is_available() {
        let result = backend.propose_annotations("fn foo() {}", &[]);
        assert!(result.is_err());
        let err = result.unwrap_err();
        match &err {
            OracleError::BackendUnavailable { backend, reason } => {
                assert_eq!(backend, "claude");
                assert!(
                    reason.contains("not found"),
                    "reason should mention 'not found': got '{}'",
                    reason
                );
            }
            other => panic!("expected BackendUnavailable, got: {:?}", other),
        }
    }
}

// ===========================================================================
// Test 3: CodexBackend is_available checks CLI presence
// ===========================================================================

#[test]
fn test_codex_backend_is_available() {
    let backend = CodexBackend::new("o4-mini");
    // Just verify it returns without panicking.
    let _available = backend.is_available();
}

// ===========================================================================
// Test 4: Live Claude end-to-end test (guarded by env var)
// ===========================================================================

#[test]
fn test_live_claude_abs_function() {
    if !is_live_llm_enabled() {
        eprintln!("[skip] TRUST_VC_LIVE_LLM=1 not set, skipping live Claude test");
        return;
    }

    let backend = ClaudeBackend::new("sonnet").with_timeout(Duration::from_secs(120));
    if !backend.is_available() {
        eprintln!("[skip] claude CLI not available, skipping live test");
        return;
    }

    let func = abs_signature();
    let config = OracleConfig {
        max_iterations: 3,
        verbose: true,
    };

    let result = run_oracle(&func, &backend, &config).unwrap();

    eprintln!(
        "[live] Oracle result: verified={}, iterations={}",
        result.is_verified(),
        result.iterations
    );
    for (i, (ann, fb)) in result.history.iter().enumerate() {
        eprintln!(
            "[live]   Iteration {}: requires={:?}, ensures={:?}",
            i + 1,
            ann.requires,
            ann.ensures
        );
        eprintln!(
            "[live]   Feedback: {}",
            fb.to_llm_summary().lines().next().unwrap_or("")
        );
    }

    // We don't assert verified since LLM output is non-deterministic,
    // but we assert the pipeline ran without crashing.
    assert!(
        result.iterations >= 1,
        "should complete at least one iteration"
    );
    assert!(
        !result.history.is_empty(),
        "history should not be empty after at least one iteration"
    );
}

// ===========================================================================
// Test 5: Prompt construction — system prompt contains required sections
// ===========================================================================

#[test]
fn test_system_prompt_contains_required_sections() {
    // The system prompt must teach the LLM trust_vc syntax
    assert!(
        SYSTEM_PROMPT.contains("requires!"),
        "system prompt should mention requires! syntax"
    );
    assert!(
        SYSTEM_PROMPT.contains("ensures!"),
        "system prompt should mention ensures! syntax"
    );
    assert!(
        SYSTEM_PROMPT.contains("REQUIRES:"),
        "system prompt should show REQUIRES: format"
    );
    assert!(
        SYSTEM_PROMPT.contains("ENSURES:"),
        "system prompt should show ENSURES: format"
    );
    assert!(
        SYSTEM_PROMPT.contains("INVARIANT:"),
        "system prompt should show INVARIANT: format"
    );
    assert!(
        SYSTEM_PROMPT.contains("DECREASES:"),
        "system prompt should show DECREASES: format"
    );
    assert!(
        SYSTEM_PROMPT.contains("result"),
        "system prompt should mention 'result' variable"
    );
    assert!(
        SYSTEM_PROMPT.contains("## Examples"),
        "system prompt should include examples section"
    );
}

// ===========================================================================
// Test 6: Prompt construction — user prompt without history
// ===========================================================================

#[test]
fn test_user_prompt_without_history() {
    let source = "fn abs(x: i32) -> u32 { if x < 0 { (-x) as u32 } else { x as u32 } }";
    let prompt = build_user_prompt(source, &[]);

    assert!(
        prompt.contains("fn abs"),
        "user prompt should contain the function source"
    );
    assert!(
        prompt.contains("```rust"),
        "user prompt should wrap source in a rust code block"
    );
    assert!(
        !prompt.contains("Previous attempts"),
        "user prompt without history should not mention previous attempts"
    );
    assert!(
        !prompt.contains("Attempt 1"),
        "user prompt without history should not reference any attempt"
    );
}

// ===========================================================================
// Test 7: Prompt construction — user prompt with feedback history
// ===========================================================================

#[test]
fn test_user_prompt_with_feedback_history() {
    let source = "fn abs(x: i32) -> u32 { if x < 0 { (-x) as u32 } else { x as u32 } }";

    let history = vec![(
        ProposedAnnotations {
            requires: vec!["x >= 0".to_string()],
            ensures: vec!["result >= 0".to_string()],
            invariants: vec![],
            decreases: vec![],
            raw_response: String::new(),
        },
        ProofFeedback::Failed {
            counterexamples: vec![CounterexampleField {
                name: "x".to_string(),
                ty: "i32".to_string(),
                value: "-5".to_string(),
            }],
            localization: FailureLocalization {
                full_assertion: None,
                sub_results: vec![],
            },
            obligation_name: "ensures_result_ge_0".to_string(),
            solver_mode: "default".to_string(),
            elapsed: Duration::from_millis(10),
        },
    )];

    let prompt = build_user_prompt(source, &history);

    assert!(
        prompt.contains("Previous attempts"),
        "prompt with history should mention previous attempts"
    );
    assert!(
        prompt.contains("Attempt 1"),
        "prompt with history should reference Attempt 1"
    );
    assert!(
        prompt.contains("requires!(x >= 0)"),
        "prompt should show what was proposed"
    );
    assert!(
        prompt.contains("FAILED"),
        "prompt should include feedback summary containing FAILED"
    );
    assert!(
        prompt.contains("Counterexample") || prompt.contains("counterexample"),
        "prompt should mention counterexample feedback"
    );
    assert!(
        prompt.contains("weaken the postcondition")
            || prompt.contains("strengthen the precondition"),
        "prompt should include guidance about fixing the spec"
    );
}

// ===========================================================================
// Test 8: Annotation parser — clean structured format
// ===========================================================================

#[test]
fn test_parse_annotations_clean_structured() {
    let response =
        "REQUIRES: x > 0\nREQUIRES: y != 0\nENSURES: result >= 1\nENSURES: result <= x * y";
    let ann = parse_annotations(response);

    assert_eq!(ann.requires, vec!["x > 0", "y != 0"]);
    assert_eq!(ann.ensures, vec!["result >= 1", "result <= x * y"]);
    assert!(ann.invariants.is_empty());
    assert!(ann.decreases.is_empty());
}

// ===========================================================================
// Test 9: Annotation parser — messy markdown with code fences
// ===========================================================================

#[test]
fn test_parse_annotations_messy_markdown_code_fences() {
    let response = "Here are the formal specifications for this function:\n\n```\nREQUIRES: x != i32::MIN\nENSURES: result >= 0\nENSURES: result == x || result == -x\n```\n\nThese specifications capture the behavior of abs().\n";
    let ann = parse_annotations(response);

    assert_eq!(ann.requires, vec!["x != i32::MIN"]);
    assert_eq!(
        ann.ensures,
        vec!["result >= 0", "result == x || result == -x"]
    );
}

// ===========================================================================
// Test 10: Annotation parser — macro format with semicolons
// ===========================================================================

#[test]
fn test_parse_annotations_macro_format_with_semicolons_and_noise() {
    let response = "Looking at this function, I propose:\n\nrequires!(x > 0);\nensures!(result >= 0);\nensures!(result <= x);\n\nThis should work because the function preserves nonnegativity.\n";
    let ann = parse_annotations(response);

    assert_eq!(ann.requires, vec!["x > 0"]);
    assert_eq!(ann.ensures, vec!["result >= 0", "result <= x"]);
}

// ===========================================================================
// Test 11: Annotation parser — mixed format (structured takes priority)
// ===========================================================================

#[test]
fn test_parse_annotations_structured_takes_priority_over_macro() {
    // When both REQUIRES: and requires!() are present, structured wins
    let response = "REQUIRES: x > 0\nENSURES: result >= 0\nrequires!(y > 0)\nensures!(y >= 0)";
    let ann = parse_annotations(response);

    // Structured format was found, so macro format is ignored
    assert_eq!(ann.requires, vec!["x > 0"]);
    assert_eq!(ann.ensures, vec!["result >= 0"]);
}

// ===========================================================================
// Test 12: Annotation parser — empty/noise response produces empty annotations
// ===========================================================================

#[test]
fn test_parse_annotations_empty_response() {
    let responses = [
        "",
        "I don't know what to propose.",
        "This function is too complex for me.",
        "Sorry, I cannot determine meaningful specifications.",
        "   \n\n   \n   ",
    ];

    for response in &responses {
        let ann = parse_annotations(response);
        assert!(
            ann.requires.is_empty(),
            "noise response '{}' should produce empty requires",
            response
        );
        assert!(
            ann.ensures.is_empty(),
            "noise response '{}' should produce empty ensures",
            response
        );
        assert!(
            ann.invariants.is_empty(),
            "noise response '{}' should produce empty invariants",
            response
        );
        assert!(
            ann.decreases.is_empty(),
            "noise response '{}' should produce empty decreases",
            response
        );
    }
}

// ===========================================================================
// Test 13: Annotation parser — INVARIANT with and without labels
// ===========================================================================

#[test]
fn test_parse_annotations_invariant_variants() {
    let response = "INVARIANT: main_loop: i < n\nINVARIANT: counter >= 0";
    let ann = parse_annotations(response);

    assert_eq!(ann.invariants.len(), 2);
    assert_eq!(ann.invariants[0].0, "main_loop");
    assert_eq!(ann.invariants[0].1, "i < n");
    assert_eq!(ann.invariants[1].0, "loop");
    assert_eq!(ann.invariants[1].1, "counter >= 0");
}

// ===========================================================================
// Test 14: Annotation parser — DECREASES clauses
// ===========================================================================

#[test]
fn test_parse_annotations_decreases() {
    let response = "REQUIRES: n >= 0\nDECREASES: n\nENSURES: result >= 1";
    let ann = parse_annotations(response);

    assert_eq!(ann.requires, vec!["n >= 0"]);
    assert_eq!(ann.decreases, vec!["n"]);
    assert_eq!(ann.ensures, vec!["result >= 1"]);
}

// ===========================================================================
// Test 15: "I don't know" response — oracle handles gracefully
// ===========================================================================

#[test]
fn test_oracle_handles_empty_llm_response() {
    let func = FunctionSignature::new(
        "mystery",
        vec![("x".to_string(), "i32".to_string())],
        Some("i32".to_string()),
        "fn mystery(x: i32) -> i32 { x * 2 + 1 }",
    );

    let backend = EmptyResponseBackend;
    let config = make_config(3);

    let result = run_oracle(&func, &backend, &config).unwrap();

    // Empty annotations (no ensures, no requires) — verifier behavior depends
    // on whether "no assertions" counts as verified or error.
    // The key assertion: the oracle does NOT panic or return Err.
    assert!(
        result.iterations >= 1,
        "should complete at least one iteration"
    );
    assert!(
        !result.history.is_empty(),
        "history should record at least one attempt"
    );
}

// ===========================================================================
// Test 16: Timeout handling — oracle propagates timeout error
// ===========================================================================

#[test]
fn test_oracle_timeout_propagation() {
    let func = abs_signature();
    let backend = TimeoutBackend;
    let config = make_config(3);

    let result = run_oracle(&func, &backend, &config);

    assert!(
        result.is_err(),
        "oracle should propagate backend timeout as error"
    );
    let err = result.unwrap_err();
    match &err {
        OracleError::BackendTimeout { seconds } => {
            assert_eq!(*seconds, 30, "timeout should be 30 seconds");
        }
        other => panic!("expected BackendTimeout, got: {:?}", other),
    }
}

// ===========================================================================
// Test 17: Messy markdown response — oracle extracts annotations
// ===========================================================================

#[test]
fn test_oracle_with_messy_markdown_response() {
    let func = FunctionSignature::new(
        "nonneg",
        vec![("x".to_string(), "u32".to_string())],
        Some("u32".to_string()),
        "fn nonneg(x: u32) -> u32 { x }",
    );

    let backend = MessyMarkdownBackend {
        responses: vec![
            "Sure! Here are the specifications:\n\n```\nENSURES: x >= 0\n```\n\nThis postcondition is trivially true because x is of type u32.\n"
            .to_string(),
        ],
    };
    let config = make_config(3);

    let result = run_oracle(&func, &backend, &config).unwrap();

    assert!(
        result.is_verified(),
        "should verify u32 >= 0 even when extracted from messy markdown: {:?}",
        result.final_feedback
    );
    assert_eq!(result.iterations, 1);
}

// ===========================================================================
// Test 18: Annotation parser — raw_response is preserved
// ===========================================================================

#[test]
fn test_parse_annotations_preserves_raw_response() {
    let response = "ENSURES: result >= 0\nSome extra text here.";
    let ann = parse_annotations(response);

    assert_eq!(
        ann.raw_response, response,
        "raw_response should be the original input"
    );
    assert_eq!(ann.ensures, vec!["result >= 0"]);
}

// ===========================================================================
// Test 19: Backend name methods return expected values
// ===========================================================================

#[test]
fn test_backend_name_methods() {
    let claude = ClaudeBackend::new("sonnet");
    assert_eq!(claude.name(), "claude");

    let codex = CodexBackend::new("o4-mini");
    assert_eq!(codex.name(), "codex");

    let mock = MockBackend::new(vec![]);
    assert_eq!(mock.name(), "mock");
}

// ===========================================================================
// Test 20: ClaudeBackend builder timeout configuration
// ===========================================================================

#[test]
fn test_claude_backend_timeout_configuration() {
    let backend = ClaudeBackend::new("opus").with_timeout(Duration::from_secs(120));
    assert_eq!(backend.name(), "claude");
    // We cannot directly inspect the timeout field since it's private,
    // but we can verify the builder chain returns the right type.
}

// ===========================================================================
// Test 21: Prompt construction — full prompt combines system + user
// ===========================================================================

#[test]
fn test_full_prompt_combines_system_and_user() {
    let source = "fn double(x: i32) -> i32 { x * 2 }";
    let user_prompt = build_user_prompt(source, &[]);
    let full_prompt = format!("{}\n\n{}", SYSTEM_PROMPT, user_prompt);

    // System prompt section
    assert!(
        full_prompt.contains("formal verification expert"),
        "full prompt should contain system prompt content"
    );
    // User prompt section
    assert!(
        full_prompt.contains("fn double"),
        "full prompt should contain user function source"
    );
    // Both combined
    assert!(
        full_prompt.len() > SYSTEM_PROMPT.len(),
        "full prompt should be longer than system prompt alone"
    );
}

// ===========================================================================
// Test 22: Multiple iteration feedback history grows correctly in prompt
// ===========================================================================

#[test]
fn test_prompt_feedback_history_grows_across_iterations() {
    let source = "fn inc(x: u32) -> u32 { x + 1 }";

    let history_1 = vec![(
        proposal(&[], &["x > 0"]),
        ProofFeedback::Failed {
            counterexamples: vec![CounterexampleField {
                name: "x".to_string(),
                ty: "u32".to_string(),
                value: "0".to_string(),
            }],
            localization: FailureLocalization {
                full_assertion: None,
                sub_results: vec![],
            },
            obligation_name: "test".to_string(),
            solver_mode: "default".to_string(),
            elapsed: Duration::from_millis(5),
        },
    )];

    let prompt_1 = build_user_prompt(source, &history_1);

    let mut history_2 = history_1.clone();
    history_2.push((
        proposal(&["x > 0"], &["result > 0"]),
        ProofFeedback::Unknown {
            reason: "timeout".to_string(),
            category: "Timeout".to_string(),
            is_retriable: true,
            suggestion: "simplify the spec".to_string(),
            elapsed: Duration::from_millis(30000),
        },
    ));

    let prompt_2 = build_user_prompt(source, &history_2);

    assert!(
        prompt_2.len() > prompt_1.len(),
        "prompt with 2 history entries should be longer than with 1"
    );
    assert!(
        prompt_2.contains("Attempt 1"),
        "second prompt should contain Attempt 1"
    );
    assert!(
        prompt_2.contains("Attempt 2"),
        "second prompt should contain Attempt 2"
    );
}

// ===========================================================================
// Test 23: Annotation parser — handles whitespace-only REQUIRES/ENSURES
// ===========================================================================

#[test]
fn test_parse_annotations_ignores_empty_clauses() {
    let response = "REQUIRES:   \nENSURES:  \nENSURES: result >= 0";
    let ann = parse_annotations(response);

    // Whitespace-only clauses should be skipped
    assert!(
        ann.requires.is_empty(),
        "whitespace-only REQUIRES should be skipped"
    );
    assert_eq!(
        ann.ensures,
        vec!["result >= 0"],
        "only non-empty ENSURES should be kept"
    );
}
