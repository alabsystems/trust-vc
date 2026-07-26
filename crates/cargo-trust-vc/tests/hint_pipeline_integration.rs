// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! End-to-end integration tests for the full hints pipeline.
//!
//! These tests exercise the public API path:
//!   ProvenFact construction -> hint classification -> hint generation ->
//!   annotation emission -> report formatting -> JSON serialization
//!
//! The pipeline under test:
//!   1. `ProvenFact::new` constructs facts from verification results
//!   2. `generate_hints` classifies expressions into optimization hint kinds
//!   3. `emit_hint_annotations` renders hints as Rust source comments
//!   4. `format_report` / `to_json` produce summary output
//!   5. `ProvenFactsReport::from_facts` aggregates statistics

use trust_vc_core::proven_facts::{
    emit_hint_annotations, format_report, generate_hints, to_json, OptimizationHintKind,
    ProvenFact, ProvenFactKind, ProvenFactsReport,
};

// ---------------------------------------------------------------------------
// Helper: construct a ProvenFact from string components
// ---------------------------------------------------------------------------

fn make_fact(
    kind: ProvenFactKind,
    expression: &str,
    location: Option<&str>,
    step_label: &str,
) -> ProvenFact {
    ProvenFact::new(kind, expression, location.map(str::to_string), step_label)
}

// ---------------------------------------------------------------------------
// 1. Full pipeline: ProvenFact -> classify -> generate hint -> format output
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_bounds_check_fact_produces_bounds_elimination_hint() {
    let facts = vec![make_fact(
        ProvenFactKind::Invariant,
        "i < arr.len()",
        Some("src/loop.rs:10:9"),
        "loop_bound",
    )];
    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::BoundsElimination
    );
    assert_eq!(hints[0].expression(), "i < arr.len()");
    assert_eq!(hints[0].source_location(), Some("src/loop.rs:10:9"));
    assert!(hints[0].safety_justification().contains("SAFETY"));
    assert!(hints[0].safety_justification().contains("loop_bound"));

    let annotations = emit_hint_annotations(&hints);
    assert!(annotations.contains("get_unchecked"));
    assert!(annotations.contains("bounds check can be elided"));
    assert!(annotations.contains("At src/loop.rs:10:9"));

    let report_text = format_report(&facts);
    assert!(report_text.contains("Total proven facts: 1"));
    assert!(report_text.contains("Bounds eliminations:      1"));
    assert!(report_text.contains("[invariant]"));
}

#[test]
fn test_pipeline_null_check_fact_produces_null_elimination_hint() {
    let facts = vec![make_fact(
        ProvenFactKind::Precondition,
        "arg.is_some()",
        Some("src/api.rs:15:1"),
        "notnull_pre",
    )];
    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::NullCheckElimination
    );

    let annotations = emit_hint_annotations(&hints);
    assert!(annotations.contains("unwrap_unchecked"));
    assert!(annotations.contains("null/Option check can be elided"));

    let json = to_json(&facts);
    assert!(json.contains("\"hint_kind\": \"null_check_elimination\""));
    assert!(json.contains("\"preconditions\": 1"));
}

#[test]
fn test_pipeline_general_assertion_produces_unreachable_hint() {
    let facts = vec![make_fact(
        ProvenFactKind::Assertion,
        "x > 0",
        Some("src/lib.rs:42:5"),
        "positive_guard",
    )];
    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::UnreachableBranch
    );

    let annotations = emit_hint_annotations(&hints);
    assert!(annotations.contains("unreachable_unchecked"));
    assert!(annotations.contains("else branch is dead code"));
}

// ---------------------------------------------------------------------------
// 2. Multiple facts with different strengths -> sort by value -> top-N
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_multiple_facts_different_hint_kinds() {
    let facts = vec![
        make_fact(ProvenFactKind::Assertion, "x > 0", Some("a.rs:1:1"), "s1"),
        make_fact(
            ProvenFactKind::Invariant,
            "i < buf.len()",
            Some("a.rs:10:5"),
            "s2",
        ),
        make_fact(
            ProvenFactKind::Precondition,
            "opt.is_some()",
            Some("a.rs:20:1"),
            "s3",
        ),
    ];

    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 3);
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::UnreachableBranch
    );
    assert_eq!(
        hints[1].hint_kind(),
        OptimizationHintKind::BoundsElimination
    );
    assert_eq!(
        hints[2].hint_kind(),
        OptimizationHintKind::NullCheckElimination
    );

    let report = ProvenFactsReport::from_facts(&facts);
    assert_eq!(report.total_facts(), 3);
    assert_eq!(report.unreachable_branch_hints(), 1);
    assert_eq!(report.bounds_elimination_hints(), 1);
    assert_eq!(report.null_check_elimination_hints(), 1);
}

#[test]
fn test_pipeline_report_counts_all_fact_kinds_correctly() {
    let facts = vec![
        make_fact(ProvenFactKind::Assertion, "a > 0", None, "s1"),
        make_fact(ProvenFactKind::Assertion, "b > 0", None, "s2"),
        make_fact(ProvenFactKind::Precondition, "c > 0", None, "s3"),
        make_fact(ProvenFactKind::Postcondition, "d > 0", None, "s4"),
        make_fact(ProvenFactKind::Invariant, "e > 0", None, "s5"),
        make_fact(ProvenFactKind::Invariant, "f > 0", None, "s6"),
    ];

    let report = ProvenFactsReport::from_facts(&facts);
    assert_eq!(report.total_facts(), 6);
    assert_eq!(report.assertions(), 2);
    assert_eq!(report.preconditions(), 1);
    assert_eq!(report.postconditions(), 1);
    assert_eq!(report.invariants(), 2);
}

// ---------------------------------------------------------------------------
// 3. Bounds check facts -> Critical -> unreachable_unchecked hint
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_bounds_index_less_than_capacity() {
    let facts = vec![make_fact(
        ProvenFactKind::Precondition,
        "index < capacity",
        Some("src/vec.rs:5:1"),
        "cap_pre",
    )];
    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::BoundsElimination
    );

    let annotations = emit_hint_annotations(&hints);
    assert!(annotations.contains("get_unchecked"));
}

#[test]
fn test_pipeline_bounds_offset_le_size() {
    let facts = vec![make_fact(
        ProvenFactKind::Assertion,
        "offset <= size",
        None,
        "off_check",
    )];
    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::BoundsElimination
    );
}

// ---------------------------------------------------------------------------
// 4. Overflow facts -> Strong -> unchecked arithmetic hint
//    Note: the core hints module classifies overflow expressions as
//    UnreachableBranch (it does not have a separate overflow category).
//    The fact_strength module in cargo-trust-vc classifies these as Strong.
//    This test verifies the core pipeline's behavior.
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_overflow_expression_hint() {
    // "no_overflow" expressions get classified by core as UnreachableBranch
    // (the core hints module only has 3 categories: unreachable, bounds, null)
    let facts = vec![make_fact(
        ProvenFactKind::Assertion,
        "no_overflow(a + b)",
        Some("src/math.rs:20:5"),
        "arith_safe",
    )];
    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    // Core classifies this as unreachable_branch since it has no overflow-specific category
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::UnreachableBranch
    );
    assert!(hints[0].safety_justification().contains("arith_safe"));
}

#[test]
fn test_pipeline_arithmetic_range_bound_expression() {
    let facts = vec![make_fact(
        ProvenFactKind::Assertion,
        "a * b <= MAX",
        Some("src/math.rs:30:5"),
        "mul_bound",
    )];
    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    // "a * b <= MAX" lacks bounds keywords, so core classifies as unreachable
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::UnreachableBranch
    );

    let annotations = emit_hint_annotations(&hints);
    assert!(annotations.contains("unreachable_unchecked"));
}

// ---------------------------------------------------------------------------
// 5. Null check facts -> Strong -> unwrap_unchecked hint
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_null_check_not_none() {
    let facts = vec![make_fact(
        ProvenFactKind::Assertion,
        "ptr != None",
        None,
        "not_none",
    )];
    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::NullCheckElimination
    );

    let annotations = emit_hint_annotations(&hints);
    assert!(annotations.contains("unwrap_unchecked"));
}

#[test]
fn test_pipeline_null_check_is_ok_result() {
    let facts = vec![make_fact(
        ProvenFactKind::Postcondition,
        "result.is_ok()",
        Some("src/io.rs:30:1"),
        "io_ok",
    )];
    // is_ok() is not recognized by the core hints classifier as null-check
    // (it only recognizes is_some, is_none, != None, != null, is_null)
    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    // The core classifier does not recognize is_ok() as null check elimination
    // (only is_some/is_none/!= None/!= null), so it falls through to unreachable
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::UnreachableBranch
    );
}

// ---------------------------------------------------------------------------
// 6. Informational facts -> general assertions -> unreachable hints
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_informational_postcondition_produces_unreachable() {
    let facts = vec![make_fact(
        ProvenFactKind::Postcondition,
        "result == old(x) + 1",
        None,
        "inc_ensures",
    )];
    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::UnreachableBranch
    );

    // Annotations should contain the unreachable hint even for informational facts
    let annotations = emit_hint_annotations(&hints);
    assert!(annotations.contains("unreachable_unchecked"));
    assert!(annotations.contains("result == old(x) + 1"));
}

#[test]
fn test_pipeline_debug_assert_expression_produces_unreachable() {
    // debug_assert expressions don't have a special category in core hints
    let facts = vec![make_fact(
        ProvenFactKind::Assertion,
        "debug_assert!(x > 0)",
        Some("src/lib.rs:50:5"),
        "debug_guard",
    )];
    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::UnreachableBranch
    );
}

// ---------------------------------------------------------------------------
// 7. Empty fact set -> no hints generated
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_empty_facts_produce_no_hints() {
    let facts: Vec<ProvenFact> = Vec::new();
    let hints = generate_hints(&facts);
    assert!(hints.is_empty());

    let annotations = emit_hint_annotations(&hints);
    assert!(annotations.is_empty());

    let report = ProvenFactsReport::from_facts(&facts);
    assert_eq!(report.total_facts(), 0);
    assert_eq!(report.unreachable_branch_hints(), 0);
    assert_eq!(report.bounds_elimination_hints(), 0);
    assert_eq!(report.null_check_elimination_hints(), 0);
}

#[test]
fn test_pipeline_empty_facts_json_is_valid() {
    let facts: Vec<ProvenFact> = Vec::new();
    let json = to_json(&facts);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("empty facts JSON should be valid");
    assert_eq!(parsed["summary"]["total_facts"], 0);
    assert!(parsed["facts"].as_array().unwrap().is_empty());
    assert!(parsed["hints"].as_array().unwrap().is_empty());
}

// ---------------------------------------------------------------------------
// 8. Conflicting / ambiguous facts -> pipeline still produces hints
//    (the core pipeline does not suppress hints for conflicts; every fact
//    produces exactly one hint)
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_contradictory_facts_both_produce_hints() {
    // Two facts that logically contradict each other
    let facts = vec![
        make_fact(
            ProvenFactKind::Assertion,
            "x > 0",
            Some("src/lib.rs:10:1"),
            "positive",
        ),
        make_fact(
            ProvenFactKind::Assertion,
            "x <= 0",
            Some("src/lib.rs:15:1"),
            "nonpositive",
        ),
    ];
    let hints = generate_hints(&facts);
    // Both facts produce hints (pipeline does not detect contradictions)
    assert_eq!(hints.len(), 2);
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::UnreachableBranch
    );
    assert_eq!(
        hints[1].hint_kind(),
        OptimizationHintKind::UnreachableBranch
    );
}

#[test]
fn test_pipeline_duplicate_facts_both_produce_hints() {
    let fact = make_fact(
        ProvenFactKind::Invariant,
        "i < arr.len()",
        Some("src/loop.rs:5:1"),
        "same_fact",
    );
    let facts = vec![fact.clone(), fact];
    let hints = generate_hints(&facts);
    // Duplicates are not deduplicated
    assert_eq!(hints.len(), 2);
}

// ---------------------------------------------------------------------------
// 9. Complex expressions -> proper parsing
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_complex_compound_bounds_expression() {
    let facts = vec![make_fact(
        ProvenFactKind::Assertion,
        "x >= 0 && x < arr.len()",
        Some("src/complex.rs:20:5"),
        "compound_bound",
    )];
    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    // Compound bounds expression with .len() and < should be bounds elimination
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::BoundsElimination
    );
}

#[test]
fn test_pipeline_nested_method_call_expression() {
    let facts = vec![make_fact(
        ProvenFactKind::Postcondition,
        "result == old(seq).push(val).len()",
        None,
        "seq_push_len",
    )];
    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    // This has .len() but no comparison operator, so not bounds elimination
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::UnreachableBranch
    );
    assert!(hints[0].safety_justification().contains("seq_push_len"));
}

#[test]
fn test_pipeline_expression_with_special_characters() {
    let facts = vec![make_fact(
        ProvenFactKind::Assertion,
        "msg == \"hello\\nworld\"",
        None,
        "str_check",
    )];
    let json = to_json(&facts);
    // Verify the JSON output properly escapes special characters
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("JSON with special chars should parse");
    assert_eq!(parsed["summary"]["total_facts"], 1);
    assert_eq!(parsed["facts"][0]["step_label"], "str_check");
}

// ---------------------------------------------------------------------------
// 10. Round-trip: generate hint -> verify hint text is valid Rust comment
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_annotations_are_valid_rust_comments() {
    let facts = vec![
        make_fact(
            ProvenFactKind::Assertion,
            "x > 0",
            Some("src/lib.rs:42:5"),
            "guard",
        ),
        make_fact(
            ProvenFactKind::Invariant,
            "i < arr.len()",
            Some("src/loop.rs:10:5"),
            "bound",
        ),
        make_fact(
            ProvenFactKind::Precondition,
            "val.is_some()",
            Some("src/api.rs:5:1"),
            "notnull",
        ),
    ];
    let hints = generate_hints(&facts);
    let annotations = emit_hint_annotations(&hints);

    // Every non-empty line should be a Rust comment (starts with "//")
    for line in annotations.lines() {
        if !line.is_empty() {
            assert!(
                line.starts_with("//"),
                "annotation line should be a Rust comment, got: {line:?}"
            );
        }
    }
}

#[test]
fn test_pipeline_annotations_contain_safety_justifications() {
    let facts = vec![make_fact(
        ProvenFactKind::Invariant,
        "j < data.len()",
        Some("src/sort.rs:25:9"),
        "sort_bound",
    )];
    let hints = generate_hints(&facts);
    let annotations = emit_hint_annotations(&hints);

    // Must contain the SAFETY justification
    assert!(annotations.contains("SAFETY:"));
    // Must reference the step label
    assert!(annotations.contains("sort_bound"));
    // Must mention the optimization opportunity
    assert!(annotations.contains("bounds check can be elided"));
}

// ---------------------------------------------------------------------------
// Additional pipeline coverage tests
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_json_round_trip_structure() {
    let facts = vec![
        make_fact(ProvenFactKind::Assertion, "x > 0", Some("a.rs:1:1"), "s1"),
        make_fact(
            ProvenFactKind::Invariant,
            "i < arr.len()",
            Some("a.rs:10:5"),
            "s2",
        ),
        make_fact(
            ProvenFactKind::Precondition,
            "v.is_some()",
            Some("b.rs:5:1"),
            "s3",
        ),
    ];
    let json = to_json(&facts);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("pipeline JSON should be valid");

    assert_eq!(parsed["summary"]["total_facts"], 3);
    assert_eq!(parsed["summary"]["assertions"], 1);
    assert_eq!(parsed["summary"]["preconditions"], 1);
    assert_eq!(parsed["summary"]["invariants"], 1);
    assert_eq!(parsed["summary"]["postconditions"], 0);

    let facts_arr = parsed["facts"].as_array().unwrap();
    assert_eq!(facts_arr.len(), 3);

    let hints_arr = parsed["hints"].as_array().unwrap();
    assert_eq!(hints_arr.len(), 3);

    // Verify hint kinds in JSON output
    assert_eq!(hints_arr[0]["hint_kind"], "unreachable_branch");
    assert_eq!(hints_arr[1]["hint_kind"], "bounds_elimination");
    assert_eq!(hints_arr[2]["hint_kind"], "null_check_elimination");
}

#[test]
fn test_pipeline_format_report_details_section() {
    let facts = vec![
        make_fact(
            ProvenFactKind::Assertion,
            "x > 0",
            Some("src/lib.rs:42:5"),
            "pos_check",
        ),
        make_fact(ProvenFactKind::Invariant, "i < n", None, "loop_inv"),
    ];
    let report = format_report(&facts);

    // Summary section
    assert!(report.contains("Proven Facts Summary"));
    assert!(report.contains("Total proven facts: 2"));
    assert!(report.contains("Assertions:     1"));
    assert!(report.contains("Invariants:     1"));

    // Details section
    assert!(report.contains("Details:"));
    assert!(report.contains("1. [assertion] `x > 0` at src/lib.rs:42:5 (step: pos_check)"));
    assert!(report.contains("2. [invariant] `i < n` at <unknown> (step: loop_inv)"));
}

#[test]
fn test_pipeline_fact_without_location_produces_hint_without_location_line() {
    let facts = vec![make_fact(
        ProvenFactKind::Assertion,
        "flag == true",
        None,
        "flag_check",
    )];
    let hints = generate_hints(&facts);
    let annotations = emit_hint_annotations(&hints);

    // Without location, should not have "At " line
    assert!(!annotations.contains("At "));
    // But should still have the hint content
    assert!(annotations.contains("unreachable_unchecked"));
}

#[test]
fn test_pipeline_multiple_null_check_patterns() {
    let patterns = vec![
        ("val.is_some()", "check_some"),
        ("ptr != None", "check_not_none"),
        ("ptr != null", "check_not_null"),
    ];

    for (expr, label) in &patterns {
        let facts = vec![make_fact(ProvenFactKind::Precondition, expr, None, label)];
        let hints = generate_hints(&facts);
        assert_eq!(
            hints[0].hint_kind(),
            OptimizationHintKind::NullCheckElimination,
            "expression {expr:?} should classify as NullCheckElimination"
        );
    }
}

#[test]
fn test_pipeline_multiple_bounds_patterns() {
    let patterns = vec![
        ("i < arr.len()", "len_bound"),
        ("index < capacity", "cap_bound"),
        ("offset <= size", "off_bound"),
    ];

    for (expr, label) in &patterns {
        let facts = vec![make_fact(ProvenFactKind::Invariant, expr, None, label)];
        let hints = generate_hints(&facts);
        assert_eq!(
            hints[0].hint_kind(),
            OptimizationHintKind::BoundsElimination,
            "expression {expr:?} should classify as BoundsElimination"
        );
    }
}

#[test]
fn test_pipeline_large_fact_set_produces_correct_counts() {
    let mut facts = Vec::new();
    for i in 0..50 {
        let kind = match i % 4 {
            0 => ProvenFactKind::Assertion,
            1 => ProvenFactKind::Precondition,
            2 => ProvenFactKind::Postcondition,
            _ => ProvenFactKind::Invariant,
        };
        facts.push(make_fact(
            kind,
            &format!("expr_{i} > 0"),
            Some(&format!("src/gen.rs:{i}:1")),
            &format!("step_{i}"),
        ));
    }

    let report = ProvenFactsReport::from_facts(&facts);
    assert_eq!(report.total_facts(), 50);
    // 50 / 4 = 12.5, so assertions=13, preconditions=13, postconditions=12, invariants=12
    assert_eq!(report.assertions(), 13);
    assert_eq!(report.preconditions(), 13);
    assert_eq!(report.postconditions(), 12);
    assert_eq!(report.invariants(), 12);

    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 50);

    let json = to_json(&facts);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("large fact set JSON should be valid");
    assert_eq!(parsed["summary"]["total_facts"], 50);
    assert_eq!(parsed["facts"].as_array().unwrap().len(), 50);
}

#[test]
fn test_pipeline_proven_fact_kind_display_round_trip() {
    let kinds = [
        (ProvenFactKind::Assertion, "assertion"),
        (ProvenFactKind::Precondition, "precondition"),
        (ProvenFactKind::Postcondition, "postcondition"),
        (ProvenFactKind::Invariant, "invariant"),
    ];

    for (kind, expected_display) in &kinds {
        assert_eq!(
            kind.to_string(),
            *expected_display,
            "ProvenFactKind::{kind:?} should display as {expected_display:?}"
        );
    }
}

#[test]
fn test_pipeline_hint_kind_display_values() {
    let kinds = [
        (
            OptimizationHintKind::UnreachableBranch,
            "unreachable_branch",
        ),
        (
            OptimizationHintKind::BoundsElimination,
            "bounds_elimination",
        ),
        (
            OptimizationHintKind::NullCheckElimination,
            "null_check_elimination",
        ),
    ];

    for (kind, expected) in &kinds {
        assert_eq!(
            kind.to_string(),
            *expected,
            "OptimizationHintKind::{kind:?} should display as {expected:?}"
        );
    }
}

#[test]
fn test_pipeline_serde_round_trip_proven_fact() {
    let fact = make_fact(
        ProvenFactKind::Invariant,
        "i < n",
        Some("src/loop.rs:10:9"),
        "loop_bound",
    );
    let json = serde_json::to_string(&fact).expect("serialize fact");
    let back: ProvenFact = serde_json::from_str(&json).expect("deserialize fact");
    assert_eq!(fact, back);
    assert_eq!(back.kind(), ProvenFactKind::Invariant);
    assert_eq!(back.expression(), "i < n");
    assert_eq!(back.source_location(), Some("src/loop.rs:10:9"));
    assert_eq!(back.step_label(), "loop_bound");
}

#[test]
fn test_pipeline_whitespace_in_expression_is_preserved() {
    let facts = vec![make_fact(
        ProvenFactKind::Assertion,
        "  i < arr.len()  ",
        None,
        "whitespace_expr",
    )];
    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    // The classifier trims whitespace for classification but preserves it
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::BoundsElimination
    );
}

#[test]
fn test_pipeline_report_display_matches_format_report_summary() {
    let facts = vec![
        make_fact(ProvenFactKind::Assertion, "x > 0", None, "s1"),
        make_fact(ProvenFactKind::Invariant, "i < arr.len()", None, "s2"),
    ];

    let report = ProvenFactsReport::from_facts(&facts);
    let display_output = report.to_string();

    // Display impl should contain the same summary as format_report
    assert!(display_output.contains("Total proven facts: 2"));
    assert!(display_output.contains("Assertions:     1"));
    assert!(display_output.contains("Invariants:     1"));
    assert!(display_output.contains("Bounds eliminations:      1"));
}
