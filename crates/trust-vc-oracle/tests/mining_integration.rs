// trust-vc-oracle — End-to-end mining integration tests
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Tests exercise the full oracle pipeline: source parsing -> template matching
// -> oracle loop (propose -> verify -> feedback -> refine) using MockBackend
// and inline Rust source strings. No external LLM service required.
//
// NOTE: `run_oracle` feeds `func.params` as declared ay variables and
// `ensures` as assertions. When using `parse_function_by_name`, the params
// are the actual function parameters (no implicit `result` variable).
// For ensures referencing `result`, build FunctionSignature manually with
// `result` in params (matching the existing integration.rs pattern).
//
// NOTE: `parse_functions` uses `quote::quote!(#ty).to_string()` which inserts
// spaces around angle brackets (e.g., `Vec < i32 >` not `Vec<i32>`). The
// template library normalizes this spacing now, but these tests still use
// hand-built signatures where that makes the expected shapes more explicit.

use trust_vc_oracle::{
    all_templates, applicable_templates, parse_function_by_name, parse_functions, run_oracle,
    FunctionSignature, MockBackend, OracleConfig, ProposedAnnotations,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn config(max_iterations: usize) -> OracleConfig {
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

/// Build a FunctionSignature manually with canonical type strings
/// (no spaces in generics) so templates match correctly.
fn sig(
    name: &str,
    params: &[(&str, &str)],
    return_type: Option<&str>,
    source: &str,
) -> FunctionSignature {
    FunctionSignature::new(
        name,
        params
            .iter()
            .map(|(n, t)| (n.to_string(), t.to_string()))
            .collect(),
        return_type.map(String::from),
        source,
    )
}

// ---------------------------------------------------------------------------
// 1. u32 functions get NonNegative template verified via oracle loop
// ---------------------------------------------------------------------------

#[test]
fn test_mining_u32_function_nonnegative_verified() {
    // Build sig manually with `result` in params so ensures!(result >= 0) verifies.
    let func = sig(
        "square",
        &[("x", "u32"), ("result", "u32")],
        Some("u32"),
        "fn square(x: u32) -> u32 { x * x }",
    );

    let backend = MockBackend::new(vec![proposal(&[], &["result >= 0"])]);
    let result = run_oracle(&func, &backend, &config(5)).unwrap();

    assert!(
        result.is_verified(),
        "u32 result >= 0 should verify: {:?}",
        result.final_feedback
    );
    assert_eq!(result.iterations, 1);

    let ann = result.annotations.unwrap();
    assert_eq!(ann.ensures, vec!["result >= 0"]);
}

// ---------------------------------------------------------------------------
// 2. Sort functions get Sorted/Permutation templates applicable
// ---------------------------------------------------------------------------

#[test]
fn test_mining_sort_function_templates_applicable() {
    // Use hand-built sig with canonical type strings for template matching.
    let func = sig(
        "sort",
        &[("v", "Vec<i32>")],
        Some("Vec<i32>"),
        "fn sort(v: Vec<i32>) -> Vec<i32> { todo!() }",
    );

    let templates = applicable_templates(&func);
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();

    assert!(
        names.contains(&"sorted"),
        "sort function should have sorted template, got: {:?}",
        names
    );
    assert!(
        names.contains(&"permutation"),
        "sort function should have permutation template, got: {:?}",
        names
    );
    assert!(
        names.contains(&"length_preserving"),
        "sort function should have length_preserving template, got: {:?}",
        names
    );
    assert!(
        names.contains(&"invariant"),
        "sort function should have invariant template, got: {:?}",
        names
    );
}

// ---------------------------------------------------------------------------
// 3. Binary ops get Commutativity/Associativity templates
// ---------------------------------------------------------------------------

#[test]
fn test_mining_binary_op_algebraic_templates() {
    let func = sig(
        "add",
        &[("a", "i32"), ("b", "i32")],
        Some("i32"),
        "fn add(a: i32, b: i32) -> i32 { a + b }",
    );

    let templates = applicable_templates(&func);
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();

    assert!(
        names.contains(&"commutativity"),
        "binary op should have commutativity template, got: {:?}",
        names
    );
    assert!(
        names.contains(&"associativity"),
        "binary op should have associativity template, got: {:?}",
        names
    );
    assert!(
        names.contains(&"distributivity"),
        "binary op should have distributivity template, got: {:?}",
        names
    );
    assert!(
        names.contains(&"monotonic"),
        "binary op should have monotonic template, got: {:?}",
        names
    );
}

// ---------------------------------------------------------------------------
// 4. Result-returning functions get ErrorFree template
// ---------------------------------------------------------------------------

#[test]
fn test_mining_result_function_error_free_template() {
    let func = sig(
        "try_parse",
        &[("s", "&str")],
        Some("Result<i32, String>"),
        "fn try_parse(s: &str) -> Result<i32, String> { todo!() }",
    );

    let templates = applicable_templates(&func);
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();

    assert!(
        names.contains(&"error_free"),
        "Result-returning function should have error_free template, got: {:?}",
        names
    );

    // Numeric templates should NOT apply (return type is Result, not numeric)
    assert!(
        !names.contains(&"range"),
        "Result fn should not have range template"
    );
    assert!(
        !names.contains(&"non_negative"),
        "Result fn should not have non_negative template"
    );
}

// ---------------------------------------------------------------------------
// 5. Mining with max_iterations=1 (single-shot, no refinement possible)
// ---------------------------------------------------------------------------

#[test]
fn test_mining_single_shot_no_refinement() {
    let source = "fn id(x: i32) -> i32 { x }";
    let func = parse_function_by_name(source, "id").expect("should parse id");

    // Propose something that will fail (i32 is not always > 0).
    // Uses param name `x` (not `result`) so it references a declared variable.
    let backend = MockBackend::new(vec![proposal(&[], &["x > 0"])]);
    let result = run_oracle(&func, &backend, &config(1)).unwrap();

    assert!(
        !result.is_verified(),
        "single-shot with wrong spec should not verify"
    );
    assert_eq!(result.iterations, 1);
    assert!(result.annotations.is_none());
    assert_eq!(result.history.len(), 1);
}

// ---------------------------------------------------------------------------
// 6. Mining with targeted function name from multi-function source
// ---------------------------------------------------------------------------

#[test]
fn test_mining_targeted_function_in_multi_function_source() {
    let source = r#"
        fn helper(x: u32) -> u32 { x + 1 }
        fn target(x: u32) -> u32 { x }
        fn other(x: i32) -> i32 { -x }
    "#;

    // Parse only the target function
    let func = parse_function_by_name(source, "target").expect("should find target");
    assert_eq!(func.name, "target");

    // Verify that parse_functions finds all three
    let all = parse_functions(source);
    assert_eq!(all.len(), 3);

    // Run oracle: ensures uses `x` (declared param), not `result`.
    // u32 x >= 0 is trivially true.
    let backend = MockBackend::new(vec![proposal(&[], &["x >= 0"])]);
    let result = run_oracle(&func, &backend, &config(3)).unwrap();

    assert!(
        result.is_verified(),
        "u32 x >= 0 should verify for target: {:?}",
        result.final_feedback
    );

    let ann = result.annotations.unwrap();
    assert_eq!(ann.ensures, vec!["x >= 0"]);
}

// ---------------------------------------------------------------------------
// 7. Mining on source with no functions
// ---------------------------------------------------------------------------

#[test]
fn test_mining_empty_source_no_functions() {
    let source = "";
    let functions = parse_functions(source);
    assert!(
        functions.is_empty(),
        "empty source should yield no functions"
    );
}

#[test]
fn test_mining_source_with_no_functions_only_types() {
    let source = r#"
        struct Point { x: f64, y: f64 }
        enum Color { Red, Green, Blue }
        type Alias = Vec<u32>;
    "#;
    let functions = parse_functions(source);
    assert!(
        functions.is_empty(),
        "source with only types should yield no functions"
    );
}

// ---------------------------------------------------------------------------
// 8. Mining produces deterministic results
// ---------------------------------------------------------------------------

#[test]
fn test_mining_deterministic_results() {
    // Use param-name ensures so ay can verify without manual `result` decl.
    let source = "fn double(x: u32) -> u32 { x * 2 }";
    let func = parse_function_by_name(source, "double").expect("should parse double");

    let backend1 = MockBackend::new(vec![proposal(&[], &["x >= 0"])]);
    let backend2 = MockBackend::new(vec![proposal(&[], &["x >= 0"])]);

    let result1 = run_oracle(&func, &backend1, &config(3)).unwrap();
    let result2 = run_oracle(&func, &backend2, &config(3)).unwrap();

    assert_eq!(
        result1.is_verified(),
        result2.is_verified(),
        "same input should produce same verification outcome"
    );
    assert_eq!(
        result1.iterations, result2.iterations,
        "same input should use same number of iterations"
    );
    assert_eq!(
        result1.history.len(),
        result2.history.len(),
        "same input should produce same history length"
    );
}

// ---------------------------------------------------------------------------
// 9. Full pipeline: parse -> match templates -> instantiate -> oracle verify
// ---------------------------------------------------------------------------

#[test]
fn test_full_pipeline_parse_match_verify() {
    // Step 1: Parse
    let source = "fn clamp(x: u32, lo: u32, hi: u32) -> u32 { if x < lo { lo } else if x > hi { hi } else { x } }";
    let parsed = parse_function_by_name(source, "clamp").expect("should parse clamp");
    assert_eq!(parsed.params.len(), 3);

    // Step 2: Match templates using hand-built sig (canonical types)
    let func_for_templates = sig(
        "clamp",
        &[("x", "u32"), ("lo", "u32"), ("hi", "u32")],
        Some("u32"),
        source,
    );
    let templates = applicable_templates(&func_for_templates);
    assert!(
        !templates.is_empty(),
        "clamp should have applicable templates"
    );
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();
    assert!(
        names.contains(&"range"),
        "clamp should match range template"
    );
    assert!(
        names.contains(&"non_negative"),
        "clamp should match non_negative template"
    );
    assert!(
        names.contains(&"bounded_by_input"),
        "clamp should match bounded_by_input template"
    );

    // Step 3: Instantiate the first applicable template
    let first_template = &templates[0];
    let proposals = first_template.instantiate(&func_for_templates);
    assert!(
        !proposals.is_empty(),
        "template should produce proposals for clamp"
    );

    // Step 4: Oracle loop with ensures referencing declared params only
    let backend = MockBackend::new(vec![proposal(&[], &["x >= 0"])]);
    let result = run_oracle(&parsed, &backend, &config(3)).unwrap();
    assert!(
        result.is_verified(),
        "u32 x >= 0 should verify for clamp: {:?}",
        result.final_feedback
    );
}

// ---------------------------------------------------------------------------
// 10. Refinement with precondition strengthening
// ---------------------------------------------------------------------------

#[test]
fn test_refinement_strengthens_precondition() {
    let source = "fn safe_sub(a: i32, b: i32) -> i32 { a - b }";
    let func = parse_function_by_name(source, "safe_sub").expect("should parse safe_sub");

    // First: postcondition too strong without precondition (a - b >= 0 not always true)
    // Second: add precondition that makes postcondition provable.
    // All references use declared param names `a`, `b` (not `result`).
    let backend = MockBackend::new(vec![
        proposal(&[], &["a - b >= 0"]),
        proposal(&["a >= b", "a >= 0", "b >= 0"], &["a - b >= 0"]),
    ]);

    let result = run_oracle(&func, &backend, &config(5)).unwrap();

    assert!(
        result.is_verified(),
        "a >= b && a >= 0 && b >= 0 => a - b >= 0 should verify: {:?}",
        result.final_feedback
    );
    assert_eq!(
        result.iterations, 2,
        "should take 2 iterations (fail then pass)"
    );
    assert_eq!(result.history.len(), 2);

    // First attempt should have failed
    let first = &result.history[0].1;
    assert!(
        first.is_failed() || first.is_unknown(),
        "first attempt without precondition should fail"
    );

    // Winning annotations should have preconditions
    let ann = result.annotations.unwrap();
    assert!(
        !ann.requires.is_empty(),
        "winning annotations should have preconditions"
    );
    assert!(ann.requires.iter().any(|r| r.contains("a >= b")));
}

// ---------------------------------------------------------------------------
// 11. Parsing impl blocks extracts methods
// ---------------------------------------------------------------------------

#[test]
fn test_mining_impl_block_methods() {
    let source = r#"
        struct Counter { val: u32 }
        impl Counter {
            fn new() -> Counter { Counter { val: 0 } }
            fn get(&self) -> u32 { self.val }
            fn increment(&mut self) { self.val += 1; }
        }
    "#;

    let functions = parse_functions(source);
    let names: Vec<&str> = functions.iter().map(|f| f.name.as_str()).collect();

    assert!(names.contains(&"new"), "should parse new from impl block");
    assert!(names.contains(&"get"), "should parse get from impl block");
    assert!(
        names.contains(&"increment"),
        "should parse increment from impl block"
    );
    assert_eq!(functions.len(), 3);
}

// ---------------------------------------------------------------------------
// 12. Parsing trait methods
// ---------------------------------------------------------------------------

#[test]
fn test_mining_trait_methods() {
    let source = r#"
        trait Bounded {
            fn lower(&self) -> i32;
            fn upper(&self) -> i32;
            fn contains(&self, x: i32) -> bool { x >= self.lower() && x <= self.upper() }
        }
    "#;

    let functions = parse_functions(source);
    let names: Vec<&str> = functions.iter().map(|f| f.name.as_str()).collect();

    assert!(names.contains(&"lower"), "should parse lower from trait");
    assert!(names.contains(&"upper"), "should parse upper from trait");
    assert!(
        names.contains(&"contains"),
        "should parse default method from trait"
    );
}

// ---------------------------------------------------------------------------
// 13. Oracle with multiple ensures clauses, all must verify
// ---------------------------------------------------------------------------

#[test]
fn test_oracle_multiple_ensures_all_verified() {
    // Build sig with `result` in params so ensures!(result >= 0) has a declared variable.
    let func = sig(
        "id",
        &[("x", "u32"), ("result", "u32")],
        Some("u32"),
        "fn id(x: u32) -> u32 { x }",
    );

    // Both postconditions are trivially true for u32
    let backend = MockBackend::new(vec![proposal(&[], &["result >= 0", "x >= 0"])]);
    let result = run_oracle(&func, &backend, &config(3)).unwrap();

    assert!(
        result.is_verified(),
        "both u32 ensures should verify: {:?}",
        result.final_feedback
    );
    let ann = result.annotations.unwrap();
    assert_eq!(ann.ensures.len(), 2, "should preserve both ensures clauses");
}

// ---------------------------------------------------------------------------
// 14. Backend exhaustion returns graceful error
// ---------------------------------------------------------------------------

#[test]
fn test_oracle_backend_exhaustion() {
    let source = "fn f(x: i32) -> i32 { x }";
    let func = parse_function_by_name(source, "f").expect("should parse f");

    // Backend only has 1 proposal but oracle wants 3 iterations.
    // First iteration fails (i32 x > 100 is false), then backend exhausts.
    let backend = MockBackend::new(vec![proposal(&[], &["x > 100"])]);
    let result = run_oracle(&func, &backend, &config(3));

    match result {
        Ok(r) => {
            assert!(!r.is_verified(), "wrong spec should not verify");
        }
        Err(e) => {
            let msg = format!("{}", e);
            assert!(
                msg.contains("exhausted"),
                "error should mention exhaustion: {}",
                msg
            );
        }
    }
}

// ---------------------------------------------------------------------------
// 15. Template applicability for identity function (single param, same in/out type)
// ---------------------------------------------------------------------------

#[test]
fn test_template_applicability_identity_function() {
    // Hand-built sig for correct template matching
    let func = sig(
        "passthrough",
        &[("val", "i64")],
        Some("i64"),
        "fn passthrough(val: i64) -> i64 { val }",
    );

    let templates = applicable_templates(&func);
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();

    assert!(
        names.contains(&"identity"),
        "should match identity template"
    );
    assert!(
        names.contains(&"idempotent"),
        "should match idempotent template"
    );
    assert!(
        names.contains(&"preserves_property"),
        "should match preserves_property template"
    );
    assert!(
        names.contains(&"injective"),
        "should match injective template"
    );
    assert!(
        names.contains(&"bounded_by_input"),
        "should match bounded_by_input template"
    );
    assert!(
        names.contains(&"non_negative"),
        "should match non_negative template"
    );
    assert!(names.contains(&"range"), "should match range template");
}

// ---------------------------------------------------------------------------
// 16. Verified feedback contains timing information
// ---------------------------------------------------------------------------

#[test]
fn test_verified_feedback_has_timing() {
    let source = "fn trivial(x: u32) -> u32 { x }";
    let func = parse_function_by_name(source, "trivial").expect("should parse trivial");

    // Uses param name `x` (not `result`) — x is declared as u32
    let backend = MockBackend::new(vec![proposal(&[], &["x >= 0"])]);
    let result = run_oracle(&func, &backend, &config(1)).unwrap();

    assert!(result.is_verified());

    match &result.final_feedback {
        trust_vc_oracle::ProofFeedback::Verified { elapsed, .. } => {
            assert!(
                elapsed.as_nanos() > 0,
                "elapsed time should be non-zero for real verification"
            );
        }
        other => panic!("expected Verified, got: {:?}", other),
    }
}

// ---------------------------------------------------------------------------
// 17. Failed feedback contains counterexample information
// ---------------------------------------------------------------------------

#[test]
fn test_failed_feedback_has_counterexample() {
    let source = "fn f(x: i32) -> i32 { x }";
    let func = parse_function_by_name(source, "f").expect("should parse f");

    // i32 is not always > 0
    let backend = MockBackend::new(vec![proposal(&[], &["x > 0"])]);
    let result = run_oracle(&func, &backend, &config(1)).unwrap();

    assert!(!result.is_verified());

    let feedback = &result.history[0].1;
    match feedback {
        trust_vc_oracle::ProofFeedback::Failed {
            counterexamples,
            obligation_name,
            ..
        } => {
            assert!(
                !counterexamples.is_empty(),
                "failed feedback should have counterexamples"
            );
            assert!(
                !obligation_name.is_empty(),
                "failed feedback should have obligation name"
            );
        }
        trust_vc_oracle::ProofFeedback::Unknown { reason, .. } => {
            // Unknown is also acceptable (solver timeout, etc.)
            assert!(!reason.is_empty(), "unknown feedback should have a reason");
        }
        other => panic!("expected Failed or Unknown for i32 x > 0, got: {:?}", other),
    }
}

// ---------------------------------------------------------------------------
// 18. parse_function_by_name returns None for nonexistent
// ---------------------------------------------------------------------------

#[test]
fn test_parse_function_by_name_nonexistent() {
    let source = "fn exists() -> bool { true }";
    let result = parse_function_by_name(source, "does_not_exist");
    assert!(result.is_none(), "nonexistent function should return None");
}

// ---------------------------------------------------------------------------
// 19. All 32 templates are registered
// ---------------------------------------------------------------------------

#[test]
fn test_all_templates_count_thirty_two() {
    let templates = all_templates();
    assert_eq!(
        templates.len(),
        32,
        "all_templates() should return exactly 32 templates, got {}",
        templates.len()
    );
}

// ---------------------------------------------------------------------------
// 20. Parsing handles complex signatures (generics, lifetimes, Result types)
// ---------------------------------------------------------------------------

#[test]
fn test_parsing_complex_signatures() {
    let source = r#"
        fn map_or<T, U>(opt: Option<T>, default: U, f: fn(T) -> U) -> U { match opt { Some(v) => f(v), None => default } }
        fn longest<'a>(x: &'a str, y: &'a str) -> &'a str { if x.len() > y.len() { x } else { y } }
        fn try_convert(input: &str) -> Result<Vec<u8>, String> { Ok(input.as_bytes().to_vec()) }
    "#;

    let functions = parse_functions(source);
    assert_eq!(functions.len(), 3, "should parse all 3 functions");

    let map_or = &functions[0];
    assert_eq!(map_or.name, "map_or");
    assert_eq!(map_or.params.len(), 3);

    let longest = &functions[1];
    assert_eq!(longest.name, "longest");
    assert_eq!(longest.params.len(), 2);
    assert!(
        longest.params[0].1.contains("'a"),
        "should preserve lifetime"
    );

    let try_convert = &functions[2];
    assert_eq!(try_convert.name, "try_convert");
    let ret = try_convert
        .return_type
        .as_deref()
        .expect("should have return type");
    assert!(ret.contains("Result"), "should have Result return type");
}

// ---------------------------------------------------------------------------
// 21. Oracle loop handles verbose mode without crashing
// ---------------------------------------------------------------------------

#[test]
fn test_oracle_verbose_mode_does_not_crash() {
    let source = "fn f(x: u32) -> u32 { x }";
    let func = parse_function_by_name(source, "f").expect("should parse f");

    let backend = MockBackend::new(vec![proposal(&[], &["x >= 0"])]);
    let verbose_config = OracleConfig {
        max_iterations: 3,
        verbose: true,
    };

    let result = run_oracle(&func, &backend, &verbose_config).unwrap();
    assert!(result.is_verified());
}

// ---------------------------------------------------------------------------
// 22. Oracle history records all attempts in order
// ---------------------------------------------------------------------------

#[test]
fn test_oracle_history_records_attempts_in_order() {
    let source = "fn f(x: i32) -> i32 { x }";
    let func = parse_function_by_name(source, "f").expect("should parse f");

    let backend = MockBackend::new(vec![
        proposal(&[], &["x > 100"]),       // will fail
        proposal(&[], &["x > 50"]),        // will fail
        proposal(&["x > 0"], &["x >= 1"]), // will pass
    ]);

    let result = run_oracle(&func, &backend, &config(5)).unwrap();

    assert!(result.is_verified());
    assert_eq!(result.history.len(), 3);

    // First two should have failed
    assert!(
        result.history[0].1.is_failed() || result.history[0].1.is_unknown(),
        "first attempt should fail"
    );
    assert!(
        result.history[1].1.is_failed() || result.history[1].1.is_unknown(),
        "second attempt should fail"
    );
    // Third should have verified
    assert!(
        result.history[2].1.is_verified(),
        "third attempt should verify"
    );

    // Proposals should be in order
    assert_eq!(result.history[0].0.ensures, vec!["x > 100"]);
    assert_eq!(result.history[1].0.ensures, vec!["x > 50"]);
    assert_eq!(result.history[2].0.ensures, vec!["x >= 1"]);
}

// ---------------------------------------------------------------------------
// 23. Parsed types preserve structure even with spaces from quote
// ---------------------------------------------------------------------------

#[test]
fn test_parsed_types_contain_expected_tokens() {
    let source = r#"
        fn sort(v: Vec<i32>) -> Vec<i32> { todo!() }
        fn parse_it(s: &str) -> Result<i32, String> { todo!() }
    "#;

    let functions = parse_functions(source);
    assert_eq!(functions.len(), 2);

    // quote inserts spaces, so Vec<i32> becomes something like "Vec < i32 >"
    let sort_fn = &functions[0];
    assert!(
        sort_fn.params[0].1.contains("Vec"),
        "param type should contain Vec"
    );
    assert!(
        sort_fn.params[0].1.contains("i32"),
        "param type should contain i32"
    );
    let sort_ret = sort_fn.return_type.as_deref().unwrap();
    assert!(sort_ret.contains("Vec"), "return type should contain Vec");

    let parse_fn = &functions[1];
    let parse_ret = parse_fn.return_type.as_deref().unwrap();
    assert!(
        parse_ret.contains("Result"),
        "return type should contain Result"
    );
    assert!(
        parse_ret.contains("String"),
        "return type should contain String"
    );
}
