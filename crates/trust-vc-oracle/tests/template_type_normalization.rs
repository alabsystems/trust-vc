// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_vc_oracle::{applicable_templates, parse_function_by_name};

#[test]
fn test_templates_match_parsed_collection_signature_with_spaced_generics() {
    let source = "fn sort(v: Vec<i32>) -> Vec<i32> { v }";
    let function = parse_function_by_name(source, "sort").expect("should parse function");

    let templates = applicable_templates(&function);
    let names: Vec<&str> = templates.iter().map(|template| template.name()).collect();

    assert!(names.contains(&"sorted"), "expected sorted, got {names:?}");
    assert!(
        names.contains(&"permutation"),
        "expected permutation, got {names:?}"
    );
    assert!(
        names.contains(&"length_preserving"),
        "expected length_preserving, got {names:?}"
    );
}

#[test]
fn test_templates_match_parsed_result_and_option_signatures_with_spaced_generics() {
    let result_source =
        "fn safe_div(a: i32, b: i32) -> Result<i32, String> { if b == 0 { Err(String::new()) } else { Ok(a / b) } }";
    let result_function =
        parse_function_by_name(result_source, "safe_div").expect("should parse result fn");
    let result_templates = applicable_templates(&result_function);
    let result_names: Vec<&str> = result_templates
        .iter()
        .map(|template| template.name())
        .collect();
    assert!(
        result_names.contains(&"error_free"),
        "expected error_free, got {result_names:?}"
    );

    let option_source = "fn get(v: Vec<i32>, idx: usize) -> Option<i32> { v.get(idx).copied() }";
    let option_function =
        parse_function_by_name(option_source, "get").expect("should parse option fn");
    let option_templates = applicable_templates(&option_function);
    let option_names: Vec<&str> = option_templates
        .iter()
        .map(|template| template.name())
        .collect();
    assert!(
        option_names.contains(&"nullability_guard"),
        "expected nullability_guard, got {option_names:?}"
    );
}
