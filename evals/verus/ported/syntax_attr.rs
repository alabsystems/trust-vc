// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(dead_code)]

// First partial executable TrustVc scout for upstream
// `source/rust_verify_test/tests/syntax_attr.rs`.
//
// This is intentionally not a replacement port. It covers only the current
// Rust-valid TrustVc syntax surface for function contracts, return bindings,
// verifier options, and loop invariant clauses. Upstream Verus attribute
// forms such as `#[verus_spec(... with ...)]`, proof declarations, dual specs,
// trait-associated-item diagnostics, and Verus macro-attribute placement remain
// unsupported here while the manifest entry stays `unsupported-gap`.

pub const SYNTAX_ATTR_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "basic_while_invariant_attr_syntax",
        "verus_verify_basic_while",
        "verified",
        1,
    ),
    (
        "basic_loop_invariant_except_break_attr_syntax",
        "verus_verify_basic_loop",
        "verified",
        1,
    ),
    (
        "returned_bool_attr_syntax",
        "test_use_macro_attributes",
        "verified",
        1,
    ),
    (
        "verifier_option_and_grouped_contract_attr_syntax",
        "test_prover_attributes",
        "verified",
        1,
    ),
    (
        "grouped_contract_requires_ensures_returns_syntax",
        "test_use_macro_attributes",
        "verified",
        1,
    ),
    (
        "returned_bool_attr_counterexample",
        "test_failed_ensures_macro_attributes",
        "counterexample",
        1,
    ),
    (
        "with_clause_attr_boundary_currently_error",
        "test_with",
        "error",
        0,
    ),
];

pub fn syntax_attr_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    SYNTAX_ATTR_RS_EXPECTED_CASES
}

pub const SYNTAX_ATTR_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[(
    "with_clause_attr_boundary_currently_error",
    &["unknown contract clause `with` in #[contract]"],
)];

pub fn syntax_attr_rs_expected_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    SYNTAX_ATTR_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::ensures(true)]
fn basic_while_invariant_attr_syntax(mut i: u64) {
    while i < 10u64 {
        trust_vc::invariant!(true);
        i = i + 1u64;
    }

    trust_vc::assert!(i >= 10u64);
}

#[trust_vc::ensures(true)]
fn basic_loop_invariant_except_break_attr_syntax() {
    loop {
        trust_vc::invariant!(true);
        trust_vc::invariant_except_break!(true);
        trust_vc::loop_ensures!(true);
        break;
    }

    trust_vc::assert!(true);
}

#[trust_vc::returns(ret)]
#[trust_vc::ensures(ret)]
fn returned_bool_attr_syntax() -> bool {
    true
}

#[trust_vc::returns(ret)]
#[trust_vc::ensures(ret)]
fn returned_bool_attr_counterexample() -> bool {
    false
}

#[trust_vc::verifier(spinoff_prover)]
#[trust_vc::contract(returns(result), ensures(result))]
fn verifier_option_and_grouped_contract_attr_syntax() -> bool {
    true
}

#[trust_vc::contract(requires(x <= y), returns(result), ensures(result >= x))]
fn grouped_contract_requires_ensures_returns_syntax(x: u64, y: u64) -> u64 {
    y
}

#[trust_vc::contract(with(Ghost(token)), returns(result), ensures(result == x))]
fn with_clause_attr_boundary_currently_error(x: u64) -> u64 {
    x
}
