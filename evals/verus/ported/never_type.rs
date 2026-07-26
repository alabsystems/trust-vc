// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(dead_code)]

// Partial direct TrustVc port for selected executable never_type.rs behavior.
//
// This intentionally does not claim full upstream parity. It covers a reduced
// exec never-expression control-flow shape from `coercion_in_exec` with a
// direct `loop {}` let-else fallback, plus fail-closed guards for upstream
// match-arm coercion and the helper function returning `!`.

enum NeverTypeOption<V> {
    Some(V),
    None,
}

pub const NEVER_TYPE_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "never_expression_let_else_some_path_verified",
        "coercion_in_exec direct loop fallback, reduced to let-else control flow",
        "verified",
        1,
    ),
    (
        "never_expression_let_else_some_path_wrong_value_counterexample",
        "coercion_in_exec/stuff_fails direct loop fallback, reduced to let-else control flow",
        "counterexample",
        1,
    ),
    (
        "never_expression_match_some_arm_fails_closed",
        "coercion_in_exec/stuff direct match loop fallback",
        "error",
        0,
    ),
    (
        "never_expression_match_some_arm_wrong_value_fails_closed",
        "coercion_in_exec/stuff_fails direct match loop fallback",
        "error",
        0,
    ),
    (
        "never_returning_helper_match_arm_fails_closed",
        "coercion_in_exec/never_returns helper arm",
        "error",
        0,
    ),
    (
        "never_expression_let_else_value_assert_verified",
        "coercion_in_exec value binding after direct loop fallback",
        "error",
        0,
    ),
    (
        "never_expression_let_else_wrong_value_counterexample",
        "coercion_in_exec/stuff_fails value binding after direct loop fallback",
        "error",
        0,
    ),
    (
        "never_expression_custom_option_match_helper_fails_closed",
        "coercion_in_exec upstream-shaped custom Option helper arm",
        "error",
        0,
    ),
    (
        "never_value_in_assert_spec_context_fails_closed",
        "test_coercion_not_allowed_in_spec/spec never caught as assertion expression",
        "error",
        0,
    ),
    (
        "never_value_in_ensures_spec_context_fails_closed",
        "test_spec_never_caught3/spec never caught as postcondition expression",
        "error",
        0,
    ),
];

pub fn never_type_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)]
{
    NEVER_TYPE_RS_EXPECTED_CASES
}

fn never_returns_loop() -> ! {
    loop {}
}

#[trust_vc::ensures(true)]
fn never_expression_let_else_some_path_verified() {
    let Some(_) = Some(17u64) else { loop {} };

    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn never_expression_let_else_value_assert_verified() {
    let Some(value) = Some(17u64) else { loop {} };

    trust_vc::assert!(value == 17u64);
}

#[trust_vc::ensures(true)]
fn never_expression_let_else_some_path_wrong_value_counterexample() {
    let Some(_) = Some(17u64) else { loop {} };

    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn never_expression_let_else_wrong_value_counterexample() {
    let Some(value) = Some(17u64) else { loop {} };

    trust_vc::assert!(value == 18u64);
}

#[trust_vc::ensures(result == 17u64)]
fn never_expression_match_some_arm_fails_closed() -> u64 {
    match Some(17u64) {
        Some(value) => value,
        None => loop {},
    }
}

#[trust_vc::ensures(true)]
fn never_expression_match_some_arm_wrong_value_fails_closed() {
    let value = match Some(17u64) {
        Some(value) => value,
        None => loop {},
    };

    trust_vc::assert!(value == 18u64);
}

#[trust_vc::ensures(result == 17u64)]
fn never_returning_helper_match_arm_fails_closed() -> u64 {
    match Some(17u64) {
        Some(value) => value,
        None => never_returns_loop(),
    }
}

#[trust_vc::ensures(result == 17u64)]
fn never_expression_custom_option_match_helper_fails_closed() -> u64 {
    match NeverTypeOption::Some(17u64) {
        NeverTypeOption::Some(value) => value,
        NeverTypeOption::None => never_returns_loop(),
    }
}

#[trust_vc::ensures(true)]
fn never_value_in_assert_spec_context_fails_closed() {
    trust_vc::assert!(never_returns_loop() == 0u64);
}

#[trust_vc::ensures(never_returns_loop() == 0u64)]
fn never_value_in_ensures_spec_context_fails_closed() {}
