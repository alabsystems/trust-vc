// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream Verus
// `rust_verify_test/tests/async_functions.rs`.
//
// This is scout coverage only. It pins the Rust-valid async function surface
// that current TrustVc extraction can observe as a result contract, plus a
// parameterized bool-contract surrogate for an external async specification
// and the unsupported `.await` lowering boundary. The upstream manifest entry
// remains an unsupported gap: async future semantics, awaited postconditions,
// borrowed futures, nested futures, external async specifications,
// mutable-reference awaits, and diagnostic parity are not accepted replacement
// evidence here.

#![allow(dead_code)]

pub type AsyncFunctionsRsExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type AsyncFunctionsRsFailClosedErrorPatterns = (&'static str, &'static [&'static str]);

pub const ASYNC_FUNCTIONS_RS_EXPECTED_CASES: &[AsyncFunctionsRsExpectedCase] = &[
    (
        "async_basic_result_verified",
        "test_basic_async_function_ensures_pass",
        "verified",
        1,
    ),
    (
        "async_basic_wrong_result_counterexample",
        "test_basic_async_function_ensures_fail",
        "counterexample",
        1,
    ),
    (
        "async_external_spec_bool_contract_surrogate_verified",
        "test_async_function_external_specification bool contract surrogate",
        "verified",
        1,
    ),
    (
        "async_external_spec_bool_contract_wrong_counterexample",
        "test_async_function_external_specification wrong bool body",
        "counterexample",
        1,
    ),
    (
        "async_await_boundary_currently_blocked",
        "test_basic_async_function_and_await",
        "error",
        0,
    ),
];

pub const ASYNC_FUNCTIONS_RS_FAIL_CLOSED_ERROR_PATTERNS: &[AsyncFunctionsRsFailClosedErrorPatterns] =
    &[("async_await_boundary_currently_blocked", &["await"])];

pub fn async_functions_rs_expected_cases() -> &'static [AsyncFunctionsRsExpectedCase] {
    ASYNC_FUNCTIONS_RS_EXPECTED_CASES
}

pub fn async_functions_rs_fail_closed_error_patterns(
) -> &'static [AsyncFunctionsRsFailClosedErrorPatterns] {
    ASYNC_FUNCTIONS_RS_FAIL_CLOSED_ERROR_PATTERNS
}

#[trust_vc::ensures(result == 1usize)]
async fn async_basic_result_verified() -> usize {
    1usize
}

#[trust_vc::ensures(result == 2usize)]
async fn async_basic_wrong_result_counterexample() -> usize {
    1usize
}

#[trust_vc::requires(x != 0u8)]
#[trust_vc::ensures(result == !b)]
async fn async_external_spec_bool_contract_surrogate_verified(b: bool, x: u8) -> bool {
    !b
}

#[trust_vc::requires(x != 0u8)]
#[trust_vc::ensures(result == !b)]
async fn async_external_spec_bool_contract_wrong_counterexample(b: bool, x: u8) -> bool {
    b
}

#[trust_vc::ensures(result == 1usize)]
async fn async_await_boundary_currently_blocked() -> usize {
    async_basic_result_verified().await
}
