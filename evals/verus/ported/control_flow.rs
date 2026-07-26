// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Partial direct TrustVc port for selected executable control_flow.rs cases.
//
// This is intentionally not a full replacement for upstream control_flow.rs.
// It covers narrow early-return path refinement, match-arm and tail
// short-circuit returns, local-initializer returns, and unsupported
// never-expression placements used to keep the manifest fail-closed.

pub type ControlFlowExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type ControlFlowFailClosedErrorPatterns = (&'static str, &'static [&'static str]);

pub const CONTROL_FLOW_RS_EXPECTED_CASES: &[ControlFlowExpectedCase] = &[
    (
        "control_flow_final_stmt_return_verified",
        "distinguish_returns_and_implict_units::test_final_stmt_return",
        "verified",
        2,
    ),
    (
        "control_flow_final_stmt_return_counterexample",
        "final_stmt_return_fail::test_final_stmt_return",
        "counterexample",
        2,
    ),
    (
        "control_flow_postcondition_fail_if_value_counterexample",
        "postconditions_fail_in_returns_in_conditional::postcondition_fail_if_value",
        "counterexample",
        2,
    ),
    (
        "control_flow_postcondition_fail_else_value_counterexample",
        "postconditions_fail_in_returns_in_conditional::postcondition_fail_else_value",
        "counterexample",
        2,
    ),
    (
        "control_flow_tail_if_return_verified",
        "distinguish_returns_and_implict_units::test_return_from_if",
        "verified",
        2,
    ),
    (
        "control_flow_tail_if_return_counterexample",
        "return_from_if_else_fail::test_return_from_if",
        "counterexample",
        2,
    ),
    (
        "control_flow_tail_else_return_verified",
        "distinguish_returns_and_implict_units::test_return_from_else",
        "verified",
        2,
    ),
    (
        "control_flow_short_circuit_return_verified",
        "distinguish_returns_and_implict_units::never_short_circuit_right",
        "verified",
        2,
    ),
    (
        "control_flow_short_circuit_return_counterexample",
        "short_circuit_returns_fail::never_short_circuit_right",
        "counterexample",
        2,
    ),
    (
        "control_flow_match_arm_return_verified",
        "distinguish_returns_and_implict_units::test_return_from_match",
        "verified",
        2,
    ),
    (
        "control_flow_match_arm_return_counterexample",
        "return_from_match_fail::test_return_from_match",
        "counterexample",
        2,
    ),
    (
        "control_flow_local_initializer_return_verified",
        "distinguish_returns_and_implict_units::test_add_u32_and_never",
        "verified",
        2,
    ),
    (
        "control_flow_requires_in_conditional_counterexample",
        "requires_in_conditional_pure::test",
        "counterexample",
        1,
    ),
    (
        "control_flow_never_expression_binop_error",
        "distinguish_returns_and_implict_units::never_binop_left",
        "error",
        0,
    ),
    (
        "control_flow_nested_return_in_return_value_error",
        "misc_never_returns_fail::never_in_return",
        "error",
        0,
    ),
    (
        "control_flow_multiple_top_level_returns_first_dominates_verified",
        "misc_never_returns_fail::return_return",
        "verified",
        2,
    ),
];

pub fn control_flow_rs_expected_cases() -> &'static [ControlFlowExpectedCase] {
    CONTROL_FLOW_RS_EXPECTED_CASES
}

pub const CONTROL_FLOW_RS_FAIL_CLOSED_ERROR_PATTERNS: &[ControlFlowFailClosedErrorPatterns] = &[
    (
        "control_flow_never_expression_binop_error",
        &["return", "never", "unsupported nested explicit return path"],
    ),
    (
        "control_flow_nested_return_in_return_value_error",
        &["nested explicit return in return value"],
    ),
];

pub fn control_flow_rs_fail_closed_error_patterns(
) -> &'static [ControlFlowFailClosedErrorPatterns] {
    CONTROL_FLOW_RS_FAIL_CLOSED_ERROR_PATTERNS
}

#[trust_vc::ensures(result == 5u8)]
fn control_flow_final_stmt_return_verified() -> u8 {
    return 5u8;
}

#[trust_vc::ensures(result == 6u8)]
fn control_flow_final_stmt_return_counterexample() -> u8 {
    return 5u8;
}

#[trust_vc::ensures(result == 4u8)]
fn control_flow_postcondition_fail_if_value_counterexample(b: bool) -> u8 {
    if b {
        return 7u8;
    }
    4u8
}

#[trust_vc::ensures(result == 4u8)]
fn control_flow_postcondition_fail_else_value_counterexample(b: bool) -> u8 {
    if b {
        4u8
    } else {
        return 7u8;
    }
}

#[trust_vc::ensures(result == 1u64 || result == 2u64)]
fn control_flow_tail_if_return_verified(flag: bool) -> u64 {
    if flag {
        return 1u64;
    } else {
        2u64
    }
}

#[trust_vc::ensures(result == 2u64)]
fn control_flow_tail_if_return_counterexample(flag: bool) -> u64 {
    if flag {
        return 1u64;
    } else {
        2u64
    }
}

#[trust_vc::ensures(result == 1u64 || result == 2u64)]
fn control_flow_tail_else_return_verified(flag: bool) -> u64 {
    if flag {
        2u64
    } else {
        return 1u64;
    }
}

#[trust_vc::ensures(result == 11u64 || result == 17u64)]
fn control_flow_short_circuit_return_verified(flag: bool) -> u64 {
    if flag || {
        return 11u64;
    } {
        17u64
    } else {
        13u64
    }
}

#[trust_vc::ensures(result == 17u64)]
fn control_flow_short_circuit_return_counterexample(flag: bool) -> u64 {
    if flag || {
        return 11u64;
    } {
        17u64
    } else {
        13u64
    }
}

#[trust_vc::ensures(result == 11u64 || result == 13u64)]
fn control_flow_match_arm_return_verified(flag: bool) -> u64 {
    match flag {
        true => {
            return 11u64;
        }
        false => 13u64,
    }
}

#[trust_vc::ensures(result == 13u64)]
fn control_flow_match_arm_return_counterexample(flag: bool) -> u64 {
    match flag {
        true => {
            return 11u64;
        }
        false => 13u64,
    }
}

#[trust_vc::ensures(result == 1u32 || result == 3u32)]
fn control_flow_local_initializer_return_verified() -> u32 {
    let x: u32 = {
        return 1u32;
        3u32
    };
    x
}

#[trust_vc::requires(b)]
#[trust_vc::ensures(result)]
fn control_flow_requires_helper(b: bool) -> bool {
    true
}

#[trust_vc::ensures(result == 20u64 || result == 30u64)]
fn control_flow_requires_in_conditional_counterexample() -> u64 {
    if control_flow_requires_helper(false) {
        20u64
    } else {
        30u64
    }
}

#[trust_vc::ensures(result < 3u32)]
fn control_flow_never_expression_binop_error() -> u32 {
    let x = {
        return 1u32;
        3u32
    } + 5u32;
    x
}

#[trust_vc::ensures(result == 3u8)]
fn control_flow_nested_return_in_return_value_error() -> u8 {
    return {
        return 3u8;
        5u8
    };
}

#[trust_vc::ensures(result == 3u8)]
fn control_flow_multiple_top_level_returns_first_dominates_verified() -> u8 {
    return 3u8;
    return 5u8;
}
