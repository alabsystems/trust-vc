// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Partial return.rs port: this file is still an unsupported-gap witness, not
// full replacement evidence. It covers selected explicit-return/control-flow
// shapes, including the contract expression-context slices below. Broader
// standalone #[ensures] precision and the full upstream trait/spec unit-return
// matrix remain unsupported. Solver Unknown outcomes are not accepted as
// expected evidence in this scout.

#![allow(dead_code, unreachable_code)]

pub const RETURN_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    ("test1", "test1", "verified", 2),
    ("test1_fails1", "test1_fails1", "counterexample", 2),
    ("test1_fails2", "test1_fails2", "counterexample", 2),
    ("test2", "test2", "verified", 1),
    ("test2_fails", "test2_fails", "counterexample", 2),
    ("regression_215", "regression_215", "verified", 1),
    (
        "standalone_ensures_single_explicit_return_value",
        "test1",
        "verified",
        2,
    ),
    (
        "standalone_ensures_single_explicit_return_value_fails",
        "test1_fails1",
        "counterexample",
        2,
    ),
    (
        "standalone_ensures_return_from_local_initializer",
        "test1",
        "verified",
        2,
    ),
    (
        "standalone_ensures_return_from_local_initializer_fails",
        "test1_fails1",
        "counterexample",
        2,
    ),
    (
        "top_level_explicit_return_uses_precondition",
        "test1",
        "verified",
        3,
    ),
    (
        "top_level_explicit_return_precondition_fails",
        "test1_fails1",
        "counterexample",
        3,
    ),
    (
        "early_return_uses_precondition_contract",
        "test1",
        "verified",
        3,
    ),
    (
        "early_return_infeasible_branch_current_gap_counterexample",
        "test1",
        "counterexample",
        3,
    ),
    (
        "return_from_local_initializer_contract",
        "test1",
        "verified",
        2,
    ),
    ("return_from_match_arm_contract", "test1", "verified", 2),
    (
        "return_from_match_arm_contract_fails",
        "test1_fails1",
        "counterexample",
        2,
    ),
    (
        "return_only_tail_if_branches_contract",
        "test1",
        "verified",
        2,
    ),
    (
        "return_only_tail_if_branches_contract_fails",
        "test1_fails1",
        "counterexample",
        2,
    ),
    (
        "return_only_match_branches_contract",
        "test1",
        "verified",
        2,
    ),
    (
        "return_only_match_branches_contract_fails",
        "test1_fails1",
        "counterexample",
        2,
    ),
    (
        "return_from_if_let_no_binding_contract",
        "test1",
        "verified",
        2,
    ),
    (
        "return_from_if_let_no_binding_contract_fails",
        "test1_fails1",
        "counterexample",
        2,
    ),
    (
        "return_from_tuple_field_expression_contract",
        "test1",
        "verified",
        2,
    ),
    (
        "return_from_tuple_field_expression_contract_fails",
        "test1_fails1",
        "counterexample",
        2,
    ),
    (
        "return_from_short_circuit_expression_contract",
        "test1",
        "verified",
        2,
    ),
    (
        "return_from_tail_if_expression_contract",
        "test1",
        "verified",
        2,
    ),
    (
        "return_from_tail_if_expression_contract_fails",
        "test1_fails1",
        "counterexample",
        2,
    ),
    (
        "return_from_tail_block_expression_contract",
        "test1",
        "verified",
        2,
    ),
    (
        "return_from_tail_block_expression_contract_fails",
        "test1_fails1",
        "counterexample",
        2,
    ),
    (
        "return_from_loop_contract",
        "test1",
        "verified",
        2,
    ),
    (
        "return_from_while_loop_contract_currently_errors",
        "test3",
        "verified",
        2,
    ),
    (
        "return_from_for_loop_contract_currently_errors",
        "for",
        "verified",
        2,
    ),
    (
        "return_from_if_let_expression_contract",
        "test1",
        "error",
        0,
    ),
    (
        "return_from_let_else_contract",
        "test1",
        "verified",
        1,
    ),
    (
        "return_from_let_else_contract_payload_counterexample",
        "test1",
        "counterexample",
        1,
    ),
    (
        "return_from_call_argument_contract",
        "test1",
        "error",
        0,
    ),
    (
        "return_from_match_binding_contract_currently_errors",
        "test1",
        "error",
        0,
    ),
    (
        "return_from_match_guard_contract_currently_errors",
        "test1",
        "error",
        0,
    ),
    (
        "multiple_top_level_returns_first_dominates_verified",
        "multiple",
        "verified",
        2,
    ),
    (
        "nested_return_value_currently_errors",
        "nested",
        "error",
        0,
    ),
    (
        "non_tail_local_initializer_return_currently_errors",
        "local",
        "error",
        0,
    ),
    (
        "return_with_nested_impl_method_contract",
        "nested",
        "error",
        0,
    ),
    (
        "returning_named_unit_issue1108",
        "returning_named_unit_issue1108",
        "verified",
        2,
    ),
    (
        "returning_named_unit_with_value_issue1108",
        "returning_named_unit_issue1108",
        "verified",
        2,
    ),
    (
        "returning_named_unit_caller_issue1108",
        "returning_named_unit_issue1108",
        "verified",
        1,
    ),
    (
        "return_unit_trait_issue1278",
        "return_unit_trait_issue1278",
        "verified",
        2,
    ),
    (
        "trait_clone_unit_issue1108",
        "trait_clone_unit_issue1108",
        "verified",
        2,
    ),
    (
        "trait_impl_return_unit_issue1108",
        "trait_impl_return_unit_issue1108",
        "verified",
        2,
    ),
    (
        "default_trait_return_unit_issue1108",
        "trait_clone_unit_issue1108",
        "verified",
        2,
    ),
    (
        "default_trait_return_unit_concrete_call_issue1108",
        "trait_clone_unit_issue1108",
        "error",
        0,
    ),
    (
        "generic_spec_funs_returning_unit_issue1108",
        "generic_spec_funs_returning_unit_issue1108",
        "verified",
        2,
    ),
    (
        "spec_fun_returning_unit_call_issue1108",
        "generic_spec_funs_returning_unit_issue1108",
        "verified",
        1,
    ),
    (
        "spec_fun_returning_unit_returns_clause_currently_rejected",
        "generic_spec_funs_returning_unit_issue1108",
        "error",
        0,
    ),
];

pub const RETURN_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "return_from_if_let_expression_contract",
        &["fail closed without solver Unknown evidence"],
    ),
    (
        "return_from_call_argument_contract",
        &["fail closed without solver Unknown evidence"],
    ),
    (
        "return_from_match_binding_contract_currently_errors",
        &["fail closed without solver Unknown evidence"],
    ),
    (
        "return_from_match_guard_contract_currently_errors",
        &["fail closed without solver Unknown evidence"],
    ),
    (
        "nested_return_value_currently_errors",
        &["fail closed without solver Unknown evidence"],
    ),
    (
        "non_tail_local_initializer_return_currently_errors",
        &["fail closed without solver Unknown evidence"],
    ),
    (
        "return_with_nested_impl_method_contract",
        &["fail closed without solver Unknown evidence"],
    ),
    (
        "default_trait_return_unit_concrete_call_issue1108",
        &["fail closed without solver Unknown evidence"],
    ),
    (
        "spec_fun_returning_unit_returns_clause_currently_rejected",
        &["fail closed without solver Unknown evidence"],
    ),
];

pub const RETURN_RS_UNPROMOTED_UPSTREAM_CASES: &[(&str, &str)] = &[
    (
        "test3",
        "while-loop explicit unit-return with invariant parity remains unsupported",
    ),
    (
        "test3_fails",
        "while-loop explicit unit-return missing-invariant counterexample parity remains unsupported",
    ),
];

pub fn return_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    RETURN_RS_EXPECTED_CASES
}

pub fn return_rs_expected_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    RETURN_RS_EXPECTED_ERROR_PATTERNS
}

pub fn return_rs_unpromoted_upstream_cases() -> &'static [(&'static str, &'static str)] {
    RETURN_RS_UNPROMOTED_UPSTREAM_CASES
}

#[trust_vc::ensures(10u64 <= result && 20u64 <= result)]
fn test1(b: bool) -> u64 {
    if b {
        return 20u64;
    }
    30u64
}

#[trust_vc::ensures(10u64 <= result && 20u64 <= result)]
fn test1_fails1(b: bool) -> u64 {
    if b {
        return 10u64;
    }
    30u64
}

#[trust_vc::ensures(10u64 <= result && 20u64 <= result)]
fn test1_fails2(b: bool) -> u64 {
    if b {
        return 20u64;
    }
    10u64
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 13u64),
    returns(result),
)]
fn return_from_match_arm_contract(flag: bool) -> u64 {
    match flag {
        true => {
            return 11u64;
        }
        false => 13u64,
    }
}

#[trust_vc::contract(
    ensures(result == 13u64),
    returns(result),
)]
fn return_from_match_arm_contract_fails(flag: bool) -> u64 {
    match flag {
        true => {
            return 11u64;
        }
        false => 13u64,
    }
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 13u64),
    returns(result),
)]
fn return_from_loop_contract(flag: bool) -> u64 {
    loop {
        if flag {
            return 11u64;
        }
        break;
    }
    13u64
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 17u64),
    returns(result),
)]
fn return_from_local_initializer_contract(flag: bool) -> u64 {
    let value: u64 = if flag {
        return 11u64;
    } else {
        17u64
    };
    value
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 13u64),
    returns(result),
)]
fn return_from_if_let_expression_contract(maybe: Option<u64>) -> u64 {
    let value = if let Some(value) = maybe {
        value
    } else {
        return 13u64;
    };
    value
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 13u64),
    returns(result),
)]
fn return_from_if_let_no_binding_contract(value: u64) -> u64 {
    if let 0u64 = value {
        return 11u64;
    } else {
        13u64
    }
}

#[trust_vc::contract(
    ensures(result == 13u64),
    returns(result),
)]
fn return_from_if_let_no_binding_contract_fails(value: u64) -> u64 {
    if let 0u64 = value {
        return 11u64;
    } else {
        13u64
    }
}

// Port-author extension (upstream return.rs has no let-else case): the
// `else` arm returns 13 and the `Some` arm returns the payload, so the
// contract must admit any `Some` payload.
#[trust_vc::contract(
    ensures(maybe.is_some() || result == 13u64),
    returns(result),
)]
fn return_from_let_else_contract(maybe: Option<u64>) -> u64 {
    let Some(value) = maybe else {
        return 13u64;
    };
    value
}

// LIAR (genuine): the `Some` payload is unconstrained, so `result == 11 ||
// result == 13` is false (witness: `Some(0x800000000000000d)`).
#[trust_vc::contract(
    ensures(result == 11u64 || result == 13u64),
    returns(result),
)]
fn return_from_let_else_contract_payload_counterexample(maybe: Option<u64>) -> u64 {
    let Some(value) = maybe else {
        return 13u64;
    };
    value
}

fn identity_u64(value: u64) -> u64 {
    value
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 17u64),
    returns(result),
)]
fn return_from_call_argument_contract(flag: bool) -> u64 {
    identity_u64(if flag {
        return 11u64;
    } else {
        17u64
    })
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 17u64),
    returns(result),
)]
fn return_from_tuple_field_expression_contract(flag: bool) -> u64 {
    (
        if flag {
            return 11u64;
        } else {
            17u64
        },
        0u64,
    )
        .0
}

#[trust_vc::contract(
    ensures(result == 17u64),
    returns(result),
)]
fn return_from_tuple_field_expression_contract_fails(flag: bool) -> u64 {
    (
        if flag {
            return 11u64;
        } else {
            17u64
        },
        0u64,
    )
        .0
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 17u64),
    returns(result),
)]
fn return_from_short_circuit_expression_contract(flag: bool) -> u64 {
    if flag || {
        return 11u64;
    } {
        17u64
    } else {
        13u64
    }
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 17u64),
    returns(result),
)]
fn return_from_tail_if_expression_contract(flag: bool) -> u64 {
    if flag {
        return 11u64;
    } else {
        17u64
    }
}

#[trust_vc::contract(
    ensures(result == 17u64),
    returns(result),
)]
fn return_from_tail_if_expression_contract_fails(flag: bool) -> u64 {
    if flag {
        return 11u64;
    } else {
        17u64
    }
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 17u64),
    returns(result),
)]
fn return_from_tail_block_expression_contract(flag: bool) -> u64 {
    {
        if flag {
            return 11u64;
        }
        17u64
    }
}

#[trust_vc::contract(
    ensures(result == 17u64),
    returns(result),
)]
fn return_from_tail_block_expression_contract_fails(flag: bool) -> u64 {
    {
        if flag {
            return 11u64;
        }
        17u64
    }
}

#[trust_vc::ensures(result == 20u64)]
fn standalone_ensures_single_explicit_return_value() -> u64 {
    return 20u64;
}

#[trust_vc::ensures(result == 20u64)]
fn standalone_ensures_single_explicit_return_value_fails() -> u64 {
    return 10u64;
}

#[trust_vc::ensures(result == 11u64 || result == 17u64)]
fn standalone_ensures_return_from_local_initializer(flag: bool) -> u64 {
    let value: u64 = if flag {
        return 11u64;
    } else {
        17u64
    };
    value
}

#[trust_vc::ensures(false)]
fn standalone_ensures_return_from_local_initializer_fails(flag: bool) -> u64 {
    let value: u64 = if flag {
        return 11u64;
    } else {
        17u64
    };
    value
}

#[trust_vc::requires(seed == 41u64)]
#[trust_vc::ensures(result == 42u64)]
fn top_level_explicit_return_uses_precondition(seed: u64) -> u64 {
    return seed + 1u64;
}

#[trust_vc::requires(seed == 41u64)]
#[trust_vc::ensures(result == 43u64)]
fn top_level_explicit_return_precondition_fails(seed: u64) -> u64 {
    return seed + 1u64;
}

#[trust_vc::requires(value == 7u64)]
#[trust_vc::contract(
    ensures(result == 7u64),
    returns(result),
)]
fn early_return_uses_precondition_contract(flag: bool, value: u64) -> u64 {
    if flag {
        return value;
    }
    7u64
}

#[trust_vc::requires(!flag)]
#[trust_vc::contract(
    ensures(result == 17u64),
    returns(result),
)]
fn early_return_infeasible_branch_current_gap_counterexample(flag: bool) -> u64 {
    if flag {
        return 11u64;
    }
    17u64
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 13u64),
    returns(result),
)]
fn return_only_tail_if_branches_contract(flag: bool) -> u64 {
    if flag {
        return 11u64;
    } else {
        return 13u64;
    }
}

#[trust_vc::contract(
    ensures(result == 13u64),
    returns(result),
)]
fn return_only_tail_if_branches_contract_fails(flag: bool) -> u64 {
    if flag {
        return 11u64;
    } else {
        return 13u64;
    }
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 13u64),
    returns(result),
)]
fn return_only_match_branches_contract(flag: bool) -> u64 {
    match flag {
        true => return 11u64,
        false => return 13u64,
    }
}

#[trust_vc::contract(
    ensures(result == 13u64),
    returns(result),
)]
fn return_only_match_branches_contract_fails(flag: bool) -> u64 {
    match flag {
        true => return 11u64,
        false => return 13u64,
    }
}

#[trust_vc::contract(
    ensures(result == 13u64),
    returns(result),
)]
fn return_from_match_binding_contract_currently_errors(maybe: Option<u64>) -> u64 {
    match maybe {
        Some(value) => {
            return value;
        }
        None => 13u64,
    }
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 13u64),
    returns(result),
)]
fn return_from_match_guard_contract_currently_errors(flag: bool, value: u64) -> u64 {
    match value {
        0u64 if flag => return 11u64,
        _ => 13u64,
    }
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 13u64),
    returns(result),
)]
fn multiple_top_level_returns_first_dominates_verified() -> u64 {
    return 11u64;
    return 13u64;
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 17u64),
    returns(result),
)]
fn nested_return_value_currently_errors(flag: bool) -> u64 {
    return if flag {
        return 11u64;
    } else {
        17u64
    };
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 17u64),
    returns(result),
)]
fn non_tail_local_initializer_return_currently_errors(flag: bool) -> u64 {
    let value = if flag {
        return 11u64;
    } else {
        17u64
    };
    value + 1u64
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 17u64),
    returns(result),
)]
fn return_from_while_loop_contract_currently_errors(flag: bool) -> u64 {
    while flag {
        return 11u64;
    }
    17u64
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 17u64),
    returns(result),
)]
fn return_from_for_loop_contract_currently_errors() -> u64 {
    for value in [0u64, 1u64] {
        if value == 1u64 {
            return 11u64;
        }
    }
    17u64
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 17u64),
    returns(result),
)]
fn return_with_nested_impl_method_contract(flag: bool) -> u64 {
    struct Local;
    impl Local {
        fn value() -> u64 {
            return 11u64;
        }
    }

    if flag {
        return Local::value();
    }
    17u64
}

#[trust_vc::ensures(true)]
fn test2(b: bool) {
    if b {
        return;
    }
}

#[trust_vc::requires(b)]
#[trust_vc::ensures(false)]
fn test2_fails(b: bool) {
    if b {
        return;
    }
}

#[trust_vc::requires(b)]
#[trust_vc::ensures(b)]
fn test3(b: bool) {
    while b || !b {
        trust_vc::invariant!(b);
        return;
    }
}

#[trust_vc::requires(b)]
#[trust_vc::ensures(b)]
fn test3_fails(b: bool) {
    while b || !b {
        return;
    }
}

#[trust_vc::ensures(true)]
fn regression_215() {
    return ();
}

#[trust_vc::contract(
    ensures(n == ()),
    returns(n),
)]
#[trust_vc::proof]
fn returning_named_unit_issue1108() -> () {
    return;
}

#[trust_vc::contract(
    ensures(result == ()),
    returns(result),
)]
#[trust_vc::proof]
fn returning_named_unit_with_value_issue1108() -> () {
    return ();
}

#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn returning_named_unit_caller_issue1108() {
    let first = returning_named_unit_issue1108();
    let second = returning_named_unit_with_value_issue1108();
    trust_vc::assert!(first == ());
    trust_vc::assert!(second == ());
}

#[trust_vc::contract(
    ensures(result == ()),
    returns(result),
)]
#[trust_vc::proof]
fn return_unit_trait_issue1278() -> () {}

#[trust_vc::contract(
    ensures(result == ()),
    returns(result),
)]
fn trait_clone_unit_issue1108() -> () {
    ()
}

#[trust_vc::contract(
    ensures(result == ()),
    returns(result),
)]
fn trait_impl_return_unit_issue1108() -> () {}

#[trust_vc::trait_spec]
trait DefaultTraitReturnUnitIssue1108: Sized {
    #[trust_vc::contract(
        ensures(result == ()),
        returns(result),
    )]
    fn default_trait_return_unit_issue1108() -> () {
        ()
    }
}

#[trust_vc::trait_impl]
impl DefaultTraitReturnUnitIssue1108 for bool {}

#[trust_vc::ensures(true)]
fn default_trait_return_unit_concrete_call_issue1108() {
    let value = <bool as DefaultTraitReturnUnitIssue1108>::default_trait_return_unit_issue1108();
    trust_vc::assert!(value == ());
}

#[trust_vc::contract(
    ensures(result == ()),
    returns(result),
)]
#[trust_vc::proof]
fn generic_spec_funs_returning_unit_issue1108() -> () {
    return;
}

#[trust_vc::spec]
fn spec_fun_returning_unit_body_issue1108() -> () {
    ()
}

#[trust_vc::ensures(true)]
fn spec_fun_returning_unit_call_issue1108() {
    let result = spec_fun_returning_unit_body_issue1108();
    trust_vc::assert!(result == ());
}

#[trust_vc::spec]
#[trust_vc::contract(
    ensures(result == ()),
    returns(result),
)]
fn spec_fun_returning_unit_returns_clause_currently_rejected() -> () {
    ()
}
