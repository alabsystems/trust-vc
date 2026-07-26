// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream regression.rs.
//
// This file intentionally covers only a small Rust-valid subset of the pinned
// upstream regression corpus: set insertion/membership, ordinary identifier
// shadowing, tuple/named field reads, casts, named Map returns, unit returns,
// generic struct update, choose witnesses, parenthesized let bindings, simple
// enum construction/copy parsing, tuple copy-bound parsing, field update plus
// map insertion, lifetime/associated-type constructor parsing, and explicit
// return syntax. The full upstream file remains unsupported because it also
// exercises Verus-only syntax, macro hygiene, reveal/fuel diagnostics,
// verifier attributes, module visibility, opaque datatypes, and many unrelated
// regression families.

#![allow(dead_code)]

use trust_vc_types::{int, nat, Map, Set};

pub const UPSTREAM_REGRESSION_RS_PINNED_CASES: &[&str] = &[
    "test_189a",
    "test_189b",
    "test_verifier_truncate_allowed_on_cast",
    "test_hygienic_identifiers_regression_279",
    "fields_from_macros_not_treated_as_distinct_identifiers",
    "parse_named_return_type_with_comma_in_type_args",
    "forall_in_ensures_with_return_keyword_regression_216",
    "reveal_func_unused_from_other_module_issue_411",
    "reveal_exec_fn_issue_411",
    "reveal_proof_fn_issue_411",
    "let_with_parens_issue_260",
    "reveal_non_opaque_issue236_1",
    "reveal_non_opaque_issue236_2",
    "reveal_with_fuel_non_opaque_non_recursive_issue236_373_pass",
    "reveal_with_fuel_non_opaque_non_recursive_issue236_373_fail",
    "test_lifetime_constructor_regression_768",
    "lifetime_generate_assoc_type_regression_769",
    "nested_macros_regression_866",
    "parsing_unit_ret_type_issue937",
    "struct_with_updater_and_typ_subst_in_field_issue956",
    "external_module_issue618",
    "arithmetic_trigger_choose_issue923",
    "test_modules_nested_in_items_external_code",
    "fieldless_enum_regression_1339",
    "derive_regression_1575",
    "field_update_regression_1591",
    "well_formed_pattern_check_issue1741",
    "tuple_copy_bound_issue2211",
    "no_verus_attribute_warning_issue2211",
];

pub fn upstream_regression_rs_pinned_cases() -> &'static [&'static str] {
    UPSTREAM_REGRESSION_RS_PINNED_CASES
}

pub type RegressionExpectedCase = (&'static str, &'static str, &'static str, usize);

pub const REGRESSION_RS_EXPECTED_CASES: &[RegressionExpectedCase] = &[
    (
        "regression_test_189a_set_insert_membership",
        "test_189a",
        "verified",
        1,
    ),
    (
        "regression_test_189b_empty_set_witness_membership",
        "test_189b",
        "verified",
        1,
    ),
    (
        "regression_truncate_cast_u64_to_u8",
        "test_verifier_truncate_allowed_on_cast",
        "verified",
        1,
    ),
    (
        "regression_identifier_shadowing_model",
        "test_hygienic_identifiers_regression_279",
        "verified",
        1,
    ),
    (
        "regression_field_access_model",
        "fields_from_macros_not_treated_as_distinct_identifiers",
        "verified",
        1,
    ),
    (
        "regression_named_map_return_type_with_comma",
        "parse_named_return_type_with_comma_in_type_args",
        "verified",
        1,
    ),
    (
        "regression_named_map_return_caller",
        "parse_named_return_type_with_comma_in_type_args",
        "verified",
        1,
    ),
    (
        "regression_return_keyword_result_postcondition",
        "forall_in_ensures_with_return_keyword_regression_216",
        "verified",
        1,
    ),
    (
        "regression_lifetime_constructor_option_none",
        "test_lifetime_constructor_regression_768",
        "verified",
        1,
    ),
    (
        "regression_lifetime_assoc_type_constructor_issue769",
        "lifetime_generate_assoc_type_regression_769",
        "verified",
        1,
    ),
    (
        "regression_parsing_unit_ret_type_issue937",
        "parsing_unit_ret_type_issue937",
        "verified",
        1,
    ),
    (
        "regression_named_unit_return_issue937",
        "parsing_unit_ret_type_issue937",
        "verified",
        1,
    ),
    (
        "regression_struct_update_generic_field_subst",
        "struct_with_updater_and_typ_subst_in_field_issue956",
        "verified",
        1,
    ),
    (
        "regression_arithmetic_trigger_choose",
        "arithmetic_trigger_choose_issue923",
        "verified",
        1,
    ),
    (
        "regression_fieldless_enum_regression_1339",
        "fieldless_enum_regression_1339",
        "verified",
        1,
    ),
    (
        "regression_derive_clone_copy_enum",
        "derive_regression_1575",
        "verified",
        1,
    ),
    (
        "regression_field_update_map_insert_issue1591",
        "field_update_regression_1591",
        "verified",
        1,
    ),
    (
        "regression_tuple_copy_bound_issue2211",
        "tuple_copy_bound_issue2211",
        "verified",
        1,
    ),
    (
        "regression_identifier_shadowing_wrong_value_counterexample",
        "test_hygienic_identifiers_regression_279",
        "counterexample",
        1,
    ),
    (
        "regression_return_keyword_assert_false_counterexample",
        "forall_in_ensures_with_return_keyword_regression_216",
        "counterexample",
        1,
    ),
    (
        "regression_let_with_parens_issue260",
        "let_with_parens_issue_260",
        "error",
        0,
    ),
    (
        "regression_verus_not_ext_equal_syntax_currently_errors",
        "test_189a",
        "error",
        0,
    ),
    (
        "regression_verus_exists_syntax_currently_errors",
        "test_189b",
        "error",
        0,
    ),
    (
        "regression_macro_argument_hygiene_currently_errors",
        "test_hygienic_identifiers_regression_279",
        "error",
        0,
    ),
    (
        "regression_reveal_exec_fn_currently_errors",
        "reveal_exec_fn_issue_411",
        "error",
        0,
    ),
    (
        "regression_qualified_module_reveal_currently_errors",
        "reveal_func_unused_from_other_module_issue_411",
        "error",
        0,
    ),
    (
        "regression_reveal_with_fuel_currently_errors",
        "reveal_with_fuel_non_opaque_non_recursive_issue236_373_fail",
        "error",
        0,
    ),
    (
        "regression_nested_module_item_currently_errors",
        "test_modules_nested_in_items_external_code",
        "error",
        0,
    ),
];

pub const REGRESSION_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "regression_let_with_parens_issue260",
        &["unresolved variable `x`", "Failed to lower obligation"],
    ),
    (
        "regression_verus_not_ext_equal_syntax_currently_errors",
        &["Failed to parse assert!() expression", "!==", "unexpected"],
    ),
    (
        "regression_verus_exists_syntax_currently_errors",
        &["Failed to parse assert!() expression", "exists"],
    ),
    (
        "regression_macro_argument_hygiene_currently_errors",
        &[
            "Unsupported nested macro_rules! item",
            "only an empty `()` matcher is supported",
        ],
    ),
    (
        "regression_reveal_exec_fn_currently_errors",
        &[
            "reveal!(regression_exec_reveal_target) references unknown function",
            "Available functions",
        ],
    ),
    (
        "regression_qualified_module_reveal_currently_errors",
        &["supports only unqualified function names"],
    ),
    (
        "regression_reveal_with_fuel_currently_errors",
        &[
            "Unsupported reveal_with_fuel!()",
            "unsupported macros are rejected",
        ],
    ),
    (
        "regression_nested_module_item_currently_errors",
        &["Unsupported nested mod item in function body"],
    ),
];

pub fn regression_rs_expected_cases() -> &'static [RegressionExpectedCase] {
    REGRESSION_RS_EXPECTED_CASES
}

pub fn regression_rs_expected_error_patterns() -> &'static [(&'static str, &'static [&'static str])]
{
    REGRESSION_RS_EXPECTED_ERROR_PATTERNS
}

struct RegressionFoo(pub u64);

struct RegressionBar {
    val: u64,
}

struct RegressionUpdater<T> {
    a: int,
    b: T,
}

struct RegressionPcb {
    pid: usize,
    parent_pid: usize,
}

trait RegressionEa {
    type I;
    type O;
}

struct RegressionEmpty;

struct RegressionEaa;

impl RegressionEa for RegressionEaa {
    type I = RegressionEmpty;
    type O = RegressionEmpty;
}

struct RegressionMc<E>(E);

struct RegressionM<E: RegressionEa> {
    content: RegressionMc<E>,
}

enum RegressionAssocA<X> {
    Y(X),
    Z,
}

#[derive(Clone, Copy)]
enum RegressionFieldless {
    A = 0,
    B = 1,
    C = 2,
}

#[trust_vc::spec]
#[trust_vc::opaque]
fn regression_opaque_successor(x: u64) -> u64 {
    x + 1
}

mod regression_opaque_module_boundary {
    #[trust_vc::spec]
    #[trust_vc::opaque]
    pub fn hidden_identity(x: u64) -> u64 {
        x
    }
}

fn regression_exec_reveal_target() -> bool {
    true
}

#[trust_vc::ensures(true)]
fn regression_test_189a_set_insert_membership() {
    let s1: Set<i32> = Set::<i32>::empty().insert(1i32);
    let s2: Set<i32> = Set::<i32>::empty();

    trust_vc::assert!(s1.contains(1i32));
    trust_vc::assert!(!s2.contains(1i32));
}

#[trust_vc::ensures(true)]
fn regression_test_189b_empty_set_witness_membership() {
    let s1: Set<i32> = Set::<i32>::empty().insert(1i32);
    let s3: Set<i32> = Set::<i32>::empty();

    trust_vc::assert!(s1.contains(1i32));
    trust_vc::assert!(!s3.contains(1i32));
}

#[trust_vc::ensures(result == (a as u8))]
fn regression_truncate_cast_u64_to_u8(a: u64) -> u8 {
    a as u8
}

#[trust_vc::ensures(true)]
fn regression_identifier_shadowing_model() {
    let s: u8 = 20u8;
    {
        let s: u8 = 5u8;
        trust_vc::assert!(s == 5u8);
    }

    trust_vc::assert!(s == 20u8);

    let s: u8 = 19u8;
    trust_vc::assert!(s == 19u8);
}

#[trust_vc::ensures(true)]
fn regression_field_access_model() {
    let foo = RegressionFoo(20u64);
    trust_vc::assert!(foo.0 == 20u64);

    let bar = RegressionBar { val: 30u64 };
    trust_vc::assert!(bar.val == 30u64);
}

#[trust_vc::ensures(result == Map::<int, int>::empty())]
fn regression_named_map_return_type_with_comma() -> Map<int, int> {
    Map::<int, int>::empty()
}

#[trust_vc::ensures(true)]
fn regression_named_map_return_caller() {
    let m = regression_named_map_return_type_with_comma();
    trust_vc::assert!(m == Map::<int, int>::empty());
}

#[trust_vc::ensures(true)]
fn regression_return_keyword_result_postcondition() -> bool {
    return true;
}

#[trust_vc::ensures(true)]
fn regression_return_keyword_assert_false_counterexample() {
    trust_vc::assert!(0u8 == 1u8);
    return;
}

#[trust_vc::ensures(true)]
fn regression_let_with_parens_issue260() {
    let (x): usize = 0usize;
    trust_vc::assert!(x == 0usize);
}

#[trust_vc::ensures(true)]
fn regression_identifier_shadowing_wrong_value_counterexample() {
    let s: u8 = 20u8;
    {
        let s: u8 = 5u8;
        trust_vc::assert!(s == 5u8);
    }

    trust_vc::assert!(s == 21u8);
}

#[trust_vc::ensures(true)]
fn regression_lifetime_constructor_option_none() {
    let input: Option<u64> = None;
    trust_vc::assert!(input.is_none());
}

#[trust_vc::ensures(true)]
fn regression_lifetime_assoc_type_constructor_issue769() {
    let input: RegressionAssocA<RegressionM<RegressionEaa>> = RegressionAssocA::Z;
    let _ = input;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn regression_parsing_unit_ret_type_issue937() -> () {
    let x: () = ();
    trust_vc::assert!(x == ());
}

#[trust_vc::contract(
    ensures(t == ()),
    returns(t),
)]
fn regression_named_unit_return_issue937() -> () {}

#[trust_vc::ensures(true)]
fn regression_struct_update_generic_field_subst(x: RegressionUpdater<bool>) {
    let y = RegressionUpdater { a: x.a + 1, ..x };

    trust_vc::assert!(y.a == x.a + 1);
    trust_vc::assert!(y.b == x.b);
}

#[trust_vc::requires(a == 0)]
#[trust_vc::requires(b == 0)]
#[trust_vc::ensures(true)]
fn regression_arithmetic_trigger_choose(a: nat, b: nat) {
    let i: nat = trust_vc::choose!(|i: nat| a == b * i);

    trust_vc::assert!(a == b * i);
}

#[trust_vc::ensures(true)]
fn regression_fieldless_enum_regression_1339() {
    let _a = RegressionFieldless::A;
    let _b = RegressionFieldless::B;
    let _c = RegressionFieldless::C;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn regression_derive_clone_copy_enum() {
    let a = RegressionFieldless::A;
    let b = a;
    let _c = a;
    let _ = b;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn regression_field_update_map_insert_issue1591(m: Map<usize, bool>) {
    let mut pcb = RegressionPcb {
        pid: 7usize,
        parent_pid: 0usize,
    };

    pcb.parent_pid = 10usize;

    trust_vc::assert!(m.insert(pcb.pid, false).contains_key(pcb.pid));
}

#[trust_vc::ensures(true)]
fn regression_tuple_copy_bound_issue2211() {
    let a = 5u8;
    let b = 5u8;
    let ref_a = &a;
    let ref_b = &b;
    let copied_values = (a, b);
    let copied_refs = (ref_a, ref_b);
    let _ = copied_values;
    let _ = copied_refs;

    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn regression_verus_not_ext_equal_syntax_currently_errors() {
    trust_vc::assert!(1u8 !== 2u8);
}

#[trust_vc::ensures(true)]
fn regression_verus_exists_syntax_currently_errors() {
    trust_vc::assert!(exists|s3: Set<i32>| s3 !== Set::<i32>::empty());
}

#[trust_vc::ensures(true)]
fn regression_macro_argument_hygiene_currently_errors() {
    macro_rules! assert_with_binding {
        ($s1:expr) => {{
            let s1 = $s1;
            trust_vc::assert!(s1);
        }};
    }

    let s1 = false;
    assert_with_binding!(true);
    trust_vc::assert!(!s1);
}

#[trust_vc::ensures(true)]
fn regression_reveal_exec_fn_currently_errors() {
    trust_vc::reveal!(regression_exec_reveal_target);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn regression_qualified_module_reveal_currently_errors() {
    trust_vc::reveal!(regression_opaque_module_boundary::hidden_identity);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn regression_reveal_with_fuel_currently_errors() {
    let _ = regression_opaque_successor(0u64);
    trust_vc::reveal_with_fuel!(regression_opaque_successor, 2);
    trust_vc::assert!(regression_opaque_successor(4u64) == 5u64);
}

#[trust_vc::ensures(true)]
fn regression_nested_module_item_currently_errors() {
    mod nested_regression_module {
        pub fn marker() -> bool {
            true
        }
    }

    trust_vc::assert!(nested_regression_module::marker());
}
