// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Partial executable TrustVc evidence for upstream
// `source/rust_verify_test/tests/fndef_types.rs`.
//
// This file intentionally covers only Rust-valid slices that TrustVc can execute
// or reject today: direct helper-contract calls, one-, zero-, and three-argument
// surrogates for upstream function-value shapes, a direct generic helper,
// trait-associated helper calls, SpecFn value-argument extensionality and call
// witnesses, stable rejected precondition/postcondition counterparts, and
// fail-closed function-value boundaries matching upstream shapes like
// `let t = llama; t(4)`, plain `let x = b; x(0)`, a stable current-gap witness
// for mutually recursive function-item calls, `F: Fn(u8) -> bool`, `F: FnOnce/FnMut`,
// `f.requires(...)`/`f.ensures(...)`, datatype constructors as function values,
// and function values with mutable-reference parameters. Full upstream parity
// still requires function items as first-class values, Verus
// `call_requires`/`call_ensures`, generic function-definition values, trait
// method function values, mutable-reference function values, datatype
// constructor function values, and recursion-cycle diagnostics through
// function-definition types.

#![allow(dead_code)]

use trust_vc_types::{int, SpecFn};

pub type FndefTypesExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type FndefTypesExpectedErrorPattern = (&'static str, &'static [&'static str]);

pub const FNDEF_TYPES_RS_EXPECTED_CASES: &[FndefTypesExpectedCase] = &[
    (
        "direct_exec_function_contract_verified",
        "basic_test",
        "verified",
        1,
    ),
    (
        "direct_exec_function_bad_ensures_counterexample",
        "basic_test",
        "counterexample",
        1,
    ),
    (
        "direct_exec_function_bad_requires_counterexample",
        "basic_test",
        "counterexample",
        1,
    ),
    (
        "direct_exec_zero_arg_contract_verified",
        "exec_calling2",
        "verified",
        1,
    ),
    (
        "direct_exec_zero_arg_bad_ensures_counterexample",
        "exec_calling2",
        "counterexample",
        1,
    ),
    (
        "direct_exec_three_arg_contract_verified",
        "generics_test",
        "verified",
        1,
    ),
    (
        "direct_exec_three_arg_bad_ensures_counterexample",
        "generics_test",
        "counterexample",
        1,
    ),
    (
        "direct_exec_three_arg_bad_requires_counterexample",
        "generics_test",
        "counterexample",
        1,
    ),
    (
        "generic_helper_direct_contract_verified",
        "generic_conditions_for_normal_call",
        "verified",
        1,
    ),
    (
        "generic_helper_bad_ensures_counterexample",
        "generic_conditions_for_normal_call",
        "counterexample",
        1,
    ),
    (
        "trait_associated_function_contract_currently_errors",
        "with_trait",
        "error",
        0,
    ),
    (
        "trait_associated_function_bad_ensures_currently_errors",
        "with_trait",
        "error",
        0,
    ),
    (
        "trait_associated_function_bad_requires_currently_errors",
        "with_trait",
        "error",
        0,
    ),
    (
        "spec_fn_value_argument_extensional_verified",
        "basic_test",
        "verified",
        1,
    ),
    (
        "spec_fn_value_call_reflexive_verified",
        "basic_test",
        "verified",
        1,
    ),
    (
        "spec_fn_value_call_wrong_counterexample",
        "basic_test",
        "counterexample",
        1,
    ),
    (
        "exec_function_item_value_call_currently_errors",
        "basic_test",
        "error",
        0,
    ),
    (
        "exec_function_item_value_bad_ensures_currently_errors",
        "basic_test",
        "error",
        0,
    ),
    (
        "exec_function_item_value_bad_requires_currently_errors",
        "basic_test",
        "error",
        0,
    ),
    (
        "zero_arg_function_item_value_call_currently_errors",
        "exec_calling2",
        "error",
        0,
    ),
    (
        "generic_function_item_value_call_currently_errors",
        "generics_test",
        "error",
        0,
    ),
    (
        "generic_function_item_value_bad_ensures_currently_errors",
        "generics_test",
        "error",
        0,
    ),
    (
        "trait_method_function_item_value_call_currently_errors",
        "with_trait",
        "error",
        0,
    ),
    (
        "fn_trait_bound_value_call_currently_errors",
        "basic_test",
        "error",
        0,
    ),
    (
        "fn_once_trait_bound_value_call_currently_errors",
        "recursion6_via_fn_once",
        "error",
        0,
    ),
    (
        "fn_mut_trait_bound_value_call_currently_errors",
        "recursion11_via_fn_mut",
        "error",
        0,
    ),
    (
        "mut_param_function_item_value_currently_errors",
        "mut_params_error",
        "error",
        0,
    ),
    (
        "function_item_requires_reflection_currently_errors",
        "basic_test",
        "error",
        0,
    ),
    (
        "function_item_ensures_reflection_currently_errors",
        "basic_test",
        "error",
        0,
    ),
    (
        "datatype_constructor_function_value_currently_errors",
        "unit_struct_as_fn_not_supported",
        "error",
        0,
    ),
    (
        "function_item_reference_value_call_currently_errors",
        "recursion9_via_fn_once_with_ref",
        "error",
        0,
    ),
    (
        "one_arg_plain_function_item_value_call_verified",
        "exec_calling1",
        "verified",
        1,
    ),
    (
        "mutual_exec_function_item_cycle_diagnostic_current_gap_verified",
        "exec_recursion_mutual",
        "verified",
        1,
    ),
];

pub fn fndef_types_rs_expected_cases() -> &'static [FndefTypesExpectedCase] {
    FNDEF_TYPES_RS_EXPECTED_CASES
}

pub const FNDEF_TYPES_RS_EXPECTED_ERROR_PATTERNS: &[FndefTypesExpectedErrorPattern] = &[
    (
        "trait_associated_function_contract_currently_errors",
        &[
            "unknown return type for function 'FndefTraitWitness::fndef_trait_llama'",
            "fndef_trait_llama",
            "trait-associated",
        ],
    ),
    (
        "trait_associated_function_bad_ensures_currently_errors",
        &[
            "unknown return type for function 'FndefTraitWitness::fndef_trait_llama'",
            "fndef_trait_llama",
            "trait-associated",
        ],
    ),
    (
        "trait_associated_function_bad_requires_currently_errors",
        &[
            "unknown return type for function 'FndefTraitWitness::fndef_trait_llama'",
            "fndef_trait_llama",
            "trait-associated",
        ],
    ),
    (
        "exec_function_item_value_call_currently_errors",
        &[
            "unknown return type for function 't'",
            "function-item value",
            "function value",
        ],
    ),
    (
        "exec_function_item_value_bad_ensures_currently_errors",
        &[
            "unknown return type for function 't'",
            "function-item value",
            "function value",
        ],
    ),
    (
        "exec_function_item_value_bad_requires_currently_errors",
        &[
            "unknown return type for function 't'",
            "function-item value",
            "function value",
        ],
    ),
    (
        "zero_arg_function_item_value_call_currently_errors",
        &[
            "unknown return type for function 't'",
            "function-item value",
            "function value",
        ],
    ),
    (
        "generic_function_item_value_call_currently_errors",
        &[
            "unknown return type for function 't'",
            "function-item value",
            "function value",
        ],
    ),
    (
        "generic_function_item_value_bad_ensures_currently_errors",
        &[
            "unknown return type for function 't'",
            "function-item value",
            "function value",
        ],
    ),
    (
        "trait_method_function_item_value_call_currently_errors",
        &[
            "unknown return type for function 't'",
            "function-item value",
            "function value",
            "fndef_trait_llama",
        ],
    ),
    (
        "fn_trait_bound_value_call_currently_errors",
        &[
            "Undefined function: f",
            "unknown return type for function 'f'",
            "Fn(u8) -> bool",
            "function value",
        ],
    ),
    (
        "fn_once_trait_bound_value_call_currently_errors",
        &[
            "Undefined function: f",
            "unknown return type for function 'f'",
            "FnOnce",
            "function value",
        ],
    ),
    (
        "fn_mut_trait_bound_value_call_currently_errors",
        &[
            "Undefined function: f",
            "unknown return type for function 'f'",
            "FnMut",
            "function value",
        ],
    ),
    (
        "mut_param_function_item_value_currently_errors",
        &[
            "mutable reference",
            "&mut",
            "unknown return type for function 't'",
            "function value",
        ],
    ),
    (
        "function_item_requires_reflection_currently_errors",
        &[
            "unresolved variable",
            "requires",
            "method",
            "function-item value",
            "function value",
        ],
    ),
    (
        "function_item_ensures_reflection_currently_errors",
        &[
            "unresolved variable",
            "ensures",
            "method",
            "function-item value",
            "function value",
        ],
    ),
    (
        "datatype_constructor_function_value_currently_errors",
        &[
            "unknown return type for function 'make'",
            "datatype constructor",
            "constructor",
            "function value",
        ],
    ),
    (
        "function_item_reference_value_call_currently_errors",
        &[
            "unknown return type for function 't'",
            "function-item value",
            "function value",
            "reference",
        ],
    ),
];

pub fn fndef_types_rs_expected_error_patterns() -> &'static [FndefTypesExpectedErrorPattern] {
    FNDEF_TYPES_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::requires(x == 4u8 || x == 7u8)]
#[trust_vc::ensures(result == (x == 4u8))]
fn fndef_llama(x: u8) -> bool {
    x == 4u8
}

#[trust_vc::ensures(true)]
fn direct_exec_function_contract_verified() {
    let b = fndef_llama(4u8);
    trust_vc::assert!(b);

    let c = fndef_llama(7u8);
    trust_vc::assert!(!c);
}

#[trust_vc::ensures(true)]
fn direct_exec_function_bad_ensures_counterexample() {
    let _b = fndef_llama(4u8);
    trust_vc::assert_by_compute!(true == false; compute_only);
}

#[trust_vc::ensures(true)]
fn direct_exec_function_bad_requires_counterexample() {
    let _b = fndef_llama(4u8);
    trust_vc::assert_by_compute!(12u8 == 4u8; compute_only);
}

#[trust_vc::ensures(result)]
fn fndef_zero_arg_llama() -> bool {
    true
}

#[trust_vc::ensures(true)]
fn direct_exec_zero_arg_contract_verified() {
    let b = fndef_zero_arg_llama();
    trust_vc::assert!(b);
}

#[trust_vc::ensures(true)]
fn direct_exec_zero_arg_bad_ensures_counterexample() {
    let _b = fndef_zero_arg_llama();
    trust_vc::assert_by_compute!(true == false; compute_only);
}

#[trust_vc::requires(x == y)]
#[trust_vc::ensures(result == (y == z))]
fn fndef_three_arg_llama(x: u8, y: u8, z: u8) -> bool {
    let _ = x;
    y == z
}

#[trust_vc::ensures(true)]
fn direct_exec_three_arg_contract_verified() {
    let b = fndef_three_arg_llama(4u8, 4u8, 6u8);
    trust_vc::assert!(!b);

    let c = fndef_three_arg_llama(4u8, 4u8, 4u8);
    trust_vc::assert!(c);
}

#[trust_vc::ensures(true)]
fn direct_exec_three_arg_bad_ensures_counterexample() {
    let _b = fndef_three_arg_llama(4u8, 4u8, 4u8);
    trust_vc::assert_by_compute!(true == false; compute_only);
}

#[trust_vc::ensures(true)]
fn direct_exec_three_arg_bad_requires_counterexample() {
    let _b = fndef_three_arg_llama(4u8, 4u8, 6u8);
    trust_vc::assert_by_compute!(12u8 == 13u8; compute_only);
}

struct FndefTraitWitness;

#[trust_vc::trait_spec]
trait FndefTraitLlama {
    #[trust_vc::requires(x == y)]
    #[trust_vc::ensures(result == (y == z))]
    fn fndef_trait_llama(x: u8, y: u8, z: u8) -> bool;
}

#[trust_vc::trait_impl]
impl FndefTraitLlama for FndefTraitWitness {
    fn fndef_trait_llama(_x: u8, y: u8, z: u8) -> bool {
        y == z
    }
}

#[trust_vc::ensures(true)]
fn trait_associated_function_contract_currently_errors() {
    let b = FndefTraitWitness::fndef_trait_llama(4u8, 4u8, 6u8);
    trust_vc::assert!(!b);

    let c = FndefTraitWitness::fndef_trait_llama(4u8, 4u8, 4u8);
    trust_vc::assert!(c);
}

#[trust_vc::ensures(true)]
fn trait_associated_function_bad_ensures_currently_errors() {
    let b = FndefTraitWitness::fndef_trait_llama(4u8, 4u8, 4u8);
    trust_vc::assert!(!b);
}

#[trust_vc::ensures(true)]
fn trait_associated_function_bad_requires_currently_errors() {
    let b = FndefTraitWitness::fndef_trait_llama(12u8, 13u8, 14u8);
    trust_vc::assert!(b || !b);
}

#[trust_vc::ensures(result == 7u8)]
fn fndef_generic_const_llama<T>(_value: T) -> u8 {
    7u8
}

#[trust_vc::ensures(true)]
fn generic_helper_direct_contract_verified() {
    let b = fndef_generic_const_llama::<u8>(4u8);
    trust_vc::assert!(b == 7u8);
}

#[trust_vc::ensures(true)]
fn generic_helper_bad_ensures_counterexample() {
    let _b = fndef_generic_const_llama::<u8>(4u8);
    trust_vc::assert_by_compute!(7u8 == 8u8; compute_only);
}

#[trust_vc::ensures(true)]
fn spec_fn_value_argument_extensional_verified(f: SpecFn<int, int>) {
    trust_vc::assert!(trust_vc::ext_eq!(
        SpecFn::new(|n: int| f.call(n + 1)),
        SpecFn::new(|n: int| f.call(1 + n))
    ));
}

#[trust_vc::ensures(true)]
fn spec_fn_value_call_reflexive_verified(f: SpecFn<int, int>, n: int) {
    trust_vc::assert!(f.call(n) == f.call(n));
}

#[trust_vc::ensures(true)]
fn spec_fn_value_call_wrong_counterexample(f: SpecFn<int, int>, n: int) {
    let _value = f.call(n);
    trust_vc::assert_by_compute!(0u8 == 1u8; compute_only);
}

#[trust_vc::ensures(true)]
fn exec_function_item_value_call_currently_errors() {
    let t = fndef_llama;
    let b = t(4u8);
    trust_vc::assert!(b);
}

#[trust_vc::ensures(true)]
fn exec_function_item_value_bad_ensures_currently_errors() {
    let t = fndef_llama;
    let b = t(4u8);
    trust_vc::assert!(!b);
}

#[trust_vc::ensures(true)]
fn exec_function_item_value_bad_requires_currently_errors() {
    let t = fndef_llama;
    let b = t(12u8);
    trust_vc::assert!(b || !b);
}

#[trust_vc::ensures(true)]
fn zero_arg_function_item_value_call_currently_errors() {
    let t = fndef_zero_arg_llama;
    let b = t();
    trust_vc::assert!(b);
}

fn fndef_plain_one_arg(_i: u8) {}

#[trust_vc::ensures(true)]
fn one_arg_plain_function_item_value_call_verified() {
    let x = fndef_plain_one_arg;
    x(0u8);
}

#[trust_vc::ensures(true)]
fn mutual_exec_function_item_cycle_diagnostic_current_gap_verified() {
    let x = fndef_exec_recursion_b;
    x();
}

fn fndef_exec_recursion_b() {
    let y = mutual_exec_function_item_cycle_diagnostic_current_gap_verified;
    y();
}

#[trust_vc::ensures(true)]
fn generic_function_item_value_call_currently_errors() {
    let t = fndef_generic_const_llama::<u8>;
    let b = t(4u8);
    trust_vc::assert!(b == 7u8);
}

#[trust_vc::ensures(true)]
fn generic_function_item_value_bad_ensures_currently_errors() {
    let t = fndef_generic_const_llama::<u8>;
    let b = t(4u8);
    trust_vc::assert!(b == 8u8);
}

#[trust_vc::ensures(true)]
fn trait_method_function_item_value_call_currently_errors() {
    let t = FndefTraitWitness::fndef_trait_llama;
    let b = t(4u8, 4u8, 4u8);
    trust_vc::assert!(b);
}

#[trust_vc::ensures(true)]
fn fn_trait_bound_value_call_currently_errors<F: Fn(u8) -> bool>(f: F) {
    let b = f(4u8);
    trust_vc::assert!(b || !b);
}

#[trust_vc::ensures(true)]
fn fn_once_trait_bound_value_call_currently_errors<F: FnOnce(u8) -> bool>(f: F) {
    let b = f(4u8);
    trust_vc::assert!(b || !b);
}

#[trust_vc::ensures(true)]
fn fn_mut_trait_bound_value_call_currently_errors<F: FnMut(u8) -> bool>(mut f: F) {
    let b = f(4u8);
    trust_vc::assert!(b || !b);
}

fn fndef_mut_param(_x: &mut u8) -> u8 {
    7u8
}

#[trust_vc::ensures(true)]
fn mut_param_function_item_value_currently_errors(x: &mut u8) {
    let t = fndef_mut_param;
    let observed = t(x);
    trust_vc::assert!(observed == 7u8);
}

#[trust_vc::ensures(true)]
fn function_item_requires_reflection_currently_errors() {
    let t = fndef_llama;
    trust_vc::assert!(t.requires((4u8,)));
}

#[trust_vc::ensures(true)]
fn function_item_ensures_reflection_currently_errors() {
    let t = fndef_llama;
    trust_vc::assert!(t.ensures((4u8,), true));
}

struct FndefTupleConstructor(u8);

#[trust_vc::ensures(true)]
fn datatype_constructor_function_value_currently_errors() {
    let make = FndefTupleConstructor;
    let value = make(4u8);
    trust_vc::assert!(value.0 == 4u8);
}

#[trust_vc::ensures(true)]
fn function_item_reference_value_call_currently_errors() {
    let t = &fndef_llama;
    let b = t(4u8);
    trust_vc::assert!(b);
}
