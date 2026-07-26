// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream Verus
// `rust_verify_test/tests/default_trait.rs`.
//
// This file intentionally keeps the upstream manifest entry as an
// unsupported-gap. The upstream file checks Rust `Default` over primitive
// values, inference, UFCS, std containers, smart pointers, generics, and custom
// types. TrustVc models only the direct primitive/Option/tuple constructor
// slice of those std `Default` constructors today.
//
// This scout slice pins only Rust-valid TrustVc evidence:
// - Explicit zero/false/None/tuple default-value surrogates verify primitive,
//   Option, and tuple shapes.
// - A custom default trait method body verifies its postconditions.
// - std Vec empty-view constructor, direct HashMap/HashSet view surrogates, and
//   direct Rust Vec/HashMap/HashSet associated Default constructors verify the
//   simplest collection shapes.
// - Wrong scalar default-value assertions are rejected with stable
//   counterexamples.
// - Direct Rust u32/bool/Option/typed tuple associated Default constructors
//   verify.
// - Direct Rust inference/UFCS Default constructors, string, unsupported std
//   collection, smart-pointer, smart-pointer custom Default, PhantomData, and
//   generic Default constructors remain fail-closed unsupported boundaries
//   rather than accepted replacement evidence.

#![allow(dead_code)]

use trust_vc_types::View;
use std::collections::{HashMap, HashSet, VecDeque};
use std::marker::PhantomData;
use std::rc::Rc;
use std::sync::Arc;

pub const DEFAULT_TRAIT_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "trust_vc_default_u32_zero_value_verified",
        "test_default_u32_ok",
        "verified",
        2,
    ),
    (
        "trust_vc_default_bool_false_value_verified",
        "test_default_bool_ok",
        "verified",
        2,
    ),
    (
        "trust_vc_default_option_u32_none_verified",
        "test_default_option_u32_ok",
        "verified",
        2,
    ),
    (
        "trust_vc_default_u32_arithmetic_zero_verified",
        "test_default_arithmetic",
        "verified",
        2,
    ),
    (
        "trust_vc_default_tuple2_surrogate_verified",
        "test_default_tuple2_ok",
        "verified",
        2,
    ),
    (
        "trust_vc_default_tuple3_surrogate_verified",
        "test_default_tuple3_ok",
        "verified",
        3,
    ),
    (
        "trust_vc_default_record_verified",
        "test_default_custom_type_spec",
        "verified",
        2,
    ),
    (
        "trust_vc_default_vec_new_empty_view_verified",
        "test_default_vec_u32_ok",
        "verified",
        2,
    ),
    (
        "trust_vc_default_hash_map_direct_view_reflexive_verified",
        "test_default_hash_map_u32_ok",
        "verified",
        1,
    ),
    (
        "trust_vc_default_hash_set_direct_view_reflexive_verified",
        "test_default_hash_set_u32_ok",
        "verified",
        1,
    ),
    (
        "trust_vc_default_u32_wrong_value_counterexample",
        "test_default_u32_wrong",
        "counterexample",
        2,
    ),
    (
        "trust_vc_default_bool_wrong_value_counterexample",
        "test_default_bool_wrong",
        "counterexample",
        2,
    ),
    (
        "trust_vc_default_f32_zero_literal_verified",
        "test_default_f32_ok",
        "verified",
        2,
    ),
    (
        "trust_vc_default_f64_zero_literal_verified",
        "test_default_f64_ok",
        "verified",
        2,
    ),
    (
        "rust_default_trait_inference_currently_blocked",
        "test_default_u32_ok",
        "error",
        0,
    ),
    (
        "rust_default_u32_associated_constructor_verified",
        "test_default_u32_ok",
        "verified",
        2,
    ),
    (
        "rust_default_bool_associated_constructor_verified",
        "test_default_bool_ok",
        "verified",
        2,
    ),
    (
        "rust_default_option_u32_associated_constructor_verified",
        "test_default_option_u32_ok",
        "verified",
        2,
    ),
    (
        "rust_default_vec_u32_constructor_verified",
        "test_default_vec_u32_ok",
        "verified",
        2,
    ),
    (
        "rust_default_hash_map_constructor_verified",
        "test_default_hash_map_u32_ok",
        "verified",
        2,
    ),
    (
        "rust_default_hash_set_constructor_verified",
        "test_default_hash_set_u32_ok",
        "verified",
        2,
    ),
    (
        "rust_default_str_associated_constructor_currently_blocked",
        "test_default_str_ok",
        "error",
        0,
    ),
    (
        "rust_default_tuple2_associated_constructor_verified",
        "test_default_tuple2_ok",
        "verified",
        2,
    ),
    (
        "rust_default_tuple3_associated_constructor_verified",
        "test_default_tuple3_ok",
        "verified",
        3,
    ),
    (
        "rust_default_u32_ufcs_constructor_currently_blocked",
        "test_default_u32_ok",
        "error",
        0,
    ),
    (
        "rust_default_string_constructor_currently_blocked",
        "test_default_string_ok",
        "error",
        0,
    ),
    (
        "rust_default_vec_deque_constructor_currently_blocked",
        "test_default_vec_deque_u32_ok",
        "error",
        0,
    ),
    (
        "rust_default_box_u32_constructor_currently_blocked",
        "test_default_box_u32_ok",
        "error",
        0,
    ),
    (
        "rust_default_box_vec_u32_constructor_currently_blocked",
        "test_default_box_vec_u32_ok",
        "error",
        0,
    ),
    (
        "rust_default_rc_u32_constructor_currently_blocked",
        "test_default_rc_u32_ok",
        "error",
        0,
    ),
    (
        "rust_default_arc_u32_constructor_currently_blocked",
        "test_default_arc_u32_ok",
        "error",
        0,
    ),
    (
        "rust_default_box_custom_type_constructor_currently_blocked",
        "test_default_custom_type_ensures_in_smart_ptrs",
        "error",
        0,
    ),
    (
        "rust_default_rc_custom_type_constructor_currently_blocked",
        "test_default_custom_type_ensures_in_smart_ptrs",
        "error",
        0,
    ),
    (
        "rust_default_arc_custom_type_constructor_currently_blocked",
        "test_default_custom_type_ensures_in_smart_ptrs",
        "error",
        0,
    ),
    (
        "rust_default_phantom_constructor_currently_blocked",
        "test_default_phantom_ok",
        "error",
        0,
    ),
    (
        "rust_default_generic_instantiation_currently_blocked",
        "test_default_generic_instantiation",
        "error",
        0,
    ),
];

pub fn default_trait_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    DEFAULT_TRAIT_RS_EXPECTED_CASES
}

pub const DEFAULT_TRAIT_RS_FAIL_CLOSED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "rust_default_trait_inference_currently_blocked",
        &["unknown return type for function 'Default::default'"],
    ),
    (
        "rust_default_str_associated_constructor_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'default'",
        ],
    ),
    (
        "rust_default_u32_ufcs_constructor_currently_blocked",
        &["unknown return type for function 'core::default::Default::default'"],
    ),
    (
        "rust_default_string_constructor_currently_blocked",
        &["unknown return type for function 'String::default'"],
    ),
    (
        "rust_default_vec_deque_constructor_currently_blocked",
        &["unknown return type for function 'VecDeque::default'"],
    ),
    (
        "rust_default_box_u32_constructor_currently_blocked",
        &["unknown return type for function 'Box::default'"],
    ),
    (
        "rust_default_box_vec_u32_constructor_currently_blocked",
        &["unknown return type for function 'Box::default'"],
    ),
    (
        "rust_default_rc_u32_constructor_currently_blocked",
        &["unknown return type for function 'Rc::default'"],
    ),
    (
        "rust_default_arc_u32_constructor_currently_blocked",
        &["unknown return type for function 'Arc::default'"],
    ),
    (
        "rust_default_box_custom_type_constructor_currently_blocked",
        &["unknown return type for function 'Box::default'"],
    ),
    (
        "rust_default_rc_custom_type_constructor_currently_blocked",
        &["unknown return type for function 'Rc::default'"],
    ),
    (
        "rust_default_arc_custom_type_constructor_currently_blocked",
        &["unknown return type for function 'Arc::default'"],
    ),
    (
        "rust_default_phantom_constructor_currently_blocked",
        &["unknown return type for function 'PhantomData::default'"],
    ),
    (
        "rust_default_generic_instantiation_currently_blocked",
        &["unknown return type for function 'T::default'"],
    ),
];

pub fn default_trait_rs_fail_closed_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    DEFAULT_TRAIT_RS_FAIL_CLOSED_ERROR_PATTERNS
}

#[trust_vc::ensures(true)]
fn trust_vc_default_u32_zero_value_verified() {
    let default_value = 0u32;
    trust_vc::assert!(default_value == 0u32);
}

#[trust_vc::ensures(true)]
fn trust_vc_default_u32_arithmetic_zero_verified() {
    let x = 0u32;
    let y = x + 5u32;
    trust_vc::assert!(y == 5u32);
}

#[trust_vc::ensures(true)]
fn trust_vc_default_f32_zero_literal_verified() {
    let default_value = 0.0f32;
    trust_vc::assert!(default_value == 0.0f32);
}

#[trust_vc::ensures(true)]
fn trust_vc_default_f64_zero_literal_verified() {
    let default_value = 0.0f64;
    trust_vc::assert!(default_value == 0.0f64);
}

#[trust_vc::ensures(true)]
fn trust_vc_default_u32_wrong_value_counterexample() {
    let default_value = 0u32;
    trust_vc::assert!(default_value == 1u32);
}

#[trust_vc::ensures(true)]
fn trust_vc_default_bool_false_value_verified() {
    let default_value = false;
    trust_vc::assert!(default_value == false);
}

#[trust_vc::ensures(true)]
fn trust_vc_default_option_u32_none_verified() {
    let default_value: Option<u32> = None;
    trust_vc::assert!(default_value == Option::<u32>::None);
}

#[trust_vc::ensures(true)]
fn trust_vc_default_tuple2_surrogate_verified() {
    let default_value = (0u32, false);
    trust_vc::assert!(default_value.0 == 0u32);
    trust_vc::assert!(default_value.1 == false);
}

#[trust_vc::ensures(true)]
fn trust_vc_default_tuple3_surrogate_verified() {
    let default_value = (0u32, false, '\0');
    trust_vc::assert!(default_value.0 == 0u32);
    trust_vc::assert!(default_value.1 == false);
    trust_vc::assert!(default_value.2 == '\0');
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct DefaultTraitRecord {
    x: u32,
    enabled: bool,
}

struct DefaultTraitGood;
#[trust_vc::trait_spec]
trait TrustVcDefaultRecord {
    #[trust_vc::ensures(true)]
    fn trust_vc_default_record_verified() -> DefaultTraitRecord {
        let result = DefaultTraitRecord {
            x: 10u32,
            enabled: true,
        };
        trust_vc::assert!(result.x == 10u32);
        trust_vc::assert!(result.enabled);
        result
    }
}

#[trust_vc::trait_impl]
impl TrustVcDefaultRecord for DefaultTraitGood {}

#[derive(Default)]
struct DefaultTraitSmartPtrRecord {
    x: u32,
    y: u32,
}

#[trust_vc::ensures(true)]
fn trust_vc_default_vec_new_empty_view_verified() {
    let v: Vec<u32> = Vec::new();
    trust_vc::assert!(v.view().len() == 0usize);
}

#[trust_vc::ensures(true)]
fn trust_vc_default_hash_map_direct_view_reflexive_verified(m: HashMap<u32, u32>) {
    trust_vc::assert!(m.view().len() == m.view().len());
}

#[trust_vc::ensures(true)]
fn trust_vc_default_hash_set_direct_view_reflexive_verified(s: HashSet<u32>) {
    trust_vc::assert!(s.view().len() == s.view().len());
}

#[trust_vc::ensures(true)]
fn trust_vc_default_bool_wrong_value_counterexample() {
    let default_value = false;
    trust_vc::assert!(default_value);
}

#[trust_vc::ensures(result == 0u32)]
fn rust_default_trait_inference_currently_blocked() -> u32 {
    Default::default()
}

#[trust_vc::ensures(result == 0u32)]
fn rust_default_u32_associated_constructor_verified() -> u32 {
    u32::default()
}

#[trust_vc::ensures(result == false)]
fn rust_default_bool_associated_constructor_verified() -> bool {
    bool::default()
}

#[trust_vc::ensures(result == Option::<u32>::None)]
fn rust_default_option_u32_associated_constructor_verified() -> Option<u32> {
    Option::<u32>::default()
}

#[trust_vc::ensures(true)]
fn rust_default_str_associated_constructor_currently_blocked() {
    let value: &'static str = <&'static str>::default();
    trust_vc::assert!(value == "");
}

#[trust_vc::ensures(true)]
fn rust_default_tuple2_associated_constructor_verified() {
    let value: (u32, bool) = <(u32, bool)>::default();
    trust_vc::assert!(value.0 == 0u32);
    trust_vc::assert!(value.1 == false);
}

#[trust_vc::ensures(true)]
fn rust_default_tuple3_associated_constructor_verified() {
    let value: (u32, bool, char) = <(u32, bool, char)>::default();
    trust_vc::assert!(value.0 == 0u32);
    trust_vc::assert!(value.1 == false);
    trust_vc::assert!(value.2 == '\0');
}

#[trust_vc::ensures(result == 0u32)]
fn rust_default_u32_ufcs_constructor_currently_blocked() -> u32 {
    <u32 as core::default::Default>::default()
}

#[trust_vc::ensures(true)]
fn rust_default_vec_u32_constructor_verified() {
    let v: Vec<u32> = Vec::default();
    trust_vc::assert!(v.view().len() == 0usize);
}

#[trust_vc::ensures(true)]
fn rust_default_string_constructor_currently_blocked() {
    let s: String = String::default();
    trust_vc::assert!(s.view().len() == 0usize);
}

#[trust_vc::ensures(true)]
fn rust_default_hash_map_constructor_verified() {
    let m: HashMap<u32, u32> = HashMap::default();
    trust_vc::assert!(m.view().len() == 0usize);
}

#[trust_vc::ensures(true)]
fn rust_default_hash_set_constructor_verified() {
    let s: HashSet<u32> = HashSet::default();
    trust_vc::assert!(s.view().len() == 0usize);
}

#[trust_vc::ensures(true)]
fn rust_default_vec_deque_constructor_currently_blocked() {
    let v: VecDeque<u32> = VecDeque::default();
    trust_vc::assert!(v.view().len() == 0usize);
}

#[trust_vc::ensures(true)]
fn rust_default_box_u32_constructor_currently_blocked() {
    let b: Box<u32> = Box::default();
    trust_vc::assert!(*b == 0u32);
}

#[trust_vc::ensures(true)]
fn rust_default_box_vec_u32_constructor_currently_blocked() {
    let b: Box<Vec<u32>> = Box::default();
    let v: Vec<u32> = *b;
    trust_vc::assert!(v.view().len() == 0usize);
}

#[trust_vc::ensures(true)]
fn rust_default_rc_u32_constructor_currently_blocked() {
    let r: Rc<u32> = Rc::default();
    trust_vc::assert!(*r == 0u32);
}

#[trust_vc::ensures(true)]
fn rust_default_arc_u32_constructor_currently_blocked() {
    let a: Arc<u32> = Arc::default();
    trust_vc::assert!(*a == 0u32);
}

#[trust_vc::ensures(true)]
fn rust_default_box_custom_type_constructor_currently_blocked() {
    let b: Box<DefaultTraitSmartPtrRecord> = Box::default();
    trust_vc::assert!((*b).x == 0u32);
    trust_vc::assert!((*b).y == 0u32);
}

#[trust_vc::ensures(true)]
fn rust_default_rc_custom_type_constructor_currently_blocked() {
    let r: Rc<DefaultTraitSmartPtrRecord> = Rc::default();
    trust_vc::assert!((*r).x == 0u32);
    trust_vc::assert!((*r).y == 0u32);
}

#[trust_vc::ensures(true)]
fn rust_default_arc_custom_type_constructor_currently_blocked() {
    let a: Arc<DefaultTraitSmartPtrRecord> = Arc::default();
    trust_vc::assert!((*a).x == 0u32);
    trust_vc::assert!((*a).y == 0u32);
}

#[trust_vc::ensures(true)]
fn rust_default_phantom_constructor_currently_blocked() {
    let p: PhantomData<u32> = PhantomData::default();
    trust_vc::assert!(p == PhantomData::<u32>);
}

#[trust_vc::ensures(true)]
fn rust_default_generic_instantiation_currently_blocked<T: Default + PartialEq>() {
    trust_vc::assert!(T::default() == T::default());
}
