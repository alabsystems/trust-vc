// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream Verus
// `rust_verify_test/tests/default_trait.rs`.
//
// This file intentionally keeps the upstream manifest entry as an
// unsupported-gap. The upstream file checks Rust `Default` over primitive
// values, inference, UFCS, std containers, smart pointers, generics, and custom
// types.
//
// The `Default::default()` constructor family is TYPE-DIRECTED (2026-09-13):
// the value is fixed by the expected type, which the source spells three ways
// — `<Ty>::default()`, `let b: Ty = Default::default()` (inference from the
// declared or return type) and `<Ty as core::default::Default>::default()`
// (UFCS) — and the engine models all three for the primitives, `&str`,
// `String`, `Option<T>`, `PhantomData<T>`, tuples, `Vec`/`VecDeque`/`HashMap`/
// `HashSet`, `Box`/`Rc`/`Arc` (their payload), a `#[derive(Default)]` struct
// (the field-wise constructor), a hand-written `impl Default` whose body is a
// single constructor expression (its body axiom), and a generic `T::default()`
// (one uninterpreted per-type-parameter constant: congruence only).
//
// This scout slice pins only Rust-valid TrustVc evidence:
// - The upstream `test_default_ok!` macro family (nine types, three spellings
//   each) and both `test_default_fail!` twins, ported VERBATIM.
// - Every modelled constructor in BOTH directions: the `_verified` claim and a
//   `_counterexample` liar twin refuted with a model.
// - The pre-existing zero/false/None/tuple surrogates and std-collection
//   witnesses are kept as they were.
// - Two shapes stay fail-closed with precise fragments: the upstream
//   `T::default.ensures((), r)` closure-reflection contract on a generic
//   `mk<T: Default>()`, and `String::is_ascii()`.

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
        "trust_vc_default_u32_arithmetic_zero_verified",
        "test_default_arithmetic",
        "verified",
        3,
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
        "trust_vc_default_u32_wrong_value_counterexample",
        "test_default_u32_wrong",
        "counterexample",
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
        "trust_vc_default_tuple2_surrogate_verified",
        "test_default_tuple2_ok",
        "verified",
        3,
    ),
    (
        "trust_vc_default_tuple3_surrogate_verified",
        "test_default_tuple3_ok",
        "verified",
        4,
    ),
    (
        "trust_vc_default_record_verified",
        "test_default_custom_type_spec",
        "verified",
        4,
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
        2,
    ),
    (
        "trust_vc_default_hash_set_direct_view_reflexive_verified",
        "test_default_hash_set_u32_ok",
        "verified",
        2,
    ),
    (
        "trust_vc_default_bool_wrong_value_counterexample",
        "test_default_bool_wrong",
        "counterexample",
        2,
    ),
    (
        "rust_default_trait_inference_verified",
        "test_default_u32_ok",
        "verified",
        5,
    ),
    (
        "rust_default_u32_associated_constructor_verified",
        "test_default_u32_ok",
        "verified",
        5,
    ),
    (
        "rust_default_bool_associated_constructor_verified",
        "test_default_bool_ok",
        "verified",
        5,
    ),
    (
        "rust_default_option_u32_associated_constructor_verified",
        "test_default_option_u32_ok",
        "verified",
        5,
    ),
    (
        "rust_default_str_associated_constructor_verified",
        "test_default_str_ok",
        "verified",
        2,
    ),
    (
        "rust_default_tuple2_associated_constructor_verified",
        "test_default_tuple2_ok",
        "verified",
        3,
    ),
    (
        "rust_default_tuple3_associated_constructor_verified",
        "test_default_tuple3_ok",
        "verified",
        4,
    ),
    (
        "rust_default_u32_ufcs_constructor_verified",
        "test_default_u32_ok",
        "verified",
        5,
    ),
    (
        "rust_default_vec_u32_constructor_verified",
        "test_default_vec_u32_ok",
        "verified",
        5,
    ),
    (
        "rust_default_string_constructor_verified",
        "test_default_string_ok",
        "verified",
        5,
    ),
    (
        "rust_default_hash_map_constructor_verified",
        "test_default_hash_map_u32_ok",
        "verified",
        5,
    ),
    (
        "rust_default_hash_set_constructor_verified",
        "test_default_hash_set_u32_ok",
        "verified",
        5,
    ),
    (
        "rust_default_vec_deque_constructor_verified",
        "test_default_vec_deque_u32_ok",
        "verified",
        5,
    ),
    (
        "rust_default_box_u32_constructor_verified",
        "test_default_box_u32_ok",
        "verified",
        5,
    ),
    (
        "rust_default_box_vec_u32_constructor_verified",
        "test_default_box_vec_u32_ok",
        "verified",
        5,
    ),
    (
        "rust_default_rc_u32_constructor_verified",
        "test_default_rc_u32_ok",
        "verified",
        5,
    ),
    (
        "rust_default_arc_u32_constructor_verified",
        "test_default_arc_u32_ok",
        "verified",
        5,
    ),
    (
        "rust_default_box_custom_type_constructor_verified",
        "test_default_custom_type_ensures_in_smart_ptrs",
        "verified",
        6,
    ),
    (
        "rust_default_rc_custom_type_constructor_verified",
        "test_default_custom_type_ensures_in_smart_ptrs",
        "verified",
        6,
    ),
    (
        "rust_default_arc_custom_type_constructor_verified",
        "test_default_custom_type_ensures_in_smart_ptrs",
        "verified",
        6,
    ),
    (
        "rust_default_phantom_constructor_verified",
        "test_default_phantom_ok",
        "verified",
        5,
    ),
    (
        "rust_default_generic_instantiation_verified",
        "test_default_generic_instantiation",
        "error",
        5,
    ),
    (
        "rust_default_trait_inference_wrong_counterexample",
        "test_default_u32_wrong",
        "counterexample",
        5,
    ),
    (
        "rust_default_str_associated_constructor_wrong_counterexample",
        "test_default_str_ok",
        "counterexample",
        2,
    ),
    (
        "rust_default_string_constructor_wrong_counterexample",
        "test_default_string_ok",
        "counterexample",
        5,
    ),
    (
        "rust_default_vec_deque_constructor_wrong_counterexample",
        "test_default_vec_deque_u32_ok",
        "counterexample",
        5,
    ),
    (
        "rust_default_box_u32_constructor_wrong_counterexample",
        "test_default_box_u32_ok",
        "counterexample",
        5,
    ),
    (
        "rust_default_box_vec_u32_constructor_wrong_counterexample",
        "test_default_box_vec_u32_ok",
        "counterexample",
        5,
    ),
    (
        "rust_default_rc_u32_constructor_wrong_counterexample",
        "test_default_rc_u32_ok",
        "counterexample",
        5,
    ),
    (
        "rust_default_arc_u32_constructor_wrong_counterexample",
        "test_default_arc_u32_ok",
        "counterexample",
        5,
    ),
    (
        "rust_default_box_custom_type_constructor_wrong_counterexample",
        "test_default_custom_type_ensures_in_smart_ptrs",
        "counterexample",
        5,
    ),
    (
        "rust_default_phantom_constructor_wrong_counterexample",
        "test_default_phantom_ok",
        "counterexample",
        5,
    ),
    (
        "rust_default_generic_instantiation_wrong_counterexample",
        "test_default_generic_instantiation",
        "counterexample",
        5,
    ),
    (
        "upstream_test_default_u32_ok_verified",
        "test_default_u32_ok",
        "verified",
        7,
    ),
    (
        "upstream_test_default_u32_wrong_counterexample",
        "test_default_u32_wrong",
        "counterexample",
        2,
    ),
    (
        "upstream_test_default_bool_ok_verified",
        "test_default_bool_ok",
        "verified",
        7,
    ),
    (
        "upstream_test_default_bool_wrong_counterexample",
        "test_default_bool_wrong",
        "counterexample",
        2,
    ),
    (
        "upstream_test_default_f32_ok_verified",
        "test_default_f32_ok",
        "verified",
        7,
    ),
    (
        "upstream_test_default_f64_ok_verified",
        "test_default_f64_ok",
        "verified",
        7,
    ),
    (
        "upstream_test_default_f64_wrong_counterexample",
        "test_default_f64_ok",
        "counterexample",
        5,
    ),
    (
        "upstream_test_default_str_ok_verified",
        "test_default_str_ok",
        "verified",
        7,
    ),
    (
        "upstream_test_default_option_u32_ok_verified",
        "test_default_option_u32_ok",
        "verified",
        7,
    ),
    (
        "upstream_test_default_option_u32_wrong_counterexample",
        "test_default_option_u32_ok",
        "counterexample",
        5,
    ),
    (
        "upstream_test_default_phantom_ok_verified",
        "test_default_phantom_ok",
        "verified",
        7,
    ),
    (
        "upstream_test_default_tuple2_ok_verified",
        "test_default_tuple2_ok",
        "verified",
        7,
    ),
    (
        "upstream_test_default_tuple2_wrong_counterexample",
        "test_default_tuple2_ok",
        "counterexample",
        5,
    ),
    (
        "upstream_test_default_tuple3_ok_verified",
        "test_default_tuple3_ok",
        "verified",
        7,
    ),
    (
        "upstream_test_default_tuple3_wrong_counterexample",
        "test_default_tuple3_ok",
        "counterexample",
        2,
    ),
    (
        "rust_default_custom_type_spec_mk_verified",
        "test_default_custom_type_spec",
        "verified",
        6,
    ),
    (
        "rust_default_custom_type_spec_test_verified",
        "test_default_custom_type_spec",
        "verified",
        9,
    ),
    (
        "rust_default_custom_type_spec_wrong_counterexample",
        "test_default_custom_type_spec",
        "counterexample",
        5,
    ),
    (
        "rust_default_custom_type_ensures_in_smart_ptrs_verified",
        "test_default_custom_type_ensures_in_smart_ptrs",
        "verified",
        10,
    ),
    (
        "rust_default_custom_type_ensures_in_smart_ptrs_wrong_counterexample",
        "test_default_custom_type_ensures_in_smart_ptrs",
        "counterexample",
        5,
    ),
    (
        "rust_default_generic_mk_reflection_currently_blocked",
        "test_default_generic_instantiation",
        "error",
        0,
    ),
    (
        "rust_default_string_is_ascii_currently_blocked",
        "test_default_string_ok",
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
        "rust_default_generic_instantiation_verified",
        &["bodiless call repeated"],
    ),
    (
        "rust_default_generic_mk_reflection_currently_blocked",
        &[
            "Failed to lower obligation 'postcondition'",
            "unsupported expression `T::default` in specification context",
        ],
    ),
    (
        "rust_default_string_is_ascii_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_1'",
            "unsupported method `is_ascii()",
        ],
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
fn rust_default_trait_inference_verified() -> u32 {
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
fn rust_default_str_associated_constructor_verified() {
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

// Promoted from `..._currently_blocked` (error) to verified. The trait-qualified
// UFCS spelling `<u32 as core::default::Default>::default()` now models as the
// same zero the plain `u32::default()` spelling does. Both DIRECTIONS measured
// before promoting: `ensures(result == 0u32)` verifies and `ensures(result ==
// 1u32)` yields a Counterexample, on both spellings; stock `rustc --edition
// 2021` prints `0`, so the verified claim is the TRUE one. The row was reading
// `error` only because the harness's fail-closed loop panicked on an earlier row
// and never reached it.
#[trust_vc::ensures(result == 0u32)]
fn rust_default_u32_ufcs_constructor_verified() -> u32 {
    <u32 as core::default::Default>::default()
}

#[trust_vc::ensures(true)]
fn rust_default_vec_u32_constructor_verified() {
    let v: Vec<u32> = Vec::default();
    trust_vc::assert!(v.view().len() == 0usize);
}

#[trust_vc::ensures(true)]
fn rust_default_string_constructor_verified() {
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
fn rust_default_vec_deque_constructor_verified() {
    let v: VecDeque<u32> = VecDeque::default();
    trust_vc::assert!(v.view().len() == 0usize);
}

#[trust_vc::ensures(true)]
fn rust_default_box_u32_constructor_verified() {
    let b: Box<u32> = Box::default();
    trust_vc::assert!(*b == 0u32);
}

#[trust_vc::ensures(true)]
fn rust_default_box_vec_u32_constructor_verified() {
    let b: Box<Vec<u32>> = Box::default();
    let v: Vec<u32> = *b;
    trust_vc::assert!(v.view().len() == 0usize);
}

#[trust_vc::ensures(true)]
fn rust_default_rc_u32_constructor_verified() {
    let r: Rc<u32> = Rc::default();
    trust_vc::assert!(*r == 0u32);
}

#[trust_vc::ensures(true)]
fn rust_default_arc_u32_constructor_verified() {
    let a: Arc<u32> = Arc::default();
    trust_vc::assert!(*a == 0u32);
}

#[trust_vc::ensures(true)]
fn rust_default_box_custom_type_constructor_verified() {
    let b: Box<DefaultTraitSmartPtrRecord> = Box::default();
    trust_vc::assert!((*b).x == 0u32);
    trust_vc::assert!((*b).y == 0u32);
}

#[trust_vc::ensures(true)]
fn rust_default_rc_custom_type_constructor_verified() {
    let r: Rc<DefaultTraitSmartPtrRecord> = Rc::default();
    trust_vc::assert!((*r).x == 0u32);
    trust_vc::assert!((*r).y == 0u32);
}

#[trust_vc::ensures(true)]
fn rust_default_arc_custom_type_constructor_verified() {
    let a: Arc<DefaultTraitSmartPtrRecord> = Arc::default();
    trust_vc::assert!((*a).x == 0u32);
    trust_vc::assert!((*a).y == 0u32);
}

#[trust_vc::ensures(true)]
fn rust_default_phantom_constructor_verified() {
    let p: PhantomData<u32> = PhantomData::default();
    trust_vc::assert!(p == PhantomData::<u32>);
}

// Two calls of `T::default()` are one term of the trait's function symbol, so
// the lane proved them equal. A `Default` impl can read a counter, so the two
// values can differ at run time and the `Verified` answer is refused
// (`bodiless call repeated`).
#[trust_vc::ensures(true)]
fn rust_default_generic_instantiation_verified<T: Default + PartialEq>() {
    trust_vc::assert!(T::default() == T::default());
}

// ---------------------------------------------------------------------------
// Liar twins of the constructors re-pinned `verified` on 2026-09-13. Each is
// the SAME shape with a false claim; each is refuted with a model, which is
// what proves the model is read rather than assumed.
// ---------------------------------------------------------------------------

#[trust_vc::ensures(result == 1u32)]
fn rust_default_trait_inference_wrong_counterexample() -> u32 {
    Default::default()
}

#[trust_vc::ensures(true)]
fn rust_default_str_associated_constructor_wrong_counterexample() {
    let value: &'static str = <&'static str>::default();
    trust_vc::assert!(value == "a");
}

#[trust_vc::ensures(true)]
fn rust_default_string_constructor_wrong_counterexample() {
    let s: String = String::default();
    trust_vc::assert!(s.view().len() == 1usize);
}

#[trust_vc::ensures(true)]
fn rust_default_vec_deque_constructor_wrong_counterexample() {
    let v: VecDeque<u32> = VecDeque::default();
    trust_vc::assert!(v.view().len() == 1usize);
}

#[trust_vc::ensures(true)]
fn rust_default_box_u32_constructor_wrong_counterexample() {
    let b: Box<u32> = Box::default();
    trust_vc::assert!(*b == 1u32);
}

#[trust_vc::ensures(true)]
fn rust_default_box_vec_u32_constructor_wrong_counterexample() {
    let b: Box<Vec<u32>> = Box::default();
    let v: Vec<u32> = *b;
    trust_vc::assert!(v.view().len() == 1usize);
}

#[trust_vc::ensures(true)]
fn rust_default_rc_u32_constructor_wrong_counterexample() {
    let r: Rc<u32> = Rc::default();
    trust_vc::assert!(*r == 1u32);
}

#[trust_vc::ensures(true)]
fn rust_default_arc_u32_constructor_wrong_counterexample() {
    let a: Arc<u32> = Arc::default();
    trust_vc::assert!(*a == 1u32);
}

#[trust_vc::ensures(true)]
fn rust_default_box_custom_type_constructor_wrong_counterexample() {
    let b: Box<DefaultTraitSmartPtrRecord> = Box::default();
    trust_vc::assert!((*b).x == 1u32);
}

#[trust_vc::ensures(true)]
fn rust_default_phantom_constructor_wrong_counterexample() {
    let p: PhantomData<u32> = PhantomData::default();
    trust_vc::assert!(p != PhantomData::<u32>);
}

#[trust_vc::ensures(true)]
fn rust_default_generic_instantiation_wrong_counterexample<T: Default + PartialEq>() {
    trust_vc::assert!(T::default() != T::default());
}

// ---------------------------------------------------------------------------
// Upstream `test_default_ok!` / `test_default_fail!` macro family, VERBATIM:
// `let a = <{ty}>::default(); let b: {ty} = Default::default(); let c = <{ty}
// as core::default::Default>::default();` then the three equalities, and the
// `_wrong` twins `let x = <{ty}>::default(); assert(x == {wrong})`.
// ---------------------------------------------------------------------------

#[trust_vc::ensures(true)]
fn upstream_test_default_u32_ok_verified() {
    let a = <u32>::default();
    let b: u32 = Default::default();
    let c = <u32 as core::default::Default>::default();
    trust_vc::assert!(a == 0u32);
    trust_vc::assert!(b == 0u32);
    trust_vc::assert!(c == 0u32);
}

#[trust_vc::ensures(true)]
fn upstream_test_default_u32_wrong_counterexample() {
    let x = <u32>::default();
    trust_vc::assert!(x == 1u32);
}

#[trust_vc::ensures(true)]
fn upstream_test_default_bool_ok_verified() {
    let a = <bool>::default();
    let b: bool = Default::default();
    let c = <bool as core::default::Default>::default();
    trust_vc::assert!(a == false);
    trust_vc::assert!(b == false);
    trust_vc::assert!(c == false);
}

#[trust_vc::ensures(true)]
fn upstream_test_default_bool_wrong_counterexample() {
    let x = <bool>::default();
    trust_vc::assert!(x == true);
}

#[trust_vc::ensures(true)]
fn upstream_test_default_f32_ok_verified() {
    let a = <f32>::default();
    let b: f32 = Default::default();
    let c = <f32 as core::default::Default>::default();
    trust_vc::assert!(a == 0.0f32);
    trust_vc::assert!(b == 0.0f32);
    trust_vc::assert!(c == 0.0f32);
}

#[trust_vc::ensures(true)]
fn upstream_test_default_f64_ok_verified() {
    let a = <f64>::default();
    let b: f64 = Default::default();
    let c = <f64 as core::default::Default>::default();
    trust_vc::assert!(a == 0.0f64);
    trust_vc::assert!(b == 0.0f64);
    trust_vc::assert!(c == 0.0f64);
}

// The float liar: `x != 0.0f64` on the inference spelling is refuted with a
// model (the `x == 1.0f64` shape comes back `NotProved (incomplete)` from the
// Real lane — fail-closed, never Verified — and is not inventoried).
#[trust_vc::ensures(true)]
fn upstream_test_default_f64_wrong_counterexample() {
    let x: f64 = Default::default();
    trust_vc::assert!(x != 0.0f64);
}

#[trust_vc::ensures(true)]
fn upstream_test_default_str_ok_verified() {
    let a = <&'static str>::default();
    let b: &'static str = Default::default();
    let c = <&'static str as core::default::Default>::default();
    trust_vc::assert!(a == "");
    trust_vc::assert!(b == "");
    trust_vc::assert!(c == "");
}

#[trust_vc::ensures(true)]
fn upstream_test_default_option_u32_ok_verified() {
    let a = <Option<u32>>::default();
    let b: Option<u32> = Default::default();
    let c = <Option<u32> as core::default::Default>::default();
    trust_vc::assert!(a == Option::<u32>::None);
    trust_vc::assert!(b == Option::<u32>::None);
    trust_vc::assert!(c == Option::<u32>::None);
}

#[trust_vc::ensures(true)]
fn upstream_test_default_option_u32_wrong_counterexample() {
    let x: Option<u32> = Default::default();
    trust_vc::assert!(x == Some(0u32));
}

#[trust_vc::ensures(true)]
fn upstream_test_default_phantom_ok_verified() {
    let a = <core::marker::PhantomData<u32>>::default();
    let b: core::marker::PhantomData<u32> = Default::default();
    let c = <core::marker::PhantomData<u32> as core::default::Default>::default();
    trust_vc::assert!(a == core::marker::PhantomData::<u32>);
    trust_vc::assert!(b == core::marker::PhantomData::<u32>);
    trust_vc::assert!(c == core::marker::PhantomData::<u32>);
}

#[trust_vc::ensures(true)]
fn upstream_test_default_tuple2_ok_verified() {
    let a = <(u32, bool)>::default();
    let b: (u32, bool) = Default::default();
    let c = <(u32, bool) as core::default::Default>::default();
    trust_vc::assert!(a == (0u32, false));
    trust_vc::assert!(b == (0u32, false));
    trust_vc::assert!(c == (0u32, false));
}

#[trust_vc::ensures(true)]
fn upstream_test_default_tuple2_wrong_counterexample() {
    let x: (u32, bool) = Default::default();
    trust_vc::assert!(x.1 == true);
}

#[trust_vc::ensures(true)]
fn upstream_test_default_tuple3_ok_verified() {
    let a = <(u32, bool, char)>::default();
    let b: (u32, bool, char) = Default::default();
    let c = <(u32, bool, char) as core::default::Default>::default();
    trust_vc::assert!(a == (0u32, false, '\0'));
    trust_vc::assert!(b == (0u32, false, '\0'));
    trust_vc::assert!(c == (0u32, false, '\0'));
}

#[trust_vc::ensures(true)]
fn upstream_test_default_tuple3_wrong_counterexample() {
    let x = <(u32, bool, char)>::default();
    trust_vc::assert!(x.2 == 'a');
}

// ---------------------------------------------------------------------------
// Upstream `test_default_custom_type_spec` (a hand-written `impl Default` with
// an `ensures`, an `mk` that relays it, and a caller of `mk`) and
// `test_default_custom_type_ensures_in_smart_ptrs` (the custom default behind
// `Box` / `Rc` / `Arc`, `x = 7, y = 8`, `r.y == r.x + 1`, `r.x < 100`).
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
struct DefaultTraitMyType {
    x: u32,
    y: bool,
}

impl Default for DefaultTraitMyType {
    #[trust_vc::ensures(result.x == 10u32)]
    #[trust_vc::ensures(result.y == true)]
    fn default() -> DefaultTraitMyType {
        DefaultTraitMyType { x: 10u32, y: true }
    }
}

#[trust_vc::ensures(result.x == 10u32)]
#[trust_vc::ensures(result.y == true)]
fn rust_default_custom_type_spec_mk_verified() -> DefaultTraitMyType {
    DefaultTraitMyType::default()
}

#[trust_vc::ensures(true)]
fn rust_default_custom_type_spec_test_verified() {
    let v = rust_default_custom_type_spec_mk_verified();
    trust_vc::assert!(v.x == 10u32);
    trust_vc::assert!(v.y == true);
}

#[trust_vc::ensures(true)]
fn rust_default_custom_type_spec_wrong_counterexample() {
    let v = DefaultTraitMyType::default();
    trust_vc::assert!(v.x == 11u32);
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct DefaultTraitPointee {
    x: u32,
    y: u32,
}

impl Default for DefaultTraitPointee {
    #[trust_vc::ensures(result.y == result.x + 1u32)]
    #[trust_vc::ensures(result.x < 100u32)]
    fn default() -> DefaultTraitPointee {
        DefaultTraitPointee { x: 7u32, y: 8u32 }
    }
}

#[trust_vc::ensures(true)]
fn rust_default_custom_type_ensures_in_smart_ptrs_verified() {
    let b: Box<DefaultTraitPointee> = Box::default();
    trust_vc::assert!((*b).y == (*b).x + 1u32);
    trust_vc::assert!((*b).x < 100u32);

    let r: Rc<DefaultTraitPointee> = Rc::default();
    trust_vc::assert!((*r).y == (*r).x + 1u32);
    trust_vc::assert!((*r).x < 100u32);

    let a: Arc<DefaultTraitPointee> = Arc::default();
    trust_vc::assert!((*a).y == (*a).x + 1u32);
    trust_vc::assert!((*a).x < 100u32);
}

#[trust_vc::ensures(true)]
fn rust_default_custom_type_ensures_in_smart_ptrs_wrong_counterexample() {
    let a: Arc<DefaultTraitPointee> = Arc::default();
    trust_vc::assert!((*a).y == (*a).x);
}

// ---------------------------------------------------------------------------
// Still fail-closed, with precise fragments.
// ---------------------------------------------------------------------------

// Upstream `test_default_generic_instantiation` writes `fn mk<T: Default>() ->
// (r: T) ensures T::default.ensures((), r) { T::default() }` — a closure-
// reflection contract on a TRAIT function. The native surface's reflection
// (`call_ensures(f, args, r)`) is defined for closure values and `Fn`-bound
// parameters, not for a trait method of a type parameter, so the contract
// fails closed.
#[trust_vc::ensures(trust_vc::call_ensures(T::default, (), result))]
fn rust_default_generic_mk_reflection_currently_blocked<T: Default>() -> T {
    T::default()
}

// Upstream `test_default_string_ok` also asserts `a.is_ascii()`; the string
// method is not modelled.
#[trust_vc::ensures(true)]
fn rust_default_string_is_ascii_currently_blocked() {
    let a = String::default();
    trust_vc::assert!(a.view().len() == 0usize);
    trust_vc::assert!(a.is_ascii());
}
