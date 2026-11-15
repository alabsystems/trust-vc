// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN (default_trait.rs, 2026-09-13): type-directed lowering of
//! the `Default::default()` constructor family. Upstream exercises THREE
//! spellings per type — `<Ty>::default()`, `let b: Ty = Default::default()`
//! (inference from the declared type) and `<Ty as core::default::Default>::
//! default()` (UFCS) — over primitives, `&str`, `Option`, `PhantomData`,
//! tuples, `String`, `Vec`/`VecDeque`, `Box`/`Rc`/`Arc`, a generic `T` and a
//! user type with its own `impl Default`. Every model is pinned in BOTH
//! directions: the `_ok` equality verifies and the `_wrong` twin (the same
//! shape with a false claim) is refuted with a model.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_dflt_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
    let _ = std::fs::remove_file(&p);
    result
}

const SRC: &str = r#"
#![allow(dead_code)]
use std::collections::{HashMap, HashSet, VecDeque};
use std::marker::PhantomData;
use std::rc::Rc;
use std::sync::Arc;
use trust_vc_types::View;

// ---- u32: the three upstream spellings, one function (upstream shape) ----
#[trust_vc::ensures(true)]
fn u32_three_spellings_ok() {
    let a = <u32>::default();
    let b: u32 = Default::default();
    let c = <u32 as core::default::Default>::default();
    trust_vc::assert!(a == 0u32);
    trust_vc::assert!(b == 0u32);
    trust_vc::assert!(c == 0u32);
}

#[trust_vc::ensures(true)]
fn u32_qself_wrong() {
    let x = <u32>::default();
    trust_vc::assert!(x == 1u32);
}

#[trust_vc::ensures(true)]
fn u32_inference_wrong() {
    let x: u32 = Default::default();
    trust_vc::assert!(x == 1u32);
}

#[trust_vc::ensures(true)]
fn u32_ufcs_wrong() {
    let x = <u32 as core::default::Default>::default();
    trust_vc::assert!(x == 1u32);
}

// ---- inference from the RETURN type (port shape) ----
#[trust_vc::ensures(result == 0u32)]
fn u32_return_inference_ok() -> u32 {
    Default::default()
}

#[trust_vc::ensures(result == 1u32)]
fn u32_return_inference_wrong() -> u32 {
    Default::default()
}

// ---- bool ----
#[trust_vc::ensures(true)]
fn bool_three_spellings_ok() {
    let a = <bool>::default();
    let b: bool = Default::default();
    let c = <bool as core::default::Default>::default();
    trust_vc::assert!(a == false);
    trust_vc::assert!(b == false);
    trust_vc::assert!(c == false);
}

#[trust_vc::ensures(true)]
fn bool_inference_wrong() {
    let x: bool = Default::default();
    trust_vc::assert!(x == true);
}

// ---- f32 / f64 ----
#[trust_vc::ensures(true)]
fn f32_three_spellings_ok() {
    let a = <f32>::default();
    let b: f32 = Default::default();
    let c = <f32 as core::default::Default>::default();
    trust_vc::assert!(a == 0.0f32);
    trust_vc::assert!(b == 0.0f32);
    trust_vc::assert!(c == 0.0f32);
}

#[trust_vc::ensures(true)]
fn f64_three_spellings_ok() {
    let a = <f64>::default();
    let b: f64 = Default::default();
    let c = <f64 as core::default::Default>::default();
    trust_vc::assert!(a == 0.0f64);
    trust_vc::assert!(b == 0.0f64);
    trust_vc::assert!(c == 0.0f64);
}

#[trust_vc::ensures(true)]
fn f64_inference_wrong() {
    let x: f64 = Default::default();
    trust_vc::assert!(x == 1.0f64);
}

#[trust_vc::ensures(true)]
fn f64_inference_wrong_ne() {
    let x: f64 = Default::default();
    trust_vc::assert!(x != 0.0f64);
}

#[trust_vc::ensures(true)]
fn f64_literal_wrong_direct() {
    let x = 0.0f64;
    trust_vc::assert!(x == 1.0f64);
}

// ---- &'static str ----
#[trust_vc::ensures(true)]
fn str_three_spellings_ok() {
    let a = <&'static str>::default();
    let b: &'static str = Default::default();
    let c = <&'static str as core::default::Default>::default();
    trust_vc::assert!(a == "");
    trust_vc::assert!(b == "");
    trust_vc::assert!(c == "");
}

#[trust_vc::ensures(true)]
fn str_qself_wrong() {
    let x = <&'static str>::default();
    trust_vc::assert!(x == "a");
}

// ---- Option<u32> ----
#[trust_vc::ensures(true)]
fn option_three_spellings_ok() {
    let a = <Option<u32>>::default();
    let b: Option<u32> = Default::default();
    let c = <Option<u32> as core::default::Default>::default();
    trust_vc::assert!(a == Option::<u32>::None);
    trust_vc::assert!(b == Option::<u32>::None);
    trust_vc::assert!(c == Option::<u32>::None);
}

#[trust_vc::ensures(true)]
fn option_inference_wrong() {
    let x: Option<u32> = Default::default();
    trust_vc::assert!(x == Some(0u32));
}

// ---- PhantomData<u32> ----
#[trust_vc::ensures(true)]
fn phantom_three_spellings_ok() {
    let a = <core::marker::PhantomData<u32>>::default();
    let b: core::marker::PhantomData<u32> = Default::default();
    let c = <core::marker::PhantomData<u32> as core::default::Default>::default();
    trust_vc::assert!(a == core::marker::PhantomData::<u32>);
    trust_vc::assert!(b == core::marker::PhantomData::<u32>);
    trust_vc::assert!(c == core::marker::PhantomData::<u32>);
}

#[trust_vc::ensures(true)]
fn phantom_receiver_ok() {
    let p: PhantomData<u32> = PhantomData::default();
    trust_vc::assert!(p == PhantomData::<u32>);
}

#[trust_vc::ensures(true)]
fn phantom_inference_wrong() {
    let p: PhantomData<u32> = Default::default();
    trust_vc::assert!(p != PhantomData::<u32>);
}

// ---- tuples ----
#[trust_vc::ensures(true)]
fn tuple2_three_spellings_ok() {
    let a = <(u32, bool)>::default();
    let b: (u32, bool) = Default::default();
    let c = <(u32, bool) as core::default::Default>::default();
    trust_vc::assert!(a == (0u32, false));
    trust_vc::assert!(b == (0u32, false));
    trust_vc::assert!(c == (0u32, false));
}

#[trust_vc::ensures(true)]
fn tuple3_three_spellings_ok() {
    let a = <(u32, bool, char)>::default();
    let b: (u32, bool, char) = Default::default();
    let c = <(u32, bool, char) as core::default::Default>::default();
    trust_vc::assert!(a == (0u32, false, '\0'));
    trust_vc::assert!(b == (0u32, false, '\0'));
    trust_vc::assert!(c == (0u32, false, '\0'));
}

#[trust_vc::ensures(true)]
fn tuple2_inference_wrong() {
    let x: (u32, bool) = Default::default();
    trust_vc::assert!(x.1 == true);
}

#[trust_vc::ensures(true)]
fn tuple3_qself_wrong() {
    let x = <(u32, bool, char)>::default();
    trust_vc::assert!(x.2 == 'a');
}

// ---- String ----
#[trust_vc::ensures(true)]
fn string_receiver_ok() {
    let a = String::default();
    trust_vc::assert!(a.view().len() == 0usize);
}

#[trust_vc::ensures(true)]
fn string_inference_ok() {
    let a: String = Default::default();
    trust_vc::assert!(a.view().len() == 0usize);
}

#[trust_vc::ensures(true)]
fn string_receiver_wrong() {
    let a = String::default();
    trust_vc::assert!(a.view().len() == 1usize);
}

// CONTROL (the constructor the default is modelled as): `String::new()` is
// the empty string.
#[trust_vc::ensures(true)]
fn string_new_ok() {
    let a = String::new();
    trust_vc::assert!(a.view().len() == 0usize);
}

#[trust_vc::ensures(true)]
fn string_new_wrong() {
    let a = String::new();
    trust_vc::assert!(a.view().len() == 2usize);
}

// ---- Vec / VecDeque / HashMap / HashSet ----
#[trust_vc::ensures(true)]
fn vec_receiver_ok() {
    let v: Vec<u32> = Vec::default();
    trust_vc::assert!(v.view().len() == 0usize);
}

#[trust_vc::ensures(true)]
fn vec_turbofish_ok() {
    let v = Vec::<u32>::default();
    trust_vc::assert!(v.view().len() == 0usize);
}

#[trust_vc::ensures(true)]
fn vec_inference_ok() {
    let v: Vec<u32> = Default::default();
    trust_vc::assert!(v.view().len() == 0usize);
}

#[trust_vc::ensures(true)]
fn vec_receiver_wrong() {
    let v: Vec<u32> = Vec::default();
    trust_vc::assert!(v.view().len() == 1usize);
}

#[trust_vc::ensures(true)]
fn vec_deque_receiver_ok() {
    let v: VecDeque<u32> = VecDeque::default();
    trust_vc::assert!(v.view().len() == 0usize);
}

#[trust_vc::ensures(true)]
fn vec_deque_receiver_wrong() {
    let v: VecDeque<u32> = VecDeque::default();
    trust_vc::assert!(v.view().len() == 1usize);
}

#[trust_vc::ensures(true)]
fn hash_map_receiver_ok() {
    let m: HashMap<u32, u32> = HashMap::default();
    trust_vc::assert!(m.view().len() == 0usize);
}

#[trust_vc::ensures(true)]
fn hash_map_receiver_wrong() {
    let m: HashMap<u32, u32> = HashMap::default();
    trust_vc::assert!(m.view().len() == 1usize);
}

#[trust_vc::ensures(true)]
fn hash_set_inference_ok() {
    let s: HashSet<u32> = Default::default();
    trust_vc::assert!(s.view().len() == 0usize);
}

// ---- Box / Rc / Arc ----
#[trust_vc::ensures(true)]
fn box_u32_receiver_ok() {
    let b: Box<u32> = Box::default();
    trust_vc::assert!(*b == 0u32);
}

#[trust_vc::ensures(true)]
fn box_u32_receiver_wrong() {
    let b: Box<u32> = Box::default();
    trust_vc::assert!(*b == 1u32);
}

#[trust_vc::ensures(true)]
fn box_u32_inference_ok() {
    let b: Box<u32> = Default::default();
    trust_vc::assert!(*b == 0u32);
}

#[trust_vc::ensures(true)]
fn box_vec_u32_receiver_ok() {
    let b: Box<Vec<u32>> = Box::default();
    let v: Vec<u32> = *b;
    trust_vc::assert!(v.view().len() == 0usize);
}

#[trust_vc::ensures(true)]
fn box_vec_u32_receiver_wrong() {
    let b: Box<Vec<u32>> = Box::default();
    let v: Vec<u32> = *b;
    trust_vc::assert!(v.view().len() == 1usize);
}

#[trust_vc::ensures(true)]
fn rc_u32_receiver_ok() {
    let r: Rc<u32> = Rc::default();
    trust_vc::assert!(*r == 0u32);
}

#[trust_vc::ensures(true)]
fn rc_u32_receiver_wrong() {
    let r: Rc<u32> = Rc::default();
    trust_vc::assert!(*r == 1u32);
}

#[trust_vc::ensures(true)]
fn arc_u32_receiver_ok() {
    let a: Arc<u32> = Arc::default();
    trust_vc::assert!(*a == 0u32);
}

#[trust_vc::ensures(true)]
fn arc_u32_receiver_wrong() {
    let a: Arc<u32> = Arc::default();
    trust_vc::assert!(*a == 1u32);
}

// ---- arithmetic on a default ----
#[trust_vc::ensures(true)]
fn arithmetic_ok() {
    let x = u32::default();
    let y = x + 5u32;
    trust_vc::assert!(y == 5u32);
}

#[trust_vc::ensures(true)]
fn arithmetic_wrong() {
    let x = u32::default();
    let y = x + 5u32;
    trust_vc::assert!(y == 6u32);
}

// ---- generic instantiation: two calls of `T::default()` ----
// A `Default` impl can read a counter, so the two calls need not be equal and
// the congruence is refused; the false twin is still refuted.
#[trust_vc::ensures(true)]
fn generic_congruence_ok<T: Default + PartialEq>() {
    trust_vc::assert!(T::default() == T::default());
}

#[trust_vc::ensures(true)]
fn generic_congruence_wrong<T: Default + PartialEq>() {
    trust_vc::assert!(T::default() != T::default());
}

// ---- custom types ----
#[derive(Default, PartialEq, Eq, Clone, Copy)]
struct Derived {
    x: u32,
    y: bool,
}

#[trust_vc::ensures(true)]
fn derived_receiver_ok() {
    let v = Derived::default();
    trust_vc::assert!(v.x == 0u32);
    trust_vc::assert!(v.y == false);
}

#[trust_vc::ensures(true)]
fn derived_receiver_wrong() {
    let v = Derived::default();
    trust_vc::assert!(v.x == 1u32);
}

#[trust_vc::ensures(true)]
fn derived_inference_ok() {
    let v: Derived = Default::default();
    trust_vc::assert!(v.x == 0u32);
    trust_vc::assert!(v.y == false);
}

#[derive(PartialEq, Eq, Clone, Copy)]
struct MyType {
    x: u32,
    y: bool,
}

impl Default for MyType {
    fn default() -> MyType {
        MyType { x: 10u32, y: true }
    }
}

#[trust_vc::ensures(true)]
fn manual_impl_receiver_ok() {
    let v = MyType::default();
    trust_vc::assert!(v.x == 10u32);
    trust_vc::assert!(v.y == true);
}

#[trust_vc::ensures(true)]
fn manual_impl_receiver_wrong() {
    let v = MyType::default();
    trust_vc::assert!(v.x == 11u32);
}

#[trust_vc::ensures(true)]
fn manual_impl_inference_ok() {
    let v: MyType = Default::default();
    trust_vc::assert!(v.x == 10u32);
}

#[trust_vc::ensures(true)]
fn manual_impl_ufcs_ok() {
    let v = <MyType as core::default::Default>::default();
    trust_vc::assert!(v.x == 10u32);
}

#[trust_vc::ensures(result.x == 10u32)]
#[trust_vc::ensures(result.y == true)]
fn manual_impl_mk_ok() -> MyType {
    MyType::default()
}

// ---- custom default behind smart pointers (upstream shape: x=7, y=8) ----
#[derive(PartialEq, Eq, Clone, Copy)]
struct Pointee {
    x: u32,
    y: u32,
}

impl Default for Pointee {
    fn default() -> Pointee {
        Pointee { x: 7u32, y: 8u32 }
    }
}

#[trust_vc::ensures(true)]
fn box_custom_ok() {
    let b: Box<Pointee> = Box::default();
    trust_vc::assert!((*b).y == (*b).x + 1u32);
    trust_vc::assert!((*b).x < 100u32);
}

#[trust_vc::ensures(true)]
fn box_custom_wrong() {
    let b: Box<Pointee> = Box::default();
    trust_vc::assert!((*b).x == 1u32);
}

#[trust_vc::ensures(true)]
fn rc_custom_ok() {
    let r: Rc<Pointee> = Rc::default();
    trust_vc::assert!((*r).y == (*r).x + 1u32);
    trust_vc::assert!((*r).x < 100u32);
}

#[trust_vc::ensures(true)]
fn arc_custom_ok() {
    let a: Arc<Pointee> = Arc::default();
    trust_vc::assert!((*a).y == (*a).x + 1u32);
    trust_vc::assert!((*a).x < 100u32);
}

#[trust_vc::ensures(true)]
fn arc_custom_wrong() {
    let a: Arc<Pointee> = Arc::default();
    trust_vc::assert!((*a).y == (*a).x);
}

// ---- derived struct behind Box (port shape: x == 0, y == 0) ----
#[derive(Default, PartialEq, Eq, Clone, Copy)]
struct DerivedPair {
    x: u32,
    y: u32,
}

#[trust_vc::ensures(true)]
fn box_derived_ok() {
    let b: Box<DerivedPair> = Box::default();
    trust_vc::assert!((*b).x == 0u32);
    trust_vc::assert!((*b).y == 0u32);
}

#[trust_vc::ensures(true)]
fn box_derived_wrong() {
    let b: Box<DerivedPair> = Box::default();
    trust_vc::assert!((*b).x == 1u32);
}

// FAIL CLOSED: a manual impl whose body is NOT a single pure constructor
// expression gets NO body axiom (the same gate every inherent body axiom has),
// so the call is an opaque value and the claim is refuted — never Verified
// against the constructor that happens to appear first in the body.
struct Opaque {
    x: u32,
}

impl Default for Opaque {
    fn default() -> Opaque {
        let mut v = Opaque { x: 0u32 };
        v.x = 3u32;
        v
    }
}

#[trust_vc::ensures(true)]
fn manual_impl_non_constructor_body_must_not_verify() {
    let v = Opaque::default();
    trust_vc::assert!(v.x == 0u32);
}
"#;

fn expect_verified(id: &str, func: &str) {
    match verify(id, func, SRC) {
        VerifyResult::Verified => {}
        other => panic!("{func}: expected Verified, got {other:?}"),
    }
}

fn expect_counterexample(id: &str, func: &str) {
    match verify(id, func, SRC) {
        VerifyResult::Counterexample { .. } => {}
        other => panic!("{func}: expected Counterexample, got {other:?}"),
    }
}

fn expect_refused(id: &str, func: &str) {
    match verify(id, func, SRC) {
        VerifyResult::Error { message } if message.starts_with("bodiless call repeated") => {}
        other => panic!("{func}: must be refused as a repeated call, got {other:?}"),
    }
}

fn expect_not_verified(id: &str, func: &str) {
    match verify(id, func, SRC) {
        VerifyResult::Verified => panic!("{func}: must NOT verify"),
        VerifyResult::Unknown { reason, .. } => {
            panic!("{func}: solver Unknown is not stable evidence: {reason}")
        }
        _ => {}
    }
}

macro_rules! pin {
    ($test:ident, verified, $id:literal, $func:literal) => {
        #[test]
        fn $test() {
            expect_verified($id, $func);
        }
    };
    ($test:ident, counterexample, $id:literal, $func:literal) => {
        #[test]
        fn $test() {
            expect_counterexample($id, $func);
        }
    };
    ($test:ident, refused, $id:literal, $func:literal) => {
        #[test]
        fn $test() {
            expect_refused($id, $func);
        }
    };
    ($test:ident, not_verified, $id:literal, $func:literal) => {
        #[test]
        fn $test() {
            expect_not_verified($id, $func);
        }
    };
}

pin!(
    control_u32_three_spellings,
    verified,
    "u1",
    "u32_three_spellings_ok"
);
pin!(liar_u32_qself, counterexample, "u2", "u32_qself_wrong");
pin!(
    liar_u32_inference,
    counterexample,
    "u3",
    "u32_inference_wrong"
);
pin!(liar_u32_ufcs, counterexample, "u4", "u32_ufcs_wrong");
pin!(
    control_u32_return_inference,
    verified,
    "u5",
    "u32_return_inference_ok"
);
pin!(
    liar_u32_return_inference,
    counterexample,
    "u6",
    "u32_return_inference_wrong"
);

pin!(
    control_bool_three_spellings,
    verified,
    "b1",
    "bool_three_spellings_ok"
);
pin!(
    liar_bool_inference,
    counterexample,
    "b2",
    "bool_inference_wrong"
);

pin!(
    control_f32_three_spellings,
    verified,
    "f1",
    "f32_three_spellings_ok"
);
pin!(
    control_f64_three_spellings,
    verified,
    "f2",
    "f64_three_spellings_ok"
);
// MEASURED (ay 0.26.0@0dc8f8f0b): the `x == 1.0f64` liar on the inference
// spelling comes back `NotProved (incomplete)` from the Real lane — fail
// closed, never Verified — while the same claim on a direct `0.0f64` literal
// and the `x != 0.0f64` liar on the inference spelling are both refuted with a
// model. The refuted `!=` twin is the liar that pins the float model; the
// `== 1.0` shape is pinned as not-verified so a future false Verified fails.
pin!(
    liar_f64_inference_eq_one_stays_unverified,
    not_verified,
    "f3",
    "f64_inference_wrong"
);
pin!(
    liar_f64_inference_ne,
    counterexample,
    "f4",
    "f64_inference_wrong_ne"
);
pin!(
    liar_f64_literal_direct,
    counterexample,
    "f6",
    "f64_literal_wrong_direct"
);
pin!(control_string_new, verified, "g4", "string_new_ok");
pin!(liar_string_new, counterexample, "g5", "string_new_wrong");

pin!(
    control_str_three_spellings,
    verified,
    "s1",
    "str_three_spellings_ok"
);
pin!(liar_str_qself, counterexample, "s2", "str_qself_wrong");

pin!(
    control_option_three_spellings,
    verified,
    "o1",
    "option_three_spellings_ok"
);
pin!(
    liar_option_inference,
    counterexample,
    "o2",
    "option_inference_wrong"
);

pin!(
    control_phantom_three_spellings,
    verified,
    "p1",
    "phantom_three_spellings_ok"
);
pin!(
    control_phantom_receiver,
    verified,
    "p2",
    "phantom_receiver_ok"
);
pin!(
    liar_phantom_inference,
    counterexample,
    "p3",
    "phantom_inference_wrong"
);

pin!(
    control_tuple2_three_spellings,
    verified,
    "t1",
    "tuple2_three_spellings_ok"
);
pin!(
    control_tuple3_three_spellings,
    verified,
    "t2",
    "tuple3_three_spellings_ok"
);
pin!(
    liar_tuple2_inference,
    counterexample,
    "t3",
    "tuple2_inference_wrong"
);
pin!(
    liar_tuple3_qself,
    counterexample,
    "t4",
    "tuple3_qself_wrong"
);

pin!(
    control_string_receiver,
    verified,
    "g1",
    "string_receiver_ok"
);
pin!(
    control_string_inference,
    verified,
    "g2",
    "string_inference_ok"
);
pin!(
    liar_string_receiver,
    counterexample,
    "g3",
    "string_receiver_wrong"
);

pin!(control_vec_receiver, verified, "v1", "vec_receiver_ok");
pin!(control_vec_turbofish, verified, "v2", "vec_turbofish_ok");
pin!(control_vec_inference, verified, "v3", "vec_inference_ok");
pin!(
    liar_vec_receiver,
    counterexample,
    "v4",
    "vec_receiver_wrong"
);
pin!(
    control_vec_deque_receiver,
    verified,
    "v5",
    "vec_deque_receiver_ok"
);
pin!(
    liar_vec_deque_receiver,
    counterexample,
    "v6",
    "vec_deque_receiver_wrong"
);
pin!(
    control_hash_map_receiver,
    verified,
    "v7",
    "hash_map_receiver_ok"
);
pin!(
    liar_hash_map_receiver,
    counterexample,
    "v8",
    "hash_map_receiver_wrong"
);
pin!(
    control_hash_set_inference,
    verified,
    "v9",
    "hash_set_inference_ok"
);

pin!(
    control_box_u32_receiver,
    verified,
    "x1",
    "box_u32_receiver_ok"
);
pin!(
    liar_box_u32_receiver,
    counterexample,
    "x2",
    "box_u32_receiver_wrong"
);
pin!(
    control_box_u32_inference,
    verified,
    "x3",
    "box_u32_inference_ok"
);
pin!(
    control_box_vec_u32_receiver,
    verified,
    "x4",
    "box_vec_u32_receiver_ok"
);
pin!(
    liar_box_vec_u32_receiver,
    counterexample,
    "x5",
    "box_vec_u32_receiver_wrong"
);
pin!(
    control_rc_u32_receiver,
    verified,
    "x6",
    "rc_u32_receiver_ok"
);
pin!(
    liar_rc_u32_receiver,
    counterexample,
    "x7",
    "rc_u32_receiver_wrong"
);
pin!(
    control_arc_u32_receiver,
    verified,
    "x8",
    "arc_u32_receiver_ok"
);
pin!(
    liar_arc_u32_receiver,
    counterexample,
    "x9",
    "arc_u32_receiver_wrong"
);

pin!(control_arithmetic, verified, "a1", "arithmetic_ok");
pin!(liar_arithmetic, counterexample, "a2", "arithmetic_wrong");

pin!(
    refused_generic_congruence,
    refused,
    "e1",
    "generic_congruence_ok"
);
pin!(
    liar_generic_congruence,
    counterexample,
    "e2",
    "generic_congruence_wrong"
);

pin!(
    control_derived_receiver,
    verified,
    "d1",
    "derived_receiver_ok"
);
pin!(
    liar_derived_receiver,
    counterexample,
    "d2",
    "derived_receiver_wrong"
);
pin!(
    control_derived_inference,
    verified,
    "d3",
    "derived_inference_ok"
);
pin!(
    control_manual_impl_receiver,
    verified,
    "m1",
    "manual_impl_receiver_ok"
);
pin!(
    liar_manual_impl_receiver,
    counterexample,
    "m2",
    "manual_impl_receiver_wrong"
);
pin!(
    control_manual_impl_inference,
    verified,
    "m3",
    "manual_impl_inference_ok"
);
pin!(
    control_manual_impl_ufcs,
    verified,
    "m4",
    "manual_impl_ufcs_ok"
);
pin!(control_manual_impl_mk, verified, "m5", "manual_impl_mk_ok");

pin!(control_box_custom, verified, "c1", "box_custom_ok");
pin!(liar_box_custom, counterexample, "c2", "box_custom_wrong");
pin!(control_rc_custom, verified, "c3", "rc_custom_ok");
pin!(control_arc_custom, verified, "c4", "arc_custom_ok");
pin!(liar_arc_custom, counterexample, "c5", "arc_custom_wrong");
pin!(control_box_derived, verified, "c6", "box_derived_ok");
pin!(liar_box_derived, counterexample, "c7", "box_derived_wrong");

pin!(
    fail_closed_manual_impl_non_constructor_body,
    counterexample,
    "z1",
    "manual_impl_non_constructor_body_must_not_verify"
);
