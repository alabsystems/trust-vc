// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! An unsuffixed literal bound by an unascribed `let` (or held in a tuple or
//! an array) takes the type its uses give it, which may be fixed far from
//! where it is evaluated: an assertion through a borrow or a capture, a
//! comparison, a copy, a nested call argument, a method argument, a return
//! value, a struct field, an element read. Read at its `i32` placeholder,
//! each overflow below was missed. Every `never_*` program compiles with
//! trustc under the default lints (or the `allow` it carries) and panics
//! natively; every `verified_*` twin runs clean. The groups whose cases came
//! back `Verified` on origin/main `7fa4db88` fail there.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

/// The binding's type is fixed by a use the assertion does not see.
const SRC_ASSERT_THROUGH_BINDING: &str = r####"
fn g8(x: u8) {}

fn g16(x: u16) {}

fn g32(x: u32) {}

fn gi8(x: i8) {}

fn id8(x: u8) -> u8 {
    x
}

fn ext(x: u8) -> u8 {
    x
}

struct B8 {
    g: u8,
}

struct S8 {
    x: u8,
}

fn never_assert_cond_through_borrow() {
    let a = 200;
    let r = &a;
    trust_vc::assert!(*r + 100 > 0);
    g8(a);
}

fn never_assert_cond_through_capture() {
    let a = 200;
    let f = || a;
    trust_vc::assert!(f() + 100 > 0);
    g8(a);
}

fn never_binding_typed_by_call_arg_used_in_assert() {
    let a = 200;
    let r = &a;
    let b = *r + 100 > 0;
    g8(a);
}

fn never_copy_chain_assert() {
    let a = 200;
    let b = a;
    let r = &b;
    trust_vc::assert!(*r + 100 > 0);
    g8(b);
}

fn never_struct_literal_field_assert() {
    let a = 200;
    let r = &a;
    let s = S8 { x: a };
    trust_vc::assert!(*r + 100 > 0);
}

fn never_method_arg_assert() {
    let a = 200;
    let r = &a;
    let mut v: Vec<u8> = Vec::new();
    trust_vc::assert!(*r + 100 > 0);
    v.push(a);
}

fn never_return_typed_assert() -> u8 {
    let a = 200;
    let r = &a;
    trust_vc::assert!(*r + 100 > 0);
    a
}

fn never_unresolved_call_assert() {
    let a = 200;
    let r = &a;
    trust_vc::assert!(*r + 100 > 0);
    let _z = ext(a);
}

fn never_if_cond_through_borrow() {
    let a = 200;
    let r = &a;
    if *r + 100 > 0 {}
    g8(a);
}

fn never_while_cond_through_borrow() {
    let a = 200;
    let r = &a;
    while *r + 100 == 0 {}
    g8(a);
}

fn verified_borrow_i32_assert() {
    let a = 200;
    let r = &a;
    trust_vc::assert!(*r + 100 == 300);
}
"####;

/// A panic-safety site whose slot types it: a nested call's parameter, a
/// method argument, a comparison peer, a return value, a later call.
const SRC_SITES: &str = r####"
fn g8(x: u8) {}

fn g16(x: u16) {}

fn g32(x: u32) {}

fn gi8(x: i8) {}

fn id8(x: u8) -> u8 {
    x
}

fn ext(x: u8) -> u8 {
    x
}

struct B8 {
    g: u8,
}

struct S8 {
    x: u8,
}

fn never_nested_call_arg() {
    let a = 200;
    let r = &a;
    g8(id8(*r + 100));
}

fn never_method_arg_typed() {
    let a = 200;
    let r = &a;
    let mut v: Vec<u8> = Vec::new();
    v.push(*r + 100);
}

fn never_two_level_borrow() {
    let a = 200;
    let r = &a;
    let q = &r;
    g8(**q + 100);
}

fn never_tuple_element_through_borrow() {
    let a = 200;
    let r = &a;
    let t: (u8, u8) = (*r + 100, 0);
}

fn never_struct_literal_through_capture_param() {
    let f = |k: u8| k + 100;
    let b = B8 { g: f(200) };
}

#[allow(arithmetic_overflow)]
fn never_shift_through_borrow() {
    let a = 1;
    let r = &a;
    g8(*r << 9);
}

fn never_div_zero_through_borrow() {
    let a = 0;
    let r = &a;
    g8(10 / *r);
}

fn never_i8_neg_through_borrow() {
    let a = 100;
    let r = &a;
    gi8(*r + 100);
}

fn never_if_tail_through_borrow(c: bool) {
    let a = 200;
    let r = &a;
    g8(if c { *r + 100 } else { 0 });
}

fn never_block_tail_through_borrow() {
    let a = 200;
    let r = &a;
    g8({ *r + 100 });
}

fn never_return_through_capture() -> u8 {
    let a = 200;
    let f = || a + 100;
    f()
}

#[allow(arithmetic_overflow)]
fn never_let_typed_by_later_call() {
    let a = 250 + 10;
    g8(a);
}

#[allow(arithmetic_overflow)]
fn never_allowed_nested() {
    g8((200 + 100) / 2);
}

fn verified_small_nested() {
    let a = 100;
    let r = &a;
    g8(*r + 100);
    let b = 100;
    let q = &b;
    g16(*q * 300);
    let c = 100;
    let p = &c;
    g32(*p * 1000);
}

fn verified_let_i32() {
    let a = 100 + 100;
    let b = 1000 * 1000;
}

fn verified_capture_typed_small() {
    let a = 100;
    let f = || a + 100;
    g8(f());
}

fn verified_let_typed_by_call() {
    let a = 100 + 100;
    g8(a);
}
"####;

/// Unsuffixed literals held in a tuple or an array, typed by the uses of
/// their elements.
const SRC_HOLDERS: &str = r####"
fn g8(x: u8) {}

fn g16(x: u16) {}

fn g32(x: u32) {}

fn gi8(x: i8) {}

fn id8(x: u8) -> u8 {
    x
}

fn ext(x: u8) -> u8 {
    x
}

struct B8 {
    g: u8,
}

struct S8 {
    x: u8,
}

fn never_tuple_holder_assert() {
    let t = (200, 1);
    let r = &t;
    trust_vc::assert!(r.0 + 100 > 0);
    g8(t.0);
}

fn never_array_holder_assert() {
    let a = [200, 1];
    let r = &a;
    trust_vc::assert!(r[0] + 100 > 0);
    g8(a[0]);
}

#[trust_vc::requires(i == 0usize)]
fn never_array_index_untyped_typed_later(i: usize) {
    let a = [200, 1];
    trust_vc::assert!(a[i] + 100 > 0);
    g8(a[0]);
}

fn never_array_holder_borrow_assert() {
    let a = [200, 1];
    let r = &a;
    trust_vc::assert!(r[0] + 100 > 0);
    g8(a[0]);
}

#[trust_vc::requires(i == 0usize)]
fn never_array_undetermined_read(i: usize) {
    let a = [200, 1];
    let r = &a;
    trust_vc::assert!(r[i] + 100 > 0);
    let _u = a.iter().map(|x| *x as u8).count();
    g8(a[0]);
}

#[trust_vc::requires(i == 0usize)]
fn verified_array_free(i: usize) {
    let a = [200, 1];
    trust_vc::assert!(a[i] + 100 == 300);
}

#[trust_vc::requires(i == 0usize)]
fn verified_array_typed_small(i: usize) {
    let a = [100, 1];
    trust_vc::assert!(a[i] + 100 == 200);
    g8(a[0]);
}

fn verified_tuple_free() {
    let t = (5, 6);
    trust_vc::assert!(t.0 + t.1 == 11);
}

fn true_tuple_small() {
    let t = (100, 1);
    let r = &t;
    trust_vc::assert!(r.0 + 100 > 0);
    g8(t.0);
}
"####;

fn verdict(r: &VerifyResult) -> &'static str {
    match r {
        VerifyResult::Verified => "Verified",
        VerifyResult::Counterexample { .. } => "Refuted",
        VerifyResult::NotProved { .. } => "NotProved",
        _ => "Unknown",
    }
}

fn run_source(src: &str, file: &str, func: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/untyped_literal_binding_soundness_src");
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let path = dir.join(file);
    let mut f = std::fs::File::create(&path).expect("create source");
    f.write_all(src.as_bytes()).expect("write source");
    drop(f);
    verify_function_from_file(path.to_str().expect("utf-8 path"), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    })
}

/// Every `never_*` case fails natively and must not be `Verified`; every
/// `verified_*` twin must stay `Verified`; a `true_*` case is true and must
/// not be refuted.
fn check(src: &str, file: &str, expected: usize) {
    let names: Vec<&str> = src
        .lines()
        .filter_map(|l| l.strip_prefix("fn "))
        .filter_map(|l| l.split('(').next())
        .filter(|n| {
            ["never_", "true_", "verified_"]
                .iter()
                .any(|prefix| n.starts_with(prefix))
        })
        .collect();
    assert_eq!(names.len(), expected, "case list truncated: {names:?}");
    let mut wrong = Vec::new();
    for func in names {
        let r = run_source(src, file, func);
        let got = verdict(&r);
        let raw: String = format!("{r:?}").chars().take(240).collect();
        println!("UNTYPED|{file}|{func}|{got}|{raw}");
        if func.starts_with("never_") && got == "Verified" {
            wrong.push(format!("FALSE VERIFIED {func}"));
        }
        if func.starts_with("true_") && got == "Refuted" {
            wrong.push(format!("TRUE CLAIM REFUTED {func}: {raw}"));
        }
        if func.starts_with("verified_") && got != "Verified" {
            wrong.push(format!("NOT VERIFIED {func}: {raw}"));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}

#[test]
fn a_binding_typed_by_a_use_the_assertion_does_not_see() {
    check(SRC_ASSERT_THROUGH_BINDING, "assert_through_binding.rs", 11);
}

#[test]
fn a_site_is_checked_at_the_slot_it_fills() {
    check(SRC_SITES, "sites.rs", 17);
}

#[test]
fn a_holder_of_untyped_literals_is_typed_by_its_elements() {
    check(SRC_HOLDERS, "holders.rs", 9);
}
