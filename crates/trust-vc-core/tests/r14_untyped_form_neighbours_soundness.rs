// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Round-14 neighbours of two verifier residuals on 923d432a, written while
//! reviewing the fix rather than taken from the verifier: an untyped literal
//! form reaching a typed slot through a borrow or a capture (`SRC_INT`), and
//! an unascribed binding whose type only a use elsewhere fixes, read through
//! a borrow into a constant form (`SRC_INT2`: `let a = 100;`, a use of `a` at
//! `u8`, `let r = &a; let q = *r + 200;`).
//!
//! Every `never_*` program compiles under trustc `-C overflow-checks=on`
//! with default lints and panics natively; every `verified_*` twin runs
//! clean.
//!
//! A = origin/main 3378cdfb: 0/2 pass, 29 `never_*` FALSE VERIFIED (`SRC_INT`
//! 10 of 20, `SRC_INT2` 19 of 19). B = this change: 2/2, every `never_*`
//! Refuted or Unknown, both twins Verified.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC_INT: &str = r####"
fn g8(x: u8) {}
fn gi8(x: i8) {}

struct B8 {
    g: u8,
}

fn never_double_borrow(y: u8) {
    let a = 200;
    let r = &&a;
    g8(**r + 100);
}

fn never_capture_plus_outside() {
    let a = 200;
    let f = || a;
    g8(f() + 100);
}


fn never_borrow_method_arg(y: u8) {
    let a = 200;
    let r = &a;
    let z = y.wrapping_add(*r + 100);
}


fn never_borrow_neg_i8() {
    let a = 100;
    let r = &a;
    gi8(-*r - 100);
}

fn never_borrow_vec_ascribed() {
    let a = 200;
    let r = &a;
    let v: Vec<u8> = vec![*r + 100];
}

fn never_borrow_array_ascribed() {
    let a = 200;
    let r = &a;
    let v: [u8; 1] = [*r + 100];
}

fn never_borrow_tuple_ascribed() {
    let a = 200;
    let r = &a;
    let t: (u8, u8) = (*r + 100, 0);
}

fn never_borrow_option_ascribed() {
    let a = 200;
    let r = &a;
    let o: Option<u8> = Some(*r + 100);
}

fn never_borrow_some_eq_peer(y: u8) {
    let a = 200;
    let r = &a;
    let b = Some(*r + 100) == Some(y);
}

fn never_borrow_if_arg(c: bool) {
    let a = 200;
    let r = &a;
    g8(if c { *r + 100 } else { 0 });
}

fn never_borrow_match_arg(c: bool) {
    let a = 200;
    let r = &a;
    g8(match c {
        true => *r + 100,
        false => 0,
    });
}

fn never_borrow_peer_add(y: u8) {
    let a = 200;
    let r = &a;
    let z = y + (*r + 100);
}

fn never_borrow_let_then_field() {
    let a = 200;
    let r = &a;
    let z = *r + 100;
    let b = B8 { g: z };
}

fn never_borrow_assign_typed(y: u8) {
    let a = 200;
    let r = &a;
    let mut z = y;
    z = *r + 100;
}

fn never_borrow_compound_typed(y: u8) {
    let a = 200;
    let r = &a;
    let mut z = y;
    z += *r + 100;
}

fn never_borrow_max_arg(y: u8) {
    let a = 200;
    let r = &a;
    let z = y.max(*r + 100);
}

fn never_capture_move_tuple() {
    let a = 200;
    let f = move || (a + 100, 0u8);
    let (p, q) = f();
    g8(p);
}

fn never_const_fn_return() -> u8 {
    let a = 200;
    let f = || a + 100;
    f()
}

fn never_borrow_through_fn_ref() {
    let a = 200;
    let r = &a;
    let h = g8;
    h(*r + 100);
}

fn never_borrow_generic_slot() {
    let a = 200;
    let r = &a;
    let v: Vec<u8> = Vec::new();
    let mut w = v;
    w.push(*r + 100);
}

fn verified_twin_borrow(y: u8) {
    let a = 20;
    let r = &a;
    g8(*r + 100);
}
"####;

const SRC_INT2: &str = r####"
fn g8(x: u8) {}

struct B8 {
    g: u8,
}

fn never_method_arg_types(y: u8) {
    let a = 100;
    let z = y.wrapping_add(a);
    let r = &a;
    let q = *r + 200;
}

fn never_vec_elem_types() {
    let a = 100;
    let v: Vec<u8> = vec![a];
    let r = &a;
    let q = *r + 200;
}

fn never_array_peer_types(y: u8) {
    let a = 100;
    let arr = [a, y];
    let r = &a;
    let q = *r + 200;
}

fn never_tuple_ascribed_types() {
    let a = 100;
    let t = (a, 0u8);
    let p: (u8, u8) = t;
    let r = &a;
    let q = *r + 200;
}

fn never_cmp_peer_types(y: u8) {
    let a = 100;
    let b = a == y;
    let r = &a;
    let q = *r + 200;
}

fn never_struct_field_types() {
    let a = 100;
    let s = B8 { g: a };
    let r = &a;
    let q = *r + 200;
}

fn never_option_ascribed_types() {
    let a = 100;
    let o = Some(a);
    let p: Option<u8> = o;
    let r = &a;
    let q = *r + 200;
}

fn never_assign_from_typed(y: u8) {
    let mut a = 100;
    let r = &a;
    let q = *r + 200;
    a = y;
}

fn never_copy_chain_types() {
    let a = 100;
    let b = a;
    g8(b);
    let r = &a;
    let q = *r + 200;
}

fn never_closure_param_types() {
    let a = 100;
    let f = |x: u8| x;
    f(a);
    let r = &a;
    let q = *r + 200;
}

fn never_return_types() -> u8 {
    let a = 100;
    let r = &a;
    let q = *r + 200;
    a
}

fn never_max_method_arg_types(y: u8) {
    let a = 100;
    let m = y.max(a);
    let r = &a;
    let q = *r + 200;
}

fn never_cmp_max_types(y: u8) {
    let a = 100;
    let m = std::cmp::max(a, y);
    let r = &a;
    let q = *r + 200;
}

fn never_later_binding_types(y: u8) {
    let a = 100;
    let r = &a;
    let q = *r + 200;
    let w = q < y;
}

fn never_if_join_types(y: u8, c: bool) {
    let a = 100;
    let m = if c { a } else { y };
    let r = &a;
    let q = *r + 200;
}

fn never_push_types() {
    let a = 100;
    let mut v: Vec<u8> = Vec::new();
    v.push(a);
    let r = &a;
    let q = *r + 200;
}

fn never_deref_assign_types(y: u8) {
    let a = 100;
    let mut t = y;
    let p = &mut t;
    *p = a;
    let r = &a;
    let q = *r + 200;
}

fn never_shadow_inner_scope(y: u8) {
    let a = 100;
    {
        let a = 5i64;
    }
    g8(a);
    let r = &a;
    let q = *r + 200;
}

fn never_capture_types() {
    let a = 100;
    let f = || g8(a);
    f();
    let r = &a;
    let q = *r + 200;
}

fn verified_twin_types(y: u8) {
    let a = 10;
    let z = y.wrapping_add(a);
    let r = &a;
    let q = *r + 200;
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
        .join("../../target/r14_untyped_form_neighbours_soundness_src");
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
        println!("R14NB|{file}|{func}|{got}|{raw}");
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
fn an_untyped_form_through_a_borrow_or_capture_meets_its_slot() {
    check(SRC_INT, "pint.rs", 21);
}

#[test]
fn a_binding_typed_by_a_use_elsewhere_is_checked_at_that_type() {
    check(SRC_INT2, "pint2.rs", 20);
}
