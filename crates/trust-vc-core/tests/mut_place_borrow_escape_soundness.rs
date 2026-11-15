// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A `&mut` to a place reaches a writer by a spelling the lane did not
//! frame: an alias stored in a holder or reborrowed and then called through,
//! a borrow lent through a conditional, a `match` scrutinee, an array, a
//! struct literal, an `Option`, a cast to a raw pointer, a method argument, a
//! `ref mut` pattern, a `Box` dereference; and the same writes read back in
//! the return value. Every `never_*` program fails natively (trustc `-C
//! overflow-checks=on`, at the `requires` values and `c == true`): its
//! assertion fails, or (`SRC_RETURN_LANE`) it returns 0 and 2 where the
//! postcondition says 1. The groups whose cases came back `Verified` on
//! origin/main `7fa4db88` fail there.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

/// A `&mut` alias of a field stored in a holder (`(r, 1u8)`, `Some(r)`),
/// reborrowed and called through (`let q = &mut *r; q.add_assign(1u8)`), an
/// alias of the whole struct used through a field, an alias passed to a
/// file method with a `&mut` parameter, a re-targeted alias.
const SRC_ALIAS_ESCAPES: &str = r####"
use std::ops::AddAssign;

struct S2 {
    g: u8,
    h: u8,
}

struct W {
    k: u8,
}

impl W {
    fn put(&self, p: &mut u8) {
        *p = 0;
    }
}


#[trust_vc::requires(y == 1u8)]
fn never_alias_in_tuple_holder(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let r = &mut s.g;
    let p = (r, 1u8);
    std::mem::swap(p.0, &mut t);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_alias_some_holder(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let r = &mut s.g;
    let o = Some(r);
    if let Some(q) = o {
        std::mem::swap(q, &mut t);
    }
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_reborrow_alias_method(y: u8) {
    let mut s = S2 { g: y, h: y };
    let r = &mut s.g;
    let q = &mut *r;
    q.add_assign(1u8);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_whole_alias_field_method(y: u8) {
    let mut s = S2 { g: y, h: y };
    let r = &mut s;
    r.g.add_assign(1u8);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_whole_alias_field_borrow_swap(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let r = &mut s;
    std::mem::swap(&mut r.g, &mut t);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_resolved_method_alias_arg(y: u8) {
    let mut s = S2 { g: y, h: y };
    let w = W { k: 0 };
    let r = &mut s.g;
    w.put(r);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_retargeted_alias_swap(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let mut r = &mut s.h;
    r = &mut s.g;
    std::mem::swap(r, &mut t);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn verified_alias_write_twin(y: u8) {
    let mut s = S2 { g: y, h: y };
    let r = &mut s.g;
    *r = 5;
    trust_vc::assert!(s.g == 5u8 && s.h == 1u8);
}
"####;

/// A `&mut` place lent through a conditional argument, a `match` scrutinee,
/// a `vec!`, a struct literal, `Some`, an array, a file method's argument, a
/// dereference of a `Box` or a `&mut` parameter, a cast to a raw pointer, a
/// closure: every later read of the place fails closed.
const SRC_PLACE_BORROWS: &str = r####"
struct S2 {
    g: u8,
    h: u8,
}

struct H<'a> {
    r: &'a mut u8,
}

struct W {
    k: u8,
}

impl W {
    fn put(&self, p: &mut u8) {
        *p = 0;
    }
}

fn set0(p: &mut u8) {
    *p = 0;
}


#[trust_vc::requires(y == 1u8)]
fn never_second_arg_if(y: u8, x: u8, c: bool) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    std::mem::swap(&mut t, if c { &mut s.g } else { &mut s.h });
    trust_vc::assert!(s.g == 1u8 && s.h == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_match_mut_field(y: u8) {
    let mut s = S2 { g: y, h: y };
    match &mut s.g {
        r => set0(r),
    }
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_vec_macro_holder(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let v = vec![&mut s.g];
    for r in v {
        std::mem::swap(r, &mut t);
    }
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_struct_holder(y: u8) {
    let mut s = S2 { g: y, h: y };
    let h = H { r: &mut s.g };
    set0(h.r);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_option_some_holder(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let o = Some(&mut s.g);
    if let Some(r) = o {
        std::mem::swap(r, &mut t);
    }
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_array_holder_for(y: u8) {
    let mut s = S2 { g: y, h: y };
    for x in [&mut s.g] {
        *x = 0;
    }
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_resolved_method_field_arg(y: u8) {
    let mut s = S2 { g: y, h: y };
    let w = W { k: 0 };
    w.put(&mut s.g);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_box_deref_swap(y: u8, x: u8) {
    let mut b = Box::new(y);
    let mut t = x;
    std::mem::swap(&mut *b, &mut t);
    trust_vc::assert!(*b == 1u8);
}

#[trust_vc::requires(*p == 1u8)]
fn never_param_deref_reborrow_swap(p: &mut u8, x: u8) {
    let mut t = x;
    std::mem::swap(&mut *p, &mut t);
    trust_vc::assert!(*p == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_raw_ptr_cast_write(y: u8) {
    let mut s = S2 { g: y, h: y };
    let p = &mut s.g as *mut u8;
    unsafe {
        std::ptr::write(p, 0);
    }
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_addr_of_mut_write(y: u8) {
    let mut s = S2 { g: y, h: y };
    let p = std::ptr::addr_of_mut!(s.g);
    unsafe {
        std::ptr::write(p, 0);
    }
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_closure_param_mut(y: u8) {
    let mut s = S2 { g: y, h: y };
    let f = |v: &mut u8| {
        *v = 0;
    };
    f(&mut s.g);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_closure_capture_write(y: u8) {
    let mut s = S2 { g: y, h: y };
    let mut f = || s.g = 0;
    f();
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn true_resolved_call_field(y: u8) {
    let mut s = S2 { g: y, h: y };
    set0(&mut s.g);
    trust_vc::assert!(s.h == 1u8);
}
"####;

/// A `ref mut` pattern (`let`, `match` arm, `if let`) borrows the
/// scrutinee's place with no `&mut` expression.
const SRC_REF_MUT_PATTERNS: &str = r####"
struct S2 {
    g: u8,
    h: u8,
}

struct SO {
    o: Option<u8>,
    k: u8,
}


#[trust_vc::requires(y == 1u8)]
fn never_ref_mut_pattern_swap(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let S2 { ref mut g, .. } = s;
    std::mem::swap(g, &mut t);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_ref_mut_match_arm(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    match s {
        S2 { ref mut g, .. } => std::mem::swap(g, &mut t),
    }
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_if_let_ref_mut_option(y: u8, x: u8) {
    let mut s = SO { o: Some(y), k: y };
    let mut t = x;
    if let Some(ref mut v) = s.o {
        std::mem::swap(v, &mut t);
    }
    trust_vc::assert!(s.o == Some(1u8));
}

#[trust_vc::requires(y == 1u8)]
fn never_default_binding_mode(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    match &mut s {
        S2 { g, .. } => std::mem::swap(g, &mut t),
    }
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_iter_mut_field(y: u8) {
    let mut s = SO { o: Some(y), k: y };
    for v in s.o.iter_mut() {
        *v = 0;
    }
    trust_vc::assert!(s.o == Some(1u8));
}

#[trust_vc::requires(y == 1u8)]
fn never_as_mut_option(y: u8, x: u8) {
    let mut s = SO { o: Some(y), k: y };
    let mut t = x;
    if let Some(v) = s.o.as_mut() {
        std::mem::swap(v, &mut t);
    }
    trust_vc::assert!(s.o == Some(1u8));
}

#[trust_vc::requires(y == 1u8)]
fn never_if_let_option_field(y: u8) {
    let mut s = SO { o: Some(y), k: y };
    if let Some(x) = &mut s.o {
        *x = 0;
    }
    trust_vc::assert!(s.o == Some(1u8));
}

#[trust_vc::requires(y == 1u8)]
fn verified_ref_pattern_read(y: u8) {
    let s = S2 { g: y, h: y };
    let S2 { ref g, .. } = s;
    trust_vc::assert!(s.g == 1u8);
}
"####;

/// The same writes, read back in the returned value.
const SRC_RETURN_LANE: &str = r####"
use std::ops::AddAssign;

struct S2 {
    g: u8,
    h: u8,
}


#[trust_vc::requires(y == 1u8)]
#[trust_vc::ensures(result == 1u8)]
fn never_return_lane_if_alias(y: u8, x: u8, c: bool) -> u8 {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let r = if c { &mut s.g } else { &mut s.h };
    std::mem::swap(r, &mut t);
    s.g
}

#[trust_vc::requires(y == 1u8)]
#[trust_vc::ensures(result == 1u8)]
fn never_return_lane_method_alias(y: u8) -> u8 {
    let mut s = S2 { g: y, h: y };
    let r = &mut s.g;
    r.add_assign(1u8);
    s.g
}

#[trust_vc::requires(y == 1u8)]
#[trust_vc::ensures(result == 1u8)]
fn verified_return_lane_other_field(y: u8) -> u8 {
    let mut s = S2 { g: y, h: y };
    let r = &mut s.h;
    *r = 5;
    s.g
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
        .join("../../target/mut_place_borrow_escape_soundness_src");
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
        println!("BORROW|{file}|{func}|{got}|{raw}");
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
fn a_borrowed_alias_that_escapes_frames_its_target() {
    check(SRC_ALIAS_ESCAPES, "alias_escapes.rs", 8);
}

#[test]
fn a_place_lent_by_any_borrow_is_framed() {
    check(SRC_PLACE_BORROWS, "place_borrows.rs", 14);
}

#[test]
fn a_ref_mut_pattern_frames_its_scrutinee() {
    check(SRC_REF_MUT_PATTERNS, "ref_mut_patterns.rs", 8);
}

#[test]
fn the_return_value_reads_the_framed_place() {
    check(SRC_RETURN_LANE, "return_lane.rs", 3);
}
