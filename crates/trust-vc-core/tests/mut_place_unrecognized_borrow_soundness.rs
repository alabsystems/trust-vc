// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Round-14 verifier residuals (trust-vc origin/main 923d432a): a `&mut`
//! place written through a callee is still dropped when the `&mut` reaches the
//! callee by a spelling that 285bbcf2 does not recognize as a borrow of that
//! place, and when the callee is a METHOD called through a `&mut` alias.
//!
//! Every `never_*` program fails its assertion natively (trustc
//! `-C overflow-checks=on`, at the `requires` values, `c == true`) and was
//! `Verified` on BOTH dd3859d2 (before 285bbcf2) and 923d432a (after it): the
//! class is pre-existing and still open. The `verified_*` twins must stay
//! `Verified`.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

/// A `&mut` bound to a name by an initializer that is not a bare
/// `&mut <place>`: a conditional, a cast, a projection of a tuple literal, a
/// slice pattern, a tuple pattern over a path. The name is no recorded alias,
/// so the callee's write never reaches `s`.
const SRC_UNRECOGNIZED_BORROW_BINDING: &str = r####"
struct S2 {
    g: u8,
    h: u8,
}

fn set0(p: &mut u8) {
    *p = 0;
}

#[trust_vc::requires(y == 1u8)]
fn never_if_alias_swap(y: u8, x: u8, c: bool) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let r = if c { &mut s.g } else { &mut s.h };
    std::mem::swap(r, &mut t);
    trust_vc::assert!(s.g == 1u8 && s.h == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_if_alias_same_place_swap(y: u8, x: u8, c: bool) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let r = if c { &mut s.g } else { &mut s.g };
    std::mem::swap(r, &mut t);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_if_alias_vec_elems_swap(y: u8, x: u8, c: bool) {
    let mut v: Vec<u8> = vec![y, y];
    let mut t = x;
    let r = if c { &mut v[0] } else { &mut v[1] };
    std::mem::swap(r, &mut t);
    trust_vc::assert!(v[0] == 1u8 && v[1] == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_if_alias_resolved_callee(y: u8, c: bool) {
    let mut s = S2 { g: y, h: y };
    let r = if c { &mut s.g } else { &mut s.h };
    set0(r);
    trust_vc::assert!(s.g == 1u8 && s.h == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_cast_alias_swap(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let r = &mut s.g as &mut u8;
    std::mem::swap(r, &mut t);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_tuple_literal_field_alias_swap(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let r = (&mut s.g, 0u8).0;
    std::mem::swap(r, &mut t);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_slice_pattern_alias_swap(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let [r] = [&mut s.g];
    std::mem::swap(r, &mut t);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_slice_pattern_resolved_callee(y: u8) {
    let mut s = S2 { g: y, h: y };
    let [r] = [&mut s.g];
    set0(r);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_tuple_pattern_over_path_swap(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let p = (&mut s.g, 1u8);
    let (r, _) = p;
    std::mem::swap(r, &mut t);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn verified_alias_to_other_field(y: u8) {
    let mut s = S2 { g: y, h: y };
    let r = &mut s.h;
    *r = 5;
    trust_vc::assert!(s.g == 1u8);
}
"####;

/// A `&mut` held in a tuple (`p.0`) or produced by an `if` passed straight to
/// a callee: the argument is neither a `&mut <place>` nor an alias name.
const SRC_BORROW_IN_HOLDER_ARG: &str = r####"
struct S2 {
    g: u8,
    h: u8,
}

fn set0(p: &mut u8) {
    *p = 0;
}

#[trust_vc::requires(y == 1u8)]
fn never_tuple_holder_swap(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let p = (&mut s.g, 1u8);
    std::mem::swap(p.0, &mut t);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_one_tuple_holder_swap(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let p = (&mut s.g,);
    std::mem::swap(p.0, &mut t);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_tuple_holder_replace(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let p = (&mut s.g, 1u8);
    let old = std::mem::replace(p.0, x);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_tuple_holder_resolved_callee(y: u8) {
    let mut s = S2 { g: y, h: y };
    let p = (&mut s.g, 1u8);
    set0(p.0);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_if_arg_swap(y: u8, x: u8, c: bool) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    std::mem::swap(if c { &mut s.g } else { &mut s.h }, &mut t);
    trust_vc::assert!(s.g == 1u8 && s.h == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_if_arg_resolved_callee(y: u8, c: bool) {
    let mut s = S2 { g: y, h: y };
    set0(if c { &mut s.g } else { &mut s.h });
    trust_vc::assert!(s.g == 1u8 && s.h == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn verified_holder_twin(y: u8) {
    let mut s = S2 { g: y, h: y };
    let r = &mut s.h;
    *r = 5;
    trust_vc::assert!(s.g == 1u8);
}
"####;

/// A method with a `&mut self` receiver called through a `&mut` alias of a
/// field or cell (`let r = &mut s.g; r.add_assign(1)`): the same call on the
/// place itself (`s.g.add_assign(1)`) fails closed, through the alias the
/// write is dropped — for trait methods (`AddAssign`, `SubAssign`,
/// `MulAssign`, `Clone::clone_from`) and a resolved user method alike.
const SRC_METHOD_THROUGH_ALIAS: &str = r####"
use std::ops::{AddAssign, MulAssign, SubAssign};

struct S2 {
    g: u8,
    h: u8,
}

struct Inner {
    v: u8,
}

impl Inner {
    fn bump(&mut self) {
        self.v = 0;
    }
}

struct Outer {
    inner: Inner,
    k: u8,
}

#[trust_vc::requires(y == 1u8)]
fn never_alias_add_assign(y: u8) {
    let mut s = S2 { g: y, h: y };
    let r = &mut s.g;
    r.add_assign(1u8);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_alias_sub_assign(y: u8) {
    let mut s = S2 { g: y, h: y };
    let r = &mut s.g;
    r.sub_assign(1u8);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 2u8)]
fn never_alias_mul_assign(y: u8) {
    let mut s = S2 { g: y, h: y };
    let r = &mut s.g;
    r.mul_assign(3u8);
    trust_vc::assert!(s.g == 2u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_alias_clone_from(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let r = &mut s.g;
    r.clone_from(&x);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_alias_deref_add_assign(y: u8) {
    let mut s = S2 { g: y, h: y };
    let r = &mut s.g;
    (*r).add_assign(1u8);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_alias_vec_cell_add_assign(y: u8) {
    let mut v: Vec<u8> = vec![y];
    let r = &mut v[0];
    r.add_assign(1u8);
    trust_vc::assert!(v[0] == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_alias_field_user_method(y: u8) {
    let mut o = Outer { inner: Inner { v: y }, k: y };
    let r = &mut o.inner;
    r.bump();
    trust_vc::assert!(o.inner.v == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn verified_method_twin(y: u8) {
    let mut s = S2 { g: y, h: y };
    let r = &mut s.h;
    *r = 5;
    trust_vc::assert!(s.g == 1u8);
}
"####;

/// A `&mut` place passed as an ARGUMENT of a method call
/// (`x.clone_into(&mut s.g)`, `b.swap_with_slice(&mut s.a)`): the free-call
/// framing of 285bbcf2 (`std::mem::swap(&mut s.g, ..)`) has no method-call
/// counterpart for a field or cell projection. And `Option`'s `&mut self`
/// methods called through a `&mut` alias of a field (`let r = &mut s.o;
/// r.take()`): the same call on the field itself fails closed.
const SRC_METHOD_MUT_ARGUMENT: &str = r####"
struct S2 {
    g: u8,
    h: u8,
}

struct SA {
    a: [u8; 1],
    k: u8,
}

struct SO {
    o: Option<u8>,
    k: u8,
}

#[trust_vc::requires(y == 1u8)]
fn never_clone_into_field(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    x.clone_into(&mut s.g);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_clone_into_alias(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let r = &mut s.g;
    x.clone_into(r);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_clone_into_vec_cell(y: u8, x: u8) {
    let mut v: Vec<u8> = vec![y];
    x.clone_into(&mut v[0]);
    trust_vc::assert!(v[0] == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_swap_with_slice_field(y: u8, x: u8) {
    let mut s = SA { a: [y], k: y };
    let mut b: [u8; 1] = [x];
    b.swap_with_slice(&mut s.a);
    trust_vc::assert!(s.a[0] == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_option_field_alias_take(y: u8) {
    let mut s = SO { o: Some(y), k: y };
    let r = &mut s.o;
    let _v = r.take();
    trust_vc::assert!(s.o == Some(1u8));
}

#[trust_vc::requires(y == 1u8)]
fn never_option_field_alias_replace(y: u8, x: u8) {
    let mut s = SO { o: Some(y), k: y };
    let r = &mut s.o;
    let _v = r.replace(x);
    trust_vc::assert!(s.o == Some(1u8));
}

#[trust_vc::requires(y == 1u8)]
fn never_option_field_alias_insert(y: u8, x: u8) {
    let mut s = SO { o: Some(y), k: y };
    let r = &mut s.o;
    r.insert(x);
    trust_vc::assert!(s.o == Some(1u8));
}

#[trust_vc::requires(y == 1u8)]
fn verified_method_argument_twin(y: u8) {
    let mut s = S2 { g: y, h: y };
    let r = &mut s.h;
    *r = 5;
    trust_vc::assert!(s.g == 1u8);
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
        .join("../../target/mut_place_unrecognized_borrow_soundness_src");
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
        println!("R14MUT|{file}|{func}|{got}|{raw}");
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
fn a_borrow_bound_by_an_unrecognized_initializer_is_written() {
    check(
        SRC_UNRECOGNIZED_BORROW_BINDING,
        "unrecognized_binding.rs",
        10,
    );
}

#[test]
fn a_borrow_passed_inside_a_holder_is_written() {
    check(SRC_BORROW_IN_HOLDER_ARG, "holder_arg.rs", 7);
}

#[test]
fn a_mut_place_passed_to_a_method_is_written() {
    check(SRC_METHOD_MUT_ARGUMENT, "method_mut_argument.rs", 8);
}

#[test]
fn a_method_through_a_mut_alias_writes_its_target() {
    check(SRC_METHOD_THROUGH_ALIAS, "method_through_alias.rs", 8);
}
