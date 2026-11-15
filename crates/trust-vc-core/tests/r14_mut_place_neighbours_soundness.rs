// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Round-14 neighbours of the escaping-`&mut`-place verifier residual on
//! 923d432a, written while reviewing the fix rather than taken from the
//! verifier: every program writes `s.g` (or a `Vec` cell) through a `&mut`
//! reached by a spelling other than a bare `let r = &mut place;` alias.
//!
//! Every `never_*` program compiles under trustc `-C overflow-checks=on`
//! with default lints and fails its assertion natively at y = 1; the twin
//! runs clean.
//!
//! A = origin/main 3378cdfb: 0/1 pass, 1 `never_*` FALSE VERIFIED
//! (`never_alias_shadow_rebind`: `let r = if true { &mut s.g } else { r };`
//! then `std::mem::swap(r, &mut t)`), the other 20 Unknown. B = this change:
//! 1/1, all 21 Unknown, the twin Verified.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC_MUT: &str = r####"
use std::ops::AddAssign;
struct S2 {
    g: u8,
    h: u8,
}

struct V {
    v: Vec<u8>,
}

fn set0(p: &mut u8) {
    *p = 0;
}

#[trust_vc::requires(y == 1u8)]
fn never_ascribed_alias_add_assign(y: u8) {
    let mut s = S2 { g: y, h: y };
    let r: &mut u8 = &mut s.g;
    std::ops::AddAssign::add_assign(r, 1u8);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_alias_moved_then_written(y: u8) {
    let mut s = S2 { g: y, h: y };
    let r = &mut s.g;
    let q = r;
    *q = 5;
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_alias_reborrow_swap(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let r = &mut s.g;
    let q = &mut *r;
    std::mem::swap(q, &mut t);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_for_over_borrow_array(y: u8) {
    let mut s = S2 { g: y, h: y };
    for r in [&mut s.g] {
        *r = 5;
    }
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_match_scrutinee_borrow(y: u8) {
    let mut s = S2 { g: y, h: y };
    match &mut s.g {
        r => *r = 5,
    }
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_option_map_borrow(y: u8) {
    let mut s = S2 { g: y, h: y };
    Some(&mut s.g).map(|r| *r = 5);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_block_alias(y: u8) {
    let mut s = S2 { g: y, h: y };
    let r = { &mut s.g };
    *r = 5;
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_paren_alias_swap(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let r = (&mut s.g);
    std::mem::swap(r, &mut t);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_double_ref_write(y: u8) {
    let mut s = S2 { g: y, h: y };
    let mut r = &mut s.g;
    let rr = &mut r;
    **rr = 5;
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_whole_struct_alias_method(y: u8) {
    let mut s = S2 { g: y, h: y };
    let r = &mut s;
    r.g.add_assign(1u8);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_whole_struct_alias_swap(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let r = &mut s;
    std::mem::swap(&mut r.g, &mut t);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_vec_field_alias_index_write(y: u8) {
    let mut s = V { v: vec![y] };
    let r = &mut s.v;
    r[0] = 5;
    trust_vc::assert!(s.v[0] == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_tuple_pattern_two_aliases(y: u8) {
    let mut s = S2 { g: y, h: y };
    let (a, b) = (&mut s.g, &mut s.h);
    *a = 5;
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_alias_reborrow_set0(y: u8) {
    let mut s = S2 { g: y, h: y };
    let r = &mut s.g;
    set0(&mut *r);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_closure_mut_capture(y: u8) {
    let mut s = S2 { g: y, h: y };
    let mut f = || s.g = 5;
    f();
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_closure_arg_borrow(y: u8) {
    let mut s = S2 { g: y, h: y };
    let f = |r: &mut u8| *r = 5;
    f(&mut s.g);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_alias_in_struct_literal(y: u8) {
    let mut s = S2 { g: y, h: y };
    struct H<'a> {
        r: &'a mut u8,
    }
    let h = H { r: &mut s.g };
    *h.r = 5;
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_vec_iter_mut(y: u8) {
    let mut v: Vec<u8> = vec![y];
    for r in v.iter_mut() {
        *r = 5;
    }
    trust_vc::assert!(v[0] == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_vec_first_mut(y: u8) {
    let mut v: Vec<u8> = vec![y];
    if let Some(r) = v.first_mut() {
        *r = 5;
    }
    trust_vc::assert!(v[0] == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_alias_fill(y: u8) {
    let mut v: Vec<u8> = vec![y];
    let r = &mut v;
    r.fill(5);
    trust_vc::assert!(v[0] == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_alias_shadow_rebind(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let r = &mut s.h;
    let r = if true { &mut s.g } else { r };
    std::mem::swap(r, &mut t);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn verified_twin_alias_write(y: u8) {
    let mut s = S2 { g: y, h: y };
    let r = &mut s.h;
    *r = 1;
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
        .join("../../target/r14_mut_place_neighbours_soundness_src");
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
fn a_place_lent_through_any_spelling_is_never_read_stale() {
    check(SRC_MUT, "pmut.rs", 22);
}
