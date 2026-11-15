// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A `&mut` place written through a callee reaches it by any spelling: a
//! `&mut` alias binding (`let r = &mut s.g; std::mem::swap(r, &mut t)`), a
//! cast (`&mut s.g as &mut u8`), a reborrow (`&mut *(&mut s.g)`, `&mut *r`),
//! a moved alias (`let q = r;`) or a destructured borrow (`let (r, q) =
//! (&mut s.g, &mut t);`). Only the literal `&mut <field|index>` argument was
//! framed, so the write was dropped and `s.g` kept its old value. Every `never_*` program
//! fails its assertion natively at (y = 1, x = 0); each was `Verified` on
//! origin/main dd3859d2. `verified_*` twins stay `Verified`.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC_MEM_REF_BINDING: &str = r####"
struct S2 {
    g: u8,
    h: u8,
}

#[trust_vc::requires(y == 1u8)]
fn never_swap_through_ref_binding(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let r = &mut s.g;
    std::mem::swap(r, &mut t);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_swap_cast_ref(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    std::mem::swap(&mut s.g as &mut u8, &mut t);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_swap_reborrow_ref(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    std::mem::swap(&mut *(&mut s.g), &mut t);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_replace_through_ref_binding(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let r = &mut s.g;
    let old = std::mem::replace(r, x);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_take_through_ref_binding(y: u8) {
    let mut s = S2 { g: y, h: y };
    let r = &mut s.g;
    let old = std::mem::take(r);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_swap_through_ref_binding_vec_cell(y: u8, x: u8) {
    let mut v: Vec<u8> = vec![y];
    let mut t = x;
    let r = &mut v[0];
    std::mem::swap(r, &mut t);
    trust_vc::assert!(v[0] == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_swap_both_ref_bindings(y: u8, x: u8) {
    let mut s = S2 { g: y, h: x };
    let r = &mut s.g;
    let mut t = x;
    let q = &mut t;
    std::mem::swap(r, q);
    trust_vc::assert!(s.g == 1u8);
}

fn set0(p: &mut u8) {
    *p = 0;
}

#[trust_vc::requires(y == 1u8)]
fn never_resolved_callee_through_ref_binding(y: u8) {
    let mut s = S2 { g: y, h: y };
    let r = &mut s.g;
    set0(r);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_resolved_callee_cast_ref(y: u8) {
    let mut s = S2 { g: y, h: y };
    set0(&mut s.g as &mut u8);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_swap_reborrow_of_ref_binding(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let r = &mut s.g;
    let r2 = &mut *r;
    std::mem::swap(r2, &mut t);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_core_swap_through_ref_binding(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let r = &mut s.g;
    core::mem::swap(r, &mut t);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_swap_destructured_borrows(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let (r, q) = (&mut s.g, &mut t);
    std::mem::swap(r, q);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_swap_destructured_conditional_borrow(y: u8, x: u8, c: bool) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let (r, q) = (if c { &mut s.g } else { &mut s.h }, &mut t);
    std::mem::swap(r, q);
    trust_vc::assert!(s.g == 1u8 || !c);
}

#[trust_vc::requires(y == 1u8)]
fn never_swap_moved_ref_binding(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    let r = &mut s.g;
    let q = r;
    std::mem::swap(q, &mut t);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_resolved_callee_moved_ref_binding(y: u8) {
    let mut s = S2 { g: y, h: y };
    let r = &mut s.g;
    let q = r;
    set0(q);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn verified_swap_leaves_other_field(y: u8, x: u8) {
    let mut s = S2 { g: y, h: y };
    let mut t = x;
    trust_vc::assert!(s.h == 1u8);
    std::mem::swap(&mut t, &mut s.g);
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
        .join("../../target/mut_place_alias_write_soundness_src");
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
        println!("MEMREF|{file}|{func}|{got}|{raw}");
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
fn a_mut_place_reaching_a_callee_by_another_spelling_is_written() {
    check(SRC_MEM_REF_BINDING, "mem_ref_binding.rs", 16);
}
