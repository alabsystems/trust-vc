// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Round-14 verifier residual (trust-vc origin/main 923d432a): an unsuffixed
//! literal reaching a typed position THROUGH a borrow or a closure capture
//! (`let a = 200; let r = &a; g8(*r + 100)`) is substituted into a CONSTANT
//! untyped form (`200 + 100`), which is checked only at its `i32`
//! placeholder: `types::untyped_form_is_conditional` leaves a constant form to
//! rustc's compile-time check. rustc's `arithmetic_overflow` lint does not
//! see through the borrow or the capture, so every program below COMPILES
//! under the default lint levels (trustc, `-C overflow-checks=on`) and panics
//! at run time. The same form under a `let z: u8 =` ascription or next to a
//! typed peer operand is refuted.
//!
//! Every `never_*` case was `Verified` on dd3859d2 and on 923d432a.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC_THROUGH_BORROW: &str = r####"
fn g8(x: u8) {}

struct B8 {
    g: u8,
}

fn never_shared_borrow_call_arg() {
    let a = 200;
    let r = &a;
    g8(*r + 100);
}

fn never_mut_borrow_call_arg() {
    let mut a = 200;
    let r = &mut a;
    g8(*r + 100);
}

fn never_write_through_alias_call_arg() {
    let mut a = 200;
    let r = &mut a;
    *r = 250;
    g8(a + 10);
}

fn never_borrow_binding_call_arg() {
    let mut a = 200;
    let r = &mut a;
    let z = *r + 100;
    g8(z);
}

fn never_borrow_sub_call_arg() {
    let a = 1;
    let r = &a;
    g8(*r - 2);
}

fn never_borrow_mul_call_arg() {
    let a = 16;
    let r = &a;
    g8(*r * 16);
}

fn never_borrow_return_position() -> u8 {
    let a = 200;
    let r = &a;
    *r + 100
}

fn never_borrow_struct_field() {
    let a = 200;
    let r = &a;
    let b = B8 { g: *r + 100 };
}

fn never_borrow_vec_push() {
    let a = 200;
    let r = &a;
    let mut v: Vec<u8> = Vec::new();
    v.push(*r + 100);
}

fn never_borrow_array_write() {
    let a = 200;
    let r = &a;
    let mut arr: [u8; 1] = [0];
    arr[0] = *r + 100;
}

fn never_borrow_compared_to_typed() {
    let a = 200;
    let r = &a;
    let y: u8 = 1;
    let b = *r + 100 == y;
}

fn verified_borrow_small_twin() {
    let a = 100;
    let r = &a;
    g8(*r + 100);
}
"####;

const SRC_THROUGH_CAPTURE: &str = r####"
fn g8(x: u8) {}

struct B8 {
    g: u8,
}

fn never_capture_call_arg() {
    let a = 200;
    let f = || a + 100;
    g8(f());
}

fn never_move_capture_call_arg() {
    let a = 200;
    let f = move || a + 100;
    g8(f());
}

fn never_capture_struct_field() {
    let a = 200;
    let f = || a + 100;
    let b = B8 { g: f() };
}

fn verified_capture_small_twin() {
    let a = 100;
    let f = || a + 100;
    g8(f());
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
        .join("../../target/untyped_constant_through_borrow_soundness_src");
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
        println!("R14CP|{file}|{func}|{got}|{raw}");
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
fn an_untyped_constant_through_a_borrow_is_checked_at_its_type() {
    check(SRC_THROUGH_BORROW, "through_borrow.rs", 12);
}

#[test]
fn an_untyped_constant_through_a_capture_is_checked_at_its_type() {
    check(SRC_THROUGH_CAPTURE, "through_capture.rs", 4);
}
