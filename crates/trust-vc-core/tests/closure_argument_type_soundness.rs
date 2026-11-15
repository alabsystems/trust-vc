// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! An invoked exec closure's arguments are read at the type Rust gives its
//! parameters (design-trust-proof-backend.md §5b rule 11). Every `never_*`
//! program panics under `-C overflow-checks=on` when compiled with trustc and
//! called as its `// native:` note says; each was `Verified` on origin/main
//! dd3859d2. Every `verified_*` twin must stay `Verified`; every `true_*`
//! twin (a program that runs clean) must not be refuted.
//!
//! * SRC_UNREAD_ASCRIPTION: a closure bound under a type the call-site lane
//!   does not read (`let f: _ = ..`, an alias `let f: F8 = ..`). 143f035f
//!   made that lane RETURN there, leaving the body checked at neither site
//!   (the definition-site planner had counted the call as coverage).
//! * SRC_INFERRED_PARAM: an unannotated parameter typed by ANOTHER call
//!   (`f(y_u8)`) took an unsuffixed literal argument (`f(200)`, `let k =
//!   200; f(k)`) bare, so the body was read in `i32`.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC_UNREAD_ASCRIPTION: &str = r####"
type F8 = fn(u8) -> u8;

// native: panics at y = 200 (u8 addition)
#[trust_vc::requires(y == 200u8)]
fn never_infer_ascribed_peer_arg(y: u8) {
    let f: _ = |a: u8| a + 100;
    let z = f(y);
    trust_vc::assert!(y == 200u8);
}

// native: panics at y = 200 (u8 addition)
#[trust_vc::requires(y == 200u8)]
fn never_alias_ascribed_peer_arg(y: u8) {
    let f: F8 = |a| a + 100;
    let z = f(y);
    trust_vc::assert!(y == 200u8);
}

// native: panics (u8 addition 200 + 100)
#[trust_vc::requires(y == 1u8)]
fn never_alias_ascribed_literal_arg(y: u8) {
    let f: F8 = |a| a + 100;
    let z = f(200);
    trust_vc::assert!(y == 1u8);
}

// native: panics at y = 0 (divide by zero)
#[trust_vc::requires(y == 0u8)]
fn never_infer_ascribed_div(y: u8) {
    let f: _ = |a: u8| 10u8 / a;
    let z = f(y);
    trust_vc::assert!(y == 0u8);
}

// native: panics at y = 0 (divide by zero)
#[trust_vc::requires(y == 0u8)]
fn never_alias_ascribed_div(y: u8) {
    let f: F8 = |a| 10u8 / a;
    let z = f(y);
    trust_vc::assert!(y == 0u8);
}

// native: panics at y = 5 (index out of bounds, len 2)
#[trust_vc::requires(y == 5usize)]
fn never_infer_ascribed_index(y: usize) {
    let v: Vec<u8> = vec![1u8, 2u8];
    let f: _ = |a: usize| v[a];
    let z = f(y);
    trust_vc::assert!(y == 5usize);
}

// native: panics (u8 addition 200 + 100)
#[trust_vc::requires(y == 100u8)]
fn never_infer_ascribed_literal_arg(y: u8) {
    let f: _ = |a: u8| a + 100;
    let z = f(200);
    trust_vc::assert!(y == 100u8);
}

// native: runs clean at y = 100
#[trust_vc::requires(y == 100u8)]
fn verified_infer_ascribed_twin(y: u8) {
    let f: _ = |a: u8| a + 100;
    let z = f(y);
    trust_vc::assert!(y == 100u8);
}

// native: runs clean at y = 100
#[trust_vc::requires(y == 100u8)]
fn verified_alias_ascribed_twin(y: u8) {
    let f: F8 = |a| a + 100;
    let z = f(y);
    trust_vc::assert!(y == 100u8);
}
"####;

const SRC_INFERRED_PARAM: &str = r####"
// native: panics at y = 100 (u8 addition 200 + 100)
#[trust_vc::requires(y == 100u8)]
fn never_param_typed_by_other_call(y: u8) {
    let f = |a| a + 100;
    let q = f(y);
    let z = f(200);
    trust_vc::assert!(y == 100u8);
}

// native: panics at y = 100 (the LATER call types `a`)
#[trust_vc::requires(y == 100u8)]
fn never_param_typed_by_later_call(y: u8) {
    let f = |a| a + 100;
    let z = f(200);
    let q = f(y);
    trust_vc::assert!(y == 100u8);
}

// native: panics at y = 100 (u8 multiplication 200 * 2)
#[trust_vc::requires(y == 100u8)]
fn never_param_mul(y: u8) {
    let f = |a| a * 2;
    let q = f(y);
    let z = f(200);
    trust_vc::assert!(y == 100u8);
}

// native: panics at y = 100 (`k` is a u8)
#[trust_vc::requires(y == 100u8)]
fn never_param_let_literal(y: u8) {
    let f = |a| a + 100;
    let q = f(y);
    let k = 200;
    let z = f(k);
    trust_vc::assert!(y == 100u8);
}

// native: panics at y = 100 (u8 addition 255 + 1)
#[trust_vc::requires(y == 100u8)]
fn never_param_value(y: u8) -> u8 {
    let f = |a| a + 1;
    let q = f(y);
    let z = f(255);
    trust_vc::assert!(y == 100u8);
    z
}

// native: panics at y = 100 (u8 addition 200 + 100)
#[trust_vc::requires(y == 100u8)]
fn never_two_params(y: u8) {
    let g = |a, b| a + b;
    let q = g(y, 1);
    let z = g(200, 100);
    trust_vc::assert!(y == 100u8);
}

// native: panics at y = 100 (u8 multiplication in the tail)
#[trust_vc::requires(y == 100u8)]
fn never_param_tail(y: u8) -> u8 {
    let f = |a| a * 2;
    let q = f(y);
    trust_vc::assert!(y == 100u8);
    f(200)
}

// native: runs clean (`a` defaults to i32)
#[trust_vc::requires(y == 1u8)]
fn true_param_defaults_to_i32(y: u8) {
    let f = |a| a + 100;
    let z = f(200);
    trust_vc::assert!(y == 1u8);
}

// native: runs clean
#[trust_vc::requires(y == 100u8)]
fn verified_param_typed_argument(y: u8) {
    let f = |a| a + 100;
    let z = f(y - 50);
    trust_vc::assert!(y == 100u8);
}

// native: runs clean
#[trust_vc::requires(y == 1u8)]
fn verified_written_param_literal(y: u8) {
    let f = |a: u8| a + 1;
    let z = f(200);
    trust_vc::assert!(y == 1u8);
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
        .join("../../target/closure_argument_type_soundness_src");
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
        println!("CLOSURE_ARG|{file}|{func}|{got}|{raw}");
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
fn an_invoked_closure_behind_an_unread_ascription_is_still_checked() {
    check(SRC_UNREAD_ASCRIPTION, "unread_ascription.rs", 9);
}

#[test]
fn an_unannotated_closure_parameter_is_never_read_at_its_literal_placeholder() {
    check(SRC_INFERRED_PARAM, "inferred_param.rs", 10);
}
