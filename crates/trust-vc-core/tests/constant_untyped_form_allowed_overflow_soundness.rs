// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Round-14 verifier residual (trust-vc origin/main 923d432a), design-level:
//! an untyped CONSTANT literal form (`200 + 100`) whose type only a call's
//! parameter (or a closure's return, typed by that call) fixes is never
//! checked at that type. `types::untyped_form_is_conditional` relies on
//! rustc's compile-time check for a constant form, but that check is the
//! deny-by-default `arithmetic_overflow` lint, which a function may `allow`:
//! the programs below compile with trustc and panic at run time. The same
//! constant next to a typed peer (`(200 + 100) * y`) IS refuted.
//!
//! Every `never_*` program compiles with `#[allow(arithmetic_overflow)]` and
//! panics natively; each was `Verified` on dd3859d2 and on 923d432a.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC_CONSTANT_FORM_ALLOWED: &str = r####"
fn g8(x: u8) {}

#[allow(arithmetic_overflow)]
fn never_constant_form_call_arg() {
    g8(200 + 100);
}

#[allow(arithmetic_overflow)]
fn never_constant_form_binding_call_arg() {
    let a = 200 + 100;
    g8(a);
}

#[allow(arithmetic_overflow)]
fn never_constant_form_closure_result_call_arg() {
    let f = || 200 + 100;
    g8(f());
}

#[allow(arithmetic_overflow)]
#[trust_vc::requires(y == 1u8)]
fn verified_constant_form_small(y: u8) {
    g8(100 + 100);
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
        .join("../../target/constant_untyped_form_allowed_overflow_soundness_src");
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
        println!("R14CONST|{file}|{func}|{got}|{raw}");
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
fn a_constant_untyped_form_under_an_allowed_lint_is_checked() {
    check(SRC_CONSTANT_FORM_ALLOWED, "constant_form_allowed.rs", 4);
}
