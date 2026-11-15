// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! An unsuffixed float literal is never the exact `real` where only a later
//! use fixes its Rust float type (design-trust-proof-backend.md §5b rule 14):
//! an array repeat (`[0.1; 2]`), a struct field whose declared type is not
//! `real` (`struct W<T> { x: T }`), and a `Box`/`Rc`/`Arc` payload join the
//! tuple, array and `Option`/`Result` holders already refused. Every
//! `never_*` program asserts a value that is false in `f64`; each was
//! `Verified` on origin/main dd3859d2. `true_*` twins must not be refuted.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC_FLOAT_REPEAT_GENERIC_BOX: &str = r####"
struct W<T> {
    x: T,
}

fn never_float_array_repeat() {
    let a = [0.1; 2];
    trust_vc::assert!(a[0] + 0.2 == 0.3);
}

fn never_float_generic_struct_field() {
    let w = W { x: 0.1 };
    trust_vc::assert!(w.x + 0.2 == 0.3);
}

fn never_float_box() {
    let b = Box::new(0.1);
    trust_vc::assert!(*b + 0.2 == 0.3);
}

fn never_float_array_nested_repeat() {
    let a = [[0.1; 1]; 1];
    trust_vc::assert!(a[0][0] + 0.2 == 0.3);
}

fn never_float_mul_three() {
    let p = W { x: 0.1 };
    trust_vc::assert!(p.x * 3.0 == 0.3);
}

fn true_float_dyadic_struct() {
    let p = W { x: 0.5 };
    trust_vc::assert!(p.x + 0.25 == 0.75);
}

fn never_float_generic_struct_let() {
    let w = W { x: 0.1 };
    let a = w.x;
    trust_vc::assert!(a + 0.2 == 0.3);
}

fn never_float_generic_struct_two() {
    let w = W { x: 0.1 };
    let v = W { x: 0.2 };
    trust_vc::assert!(w.x + v.x == 0.3);
}

fn never_float_array_repeat_ascribed() {
    let a: [f64; 2] = [0.1; 2];
    trust_vc::assert!(a[0] + 0.2 == 0.3);
}

fn never_float_box_ascribed() {
    let b: Box<f64> = Box::new(0.1);
    trust_vc::assert!(*b + 0.2 == 0.3);
}

fn never_float_rc() {
    let b = std::rc::Rc::new(0.1);
    trust_vc::assert!(*b + 0.2 == 0.3);
}

fn never_float_let_then_generic_field() {
    let a = 0.1;
    let w = W { x: a };
    trust_vc::assert!(w.x + 0.2 == 0.3);
}

fn never_float_struct_update() {
    let w0 = W { x: 0.0 };
    let w = W { x: 0.1, ..w0 };
    trust_vc::assert!(w.x + 0.2 == 0.3);
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
        .join("../../target/float_holder_soundness_src");
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
        println!("FLOAT|{file}|{func}|{got}|{raw}");
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
fn an_unsuffixed_float_in_a_repeat_array_generic_field_or_box_is_never_exact() {
    check(
        SRC_FLOAT_REPEAT_GENERIC_BOX,
        "float_repeat_generic_box.rs",
        13,
    );
}
