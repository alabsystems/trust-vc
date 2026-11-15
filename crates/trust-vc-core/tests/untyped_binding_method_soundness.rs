// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A loop-written `let mut w = 0` is typed by the TRAIT methods called on it
//! (design-trust-proof-backend.md §5b rule 2). Rust refuses an inherent
//! method on a still-unconstrained integer (E0689) but resolves a trait
//! method (`Ord::{max, min, clamp}`, `PartialEq`/`PartialOrd`/`Ord`
//! comparisons, `Clone::clone`), which unifies the binding with its `Self`
//! arguments and gives its result the binding's type. `untyped_binding_type`
//! read every method call as fixing nothing, so the loop's `u8` overflow
//! (`w = w + 100` three times) was declared `i32` and never checked. Every
//! `never_*` program panics under `-C overflow-checks=on`; each was
//! `Verified` on origin/main dd3859d2. `verified_*` twins stay `Verified`;
//! `true_*` twins must not be refuted.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC_TRAIT_METHOD_RECEIVER: &str = r####"
fn g8(x: u8) {}

struct S2 {
    g: u8,
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_method_max_result_call(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 3 {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w = w + 100;
        i = i + 1;
    }
    let z = w.max(1);
    g8(z);
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_method_clone_result_call(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 3 {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w = w + 100;
        i = i + 1;
    }
    let z = w.clone();
    g8(z);
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_method_min_peer_arg(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 3 {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w = w + 100;
        i = i + 1;
    }
    let z = w.min(y);
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_method_max_plus_peer(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 3 {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w = w + 100;
        i = i + 1;
    }
    let z = w.max(1) + y;
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_method_clone_plus_peer(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 3 {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w = w + 100;
        i = i + 1;
    }
    let z = w.clone() + y;
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_method_eq_peer(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 3 {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w = w + 100;
        i = i + 1;
    }
    let b = w.eq(&y);
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_method_lt_peer(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 3 {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w = w + 100;
        i = i + 1;
    }
    let b = w.lt(&y);
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_method_max_ascribed(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 3 {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w = w + 100;
        i = i + 1;
    }
    let z: u8 = w.max(1);
}

#[trust_vc::requires(y == 100u8)]
fn verified_loop_method_twin(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 1 {
        trust_vc::invariant!(i <= 1);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w = w + 100;
        i = i + 1;
    }
    let z = w + y;
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_method_clamp_result(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 3 {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w = w + 100;
        i = i + 1;
    }
    let z = w.clamp(0, 5);
    g8(z);
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_method_ne_peer(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 3 {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w = w + 100;
        i = i + 1;
    }
    if w.ne(&y) {
        let q = 1u8;
    }
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_method_result_compared(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 3 {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w = w + 100;
        i = i + 1;
    }
    let b = w.max(1) < y;
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_method_result_assigned(y: u8) {
    let mut t: u8 = 0;
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 3 {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w = w + 100;
        i = i + 1;
    }
    t = w.min(5);
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_method_result_struct_field(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 3 {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w = w + 100;
        i = i + 1;
    }
    let s = S2 { g: w.max(0) };
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_counter_loop_stmt(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    loop {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        if i >= 3 {
            break;
        }
        w = w + 100;
        i = i + 1;
    }
    let z = w.max(1) + y;
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_compound_method_peer(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 3 {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w += 100;
        i = i + 1;
    }
    let z = w.min(y);
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_method_cmp_peer(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 3 {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w = w + 100;
        i = i + 1;
    }
    let o = w.cmp(&y);
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_method_partial_cmp_peer(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 3 {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w = w + 100;
        i = i + 1;
    }
    let o = w.partial_cmp(&y);
}

#[trust_vc::requires(y == 100u8)]
fn never_loop_method_peer_receiver(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 3 {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w = w + 100;
        i = i + 1;
    }
    let b = y.lt(&w);
}

#[trust_vc::requires(y == 100u8)]
fn true_loop_method_untyped_comparison(y: u8) {
    let mut w = 0;
    let mut i: u8 = 0;
    while i < 3 {
        trust_vc::invariant!(i <= 3);
        trust_vc::invariant!(w as i64 == 100i64 * (i as i64));
        w = w + 100;
        i = i + 1;
    }
    let b = w.max(1) < 1000;
    trust_vc::assert!(y == 100u8);
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
        .join("../../target/untyped_binding_method_soundness_src");
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
        println!("METHOD|{file}|{func}|{got}|{raw}");
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
fn a_trait_method_on_a_loop_written_untyped_binding_types_it() {
    check(SRC_TRAIT_METHOD_RECEIVER, "trait_method_receiver.rs", 20);
}
