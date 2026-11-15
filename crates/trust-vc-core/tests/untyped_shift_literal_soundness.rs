// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A shift whose value operand is an unsuffixed literal form (`1 << k`,
//! `255 >> k`) is itself an untyped literal form (design-trust-proof-backend.md
//! §5b rule 1): its value has its LEFT operand's type, which the peer the
//! shift meets fixes; its amount is typed apart. `types::is_untyped_literal`
//! did not count it, so it stayed an `i32` value and met a `u8` peer as a
//! mixed, hence exact, operation; `!(1 << k)` also slipped past the refusal
//! of `!` over an untyped literal. Every `never_*` program panics under `-C
//! overflow-checks=on` (or asserts a value that is false natively); each was
//! `Verified` on origin/main dd3859d2 (`never_shift_returned_at_u8` was
//! refused there, and the first version of this change made it `Verified`:
//! the result bound the shift at `u8` with no `u8` amount check). The
//! `true_*` twin runs clean natively and must not be refuted.
//!
//! A shift form that meets no peer in its own obligation (`g8(1 << k)`, a
//! returned `1 << k`) takes a type this encoding does not see, so, like an
//! untyped conditional, it is checked in every width its literal fits.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC_UNTYPED_SHIFT: &str = r####"
fn g8(x: u8) {}

#[trust_vc::requires(k == 7u32 && y == 200u8)]
fn never_shift_untyped_literal_plus_peer(k: u32, y: u8) {
    let z = (1 << k) + y;
}

#[trust_vc::requires(k == 0u32 && y == 1u8)]
fn never_shr_untyped_literal_plus_peer(k: u32, y: u8) {
    let z = (255 >> k) + y;
}

#[trust_vc::requires(k == 0u32 && y == 2u8)]
fn never_not_of_shift_plus_peer(k: u32, y: u8) {
    let z = !(1 << k) + y;
}

#[trust_vc::requires(k == 8u32)]
fn never_shift_untyped_literal_call_arg(k: u32) {
    g8(1 << k);
}

#[trust_vc::requires(k == 0u32)]
fn never_shift_value_false(k: u32) {
    trust_vc::assert!(!(1 << k) != 254u8);
}

#[trust_vc::requires(k == 0u32)]
fn never_shr_value_false(k: u32) {
    trust_vc::assert!((200 >> k) + 100 != 44u8);
}

#[trust_vc::requires(k == 7u32 && y == 2u8)]
fn never_shift_untyped_mul_peer(k: u32, y: u8) {
    let z = (1 << k) * y;
}

fn g64(x: u64) {}

#[trust_vc::requires(k == 7u32 && y == 200u8)]
fn never_shift_untyped_binding_then_peer(k: u32, y: u8) {
    let a = 1 << k;
    let z = a + y;
}

#[trust_vc::requires(k == 7u32 && y == 200u8)]
fn never_shift_inside_literal_tree(k: u32, y: u8) {
    let z = ((1 << k) + 1) + y;
}

#[trust_vc::requires(k == 0u32)]
fn never_shr_value_in_tree(k: u32) {
    trust_vc::assert!((255 >> k) + 1 != 0u8);
}

#[trust_vc::requires(k == 7u32 && y == 200u8)]
fn never_shift_of_conditional_literal(k: u32, y: u8, c: bool) {
    let z = ((if c { 1 } else { 1 }) << k) + y;
}

#[trust_vc::requires(k == 8u32)]
fn never_shift_returned_at_u8(k: u32) -> u8 {
    1 << k
}

#[trust_vc::requires(k == 8u32 && y == 0u8)]
fn never_shift_amount_at_peer_width(k: u32, y: u8) {
    let z = (1 << k) + y;
}

#[trust_vc::requires(k == 5u32)]
fn true_shift_amount_valid_in_every_width(k: u32) {
    let z = 1 << k;
    trust_vc::assert!(k == 5u32);
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
        .join("../../target/untyped_shift_literal_soundness_src");
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
        println!("SHIFT|{file}|{func}|{got}|{raw}");
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
fn a_shift_of_an_unsuffixed_literal_takes_its_peer_type() {
    check(SRC_UNTYPED_SHIFT, "untyped_shift.rs", 14);
}
