// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Soundness guards for the casts-bitvec literal-width cluster (round-3 audit).
//!
//! An out-of-(signed)-range positive integer literal (e.g. `200`) fits the
//! UNSIGNED byte range `[0, 255]` but NOT the SIGNED `i8` range `[-128, 127]`.
//! The literal encoder (`encode_int_lit`) used `fits_in_bv` (signed-OR-unsigned)
//! to pick the BV width, so for a SIGNED-typed literal it encoded `200` as the
//! width-8 constant `0xC8` tagged signed, i.e. `-56`. This silently REDEFINED
//! the constraint:
//!   * `requires(x < 200)` became `requires(x < -56)`, so `assert!(x < 0)`
//!     verified even though `x = 100` is a legal `i8` with `100 < 200` true and
//!     `100 < 0` false — a catastrophic false `Verified`.
//!   * `requires(x == -56) |- assert!(x == 200)` verified because `-56` and the
//!     wrapped `200` share the bit pattern `0xC8`.
//!   * the same wrap aliased the value through an `as i32` cast / a unary `-` /
//!     a bitwise `|`.
//!
//! Fix: choose the literal's BV width by the SIGNEDNESS-CORRECT fitting
//! predicate. A signed literal must fit the signed range of the width; when it
//! does not, widen to the smallest width that PRESERVES the value (later width
//! coercion sign-extends operands at comparison sites) rather than two's-
//! complement wrapping it into a different value.
//!
//! Both directions are pinned: every genuinely-false goal must NOT verify, and
//! every in-range / legitimately-unsigned / true sibling must STILL verify (no
//! over-rejection). The cache is disabled so a stale `verified` entry from a
//! pre-fix run cannot mask a regression.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
// ---------- FALSE goals: out-of-signed-range literal must NOT silently wrap ----------

// Signed var pinned negative, asserted equal to an out-of-signed-range positive
// literal: `200` must stay `200` (no i8 equals it), NOT alias `-56`.
#[trust_vc::requires(x == -56)]
fn eq_200_false(x: i8) {
    trust_vc::assert!(x == 200);
}

// `128` fits u8 but is `i8::MIN` if wrapped; must not alias the pinned `-128`.
#[trust_vc::requires(x == -128)]
fn minus128_eq_128_false(x: i8) {
    trust_vc::assert!(x == 128);
}

// Out-of-range literal in an INEQUALITY precondition (runtime-satisfiable):
// every i8 is < 200, so `assert!(x < 0)` is genuinely false (witness x = 127).
#[trust_vc::requires(x < 200)]
fn lt200_neg_false(x: i8) {
    trust_vc::assert!(x < 0);
}

#[trust_vc::requires(x <= 200)]
fn le200_neg_false(x: i8) {
    trust_vc::assert!(x < 0);
}

// Negative out-of-range literal via unary `-` (200 -> -56 -> +56 if wrapped):
// every i8 is > -200, so `assert!(x > 0)` is genuinely false (witness x = -1).
#[trust_vc::requires(x > -200)]
fn gtneg200_pos_false(x: i8) {
    trust_vc::assert!(x > 0);
}

// Valid Rust: u8 200 cast to i8 is -56; (-56 as i32) == 200 is false at runtime.
#[trust_vc::requires(x == 200u8)]
fn cast_i32_eq200_false(x: u8) {
    let y: i8 = x as i8;
    trust_vc::assert!((y as i32) == 200);
}

// Out-of-range literal in a bitwise `|`: x = 0, 0 | 200 = 200, 200 < 0 is false.
#[trust_vc::requires(x == 0)]
fn or200_neg_false(x: i8) {
    trust_vc::assert!((x | 200) < 0);
}

// ---------- SAFE / TRUE siblings: must STILL verify (NO over-rejection) ----------

// In-range signed literal: every x < 50 is < 100.
#[trust_vc::requires(x < 50)]
fn lt50_lt100_true(x: i8) {
    trust_vc::assert!(x < 100);
}

// In-range cast: 100 fits i8, (100 as i32) == 100 holds.
#[trust_vc::requires(x == 100u8)]
fn cast_i32_eq100_true(x: u8) {
    let y: i8 = x as i8;
    trust_vc::assert!((y as i32) == 100);
}

// Legitimate suffixed unsigned literal in the unsigned byte range.
#[trust_vc::requires(x == 200u8)]
fn u8_suffixed_200_gt100_true(x: u8) {
    trust_vc::assert!(x > 100u8);
}

// Unsuffixed 200 against an UNSIGNED var (valid: fits u8).
#[trust_vc::requires(x == 200)]
fn u8_unsuffixed_200_gt100_true(x: u8) {
    trust_vc::assert!(x > 100);
}

// Genuinely-true signed equality (negative in-range literal unchanged).
#[trust_vc::requires(x == -56)]
fn eq_neg56_true(x: i8) {
    trust_vc::assert!(x == -56);
}

// ---------- CONTROLS already-correct: must NOT verify ----------

// In-range literal, genuinely-false goal (x = 31 satisfies x < 50 but not x < 0).
#[trust_vc::requires(x < 50)]
fn lt50_neg_control_false(x: i8) {
    trust_vc::assert!(x < 0);
}

// 200 fits SIGNED i32 (no wrap): x = 200 is a real counterexample to x < 0.
#[trust_vc::requires(x == 200)]
fn i32_eq200_neg_control_false(x: i32) {
    trust_vc::assert!(x < 0);
}

// 201 != -56 even when wrapped (0xC9 vs 0xC8): already a counterexample.
#[trust_vc::requires(x == -56)]
fn eq_201_control_false(x: i8) {
    trust_vc::assert!(x == 201);
}
"####;

fn run(func: &str) -> VerifyResult {
    // Disable the persistent verification cache so a stale `verified` entry
    // (e.g. written by a pre-fix run with the same IR fingerprint) cannot mask a
    // regression in this soundness guard.
    // Serialized behind the process-wide env lock and restored on scope exit
    // (guards drop before the lock releases) via the workspace env choke point.
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let dir = std::env::temp_dir().join("trust_vc_casts_literal_width_soundness");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{func}.rs"));
    let mut f = std::fs::File::create(&path).unwrap();
    f.write_all(SRC.as_bytes()).unwrap();
    drop(f);
    verify_function_from_file(path.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    })
}

fn assert_not_verified(func: &str) {
    let r = run(func);
    assert!(
        !r.is_verified(),
        "UNSOUND: out-of-signed-range literal goal {func} must NOT verify \
         (a positive literal that does not fit the signed width must not wrap \
         into a different negative value), got {r:?}"
    );
}

fn assert_verified(func: &str) {
    let r = run(func);
    assert!(
        r.is_verified(),
        "OVER-REJECTION: in-range / true sibling {func} must still verify, got {r:?}"
    );
}

#[test]
fn out_of_signed_range_literal_goals_do_not_verify() {
    for f in [
        "eq_200_false",
        "minus128_eq_128_false",
        "lt200_neg_false",
        "le200_neg_false",
        "gtneg200_pos_false",
        "cast_i32_eq200_false",
        "or200_neg_false",
    ] {
        assert_not_verified(f);
    }
}

#[test]
fn in_range_and_true_siblings_still_verify() {
    for f in [
        "lt50_lt100_true",
        "cast_i32_eq100_true",
        "u8_suffixed_200_gt100_true",
        "u8_unsuffixed_200_gt100_true",
        "eq_neg56_true",
    ] {
        assert_verified(f);
    }
}

#[test]
fn already_correct_controls_do_not_verify() {
    for f in [
        "lt50_neg_control_false",
        "i32_eq200_neg_control_false",
        "eq_201_control_false",
    ] {
        assert_not_verified(f);
    }
}
