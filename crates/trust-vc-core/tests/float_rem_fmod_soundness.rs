// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! TRUST-VC-FREM-1: Rust's float `%` is C `fmod`, never the IEEE remainder.
//!
//! The encoder lowered float `%` to SMT-LIB `fp.rem`, the IEEE 754 remainder
//! whose quotient rounds to nearest-even (`fp.rem(5, 3) = -1`), while Rust's
//! `%` truncates and keeps the dividend's sign (`5.0 % 3.0 == 2.0`). Measured
//! 2026-10-06 on the `trust-vc` CLI that atpkg installs (0.6.0, b917cb51),
//! with the programs below:
//!
//! * the FALSE `x == 5, y == 3 => x % y < 0` at f32 was `verified`;
//! * the TRUE `x == 5, y == 3 => x % y == 2` at f64 was refuted with
//!   `ret = -1.0`;
//! * the TRUE `0 <= x <= 1e6, y == 3 => x % y >= 0` was refuted at f64
//!   (`x = 1.9999999999999998`) and at f32 (`x = 1.9999999`).
//!
//! This file drives the same source-to-verdict path the CLI drives
//! (`verify_function_from_file`). Every TRUE program must verify; every
//! FALSE one must not, and is refuted where the solver answers.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_float_rem_fmod_{}_{}_{seq}.rs",
        std::process::id(),
        func
    ));
    std::fs::write(&path, src).expect("write fixture");
    let result =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            verify_function_from_file(path.to_str().expect("utf8 path"), func)
        })
        .map_err(|e| e.to_string());
    let _ = std::fs::remove_file(&path);
    result
}

#[derive(Clone, Copy, Debug)]
enum Expect {
    /// A true program: must verify.
    Verified,
    /// A false program: must be refuted with a counterexample.
    Refuted,
}

fn render(r: &Result<VerifyResult, String>) -> String {
    match r {
        Ok(VerifyResult::Verified) => "Verified".into(),
        Ok(VerifyResult::Counterexample {
            obligation_name, ..
        }) => format!("Counterexample({obligation_name})"),
        Ok(VerifyResult::Error { message }) => {
            format!("Error({})", message.chars().take(300).collect::<String>())
        }
        Ok(other) => format!("{:.300}", format!("{other:?}")),
        Err(e) => format!("Err({})", e.chars().take(300).collect::<String>()),
    }
}

fn check_table(src: &str, table: &[(&str, Expect)]) {
    let mut failures = Vec::new();
    for (func, expect) in table {
        let r = verify(src, func);
        let ok = match expect {
            Expect::Verified => matches!(r, Ok(VerifyResult::Verified)),
            Expect::Refuted => matches!(r, Ok(VerifyResult::Counterexample { .. })),
        };
        println!(
            "{func}: expect={expect:?} got={} {}",
            render(&r),
            if ok { "ok" } else { "MISMATCH" }
        );
        if !ok {
            failures.push(format!("{func}: expected {expect:?}, got {}", render(&r)));
        }
    }
    assert!(
        failures.is_empty(),
        "{} mismatch(es):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

use Expect::{Refuted, Verified};

/// The measured programs: float values spelled as integer casts, so only the
/// remainder itself is under test.
const CAST_SRC: &str = r#"
#![allow(dead_code, unused)]

// TRUE: 5.0 % 3.0 == 2.0. Bare fp.rem refuted it with ret = -1.0.
#[trust_vc::contract(
    requires(x == (5 as f64) && y == (3 as f64)),
    ensures(ret == (2 as f64)),
    returns(ret),
)]
fn rem_5_3_is_2(x: f64, y: f64) -> f64 {
    x % y
}

// FALSE: 5.0 % 3.0 == 2.0 is not negative. Bare fp.rem VERIFIED it at f32.
#[trust_vc::contract(
    requires(x == (5 as f32) && y == (3 as f32)),
    ensures(ret < (0 as f32)),
    returns(ret),
)]
fn rem_5_3_negative_f32(x: f32, y: f32) -> f32 {
    x % y
}

// FALSE at f64 too (bare fp.rem: solver unknown).
#[trust_vc::contract(
    requires(x == (5 as f64) && y == (3 as f64)),
    ensures(ret < (0 as f64)),
    returns(ret),
)]
fn rem_5_3_negative_f64(x: f64, y: f64) -> f64 {
    x % y
}

// TRUE: the dividend's sign, -5.0 % 3.0 == -2.0 (fp.rem: +1.0).
#[trust_vc::contract(
    requires(x == (-5 as f64) && y == (3 as f64)),
    ensures(ret == (-2 as f64)),
    returns(ret),
)]
fn rem_neg5_3_is_neg2(x: f64, y: f64) -> f64 {
    x % y
}

// TRUE: the tie 3.0 % 2.0 == 1.0 (1.5 rounds to even 2, so fp.rem: -1.0).
#[trust_vc::contract(
    requires(x == (3 as f64) && y == (2 as f64)),
    ensures(ret == (1 as f64)),
    returns(ret),
)]
fn rem_3_2_is_1(x: f64, y: f64) -> f64 {
    x % y
}

// TRUE: -6.0 % 3.0 is -0.0, a NEGATIVE zero, so 1 / (x % y) is -inf. The
// clause reads the remainder itself: `ret` is bound to the body by the
// source `==`, IEEE equality, which does not carry the sign of a zero.
#[trust_vc::contract(
    requires(x == (-6 as f64) && y == (3 as f64)),
    ensures((1 as f64) / (x % y) < (0 as f64)),
    returns(ret),
)]
fn rem_neg6_3_is_negative_zero(x: f64, y: f64) -> f64 {
    x % y
}

// FALSE: -6.0 % 3.0 is -0.0, not +0.0.
#[trust_vc::contract(
    requires(x == (-6 as f64) && y == (3 as f64)),
    ensures((1 as f64) / (x % y) > (0 as f64)),
    returns(ret),
)]
fn rem_neg6_3_is_positive_zero(x: f64, y: f64) -> f64 {
    x % y
}

// TRUE: every finite f32 x in [0, 1e6] has x % 3.0 >= 0.0. Bare fp.rem
// refuted it with x = 1.9999999.
#[trust_vc::contract(
    requires(x >= (0 as f32) && x <= (1000000 as f32) && y == (3 as f32)),
    ensures(ret >= (0 as f32)),
    returns(ret),
)]
fn rem_nonnegative_f32(x: f32, y: f32) -> f32 {
    x % y
}
"#;

#[test]
fn float_rem_true_programs_verify() {
    check_table(
        CAST_SRC,
        &[
            ("rem_5_3_is_2", Verified),
            ("rem_neg5_3_is_neg2", Verified),
            ("rem_3_2_is_1", Verified),
            ("rem_neg6_3_is_negative_zero", Verified),
            ("rem_nonnegative_f32", Verified),
        ],
    );
}

#[test]
fn float_rem_false_programs_are_refuted() {
    check_table(
        CAST_SRC,
        &[
            ("rem_5_3_negative_f32", Refuted),
            ("rem_5_3_negative_f64", Refuted),
            ("rem_neg6_3_is_positive_zero", Refuted),
        ],
    );
}

/// The same remainder written the way a program writes it: suffixed float
/// literals in the body and in the contract.
const LITERAL_SRC: &str = r#"
#![allow(dead_code, unused)]

// TRUE.
#[trust_vc::contract(
    ensures(ret == 2.0f64),
    returns(ret),
)]
fn lit_rem_is_2() -> f64 {
    5.0f64 % 3.0f64
}

// FALSE.
#[trust_vc::contract(
    ensures(ret < 0.0f32),
    returns(ret),
)]
fn lit_rem_negative_f32() -> f32 {
    5.0f32 % 3.0f32
}
"#;

#[test]
fn float_rem_is_fmod_on_literal_operands() {
    check_table(
        LITERAL_SRC,
        &[
            ("lit_rem_is_2", Verified),
            ("lit_rem_negative_f32", Refuted),
        ],
    );
}
