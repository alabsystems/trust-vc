// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Straight-line LOCAL scalar compound-assignment read-after coverage.
//!
//! `x op= rhs` on a `let mut` scalar local previously invalidated the binding,
//! so ANY later read of `x` failed closed as `unresolved variable` (sound but
//! incomplete — it blocked upstream `basic.rs` `test_compound_assign`
//! `x += 2; assert(x == 3)`). The fix desugars the straight-line case to
//! `x = (x) op (rhs)` (mirroring the slice-C deref desugar
//! `assign_deref_compound_expr`), reusing the SAME `old`/`rhs` renderings the
//! pre-existing scalar-compound overflow obligation already range-checks, so the
//! persisted value can never disagree with what was checked.
//!
//! These tests pin BOTH directions: the read-after now resolves and verifies
//! when correct / CEs when wrong, AND every soundness guard that keeps the
//! read-then-rebind fail-closed where a plain desugar would be unsound (loop
//! bodies, RHS side effects), plus the pre-existing overflow / divide-by-zero
//! obligations still fire in exec context.

use std::fs;
use std::path::Path;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verdict(src: &str, name: &str) -> String {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut h = DefaultHasher::new();
    name.hash(&mut h);
    let dir = Path::new("target/local_compound_assign_rebind");
    fs::create_dir_all(dir).unwrap();
    let p = dir.join(format!("{name}_{:x}.rs", h.finish()));
    fs::write(&p, src).unwrap();
    match verify_function_from_file(p.to_str().unwrap(), name) {
        Ok(VerifyResult::Verified) => "verified".into(),
        Ok(VerifyResult::Counterexample { .. }) => "counterexample".into(),
        Ok(VerifyResult::Unknown { reason, .. }) => format!("unknown: {reason}"),
        Ok(VerifyResult::Error { .. }) => "error".into(),
        Ok(other) => format!("other: {other:?}"),
        Err(_) => "error".into(),
    }
}

#[test]
fn straight_line_read_after_verifies() {
    let src = r####"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn straight_line_read_after_verifies() {
    let mut x: i32 = 1;
    x += 2;
    trust_vc::assert!(x == 3);
}
"####;
    assert_eq!(
        verdict(src, "straight_line_read_after_verifies"),
        "verified"
    );
}

#[test]
fn chained_compound_reads_track_the_running_value() {
    let src = r####"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn chained_compound_reads_track_the_running_value() {
    let mut x: i32 = 1;
    x += 2;
    x *= 2;
    trust_vc::assert!(x == 6);
}
"####;
    assert_eq!(
        verdict(src, "chained_compound_reads_track_the_running_value"),
        "verified"
    );
}

#[test]
fn wrong_read_after_is_a_counterexample() {
    let src = r####"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn wrong_read_after_is_a_counterexample() {
    let mut x: i32 = 1;
    x += 2;
    trust_vc::assert!(x == 4);
}
"####;
    assert_eq!(
        verdict(src, "wrong_read_after_is_a_counterexample"),
        "counterexample"
    );
}

#[test]
fn int_math_compound_reads_track_exactly() {
    let src = r####"
use trust_vc_types::int;

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn int_math_compound_reads_track_exactly() {
    let mut x: int = 5int;
    x -= 3int;
    trust_vc::assert!(x == 2int);
}
"####;
    assert_eq!(
        verdict(src, "int_math_compound_reads_track_exactly"),
        "verified"
    );
}

#[test]
fn bitwise_compound_tracks_and_refutes_wrong_value() {
    let ok = r####"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn bitwise_compound_tracks_and_refutes_wrong_value() {
    let mut x: u32 = 6;
    x ^= 3;
    trust_vc::assert!(x == 5);
}
"####;
    assert_eq!(
        verdict(ok, "bitwise_compound_tracks_and_refutes_wrong_value"),
        "verified"
    );
    let wrong = r####"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn bitwise_compound_tracks_and_refutes_wrong_value() {
    let mut x: u32 = 6;
    x ^= 3;
    trust_vc::assert!(x == 4);
}
"####;
    assert_eq!(
        verdict(wrong, "bitwise_compound_tracks_and_refutes_wrong_value"),
        "counterexample"
    );
}

// ---- SOUNDNESS GUARDS: the rebind must NOT fire where a plain desugar is unsound ----

#[test]
fn exec_overflow_still_counterexamples() {
    // The pre-existing scalar-compound overflow obligation still fires in exec
    // context: `p + 1` overflows at p == i8::MAX.
    let src = r####"
#[trust_vc::ensures(true)]
fn exec_overflow_still_counterexamples(p: i8) {
    let mut x: i8 = p;
    x += 1;
    trust_vc::assert!(x >= p);
}
"####;
    assert_eq!(
        verdict(src, "exec_overflow_still_counterexamples"),
        "counterexample"
    );
}

#[test]
fn exec_division_by_zero_still_counterexamples() {
    let src = r####"
#[trust_vc::ensures(true)]
fn exec_division_by_zero_still_counterexamples(p: i32) {
    let mut x: i32 = 10;
    x /= p;
    trust_vc::assert!(true);
}
"####;
    assert_eq!(
        verdict(src, "exec_division_by_zero_still_counterexamples"),
        "counterexample"
    );
}

#[test]
fn exec_bounded_compound_verifies() {
    let src = r####"
#[trust_vc::requires(p >= 0 && p < 100)]
#[trust_vc::ensures(true)]
fn exec_bounded_compound_verifies(p: i32) {
    let mut x: i32 = p;
    x += 1;
    trust_vc::assert!(x == p + 1);
}
"####;
    assert_eq!(verdict(src, "exec_bounded_compound_verifies"), "verified");
}

#[test]
fn rhs_side_effect_stays_fail_closed() {
    // Real compound evaluates the RHS BEFORE reading the place; the desugar
    // reads first, so an embedded RHS assignment keeps the pre-existing
    // fail-closed rejection (never a rebind that could reorder the effect).
    let src = r####"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn rhs_side_effect_stays_fail_closed() {
    let mut x: i32 = 1;
    let mut y: i32 = 0;
    x += { y = 5; y };
    trust_vc::assert!(x == 6);
}
"####;
    assert_eq!(verdict(src, "rhs_side_effect_stays_fail_closed"), "error");
}

#[test]
fn loop_body_compound_does_not_prove_first_iteration_facts() {
    // Inside a loop body the scoped read is the previous VISIT's value, not the
    // previous ITERATION's, so the rebind stays disabled: reading `x` after the
    // loop must NOT prove `x == 1` (false for n != 1). Fail-closed is sound.
    let src = r####"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn loop_body_compound_does_not_prove_first_iteration_facts(n: u32) {
    let mut x: u32 = 0;
    let mut i: u32 = 0;
    while i < n {
        x += 1;
        i += 1;
    }
    trust_vc::assert!(x == 1);
}
"####;
    let v = verdict(
        src,
        "loop_body_compound_does_not_prove_first_iteration_facts",
    );
    assert!(
        v == "error" || v == "counterexample" || v.starts_with("unknown"),
        "loop-body compound read-after must never VERIFY a first-iteration fact, got {v}"
    );
}
