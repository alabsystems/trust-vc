// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS regression: exec arithmetic-safety of the RIGHT operand of a
//! short-circuit `&&` / `||`.
//!
//! `collect_value_position_arith_exprs` (body_extract.rs) previously descended
//! ONLY into the LEFT operand of a value-position `&&` / `||` and DROPPED the
//! right operand, so the right operand's divide-by-zero / overflow / shift-bounds
//! obligation was never emitted. Rust evaluates the `&&` right operand exactly
//! when the left is TRUE and the `||` right operand exactly when the left is
//! FALSE, so a panicking right operand under that condition silently `Verified`
//! (e.g. `b == 0 && a / b > 0` divides by zero whenever the left guard holds, and
//! `b != 0 || a / b > 0` divides by zero whenever the left guard fails).
//!
//! The fix descends into the right operand REACHABILITY-GUARDED by the left
//! operand condition (the left for `&&`, its negation for `||`), exactly mirroring
//! the `if cond { right }` / `if !cond { right }` path condition. This is
//! direction-correct, so it must:
//!   * FAIL CLOSED (Counterexample) for a right operand that panics under its
//!     reachability condition, and
//!   * STILL VERIFY a right operand that is genuinely SAFE under that condition
//!     (`b != 0 && a / b > 0`, `b == 0 || a / b > 0`) — NO over-rejection.

use std::sync::atomic::{AtomicU64, Ordering};
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SOURCE: &str = r#"
// ======================================================================
// UNSAFE: the short-circuit RIGHT operand panics on the path that reaches
// it -> must NEVER Verify.
// ======================================================================

// `&&` right runs when left is TRUE: b == 0 forces a / 0 (divide by zero).
#[trust_vc::ensures(true)]
fn and_div_unsafe(a: u64, b: u64) {
    let _ = b == 0 && a / b > 0;
}

// `||` right runs when left is FALSE: !(b != 0) == (b == 0) forces a / 0.
#[trust_vc::ensures(true)]
fn or_div_unsafe(a: u64, b: u64) {
    let _ = b != 0 || a / b > 0;
}

// `||` right addition overflow: reachable under !(a < 10) == (a >= 10).
#[trust_vc::ensures(true)]
fn or_add_unsafe(a: u64, b: u64) {
    let _ = a < 10 || a + b > 0;
}

// `||` right signed-division overflow: i32::MIN / -1 when b == -1.
#[trust_vc::ensures(true)]
fn or_signed_div_unsafe(a: i32, b: i32) {
    let _ = b != -1i32 || a / b > 0i32;
}

// Tuple-nested short circuit: the aggregate walker reaches the `&&`.
#[trust_vc::ensures(true)]
fn and_div_unsafe_in_tuple(a: u64, b: u64) {
    let _ = (b == 0 && a / b > 0, 0u64);
}

// Chained short circuit: outer `true &&` forces the inner `&&` whose left
// (b == 0) is the UNSAFE guard for a / b.
#[trust_vc::ensures(true)]
fn and_chain_unsafe(a: u64, b: u64) {
    let _ = true && (b == 0 && a / b > 0);
}

// `||` right shift overflow: 1 << b with b >= 64 is reachable under !(b < 64).
#[trust_vc::ensures(true)]
fn or_shift_unsafe(b: u64) {
    let _ = b < 64u64 || (1u64 << b) > 0u64;
}

// ======================================================================
// SAFE siblings: the right operand is genuinely safe UNDER its reachability
// condition -> must STILL Verify (no over-rejection).
// ======================================================================

// `&&` right runs only when b != 0 -> a / b never divides by zero.
#[trust_vc::ensures(true)]
fn and_div_safe(a: u64, b: u64) {
    let _ = b != 0 && a / b > 0;
}

// `||` right runs only when !(b == 0) == (b != 0) -> a / b is safe.
#[trust_vc::ensures(true)]
fn or_div_safe(a: u64, b: u64) {
    let _ = b == 0 || a / b > 0;
}

// `||` right addition that cannot overflow (`+ 0`), reachable or not.
#[trust_vc::ensures(true)]
fn or_add_safe(a: u64) {
    let _ = a >= 10 || a + 0u64 > 0;
}

// `||` right shift runs only when b < 64 -> 1 << b is in-bounds.
#[trust_vc::ensures(true)]
fn or_shift_safe(b: u64) {
    let _ = b >= 64u64 || (1u64 << b) > 0u64;
}

// Chained short circuit whose inner right operand is guarded SAFE.
#[trust_vc::ensures(true)]
fn and_chain_safe(a: u64, b: u64) {
    let _ = true && (b != 0 && a / b > 0);
}

// Tuple-nested SAFE short circuit (the aggregate walker must not over-reject).
#[trust_vc::ensures(true)]
fn and_div_safe_in_tuple(a: u64, b: u64) {
    let _ = (b != 0 && a / b > 0, 0u64);
}
"#;

static SEQ: AtomicU64 = AtomicU64::new(0);

fn verify(func: &str) -> VerifyResult {
    let path = std::env::temp_dir().join(format!(
        "trust_vc_sc_right_arith_{}_{}.rs",
        std::process::id(),
        SEQ.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, SOURCE).expect("write temp source");
    let result = verify_function_from_file(path.to_str().unwrap(), func)
        .unwrap_or_else(|e| panic!("{func} should verify-from-file without error: {e}"));
    let _ = std::fs::remove_file(&path);
    result
}

#[test]
fn short_circuit_right_operand_panic_never_verifies() {
    for f in [
        "and_div_unsafe",
        "or_div_unsafe",
        "or_add_unsafe",
        "or_signed_div_unsafe",
        "and_div_unsafe_in_tuple",
        "and_chain_unsafe",
        "or_shift_unsafe",
    ] {
        let result = verify(f);
        assert!(
            !matches!(result, VerifyResult::Verified),
            "{f}: a short-circuit RIGHT operand that panics under its reachability \
             condition must NEVER verify, got {result:?}"
        );
    }
}

#[test]
fn short_circuit_unsafe_right_operand_is_a_decisive_counterexample() {
    // Soundness witness: the dropped right-operand obligation is genuinely
    // enforced (a concrete refuting model), not merely Unknown.
    for f in ["and_div_unsafe", "or_div_unsafe", "or_add_unsafe"] {
        assert!(
            matches!(verify(f), VerifyResult::Counterexample { .. }),
            "{f}: should expose a decisive counterexample, got {:?}",
            verify(f)
        );
    }
}

#[test]
fn short_circuit_guarded_safe_right_operand_still_verifies() {
    // No over-rejection: a right operand that is SAFE under its reachability
    // condition must continue to Verify.
    for f in [
        "and_div_safe",
        "or_div_safe",
        "or_add_safe",
        "or_shift_safe",
        "and_chain_safe",
        "and_div_safe_in_tuple",
    ] {
        assert!(
            matches!(verify(f), VerifyResult::Verified),
            "{f}: a short-circuit right operand that is safe under its guard must \
             STILL verify (no over-rejection), got {:?}",
            verify(f)
        );
    }
}
