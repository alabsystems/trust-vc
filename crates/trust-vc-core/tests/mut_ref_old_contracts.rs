// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Classic `old()` in exec-fn contracts for scalar `&mut` parameters —
//! slice A of the mut-ref two-state keystone.
//!
//! Semantics (Verus classic pre/post model, upstream refs.rs `add1` shape):
//! - `old(P)` / `*old(P)` in `requires`/`ensures` denotes the ENTRY (pre-call)
//!   value of a supported scalar `&mut` param — the declared param symbol.
//! - Bare `P` / `*P` in `ensures` keeps the existing FINAL-value substitution;
//!   bare `P` in `requires` keeps entry semantics (already live).
//!
//! THE SOUNDNESS SPLIT this suite pins in BOTH directions: the resolver's
//! per-param clean-final/no-escape/no-early-exit validation applies ONLY to
//! bare (final-semantics) references. Old-only references skip it — the entry
//! value is path-independent, so `ensures(old(x) < 100)` on an early-exit or
//! escaping body must NOT fail closed (missing split = needless
//! incompleteness), while a bare reference on the same body MUST keep failing
//! closed (inverted split = catastrophic false `Verified`).
//!
//! Fail-closed boundaries pinned here: `old()` over a non-`&mut` param or a
//! non-bare argument is a HARD error ("old() is only supported on scalar &mut
//! parameters" — silently reading the current value would over-prove);
//! `old()` under a quantifier/closure binder in `ensures` stays fail-closed
//! via the closure guard. Slice B (landed): `old()` in body asserts renders
//! the ENTRY symbol — see `mut_ref_old_body_asserts.rs` for its battery; the
//! T12 pin below keeps the exact former boundary shape as a positive witness.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
// ---------- (a) canonical add1: old = ENTRY, bare deref = FINAL ----------

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(*x == *old(x) + 1u64)]
fn old_add1_verified(x: &mut u64) {
    *x = *x + 1u64;
}

// ---------- (b) directionality witness, both ways ----------

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(*x == *old(x))]
fn old_entry_vs_final_counterexample(x: &mut u64) {
    *x = *x + 1u64;
}

// bare-P-in-ensures still reads POST (the p8 pin, must stay a counterexample)
#[trust_vc::requires(x == 10u64)]
#[trust_vc::ensures(x == 10u64)]
fn bare_final_pin_counterexample(x: &mut u64) {
    *x = 5u64;
}

// old(P) reads ENTRY on the same body: true against entry...
#[trust_vc::requires(x == 10u64)]
#[trust_vc::ensures(old(x) == 10u64)]
fn old_entry_pin_verified(x: &mut u64) {
    *x = 5u64;
}

// ...and false against the post value (if this verifies, old resolved to
// post — the classic vacuous-discharge bug).
#[trust_vc::requires(x == 10u64)]
#[trust_vc::ensures(old(x) == 5u64)]
fn old_reads_post_tripwire_counterexample(x: &mut u64) {
    *x = 5u64;
}

// ---------- (c)/(d) THE SPLIT: early exit ----------

// old-only reference: entry value is path-independent — must NOT fail closed.
#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(old(x) < 100u64)]
fn old_only_early_exit_verified(x: &mut u64, c: bool) {
    if c {
        return;
    }
    *x = 5u64;
}

// bare reference on the same body shape: fall-through final need not hold on
// the early-exit path — MUST keep failing closed.
#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(x == old(x) + 1u64)]
fn bare_early_exit_fails_closed(x: &mut u64, c: bool) {
    if c {
        return;
    }
    *x = *x + 1u64;
}

// ---------- THE SPLIT: escaping reference ----------

// old-only reference: escapes change the FINAL value, never the entry — must
// NOT fail closed.
#[trust_vc::requires(x == 5u64)]
#[trust_vc::ensures(old(x) == 5u64)]
fn old_only_escape_verified(x: &mut u64) {
    let r: &mut u64 = x;
    *r = 9u64;
}

// bare reference on the same body: the escaped final is untrusted — MUST keep
// failing closed (the p11 pin).
#[trust_vc::requires(x == 5u64)]
#[trust_vc::ensures(x == 9u64)]
fn bare_escape_fails_closed(x: &mut u64) {
    let r: &mut u64 = x;
    *r = 9u64;
}

// mixed params in ONE obligation: `a` old-only (skips validation despite the
// escape), `b` bare with a clean final (validated, passes).
#[trust_vc::requires(a == 1u64)]
#[trust_vc::ensures(b == old(a) + 1u64)]
fn old_and_bare_mixed_verified(a: &mut u64, b: &mut u64) {
    let r: &mut u64 = a;
    *r = 100u64;
    *b = 2u64;
}

// ---------- (e) old() over a non-&mut param: HARD error ----------

#[trust_vc::requires(y < 10u64)]
#[trust_vc::ensures(old(y) < 10u64)]
fn old_by_value_param_error(x: &mut u64, y: u64) {
    *x = y;
}

#[trust_vc::ensures(old(y) < 10u64)]
fn old_shared_ref_param_error(x: &mut u64, y: &u64) {
    *x = 1u64;
}

#[trust_vc::requires(old(y) < 10u64)]
#[trust_vc::ensures(true)]
fn old_non_mut_ref_requires_error(x: &mut u64, y: u64) {
    *x = y;
}

// boundary pin: with NO scalar &mut param in the signature the slice-A pass
// never runs; old() must still fail closed (encoder rejection), just without
// the slice-A message.
#[trust_vc::ensures(old(y) == y)]
fn old_without_any_mut_ref_param_error(y: u64) {
    let _ = y;
}

// ---------- (f) never-recurse-into-replacement ----------

// If the rewriter recursed into the inserted entry symbol, `old(x)` would be
// final-substituted to `7u64` and this would flip to a counterexample.
#[trust_vc::requires(x == 5u64)]
#[trust_vc::ensures(old(x) == 5u64)]
fn old_never_recurse_verified(x: &mut u64) {
    *x = 7u64;
}

// non-vacuity companion: old genuinely reads ENTRY (5), not the final 7.
#[trust_vc::requires(x == 5u64)]
#[trust_vc::ensures(old(x) == 7u64)]
fn old_never_recurse_counterexample(x: &mut u64) {
    *x = 7u64;
}

// ---------- (g) deref spelling parity ----------

#[trust_vc::requires(x == 5u64)]
#[trust_vc::ensures(*old(x) == 5u64)]
fn outer_deref_old_verified(x: &mut u64) {
    *x = 7u64;
}

#[trust_vc::requires(x == 5u64)]
#[trust_vc::ensures(old(*x) == 5u64)]
fn inner_deref_old_verified(x: &mut u64) {
    *x = 7u64;
}

#[trust_vc::requires(x == 5u64)]
#[trust_vc::ensures(*old(x) == 7u64)]
fn outer_deref_old_counterexample(x: &mut u64) {
    *x = 7u64;
}

// ---------- no-vacuity relation cross-check (T4) ----------

#[trust_vc::requires(x >= 1u64)]
#[trust_vc::requires(x <= 1000u64)]
#[trust_vc::ensures(x == old(x) * 2u64)]
fn old_relation_double_verified(x: &mut u64) {
    *x = *x * 2u64;
}

#[trust_vc::requires(x >= 1u64)]
#[trust_vc::requires(x <= 1000u64)]
#[trust_vc::ensures(x == old(x))]
fn old_relation_double_counterexample(x: &mut u64) {
    *x = *x * 2u64;
}

// ---------- requires-side old() (T6) ----------

#[trust_vc::requires(*old(x) < 10u64)]
#[trust_vc::ensures(*x == *old(x) + 1u64)]
fn requires_old_add1_verified(x: &mut u64) {
    *x = *x + 1u64;
}

// requires-old constrains the ENTRY value; bare x in ensures is the FINAL.
#[trust_vc::requires(old(x) == 5u64)]
#[trust_vc::ensures(x == 7u64)]
fn requires_old_entry_constraint_verified(x: &mut u64) {
    *x = 7u64;
}

#[trust_vc::requires(old(x) == 5u64)]
#[trust_vc::ensures(x == 5u64)]
fn requires_old_entry_constraint_counterexample(x: &mut u64) {
    *x = 7u64;
}

// ---------- (T8) non-bare old() arguments: HARD error ----------

#[trust_vc::requires(x < 5u64)]
#[trust_vc::ensures(old(x + 1u64) == 6u64)]
fn old_arith_arg_error(x: &mut u64) {
    *x = 1u64;
}

// ---------- (T9) old under a quantifier/closure binder: fail-closed ----------

#[trust_vc::requires(x < 5u64)]
#[trust_vc::ensures(forall(|i: u64| old(x) < 100u64))]
fn old_under_closure_fails_closed(x: &mut u64) {
    *x = 1u64;
}

// ---------- (T11) unchanged param tautology ----------

#[trust_vc::requires(x == 5u64)]
#[trust_vc::ensures(x == old(x))]
fn unchanged_param_old_tautology_verified(x: &mut u64) {}

// ---------- (T12) slice-B boundary: body-assert old() now ENTRY ----------

// Slice B landed: `*old(x)` in a body assert renders as the ENTRY symbol, so
// this exact shape (assert AFTER the write) verifies against the entry value
// 10 — NOT the post value 5. The full time-travel battery (both directions,
// aliases, branches, fail-closed boundaries) lives in
// `mut_ref_old_body_asserts.rs`.
#[trust_vc::requires(x == 10u64)]
#[trust_vc::ensures(true)]
fn body_assert_old_still_blocked(x: &mut u64) {
    *x = 5u64;
    trust_vc::assert!(*old(x) == 10u64);
}
"####;

fn run(func: &str) -> VerifyResult {
    // The on-disk VC-result cache stores only `verified` verdicts and replays
    // them without re-encoding — it MUST be disabled for true verdicts.
    // Serialized behind the process-wide env lock and restored on scope exit
    // (guards drop before the lock releases) via the workspace env choke point.
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let dir = std::env::temp_dir().join("trust_vc_mut_ref_old_contracts");
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

fn assert_verified(func: &str) {
    let r = run(func);
    assert!(
        r.is_verified(),
        "{func} must verify (no over-rejection), got: {r:?}"
    );
}

fn assert_counterexample(func: &str) {
    let r = run(func);
    assert!(
        r.is_counterexample(),
        "{func} must be a Counterexample (never Verified — directionality), got: {r:?}"
    );
}

fn assert_error_contains(func: &str, fragment: &str) {
    let r = run(func);
    let VerifyResult::Error { message } = &r else {
        panic!("{func} must fail closed with Error, got: {r:?}");
    };
    assert!(
        message.contains(fragment),
        "{func} error must contain `{fragment}`, got: {message}"
    );
}

const OLD_HARD_ERROR: &str = "old() is only supported on scalar &mut parameters";

// ---- (a) canonical shape ----

#[test]
fn battery_a_old_add1_verified() {
    assert_verified("old_add1_verified");
}

// ---- (b) directionality, both ways ----

#[test]
fn battery_b_old_entry_vs_final_counterexample() {
    assert_counterexample("old_entry_vs_final_counterexample");
}

#[test]
fn battery_b_bare_final_pin_counterexample() {
    assert_counterexample("bare_final_pin_counterexample");
}

#[test]
fn battery_b_old_entry_pin_verified() {
    assert_verified("old_entry_pin_verified");
}

#[test]
fn battery_b_old_reads_post_tripwire_counterexample() {
    assert_counterexample("old_reads_post_tripwire_counterexample");
}

// ---- (c)/(d) the split: early exit ----

#[test]
fn battery_c_old_only_early_exit_verified() {
    assert_verified("old_only_early_exit_verified");
}

#[test]
fn battery_d_bare_early_exit_fails_closed() {
    assert_error_contains("bare_early_exit_fails_closed", "early");
}

// ---- the split: escapes ----

#[test]
fn split_old_only_escape_verified() {
    assert_verified("old_only_escape_verified");
}

#[test]
fn split_bare_escape_fails_closed() {
    assert_error_contains("bare_escape_fails_closed", "escape");
}

#[test]
fn split_old_and_bare_mixed_verified() {
    assert_verified("old_and_bare_mixed_verified");
}

// ---- (e) old() over non-&mut params ----

#[test]
fn battery_e_old_by_value_param_error() {
    assert_error_contains("old_by_value_param_error", OLD_HARD_ERROR);
}

#[test]
fn battery_e_old_shared_ref_param_error() {
    assert_error_contains("old_shared_ref_param_error", OLD_HARD_ERROR);
}

#[test]
fn battery_e_old_non_mut_ref_requires_error() {
    assert_error_contains("old_non_mut_ref_requires_error", OLD_HARD_ERROR);
}

#[test]
fn battery_e_old_without_any_mut_ref_param_still_fails_closed() {
    // No scalar &mut param → the slice-A pass never runs; the encoder still
    // rejects the unresolved `old` call (fail-closed, pre-existing message).
    let r = run("old_without_any_mut_ref_param_error");
    assert!(
        r.is_error(),
        "old() without any scalar &mut param must stay fail-closed, got: {r:?}"
    );
}

// ---- (f) never-recurse ----

#[test]
fn battery_f_old_never_recurse_verified() {
    assert_verified("old_never_recurse_verified");
}

#[test]
fn battery_f_old_never_recurse_counterexample() {
    assert_counterexample("old_never_recurse_counterexample");
}

// ---- (g) deref spelling parity ----

#[test]
fn battery_g_outer_deref_old_verified() {
    assert_verified("outer_deref_old_verified");
}

#[test]
fn battery_g_inner_deref_old_verified() {
    assert_verified("inner_deref_old_verified");
}

#[test]
fn battery_g_outer_deref_old_counterexample() {
    assert_counterexample("outer_deref_old_counterexample");
}

// ---- no-vacuity relation (T4) ----

#[test]
fn relation_double_verified() {
    assert_verified("old_relation_double_verified");
}

#[test]
fn relation_double_counterexample() {
    assert_counterexample("old_relation_double_counterexample");
}

// ---- requires-side old() (T6) ----

#[test]
fn requires_old_add1_verified_test() {
    assert_verified("requires_old_add1_verified");
}

#[test]
fn requires_old_entry_constraint_verified_test() {
    assert_verified("requires_old_entry_constraint_verified");
}

#[test]
fn requires_old_entry_constraint_counterexample_test() {
    assert_counterexample("requires_old_entry_constraint_counterexample");
}

// ---- (T8) non-bare arguments ----

#[test]
fn battery_t8_old_arith_arg_error() {
    assert_error_contains("old_arith_arg_error", OLD_HARD_ERROR);
}

// ---- (T9) old under a closure binder ----

#[test]
fn battery_t9_old_under_closure_fails_closed() {
    assert_error_contains("old_under_closure_fails_closed", "closure");
}

// ---- (T11) unchanged param ----

#[test]
fn battery_t11_unchanged_param_old_tautology_verified() {
    assert_verified("unchanged_param_old_tautology_verified");
}

// ---- (T12) slice-B boundary pin (updated: slice B landed) ----

#[test]
fn battery_t12_body_assert_old_now_entry_verified() {
    assert_verified("body_assert_old_still_blocked");
}
