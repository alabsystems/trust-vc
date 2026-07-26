// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Slice B of the mut-ref two-state keystone: `old(P)` / `*old(P)` in body
//! asserts (exec-fn bodies) renders as the param ENTRY symbol.
//!
//! Semantics (Verus classic pre/post model, upstream basic.rs:613 `test_old`
//! shape): inside an exec-fn body with a supported scalar `&mut` param `P`,
//! `old(P)` / `old(*P)` / `*old(P)` / `*old(*P)` in `assert!`/`assume!`/value
//! positions denotes the ENTRY (pre-call) value — the DECLARED param symbol,
//! which the SSA/scoped-value machinery never rebinds (assignments rebind the
//! SCOPED value; havocs bind FRESH symbols; the bare declared symbol stays
//! pinned to the entry state by the `requires` assumptions).
//!
//! THE TIME-TRAVEL LANDMINE this suite pins in BOTH directions: the entry
//! symbol must be the PRE-ANY-ASSIGNMENT value even when the assert appears
//! AFTER writes through the param or through aliases. If the rendering ever
//! picked the CURRENT scoped value instead, `old()` would read the post state
//! — the catastrophic direction — so every positive test here has a tripwire
//! companion asserting the post-state reading is REFUTED (or rejected), never
//! Verified.
//!
//! Fail-closed boundaries pinned here: `old(field)` / `old(non-&mut)` /
//! `old()` / `old(expr)` in body asserts keep the PRE-EXISTING hard error
//! ("Unsupported old-state expression `old(...)` … current state as
//! pre-state") VERBATIM — deliberately unchanged so the manifest/port
//! fail-closed message pins (arrays.rs, mut_refs*.rs, …) stay intact; only
//! genuinely-supported shapes change behavior. `old()` under a
//! quantifier/closure binder in a body assert stays fail-closed (closure
//! bodies are rendered by the flat contract substituter, so the unresolved
//! `old` call is rejected by the encoder — never silently read as current
//! state).

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
// ---------- (a) upstream basic.rs:613 shape (exact compound-free spelling) ----------

#[trust_vc::requires(*old(y) < 100u64)]
fn basic_rs_613_old_div2_verified(y: &mut u64) {
    *y = *old(y) / 2u64;
    trust_vc::assert!(*y == *old(y) / 2u64);
}

// non-vacuity companion: the same body must REFUTE a wrong relation.
#[trust_vc::requires(*old(y) < 100u64)]
#[trust_vc::requires(*old(y) >= 10u64)]
fn basic_rs_613_wrong_relation_counterexample(y: &mut u64) {
    *y = *old(y) / 2u64;
    trust_vc::assert!(*y == *old(y));
}

// ---------- (b) time-travel: assert AFTER the write ----------

#[trust_vc::requires(x == 5u64)]
fn time_travel_entry_verified(x: &mut u64) {
    *x = 7u64;
    trust_vc::assert!(*old(x) == 5u64);
}

// If old() read the CURRENT (post-assignment) state this would verify — the
// catastrophic direction. It must be a counterexample.
#[trust_vc::requires(x == 5u64)]
fn time_travel_post_tripwire_counterexample(x: &mut u64) {
    *x = 7u64;
    trust_vc::assert!(*old(x) == 7u64);
}

// bare *x in the same position still reads the CURRENT value (directionality
// cross-check: current-state reads are untouched by slice B).
#[trust_vc::requires(x == 5u64)]
fn bare_current_read_verified(x: &mut u64) {
    *x = 7u64;
    trust_vc::assert!(*x == 7u64);
}

// ---------- (c) old AFTER multiple rebinds / branches ----------

// Multiple rebinds through branches + a subsequent write. (When slice B
// landed, the SEQUENTIAL double deref-assignment `*x = ..; *x = ..;` was a
// fail-closed modeling reject independent of old(); slice C lifted it — each
// straight-line write now rebinds in order, see mut_ref_compound_assign.rs —
// so both branch-arm rebinds and straight-line chains are supported.)
#[trust_vc::requires(x == 5u64)]
fn multiple_rebinds_entry_verified(x: &mut u64, c: bool) {
    if c {
        *x = 1u64;
    } else {
        *x = 2u64;
    }
    *x = 3u64;
    trust_vc::assert!(old(x) == 5u64);
}

#[trust_vc::requires(x == 5u64)]
fn multiple_rebinds_post_tripwire_counterexample(x: &mut u64, c: bool) {
    if c {
        *x = 1u64;
    } else {
        *x = 2u64;
    }
    *x = 3u64;
    trust_vc::assert!(old(x) == 3u64);
}

// Slice-C update: the sequential double deref-assignment is now SUPPORTED
// (each write rebinds in order). old() across the chain must still read the
// ENTRY value — with requires x == 5 the chain gives (5+1)*2 = 12, and
// old(x) == 5 must verify. The post-state tripwires for this shape live in
// mut_ref_compound_assign.rs (chain_* + old_across_compound_*).
#[trust_vc::requires(x == 5u64)]
fn sequential_double_write_old_reads_entry(x: &mut u64) {
    *x = *x + 1u64;
    *x = *x * 2u64;
    trust_vc::assert!(old(x) == 5u64);
}

#[trust_vc::requires(x == 5u64)]
fn branch_rebinds_entry_verified(x: &mut u64, c: bool) {
    if c {
        *x = 1u64;
    } else {
        *x = 2u64;
    }
    trust_vc::assert!(old(x) == 5u64);
}

// old() INSIDE a branch after that branch's write: still entry.
#[trust_vc::requires(x == 5u64)]
fn old_inside_branch_after_write_verified(x: &mut u64, c: bool) {
    if c {
        *x = 9u64;
        trust_vc::assert!(*old(x) == 5u64);
    }
}

// ---------- (d) alias write then old-assert (probed: entry semantics ship) ----------

#[trust_vc::requires(x == 5u64)]
fn alias_write_then_old_entry(x: &mut u64) {
    let r: &mut u64 = &mut *x;
    *r = 9u64;
    trust_vc::assert!(*old(x) == 5u64);
}

// NEVER-post-state tripwire: if this verifies, old() read the alias-written
// post value — catastrophic.
#[trust_vc::requires(x == 5u64)]
fn alias_write_then_old_post_tripwire(x: &mut u64) {
    let r: &mut u64 = &mut *x;
    *r = 9u64;
    trust_vc::assert!(*old(x) == 9u64);
}

// escape-by-call family: the callee havocs the referent; entry must still be
// the entry symbol (or fail closed — never the havoced/post value).
fn set9(p: &mut u64) {
    *p = 9u64;
}

#[trust_vc::requires(x == 5u64)]
fn call_escape_then_old_entry(x: &mut u64) {
    set9(x);
    trust_vc::assert!(*old(x) == 5u64);
}

#[trust_vc::requires(x == 5u64)]
fn call_escape_then_old_post_tripwire(x: &mut u64) {
    set9(x);
    trust_vc::assert!(*old(x) == 9u64);
}

// ---------- value-position old(): let-bound capture of entry ----------

#[trust_vc::requires(x == 5u64)]
fn old_in_let_value_verified(x: &mut u64) {
    *x = 7u64;
    let v: u64 = *old(x) + 1u64;
    trust_vc::assert!(v == 6u64);
}

// ---------- deref-spelling parity in body asserts ----------

#[trust_vc::requires(x == 5u64)]
fn body_inner_deref_old_verified(x: &mut u64) {
    *x = 7u64;
    trust_vc::assert!(old(*x) == 5u64);
}

#[trust_vc::requires(x == 5u64)]
fn body_bare_old_verified(x: &mut u64) {
    *x = 7u64;
    trust_vc::assert!(old(x) == 5u64);
}

// ---------- (e) fail-closed boundaries in body asserts ----------

struct S {
    f: u64,
}

#[trust_vc::requires(x == 5u64)]
fn body_old_field_error(x: &mut u64, s: S) {
    *x = s.f;
    trust_vc::assert!(old(s.f) == 5u64);
}

#[trust_vc::requires(x == 5u64)]
fn body_old_nonref_error(x: &mut u64, y: u64) {
    *x = y;
    trust_vc::assert!(old(y) == y);
}

#[trust_vc::requires(x == 5u64)]
fn body_old_zero_args_error(x: &mut u64) {
    *x = 7u64;
    trust_vc::assert!(old() == 5u64);
}

#[trust_vc::requires(x == 5u64)]
fn body_old_arith_arg_error(x: &mut u64) {
    *x = 7u64;
    trust_vc::assert!(old(x + 1u64) == 6u64);
}

// old() under a quantifier/closure binder in a body assert: the closure body
// is rendered by the flat substituter, so the unresolved `old` call must be
// rejected downstream (fail-closed) — never silently read as current state.
#[trust_vc::requires(x == 5u64)]
fn body_old_under_closure_fails_closed(x: &mut u64) {
    *x = 7u64;
    trust_vc::assert!(forall(|i: u64| old(x) < 100u64));
}
"####;

fn run(func: &str) -> VerifyResult {
    // The on-disk VC-result cache stores only `verified` verdicts and replays
    // them without re-encoding — it MUST be disabled for true verdicts.
    // Serialized behind the process-wide env lock and restored on scope exit
    // (guards drop before the lock releases) via the workspace env choke point.
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let dir = std::env::temp_dir().join("trust_vc_mut_ref_old_body_asserts");
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

/// Unknown-as-failure relaxation (docs/design-unknown-as-failure.md): a genuine
/// verification FAILURE — a model-bearing `Counterexample` OR a model-less
/// `NotProved` (incompleteness fail-close). The module contract for the (d)
/// tripwires is "REFUTED (or rejected), never Verified" — a NotProved is
/// "rejected", so directionality stays pinned without demanding a fabricated
/// model.
fn assert_fails(func: &str) {
    let r = run(func);
    assert!(
        r.is_failure(),
        "{func} must be a verification FAILURE — Counterexample or NotProved (never Verified — directionality), got: {r:?}"
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

// The PRE-EXISTING body-path hard error, kept verbatim for every unsupported
// old() shape (see the module doc — manifest/port pins depend on it).
const OLD_HARD_ERROR: &str = "Unsupported old-state expression `old(...)`";

// ---- (a) upstream basic.rs:613 shape ----

#[test]
fn battery_a_basic_rs_613_old_div2_verified() {
    assert_verified("basic_rs_613_old_div2_verified");
}

#[test]
fn battery_a_basic_rs_613_wrong_relation_counterexample() {
    assert_counterexample("basic_rs_613_wrong_relation_counterexample");
}

// ---- (b) time-travel, both directions ----

#[test]
fn battery_b_time_travel_entry_verified() {
    assert_verified("time_travel_entry_verified");
}

#[test]
fn battery_b_time_travel_post_tripwire_counterexample() {
    assert_counterexample("time_travel_post_tripwire_counterexample");
}

#[test]
fn battery_b_bare_current_read_verified() {
    assert_verified("bare_current_read_verified");
}

// ---- (c) multiple rebinds / branches ----

#[test]
fn battery_c_multiple_rebinds_entry_verified() {
    assert_verified("multiple_rebinds_entry_verified");
}

#[test]
fn battery_c_multiple_rebinds_post_tripwire_counterexample() {
    assert_counterexample("multiple_rebinds_post_tripwire_counterexample");
}

#[test]
fn battery_c_sequential_double_write_old_reads_entry() {
    // Slice C lifted the once-only sequential-write reject; old() across the
    // straight-line chain still reads the ENTRY value (never the post state —
    // the post tripwires are pinned in mut_ref_compound_assign.rs).
    assert_verified("sequential_double_write_old_reads_entry");
}

#[test]
fn battery_c_branch_rebinds_entry_verified() {
    assert_verified("branch_rebinds_entry_verified");
}

#[test]
fn battery_c_old_inside_branch_after_write_verified() {
    assert_verified("old_inside_branch_after_write_verified");
}

// ---- (d) alias write / call escape then old-assert ----
// PROBED + PINNED: the entry-asserts VERIFY with entry semantics (the reborrow
// alias write rebinds only the SCOPED value; the call escape havocs to a FRESH
// `x__havoc_0` symbol — the CE model below proves the declared symbol `x`
// stayed pinned at the entry value 5). The tripwires are genuine
// Counterexamples with model `x = 5` — the post-state reading is REFUTED,
// never Verified and never silently discharged.

#[test]
fn battery_d_alias_write_then_old_entry_pinned() {
    assert_verified("alias_write_then_old_entry");
}

#[test]
fn battery_d_alias_write_then_old_post_tripwire_counterexample() {
    assert_counterexample("alias_write_then_old_post_tripwire");
}

#[test]
fn battery_d_call_escape_then_old_entry_pinned() {
    assert_verified("call_escape_then_old_entry");
}

#[test]
fn battery_d_call_escape_then_old_post_tripwire_counterexample() {
    // Unknown-as-failure (docs/design-unknown-as-failure.md): the havoc'd fresh
    // symbol makes ay fail-close the post-state refutation to a model-less
    // NotProved — still "rejected, never Verified" per the (d) tripwire contract.
    assert_fails("call_escape_then_old_post_tripwire");
}

// ---- value position ----

#[test]
fn battery_value_old_in_let_value_verified() {
    assert_verified("old_in_let_value_verified");
}

// ---- deref-spelling parity ----

#[test]
fn battery_spelling_body_inner_deref_old_verified() {
    assert_verified("body_inner_deref_old_verified");
}

#[test]
fn battery_spelling_body_bare_old_verified() {
    assert_verified("body_bare_old_verified");
}

// ---- (e) fail-closed boundaries ----

#[test]
fn battery_e_body_old_field_error() {
    assert_error_contains("body_old_field_error", OLD_HARD_ERROR);
}

#[test]
fn battery_e_body_old_nonref_error() {
    assert_error_contains("body_old_nonref_error", OLD_HARD_ERROR);
}

#[test]
fn battery_e_body_old_zero_args_error() {
    assert_error_contains("body_old_zero_args_error", OLD_HARD_ERROR);
}

#[test]
fn battery_e_body_old_arith_arg_error() {
    assert_error_contains("body_old_arith_arg_error", OLD_HARD_ERROR);
}

#[test]
fn battery_e_body_old_under_closure_fails_closed() {
    let r = run("body_old_under_closure_fails_closed");
    assert!(
        r.is_error(),
        "old() under a closure binder in a body assert must stay fail-closed, got: {r:?}"
    );
}
