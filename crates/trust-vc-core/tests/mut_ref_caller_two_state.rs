// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Caller-side two-state for scalar `&mut` arguments — slice D of the mut-ref
//! keystone (upstream refs.rs `test_mut_ref_arg_exec` shape).
//!
//! At a call `f(&mut v)` / `f(x)` (forwarding a scalar `&mut` param) where the
//! callee `f` carries requires/ensures over its `&mut` param `P`:
//! 1. REQUIRES DISCHARGE: the callee `requires` with `P := <pre-call value>`
//!    is a caller obligation (`__call_requires_pp{N}_...`) — a violated
//!    precondition is a Counterexample, never a silent proceed. `old(P)` in
//!    `requires` == the value AT CALL TIME (same pre-call map as bare `P`).
//! 2. HAVOC: after the call the referent is rebound to a FRESH unconstrained
//!    symbol — the caller's only post-call knowledge is the callee `ensures`.
//! 3. ENSURES ASSUME — THE DIRECTIONALITY LANDMINE: in the callee `ensures`,
//!    `old(P)` binds the PRE-call value and bare `P`/`*P` binds the POST-call
//!    fresh symbol, substituted in ONE simultaneous, never-recursing pass.
//!    Inverting either direction lets a wrong caller chain verify — the
//!    tripwires below pin both.
//!
//! Fail-closed boundaries pinned here: `&mut s.field` / non-scalar `&mut`
//! struct args / alias-local forwarding (`let r = &mut a; f(r)`) stay
//! fail-closed (error or CE — NEVER a stale-value Verified); a contract-less
//! callee is havoc-only (post-state unconstrained → CE on any stale claim); an
//! expression-position contracted call (`let _r = f(&mut v)`) discharges its
//! `requires` but DROPS the `ensures` assumption (the recording runs before
//! the havoc, so binding it would pin the postcondition to the pre-call value
//! — the p10 vacuity landmine); `&mut &x` temporaries never havoc `x`.
//!
//! CORRECTION (slice-D remediation): the original slice-D report claimed the
//! scope-outs above were "all fail-closed" — that was TRUE only for the
//! `let`-local variants pinned here (f8's alias local errors). For a DECLARED
//! `requires`-pinned param, the escaping shapes NOT owned by the call-arg
//! havoc — reborrow `&mut *(&mut p)`, `&mut &mut p`, method/UFCS/fn-pointer
//! call args, alias-local `let r = &mut p;` — fell back to the ENTRY symbol
//! and false-`Verified` on the pre-remediation tree. They are now genuinely
//! closed (borrow-escape havoc `havoc_mut_borrow_escaped_binding` + region
//! recording + short-circuit-RHS ensures drop) and pinned per shape in
//! `mut_ref_call_escape_probes.rs` (the committed 28-probe adversarial
//! battery).

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
// ---------- callees ----------

// upstream refs.rs add1, faithful contract (old-form requires AND ensures)
#[trust_vc::requires(*old(a) < 10u64)]
#[trust_vc::ensures(*a == *old(a) + 1u64)]
fn add1(a: &mut u64) {
    *a = *a + 1u64;
}

// bare-form contract (no old, absolute post value)
#[trust_vc::requires(a < 10u64)]
#[trust_vc::ensures(a == 7u64)]
fn set7(a: &mut u64) {
    *a = 7u64;
}

// deref-form contract spelling (the *a erasure path)
#[trust_vc::requires(*a < 10u64)]
#[trust_vc::ensures(*a == 7u64)]
fn set7d(a: &mut u64) {
    *a = 7u64;
}

// ensures-only callee (no requires): the pre-snapshot gate must still bind
// old(P) to the PRE-call value
#[trust_vc::ensures(*a == *old(a) + 1u64)]
fn inc_no_req(a: &mut u64) {
    *a = *a + 1u64;
}

// old-only ensures: the POST value is deliberately unconstrained
#[trust_vc::requires(a == 5u64)]
#[trust_vc::ensures(old(a) == 5u64)]
fn keep5_old_only(a: &mut u64) {
    *a = 9u64;
}

// contract-less callee: havoc-only at the call site
fn nocontract(a: &mut u64) {
    *a = 99u64;
}

// non-scalar &mut struct callee
#[trust_vc::ensures(true)]
fn sbump(s: &mut SPair) {
    s.x = s.x + 1u64;
}

struct SPair {
    x: u64,
    y: u64,
}

// &mut &T callee (mutable ref to a shared-ref temporary at the call site)
fn tref(a: &mut &u64) {
    let _ = a;
}

// ---------- (a) canonical caller chain ----------

#[trust_vc::ensures(true)]
fn a1_canonical_add1_verified() {
    let mut v = 5u64;
    add1(&mut v);
    trust_vc::assert!(v == 6u64);
}

#[trust_vc::ensures(true)]
fn a2_canonical_add1_wrong_value_counterexample() {
    let mut v = 5u64;
    add1(&mut v);
    trust_vc::assert!(v == 5u64);
}

// ---------- (b) DIRECTIONALITY, both ways ----------

#[trust_vc::ensures(true)]
fn b1_relation_post_verified() {
    let mut v = 9u64;
    add1(&mut v);
    trust_vc::assert!(v == 10u64);
}

// post must NOT equal pre unless ensures says so
#[trust_vc::ensures(true)]
fn b2_relation_pre_counterexample() {
    let mut v = 9u64;
    add1(&mut v);
    trust_vc::assert!(v == 9u64);
}

// old-only ensures: if old(P) bound to the POST symbol, `ensures(old(a)==5)`
// would pin the fresh symbol to 5 and this stale claim would falsely verify.
#[trust_vc::ensures(true)]
fn b3_old_only_post_unconstrained_counterexample() {
    let mut v = 5u64;
    keep5_old_only(&mut v);
    trust_vc::assert!(v == 5u64);
}

// ensures-only callee (no requires → the snapshot gate is the only source of
// the pre-call map): old(P) must still bind PRE
#[trust_vc::ensures(true)]
fn b4_ensures_only_old_binds_pre_verified() {
    let mut v = 5u64;
    inc_no_req(&mut v);
    trust_vc::assert!(v == 6u64);
}

#[trust_vc::ensures(true)]
fn b5_ensures_only_tripwire_counterexample() {
    let mut v = 5u64;
    inc_no_req(&mut v);
    trust_vc::assert!(v == 5u64);
}

// bare-name forwarding of the caller's own scalar &mut param
#[trust_vc::requires(*old(x) == 5u64)]
#[trust_vc::ensures(true)]
fn b6_forward_old_form_verified(x: &mut u64) {
    add1(x);
    trust_vc::assert!(*x == 6u64);
}

#[trust_vc::requires(*old(x) == 5u64)]
#[trust_vc::ensures(true)]
fn b7_forward_wrong_counterexample(x: &mut u64) {
    add1(x);
    trust_vc::assert!(*x == 5u64);
}

// ---------- (c) requires discharge at the call site ----------

// violated callee requires (*old(a) < 10 with v = 50) must FAIL on the
// __call_requires discharge obligation — never silently proceed
#[trust_vc::ensures(true)]
fn c1_requires_violation_counterexample() {
    let mut v = 50u64;
    add1(&mut v);
}

// a statically-dead guarded call must not spuriously counterexample
#[trust_vc::ensures(true)]
fn c2_dead_guard_no_spurious_counterexample(c: bool) {
    let mut v = 200u64;
    if c && v < 10u64 {
        add1(&mut v);
    }
}

// deref-form contract spelling: *a in requires AND ensures is erased to the
// substituted value (forwarding path)
#[trust_vc::requires(x == 5u64)]
#[trust_vc::ensures(true)]
fn c3_deref_form_contract_verified(x: &mut u64) {
    set7d(x);
    trust_vc::assert!(*x == 7u64);
}

// ---------- (d) sequential calls chain per-call ----------

#[trust_vc::ensures(true)]
fn d1_sequential_chain_verified() {
    let mut v = 5u64;
    add1(&mut v);
    add1(&mut v);
    trust_vc::assert!(v == 7u64);
}

// second call's old = FIRST call's post; claiming the first post after the
// second call must fail
#[trust_vc::ensures(true)]
fn d2_sequential_wrong_counterexample() {
    let mut v = 5u64;
    add1(&mut v);
    add1(&mut v);
    trust_vc::assert!(v == 6u64);
}

// mixed contract forms chain: set7 pins 7, add1 relates 7 -> 8
#[trust_vc::ensures(true)]
fn d3_mixed_chain_verified() {
    let mut v = 5u64;
    set7(&mut v);
    add1(&mut v);
    trust_vc::assert!(v == 8u64);
}

// ---------- (e) calls inside branches ----------

// in-branch knowledge: the guarded ensures discharges the in-branch assert
#[trust_vc::ensures(true)]
fn e1_branch_call_inbranch_verified(c: bool) {
    let mut v = 5u64;
    if c {
        add1(&mut v);
        trust_vc::assert!(v == 6u64);
    }
}

// in-branch wrong claim is a genuine CE (ensures pins 6, not 7)
#[trust_vc::ensures(true)]
fn e2_branch_wrong_claim_counterexample(c: bool) {
    let mut v = 5u64;
    if c {
        add1(&mut v);
        trust_vc::assert!(v == 7u64);
    }
}

// post-branch stale claim (false when c): must NEVER verify. Today the
// branch-join drops the scoped-local binding — fail-closed error.
#[trust_vc::ensures(true)]
fn e3_post_branch_stale_never_verifies(c: bool) {
    let mut v = 5u64;
    if c {
        add1(&mut v);
    }
    trust_vc::assert!(v == 5u64);
}

// both arms call: post-join knowledge is not threaded yet — must never
// FALSELY verify a claim the join model cannot support; fail-closed today.
#[trust_vc::ensures(true)]
fn e4_both_arms_post_join_fail_closed(c: bool) {
    let mut v = 5u64;
    if c {
        add1(&mut v);
    } else {
        add1(&mut v);
    }
    trust_vc::assert!(v == 6u64);
}

// ---------- (f) fail-closed boundaries ----------

// contract-less callee: havoc-only — the stale claim is a genuine CE (the
// post-call state is arbitrary), never Verified, never an unresolved error
#[trust_vc::ensures(true)]
fn f1_nocontract_havoc_only_counterexample() {
    let mut v = 5u64;
    nocontract(&mut v);
    trust_vc::assert!(v == 5u64);
}

// &mut FIELD argument: out of slice-D scope — must stay fail-closed
#[trust_vc::ensures(true)]
fn f2_field_arg_fails_closed() {
    let mut s = SPair { x: 5u64, y: 7u64 };
    set7(&mut s.x);
    trust_vc::assert!(s.x == 7u64);
}

// non-scalar &mut struct arg with contracted callee: stale post-call read
// must never verify (fail-closed)
#[trust_vc::ensures(true)]
fn f3_struct_arg_stale_fails_closed() {
    let mut s = SPair { x: 5u64, y: 7u64 };
    sbump(&mut s);
    trust_vc::assert!(s.x == 5u64);
}

// `&mut &x` temporary must NOT havoc x (slice-B regression pin)
#[trust_vc::ensures(true)]
fn f4_shared_temp_regression_verified() {
    let x = 5u64;
    tref(&mut &x);
    trust_vc::assert!(x == 5u64);
}

// expression-position contracted call: the ensures assumption is DROPPED
// (recording precedes the havoc), so the true post-value claim cannot
// discharge — fail-closed-incomplete CE, never a wrong-state binding
#[trust_vc::ensures(true)]
fn f5_let_position_ensures_dropped(x: u64) {
    let mut v = 5u64;
    let _r = set7(&mut v);
    trust_vc::assert!(v == 7u64);
}

// its tripwire: binding the ensures pre-havoc manufactured a contradiction
// (v == 5 assumed AND v == 7 ensured on the SAME symbol) that vacuously
// verified everything — this must stay a genuine CE
#[trust_vc::ensures(true)]
fn f6_let_position_no_vacuity_counterexample() {
    let mut v = 5u64;
    let _r = set7(&mut v);
    trust_vc::assert!(1u64 == 2u64);
}

// an unrelated local is untouched by the neighbor's havoc
#[trust_vc::ensures(true)]
fn f7_other_local_untouched_verified() {
    let mut v = 5u64;
    let w = 3u64;
    add1(&mut v);
    trust_vc::assert!(w == 3u64);
    trust_vc::assert!(v == 6u64);
}

// alias-local forwarding (`let r: &mut u64 = &mut a; f(r)` — the current
// refs.rs port caller shape): out of slice-D scope, must stay fail-closed
// (the direct `f(&mut a)` shape is the a1 chain and verifies)
#[trust_vc::ensures(true)]
fn f8_alias_forward_fails_closed() {
    let mut a = 2u64;
    let a_ref: &mut u64 = &mut a;
    add1(a_ref);
    trust_vc::assert!(a == 3u64);
}

// A FIXED BASE-ERA HOLE (pre-slice-D false `Verified`): a by-value `mut`
// PARAM passed `&mut p` to a CONTRACT-LESS callee that writes through it.
// The call-arg havoc minted a fresh symbol, but the general borrow-escape
// invalidation then DROPPED that binding, so the post-call read fell back to
// the `requires`-pinned ENTRY symbol — `assert!(p == 5)` after `*p = 99`
// VERIFIED on the pre-slice-D base. The suppression of the double
// invalidation keeps the fresh unconstrained symbol: a genuine CE.
//
// CORRECTION: slice D fixed ONLY this literal `&mut ident` single-segment
// free-fn shape — the same hole through a reborrow, `&mut &mut p`, a
// method/UFCS/fn-pointer call arg, or an alias local stayed open until the
// slice-D remediation's general borrow-escape havoc; those shapes are pinned
// in `mut_ref_call_escape_probes.rs`.
#[trust_vc::requires(p == 5u64)]
#[trust_vc::ensures(true)]
fn f9_byvalue_param_nocontract_stale_counterexample(mut p: u64) {
    nocontract(&mut p);
    trust_vc::assert!(p == 5u64);
}

// contracted sibling of f9: ensures re-threads over the fresh symbol
#[trust_vc::requires(p == 5u64)]
#[trust_vc::ensures(true)]
fn f10_byvalue_param_contracted_verified(mut p: u64) {
    set7(&mut p);
    trust_vc::assert!(p == 7u64);
}
"####;

fn run(func: &str) -> VerifyResult {
    // The on-disk VC-result cache stores only `verified` verdicts and replays
    // them without re-encoding — it MUST be disabled for true verdicts.
    // Serialized behind the process-wide env lock and restored on scope exit
    // (guards drop before the lock releases) via the workspace env choke point.
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let dir = std::env::temp_dir().join("trust_vc_mut_ref_caller_two_state");
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
        "{func} must be a Counterexample (never Verified), got: {r:?}"
    );
}

/// Fail-closed pin: Error / Counterexample / Unknown are all acceptable — the
/// one catastrophic outcome is `Verified`.
fn assert_never_verifies(func: &str) {
    let r = run(func);
    assert!(
        !r.is_verified(),
        "{func} must NEVER verify (fail-closed boundary), got: {r:?}"
    );
}

/// Unknown-as-failure relaxation (docs/design-unknown-as-failure.md): a genuine
/// verification FAILURE — a model-bearing `Counterexample` OR a model-less
/// `NotProved` (an incompleteness fail-close under the ay bump's wrong-SAT
/// closures). Stricter than `assert_never_verifies` (rejects a soft `Unknown`/
/// `Error`), looser than `assert_counterexample` (does not demand a fabricated
/// model). For must-fail tripwires whose refutation now fail-closes to NotProved.
fn assert_fails(func: &str) {
    let r = run(func);
    assert!(
        r.is_failure(),
        "{func} must be a verification FAILURE — Counterexample or NotProved (never Verified), got: {r:?}"
    );
}

// ---- (a) canonical chain ----

#[test]
fn battery_a1_canonical_add1_verified() {
    assert_verified("a1_canonical_add1_verified");
}

#[test]
fn battery_a2_canonical_add1_wrong_value_counterexample() {
    assert_counterexample("a2_canonical_add1_wrong_value_counterexample");
}

// ---- (b) directionality ----

#[test]
fn battery_b1_relation_post_verified() {
    assert_verified("b1_relation_post_verified");
}

#[test]
fn battery_b2_relation_pre_counterexample() {
    assert_counterexample("b2_relation_pre_counterexample");
}

#[test]
fn battery_b3_old_only_post_unconstrained_counterexample() {
    assert_counterexample("b3_old_only_post_unconstrained_counterexample");
}

#[test]
fn battery_b4_ensures_only_old_binds_pre_verified() {
    assert_verified("b4_ensures_only_old_binds_pre_verified");
}

#[test]
fn battery_b5_ensures_only_tripwire_counterexample() {
    // Unknown-as-failure (docs/design-unknown-as-failure.md): the stale claim's
    // refutation now fail-closes to a model-less NotProved — still a failure.
    assert_fails("b5_ensures_only_tripwire_counterexample");
}

#[test]
fn battery_b6_forward_old_form_verified() {
    assert_verified("b6_forward_old_form_verified");
}

#[test]
fn battery_b7_forward_wrong_counterexample() {
    assert_counterexample("b7_forward_wrong_counterexample");
}

// ---- (c) requires discharge ----

#[test]
fn battery_c1_requires_violation_fails_on_discharge_obligation() {
    let r = run("c1_requires_violation_counterexample");
    let VerifyResult::Counterexample {
        obligation_name, ..
    } = &r
    else {
        panic!(
            "c1: a violated callee requires must be a Counterexample on the \
             __call_requires discharge obligation, got: {r:?}"
        );
    };
    assert!(
        obligation_name.starts_with("__call_requires"),
        "c1: the failing obligation must be the caller-side requires \
         discharge, got: {obligation_name}"
    );
}

#[test]
fn battery_c2_dead_guard_no_spurious_counterexample() {
    assert_verified("c2_dead_guard_no_spurious_counterexample");
}

#[test]
fn battery_c3_deref_form_contract_verified() {
    assert_verified("c3_deref_form_contract_verified");
}

// ---- (d) sequential chaining ----

#[test]
fn battery_d1_sequential_chain_verified() {
    assert_verified("d1_sequential_chain_verified");
}

#[test]
fn battery_d2_sequential_wrong_counterexample() {
    assert_counterexample("d2_sequential_wrong_counterexample");
}

#[test]
fn battery_d3_mixed_chain_verified() {
    assert_verified("d3_mixed_chain_verified");
}

// ---- (e) branches ----

#[test]
fn battery_e1_branch_call_inbranch_verified() {
    assert_verified("e1_branch_call_inbranch_verified");
}

#[test]
fn battery_e2_branch_wrong_claim_counterexample() {
    assert_counterexample("e2_branch_wrong_claim_counterexample");
}

#[test]
fn battery_e3_post_branch_stale_never_verifies() {
    assert_never_verifies("e3_post_branch_stale_never_verifies");
}

#[test]
fn battery_e4_both_arms_post_join_fail_closed() {
    assert_never_verifies("e4_both_arms_post_join_fail_closed");
}

// ---- (f) fail-closed boundaries ----

#[test]
fn battery_f1_nocontract_havoc_only_counterexample() {
    // Unknown-as-failure (docs/design-unknown-as-failure.md): the havoc-only
    // stale claim's refutation now fail-closes to a model-less NotProved.
    assert_fails("f1_nocontract_havoc_only_counterexample");
}

#[test]
fn battery_f2_field_arg_fails_closed() {
    assert_never_verifies("f2_field_arg_fails_closed");
}

#[test]
fn battery_f3_struct_arg_stale_fails_closed() {
    assert_never_verifies("f3_struct_arg_stale_fails_closed");
}

#[test]
fn battery_f4_shared_temp_regression_verified() {
    assert_verified("f4_shared_temp_regression_verified");
}

#[test]
fn battery_f5_let_position_ensures_dropped() {
    assert_never_verifies("f5_let_position_ensures_dropped");
}

#[test]
fn battery_f6_let_position_no_vacuity_counterexample() {
    assert_counterexample("f6_let_position_no_vacuity_counterexample");
}

#[test]
fn battery_f7_other_local_untouched_verified() {
    assert_verified("f7_other_local_untouched_verified");
}

#[test]
fn battery_f8_alias_forward_fails_closed() {
    assert_never_verifies("f8_alias_forward_fails_closed");
}

#[test]
fn battery_f9_byvalue_param_nocontract_stale_counterexample() {
    // Unknown-as-failure (docs/design-unknown-as-failure.md): the stale
    // by-value-param claim's refutation now fail-closes to a model-less NotProved.
    assert_fails("f9_byvalue_param_nocontract_stale_counterexample");
}

#[test]
fn battery_f10_byvalue_param_contracted_verified() {
    assert_verified("f10_byvalue_param_contracted_verified");
}
