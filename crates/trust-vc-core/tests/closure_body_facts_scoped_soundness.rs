// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS PIN (hole H7, measured 2026-09-14 at main `ee37bb64`): a fact
//! emitted while visiting a closure LITERAL's body leaked into the enclosing
//! function as an unconditional hypothesis, even when the closure is never
//! called.
//!
//! `visit_expr_closure` (`vc_extraction/body_extract.rs`) visits the body inside
//! `with_isolated_scopes`, which snapshots and restores SCOPES only — every
//! obligation pushed during the visit stayed in the function's obligation list,
//! and every fact emitter guards only with `path_conditions`, which the closure
//! visit never extended. The #74 capture freshening renames captured VARIABLES,
//! so a hypothesis over a 0-ary spec fn (`goo()`), a literal-argument spec call
//! (`gv(3u64)`), a contracted helper whose `ensures` names no capture, a
//! post-loop exit fact, or the `loop {}` unreachability marker `false` all
//! survived it. `trust_vc::assume!` expands to a closure that never runs and
//! Verus lowers a closure body in a `DeadEnd`, so none of these facts holds at
//! the definition point: the judges built compiled witnesses whose verified
//! assert / postcondition panics at runtime (the `runtime_*` pins below).
//!
//! THE RULE (fix): the body is visited under a fresh, declared, otherwise
//! unconstrained `Bool` path condition `g` (one per closure visit; nested
//! closures stack). Every body fact `F` becomes `!(g) || F` and every body
//! obligation `P` becomes `!(g) || P` — the existing `if g { body }` encoding.
//! `g` occurs nowhere else, so a goal outside the body sees nothing new
//! (`g := false`), while an in-body obligation keeps the closure's own
//! `assume ⟹ assert` reasoning (`g := true`). Fail-closed consequences, pinned:
//! a CALLED bare closure contributes no body fact at the call (it has no
//! `ensures`; Verus gives none either), and an in-closure `assert_by!` /
//! `assert_by_contradiction!` conclusion no longer escapes as an outer fact.
//!
//! RESIDUAL (completeness, pinned): loop-lane obligations are not guarded by
//! `path_conditions`, so an `invariant!` whose base case needs a fact under a
//! path condition is refuted — pre-existing under `if c`, and now shared by a
//! closure body whose own `assume!` establishes the invariant.
//!
//! REVIEW ROUND (`SRC_LOOP_POST_FACTS_AND_CAPTURES`): a verified loop
//! conclusion is published function-wide. `loop_ensures!` (no base case) inside
//! a closure body therefore fails closed, and a mutated capture is a fresh
//! symbol after the closure, so neither a loop post-fact nor a `requires` on the
//! capture's bare symbol reaches an outer goal.
//!
//! REVIEW ROUND 2 (`SRC_ROUND2_LOOP_FACTS_AND_NESTED_CAPTURES`), three leak
//! channels the round-1 fix left open, each measured `Verified` on `3fab140f`:
//!   1. the POSTCONDITION lane. A verified `invariant!` (and every exit-site
//!      copy of it) is republished as a function-wide post-loop fact over the
//!      BARE symbol of each modified variable. Inside a closure body that fact
//!      was established over CLOSURE-LOCAL state, and the postcondition reads a
//!      by-value `mut` parameter's bare symbol — so the after-the-closure
//!      capture havoc, which fixed the `assert!` twin, cannot reach it. A loop
//!      inside a closure body that modifies a variable declared BEFORE the body
//!      visit began now stamps its obligations `closure_scoped__`, and the typed
//!      lane checks them in full but never republishes them. A loop whose
//!      modified set is entirely closure-local is untouched
//!      (`ctrl_closure_invariant_used_inside`).
//!   2. NESTED closures. `ExternalAssignmentCollector` skipped a nested closure
//!      literal outright, so a capture assigned one level down never entered the
//!      mutated set and was never havocked — wrapping the exact liar round 1
//!      fixed in one more closure made it verify again. The closure-body
//!      consumer now descends (`externally_assigned_in_closure_body`).
//!   3. the REACHED GUARD's identifier namespace. The guard is minted into the
//!      same namespace source identifiers resolve in, so
//!      `assume!(__trust_vc_closure_body_reached_0)` bound the engine's own free
//!      `Bool`, forced `g := true` and re-admitted every guarded body fact. The
//!      prefix is now reserved and refused from source.
//!
//! Every LIAR is a claim that is false in Rust (the spec fns are uninterpreted
//! or `false` by definition) and must be refuted with a `Counterexample` at the
//! named obligation; every CONTROL is a true shape that must keep its verdict.
//! Cache off: the on-disk VC cache stores `Verified` only, and a stale entry
//! written by a pre-fix binary would mask the regression.

use std::sync::atomic::{AtomicUsize, Ordering};
use trust_vc_core::{verify_function_from_file, VerifyResult};

/// Uninterpreted spec fns and contracted helpers whose `ensures` name no capture.
const SRC_UNINTERPRETED: &str = r#"
#![allow(dead_code, unused_variables, unreachable_code, while_true)]

#[trust_vc::spec]
fn goo() -> bool;

#[trust_vc::spec]
fn flag() -> bool;

#[trust_vc::spec]
fn gv(x: u64) -> bool;

#[trust_vc::external_body]
#[trust_vc::ensures(goo())]
fn establish_goo() {}

#[trust_vc::external_body]
#[trust_vc::ensures(flag())]
fn establish_flag() {}

// ---------------------------------------------------------------- LIARS

#[trust_vc::ensures(true)]
fn liar_bare_assume_uncalled() {
    let _f = || {
        trust_vc::assume!(goo());
    };
    trust_vc::assert!(goo());
}

fn liar_expr_body_no_attrs() {
    let _f = || trust_vc::assume!(goo());
    trust_vc::assert!(goo());
}

#[trust_vc::ensures(true)]
fn liar_move_closure_assume() {
    let _f = move || {
        trust_vc::assume!(goo());
    };
    trust_vc::assert!(goo());
}

#[trust_vc::ensures(true)]
fn liar_helper_uncalled() {
    let _f = || {
        establish_goo();
    };
    trust_vc::assert!(goo());
}

#[trust_vc::ensures(true)]
fn liar_literal_arg_spec() {
    let _f = || {
        trust_vc::assume!(gv(3u64));
    };
    trust_vc::assert!(gv(3u64));
}

#[trust_vc::ensures(true)]
fn liar_option_map_uncalled() {
    let o: Option<u64> = None;
    let _v = o.map(|x: u64| {
        trust_vc::assume!(goo());
        x
    });
    trust_vc::assert!(goo());
}

#[trust_vc::ensures(true)]
fn liar_iter_map_uncalled(v: Vec<u64>) {
    let _w: Vec<u64> = v.iter().map(|x| { trust_vc::assume!(goo()); *x }).collect();
    trust_vc::assert!(goo());
}

#[trust_vc::requires(flag() == (r == 0u64))]
#[trust_vc::ensures(true)]
fn liar_requires_linked_assert(r: u64) {
    let _f = || {
        trust_vc::assume!(flag());
    };
    trust_vc::assert!(r == 0u64);
}

#[trust_vc::requires(flag() == (r == 0u64))]
#[trust_vc::ensures(true)]
fn liar_requires_linked_helper(r: u64) {
    let _f = || {
        establish_flag();
    };
    trust_vc::assert!(r == 0u64);
}

#[trust_vc::requires(flag() == (r == 0u64))]
#[trust_vc::ensures(result == 0u64)]
fn liar_requires_linked_into_ensures(r: u64) -> u64 {
    let _f = || {
        trust_vc::assume!(flag());
    };
    r
}

#[trust_vc::ensures(true)]
fn liar_loop_marker_assert_false() {
    let _f = || loop {};
    trust_vc::assert!(false);
}

#[trust_vc::ensures(result == 0u64)]
fn liar_loop_marker_into_ensures(r: u64) -> u64 {
    let _f = || loop {};
    r
}

#[trust_vc::ensures(true)]
fn liar_while_exit_over_capture(n: u64) {
    let _f = || {
        while n < 10u64 {
            trust_vc::invariant!(true);
        }
    };
    trust_vc::assert!(n >= 10u64);
}

#[trust_vc::ensures(true)]
fn liar_while_true_in_closure() {
    let _f = || {
        while true {
            trust_vc::invariant!(true);
        }
    };
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn liar_let_else_in_closure(o: Option<u64>) {
    let _f = || {
        let Some(_v) = o else { loop {} };
    };
    trust_vc::assert!(o.is_some());
}

#[trust_vc::ensures(true)]
fn liar_nested_closure() {
    let _f = || {
        let _g = || {
            trust_vc::assume!(goo());
        };
    };
    trust_vc::assert!(goo());
}

#[trust_vc::ensures(true)]
fn liar_proof_block_in_closure() {
    let _f = || {
        trust_vc::proof_block!({ trust_vc::assume!(goo()); });
    };
    trust_vc::assert!(goo());
}

#[trust_vc::ensures(true)]
fn liar_match_arms_in_closure(o: Option<u64>) {
    let _f = || {
        match o {
            Some(_) => { trust_vc::assume!(goo()); }
            None => { trust_vc::assume!(goo()); }
        }
    };
    trust_vc::assert!(goo());
}

#[trust_vc::ensures(true)]
fn liar_sibling_helper() {
    let _a = || { establish_goo(); };
    let _b = || { trust_vc::assert!(goo()); };
}

#[trust_vc::ensures(true)]
fn liar_carry_forward() {
    let _f = || {
        trust_vc::assume!(goo());
        trust_vc::assert!(goo());
    };
    trust_vc::assert!(goo());
}

#[trust_vc::ensures(true)]
fn liar_called_closure_no_callsite_fact() {
    let f = || {
        trust_vc::assume!(goo());
    };
    f();
    trust_vc::assert!(goo());
}

#[trust_vc::ensures(true)]
fn liar_assert_by_in_closure() {
    let _f = || {
        trust_vc::assert_by!(goo(), { trust_vc::assume!(goo()); });
    };
    trust_vc::assert!(goo());
}

#[trust_vc::ensures(true)]
fn liar_assert_by_contradiction_in_closure() {
    let _f = || {
        trust_vc::assert_by_contradiction!(goo(), { trust_vc::assume!(false); });
    };
    trust_vc::assert!(goo());
}

#[trust_vc::ensures(true)]
fn liar_assume_false_uncalled() {
    let _f = || {
        trust_vc::assume!(false);
    };
    trust_vc::assert!(false);
}

// The next four were found while validating the fix (all `Verified` at main
// `4cd7972e`): the same leak through an `assert_forall_by!` by-block, a closure
// in a nested block, a closure passed to `filter`, and a loop invariant the
// body's own `assume!` established.
#[trust_vc::ensures(true)]
fn liar_assert_forall_by_in_closure() {
    let _f = || {
        trust_vc::assert_forall_by!(|x: u64| gv(x), { trust_vc::assume!(gv(x)); });
    };
    trust_vc::assert!(gv(3u64));
}

#[trust_vc::ensures(true)]
fn liar_closure_in_nested_block() {
    {
        let _f = || {
            establish_goo();
        };
    }
    trust_vc::assert!(goo());
}

#[trust_vc::ensures(true)]
fn liar_filter_closure_uncalled() {
    let v: Vec<u64> = Vec::new();
    let _n = v.iter().filter(|x| { trust_vc::assume!(goo()); true }).count();
    trust_vc::assert!(goo());
}

#[trust_vc::ensures(true)]
fn liar_loop_invariant_from_body_assume() {
    let _f = || {
        trust_vc::assume!(goo());
        let mut k = 0u64;
        while k < 3u64 {
            trust_vc::invariant!(goo() && k <= 3u64);
            k = k + 1u64;
        }
    };
    trust_vc::assert!(goo());
}

// ------------------------------------------------------------- CONTROLS

#[trust_vc::ensures(true)]
fn ctrl_top_level_assume_then_assert() {
    trust_vc::assume!(goo());
    trust_vc::assert!(goo());
}

#[trust_vc::ensures(true)]
fn ctrl_top_level_helper_then_assert() {
    establish_goo();
    trust_vc::assert!(goo());
}

#[trust_vc::ensures(true)]
fn ctrl_if_false_assume() {
    if false {
        trust_vc::assume!(goo());
    }
    trust_vc::assert!(goo());
}

#[trust_vc::ensures(true)]
fn ctrl_if_false_infinite_loop() {
    if false {
        loop {}
    }
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn ctrl_closure_after_assert_order() {
    trust_vc::assert!(goo());
    let _f = || trust_vc::assume!(goo());
}

#[trust_vc::ensures(true)]
fn ctrl_own_capture_reasoning(n: u64) {
    let _a = |x: u64| { trust_vc::assume!(n > 100u64); trust_vc::assert!(n > 50u64); x };
}

#[trust_vc::ensures(true)]
fn ctrl_own_zero_ary_reasoning() {
    let _a = || { trust_vc::assume!(goo()); trust_vc::assert!(goo()); };
}

#[trust_vc::ensures(true)]
fn ctrl_own_helper_reasoning() {
    let _a = || { establish_goo(); trust_vc::assert!(goo()); };
}

#[trust_vc::ensures(true)]
fn ctrl_own_assume_guards_div(a: u64, b: u64) {
    let _a = || { trust_vc::assume!(b != 0u64); let _q = a / b; };
}

#[trust_vc::ensures(true)]
fn ctrl_two_self_contained_siblings(n: u64) {
    let _a = |x: u64| { trust_vc::assume!(n > 100u64); trust_vc::assert!(n > 50u64); x };
    let _b = |y: u64| { trust_vc::assume!(n < 10u64); trust_vc::assert!(n < 20u64); y };
}

#[trust_vc::requires(n > 0u64)]
#[trust_vc::ensures(true)]
fn ctrl_outer_requires_visible_in_closure(n: u64) {
    let _a = |x: u64| { trust_vc::assert!(n > 0u64); x };
}

#[trust_vc::ensures(true)]
fn ctrl_closure_local_loop(n: u64) {
    let _f = move || {
        let mut k = 0u64;
        while k < n {
            trust_vc::invariant!(k <= n);
            k = k + 1u64;
        }
        trust_vc::assert!(k == n);
    };
}

#[trust_vc::ensures(true)]
fn ctrl_own_unreachable_after_loop() {
    let _f = || {
        loop {}
        trust_vc::assert!(false);
    };
}

#[trust_vc::ensures(result == x + 1u64)]
fn ctrl_capture_free_inline_call(x: u64) -> u64 {
    trust_vc::assume!(x < 100u64);
    let f = |y: u64| y + 1u64;
    f(x)
}

#[trust_vc::ensures(true)]
fn ctrl_sibling_assume_does_not_discharge(n: u64) {
    let _a = |x: u64| { trust_vc::assume!(n > 100u64); x };
    let _b = |y: u64| { trust_vc::assert!(n > 50u64); y };
}

#[trust_vc::ensures(true)]
fn ctrl_lone_closure_assert_is_real(n: u64) {
    let _b = |y: u64| { trust_vc::assert!(n == 7u64); y };
}

#[trust_vc::ensures(true)]
fn ctrl_in_closure_overflow_before_assume_false(a: u64) {
    let _f = || { let _q = a + 1u64; trust_vc::assume!(false); };
}

#[trust_vc::ensures(true)]
fn ctrl_in_closure_overflow_alone(a: u64) {
    let _f = || { let _q = a + 1u64; };
}

#[trust_vc::ensures(true)]
fn ctrl_closure_defined_under_if(c: bool) {
    if c {
        let _f = || trust_vc::assume!(goo());
    }
    trust_vc::assert!(goo());
}

// RESIDUAL (completeness, not soundness): loop-lane obligations (`invariant!`
// base case and step) are not guarded by `path_conditions`, so a loop invariant
// established only by a fact under a path condition is refuted at its base
// case. Pre-existing for `if c { assume!(P); while .. { invariant!(P) } }` (the
// `_if_` twin, `Counterexample` at main `4cd7972e` too); a closure body now
// shares it, because its facts carry the reached-guard. Pinned so a fix to the
// loop lane flips these deliberately.
#[trust_vc::ensures(true)]
fn residual_if_loop_invariant_from_branch_assume(c: bool) {
    if c {
        trust_vc::assume!(goo());
        let mut k = 0u64;
        while k < 3u64 {
            trust_vc::invariant!(goo() && k <= 3u64);
            k = k + 1u64;
        }
        trust_vc::assert!(goo());
    }
}

#[trust_vc::ensures(true)]
fn residual_closure_loop_invariant_from_body_assume() {
    let _f = || {
        trust_vc::assume!(goo());
        let mut k = 0u64;
        while k < 3u64 {
            trust_vc::invariant!(goo() && k <= 3u64);
            k = k + 1u64;
        }
        trust_vc::assert!(goo());
    };
}

// CONTROL — an OUTER fact still reaches an in-closure loop invariant.
#[trust_vc::requires(n > 5u64)]
#[trust_vc::ensures(true)]
fn ctrl_closure_loop_invariant_from_outer_requires(n: u64) {
    let _f = move || {
        let mut k = 0u64;
        while k < 3u64 {
            trust_vc::invariant!(n > 5u64 && k <= 3u64);
            k = k + 1u64;
        }
        trust_vc::assert!(n > 5u64);
    };
}

#[trust_vc::ensures(true)]
fn failclosed_closure_macro_block_body() {
    let _f = trust_vc::closure!(
        |x: u64| -> u64
        requires(true)
        ensures(|z: u64| z == x)
        { trust_vc::assume!(goo()); x }
    );
    trust_vc::assert!(goo());
}
"#;

/// Runtime-grade witnesses: the spec fns are `false` BY DEFINITION, so each
/// verified claim was not merely unprovable but wrong, and the ghost-erased
/// program panics on the claimed assert / postcondition.
const SRC_RUNTIME: &str = r#"
#![allow(dead_code, unused_variables)]

#[trust_vc::spec]
#[trust_vc::opaque]
fn opq() -> bool {
    false
}

#[trust_vc::spec]
fn tf() -> bool {
    false
}

#[trust_vc::spec]
#[trust_vc::opaque]
fn flag_o() -> bool {
    false
}

// LIAR — `opq()` is false by definition.
#[trust_vc::ensures(true)]
fn runtime_opaque() {
    let _f = || trust_vc::assume!(opq());
    trust_vc::assert!(opq());
}

// LIAR — `callee(1u64)` meets the precondition (`false == (1 == 0)`), and the
// erased program panics on the assert.
#[trust_vc::requires(tf() == (r == 0u64))]
#[trust_vc::ensures(true)]
fn runtime_hide_callee(r: u64) {
    trust_vc::hide!(tf);
    let _f = || trust_vc::assume!(tf());
    trust_vc::assert!(r == 0u64);
}

// CONTROL — the precondition of the liar above is satisfiable by a real call.
#[trust_vc::ensures(true)]
fn runtime_hide_caller_one() {
    runtime_hide_callee(1u64);
}

// CONTROL — and it is really checked: `r == 0` needs `tf()`, which is false.
#[trust_vc::ensures(true)]
fn runtime_hide_caller_zero() {
    runtime_hide_callee(0u64);
}

// LIAR — `leak_assume(1)` returns 1 and the runtime postcondition panics.
#[trust_vc::contract(ensures(result == 0u64), returns(result))]
fn runtime_contract_leak_assume(r: u64) -> u64 {
    trust_vc::assume!(flag_o() == (r == 0u64));
    let _f = || {
        trust_vc::assume!(flag_o());
    };
    r
}

// CONTROL — the same function without the closure is refuted the same way.
#[trust_vc::contract(ensures(result == 0u64), returns(result))]
fn runtime_contract_no_closure(r: u64) -> u64 {
    trust_vc::assume!(flag_o() == (r == 0u64));
    r
}
"#;

/// Review round (2026-09-14, on `ad196375`): two channels the reached-guard did
/// not close. (1) The typed lane publishes every VERIFIED `loop_ensures`-kind
/// obligation (a normal-exit `loop_ensures!`, an exit-site copy) as a post-loop
/// fact for every later goal and never consults `path_conditions`; a
/// `loop_ensures` has no base case, so nothing outside the body implies it.
/// (2) A mutated capture was "havocked" by invalidating its scoped value, so a
/// later read hit the BARE declared symbol, which still carried a `mut` param's
/// `requires` and the post-loop invariant of a loop inside the body. Every
/// `liar_` below was `Verified` on `ad196375`. Fix: `loop_ensures!` inside a
/// closure body FAILS CLOSED, and each mutated capture is rebound to a FRESH
/// symbol after the closure. Guarding the loop-ensures check with the
/// reached-guard was measured and rejected: the loop lanes see every in-body
/// assumption regardless of program point, so a later `assume!(false)` or
/// `loop {}` in the same body (the fact `!(g)`) discharged `!(g) || P`
/// vacuously (`failclosed_loop_ensures_then_assume_false` below verified).
const SRC_LOOP_POST_FACTS_AND_CAPTURES: &str = r#"
#![allow(dead_code, unused_variables, unreachable_code, while_true, unused_assignments, unused_mut)]

// ---------------------------------------------------------------- LIARS

#[trust_vc::ensures(true)]
fn liar_loop_ensures_break_site_uncalled(n: u64) {
    let _f = || {
        loop {
            trust_vc::invariant!(true);
            trust_vc::loop_ensures!(n == 7u64);
            if n == 7u64 {
                break;
            }
        }
    };
    trust_vc::assert!(n == 7u64);
}

#[trust_vc::ensures(true)]
fn liar_loop_ensures_normal_exit_uncalled(n: u64) {
    let _f = || {
        while n != 7u64 {
            trust_vc::invariant!(true);
            trust_vc::loop_ensures!(n == 7u64);
        }
    };
    trust_vc::assert!(n == 7u64);
}

#[trust_vc::ensures(n == 7u64)]
fn liar_loop_ensures_into_postcondition(n: u64) {
    let _f = || {
        loop {
            trust_vc::invariant!(true);
            trust_vc::loop_ensures!(n == 7u64);
            if n == 7u64 {
                break;
            }
        }
    };
}

// `Unknown(VacuousTruth)` before `ad196375` (the unguarded exit fact `false`),
// `Verified` at it (the exit fact guarded, the `loop_ensures` still global).
#[trust_vc::ensures(true)]
fn liar_loop_ensures_false_while_true_uncalled() {
    let _f = || {
        while true {
            trust_vc::invariant!(true);
            trust_vc::loop_ensures!(false);
        }
    };
    trust_vc::assert!(false);
}

// A called closure that overwrites a `mut` param: the `requires` described the
// entry value only.
#[trust_vc::requires(x <= 5u64)]
#[trust_vc::ensures(true)]
fn liar_called_closure_mutation_keeps_requires(mut x: u64) {
    let mut set = || {
        x = 100u64;
    };
    set();
    trust_vc::assert!(x <= 5u64);
}

// Never called: `x` stays 50, but the in-body loop's invariant spoke of `x`.
#[trust_vc::ensures(true)]
fn liar_uncalled_invariant_over_mutated_capture_let() {
    let mut x = 50u64;
    let mut f = || {
        x = 0u64;
        while x < 10u64 {
            trust_vc::invariant!(x <= 10u64);
            x = x + 1u64;
        }
    };
    trust_vc::assert!(x <= 10u64);
}

#[trust_vc::ensures(true)]
fn liar_uncalled_invariant_over_mutated_capture_param(mut x: u64) {
    let mut f = || {
        x = 0u64;
        while x < 10u64 {
            trust_vc::invariant!(x <= 10u64);
            x = x + 1u64;
        }
    };
    trust_vc::assert!(x <= 10u64);
}

// Called: the body ends with `x == 100`.
#[trust_vc::ensures(true)]
fn liar_called_invariant_then_overwrite() {
    let mut x = 0u64;
    let mut f = || {
        while x < 10u64 {
            trust_vc::invariant!(x <= 10u64);
            x = x + 1u64;
        }
        x = 100u64;
    };
    f();
    trust_vc::assert!(x <= 10u64);
}

// ------------------------------------------------------------- CONTROLS

// FAIL-CLOSED (completeness cost of the refusal): a true in-closure use.
#[trust_vc::ensures(true)]
fn failclosed_loop_ensures_used_inside_closure(n: u64) {
    let _f = || {
        loop {
            trust_vc::invariant!(true);
            trust_vc::loop_ensures!(n == 7u64);
            if n == 7u64 {
                break;
            }
        }
        trust_vc::assert!(n == 7u64);
    };
}

// FAIL-CLOSED: the ensures is FALSE at the exit (`n == 7` there). With the
// check guarded by the reached-guard, the later `assume!(false)` (the fact
// `!(g)`) discharged it — measured `Verified` on the rejected variant.
#[trust_vc::ensures(true)]
fn failclosed_loop_ensures_then_assume_false(n: u64) {
    let _f = || {
        while n != 7u64 {
            trust_vc::invariant!(true);
            trust_vc::loop_ensures!(n == 8u64);
        }
        trust_vc::assume!(false);
    };
}

#[trust_vc::ensures(true)]
fn ctrl_top_level_loop_ensures_break_site(n: u64) {
    loop {
        trust_vc::invariant!(true);
        trust_vc::loop_ensures!(n == 7u64);
        if n == 7u64 {
            break;
        }
    }
    trust_vc::assert!(n == 7u64);
}

#[trust_vc::ensures(true)]
fn ctrl_top_level_loop_ensures_normal_exit(n: u64) {
    while n != 7u64 {
        trust_vc::invariant!(true);
        trust_vc::loop_ensures!(n == 7u64);
    }
    trust_vc::assert!(n == 7u64);
}

#[trust_vc::ensures(true)]
fn ctrl_closure_invariant_used_inside(n: u64) {
    let _f = || {
        let mut k = 0u64;
        while k < 10u64 {
            trust_vc::invariant!(k <= 10u64);
            k = k + 1u64;
        }
        trust_vc::assert!(k == 10u64);
    };
}

#[trust_vc::requires(x <= 5u64)]
#[trust_vc::ensures(true)]
fn ctrl_unmutated_capture_keeps_requires(x: u64) {
    let f = || {
        let _y = x;
    };
    f();
    trust_vc::assert!(x <= 5u64);
}

#[trust_vc::ensures(true)]
fn ctrl_mutated_capture_reassigned_after_call() {
    let mut x = 0u64;
    let mut set = || {
        x = 100u64;
    };
    set();
    x = 3u64;
    trust_vc::assert!(x == 3u64);
}
"#;

/// REVIEW ROUND 2. The three channels above, with the lane discriminators that
/// make each liar's verdict readable: `ctrl_ensures_entry_*` pin that this
/// `ensures` lane reads a by-value `mut` parameter's ENTRY value (so the
/// in-closure loop's post-fact is the only thing that could have discharged
/// `liar_uncalled_invariant_into_postcondition`), and the `ctrl_top_level_*`
/// pair pin that the ordinary post-loop publication is untouched.
const SRC_ROUND2_LOOP_FACTS_AND_NESTED_CAPTURES: &str = r#"
#![allow(dead_code, unused_variables, unreachable_code, while_true, unused_assignments, unused_mut)]

#[trust_vc::spec]
fn goo() -> bool;

// ---------------------------------------------------------------- LIARS
// (1) the postcondition lane.

// `f` is never called, so `x` is an arbitrary `u64` at entry AND at exit; the
// only thing that proved `x <= 10` was the in-closure loop's invariant,
// published over the bare symbol.
#[trust_vc::ensures(x <= 10u64)]
fn liar_uncalled_invariant_into_postcondition(mut x: u64) {
    let mut f = || {
        x = 0u64;
        while x < 10u64 {
            trust_vc::invariant!(x <= 10u64);
            x = x + 1u64;
        }
    };
}

// The same with a `requires` that makes the entry value CONCRETE and false.
#[trust_vc::requires(x == 50u64)]
#[trust_vc::ensures(x <= 10u64)]
fn liar_requires_linked_uncalled_invariant_into_postcondition(mut x: u64) {
    let mut f = || {
        x = 0u64;
        while x < 10u64 {
            trust_vc::invariant!(x <= 10u64);
            x = x + 1u64;
        }
    };
}

// A closure-local `let` that SHADOWS an outer parameter: the invariant is
// rendered over the shared bare symbol `i`, so it landed on the parameter.
#[trust_vc::ensures(true)]
fn liar_shadowing_loop_local_invariant_hits_outer_param(i: u64) {
    let _f = || {
        let mut i = 0u64;
        while i < 5u64 {
            trust_vc::invariant!(i <= 5u64);
            i = i + 1u64;
        }
    };
    trust_vc::assert!(i <= 5u64);
}

// A break-site exit copy of a regular `invariant!` is a `loop_ensures`-kind
// obligation and travels the same publication channel — into the postcondition
// lane, which the capture havoc cannot reach. This is the liar that makes the
// exit-site half of the stamp load-bearing: with only the `LoopInvariant`
// suppression in place it is `Verified`, measured by disabling the exit-site
// stamp alone.
#[trust_vc::ensures(x <= 10u64)]
fn liar_break_site_invariant_copy_into_postcondition(mut x: u64) {
    let mut f = || {
        x = 0u64;
        loop {
            trust_vc::invariant!(x <= 10u64);
            if x == 10u64 {
                break;
            }
            x = x + 1u64;
        }
    };
}

#[trust_vc::ensures(true)]
fn liar_break_site_invariant_copy_into_outer_assert(mut x: u64) {
    let mut f = || {
        x = 0u64;
        loop {
            trust_vc::invariant!(x <= 10u64);
            if x == 10u64 {
                break;
            }
            x = x + 1u64;
        }
    };
    trust_vc::assert!(x <= 10u64);
}

// (2) nested closures.

#[trust_vc::ensures(true)]
fn liar_nested_closure_capture_mutation(mut x: u64) {
    trust_vc::assume!(x == 0u64);
    let mut g = || {
        let mut h = || {
            x = 100u64;
        };
        h();
    };
    g();
    trust_vc::assert!(x == 0u64);
}

#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn liar_nested_closure_capture_mutation_requires(mut x: u64) {
    let mut g = || {
        let mut h = || {
            x = 100u64;
        };
        h();
    };
    g();
    trust_vc::assert!(x == 0u64);
}

#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn liar_three_level_closure_capture_mutation(mut x: u64) {
    let mut g = || {
        let mut h = || {
            let mut k = || {
                x = 100u64;
            };
            k();
        };
        h();
    };
    g();
    trust_vc::assert!(x == 0u64);
}

#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn liar_nested_map_arg_capture_mutation(mut x: u64) {
    let g = || {
        let _ = Some(1u64).map(|_v| {
            x = 100u64;
            1u64
        });
    };
    g();
    trust_vc::assert!(x == 0u64);
}

// (3) the reached guard's namespace.

#[trust_vc::ensures(true)]
fn liar_reached_guard_named_from_source() {
    let _f = || {
        trust_vc::assume!(goo());
    };
    trust_vc::assume!(__trust_vc_closure_body_reached_0);
    trust_vc::assert!(goo());
}

#[trust_vc::ensures(true)]
fn liar_reached_guard_second_index_named_from_source() {
    let _f = || {
        trust_vc::assume!(goo());
    };
    let _h = || {
        trust_vc::assume!(goo());
    };
    trust_vc::assume!(__trust_vc_closure_body_reached_1);
    trust_vc::assert!(goo());
}

// The guard resolved to the engine's declared free `Bool` rather than failing
// closed — the same namespace hole read through an `assert!`.
#[trust_vc::ensures(true)]
fn liar_reached_guard_asserted_from_source() {
    let _f = || {
        trust_vc::assume!(goo());
    };
    trust_vc::assert!(__trust_vc_closure_body_reached_0);
}

// The round-1 `loop_ensures!` refusal must fire at ANY closure depth.
#[trust_vc::ensures(true)]
fn failclosed_nested_closure_loop_ensures(n: u64) {
    let _f = || {
        let _g = || {
            loop {
                trust_vc::invariant!(true);
                trust_vc::loop_ensures!(n == 7u64);
                if n == 7u64 {
                    break;
                }
            }
        };
    };
    trust_vc::assert!(n == 7u64);
}

// An UNDECLARED scoped-only `let` capture mutated two closures down.
//
// MERGE NOTE (work/sv0 + work/sv2, 2026-09-21): on work/sv2 alone this hit the
// `invalidate_scoped` fallback and failed closed on `unresolved variable `x``.
// work/sv0 (H3) added a middle rung to the same exit ladder --
// `havoc_scoped_scalar_local_to_fresh` -- so a scoped-only SCALAR local is now
// rebound to a fresh unconstrained symbol instead. The liar below is still a
// liar (`x` is 100 after `g()`), and it is now REFUTED WITH A MODEL rather than
// failing closed. That is the stronger negative verdict, not a weaker one: a
// fresh arbitrary `u64` over-approximates every reachable value of `x`, so
// `x == 0` is unprovable, and the case is pinned as `Refuted` below.
#[trust_vc::ensures(true)]
fn liar_nested_closure_let_capture_mutation() {
    let mut x = 0u64;
    let mut g = || {
        let mut h = || {
            x = 100u64;
        };
        h();
    };
    g();
    trust_vc::assert!(x == 0u64);
}

// ------------------------------------------------------------- CONTROLS

// The `ensures` lane over a by-value `mut` parameter reads the ENTRY value:
// both of these are refuted with NO loop and NO closure anywhere. They are what
// makes `liar_uncalled_invariant_into_postcondition` readable — under this
// semantics its postcondition is false for x = 11.
#[trust_vc::ensures(x <= 10u64)]
fn ctrl_ensures_entry_empty_body(mut x: u64) {}

#[trust_vc::ensures(x <= 10u64)]
fn ctrl_ensures_entry_straight_line_assign(mut x: u64) {
    x = 0u64;
}

// The ordinary (top-level) post-loop publication is untouched: the invariant is
// still a function-wide fact for a later assert AND for the postcondition.
#[trust_vc::ensures(true)]
fn ctrl_top_level_invariant_post_fact() {
    let mut k = 0u64;
    while k < 10u64 {
        trust_vc::invariant!(k <= 10u64);
        k = k + 1u64;
    }
    trust_vc::assert!(k == 10u64);
}

#[trust_vc::requires(x == 50u64)]
#[trust_vc::ensures(x <= 10u64)]
fn ctrl_top_level_loop_into_postcondition(mut x: u64) {
    x = 0u64;
    while x < 10u64 {
        trust_vc::invariant!(x <= 10u64);
        x = x + 1u64;
    }
}

// A closure-local loop modifies NOTHING an outer goal can name, so its
// invariant is still published for the closure's own post-loop reads — the
// break-site sibling of `ctrl_closure_invariant_used_inside`.
#[trust_vc::ensures(true)]
fn ctrl_closure_break_site_invariant_used_inside() {
    let _f = || {
        let mut k = 0u64;
        loop {
            trust_vc::invariant!(k <= 10u64);
            if k == 10u64 {
                break;
            }
            k = k + 1u64;
        }
        trust_vc::assert!(k <= 10u64);
    };
}

// A nested closure that only READS the capture must not havoc it.
#[trust_vc::requires(x <= 5u64)]
#[trust_vc::ensures(true)]
fn ctrl_nested_closure_read_only(x: u64) {
    let g = || {
        let h = || {
            let _y = x;
        };
        h();
    };
    g();
    trust_vc::assert!(x <= 5u64);
}

// A nested closure whose own PARAMETER carries the capture's name binds
// locally: not a capture, so nothing is havocked.
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn ctrl_nested_closure_param_shadows_capture(x: u64) {
    let g = || {
        let h = |mut x: u64| {
            x = 100u64;
        };
        h(3u64);
    };
    g();
    trust_vc::assert!(x == 0u64);
}

// A nested closure mutating its own local is not a capture mutation either.
#[trust_vc::requires(x <= 5u64)]
#[trust_vc::ensures(true)]
fn ctrl_nested_closure_local_mutation(x: u64) {
    let g = || {
        let h = || {
            let mut z = 0u64;
            z = 1u64;
        };
        h();
    };
    g();
    trust_vc::assert!(x <= 5u64);
}
"#;

#[derive(Clone, Copy, Debug)]
enum Expect {
    Verified,
    /// A `Counterexample` whose obligation name starts with this prefix.
    Refuted(&'static str),
    /// A fail-closed extraction/encoding error whose message contains this.
    FailsClosed(&'static str),
}

static FIXTURE_SEQ: AtomicUsize = AtomicUsize::new(0);

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, Ordering::SeqCst);
    let path = std::env::temp_dir().join(format!(
        "tvc_closure_body_facts_{}_{seq}_{func}.rs",
        std::process::id()
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

fn matches_expect(result: &Result<VerifyResult, String>, expect: Expect) -> bool {
    match (expect, result) {
        (Expect::Verified, Ok(VerifyResult::Verified)) => true,
        (
            Expect::Refuted(prefix),
            Ok(VerifyResult::Counterexample {
                obligation_name, ..
            }),
        ) => obligation_name.starts_with(prefix),
        (Expect::FailsClosed(fragment), Err(message)) => message.contains(fragment),
        (Expect::FailsClosed(fragment), Ok(VerifyResult::Error { message })) => {
            message.contains(fragment)
        }
        _ => false,
    }
}

/// Check every `(function, expectation)` pair and report ALL mismatches at once,
/// so one run shows the whole verdict table.
fn check(src: &str, cases: &[(&str, Expect)]) {
    let mut mismatches = Vec::new();
    for (func, expect) in cases {
        let result = verify(src, func);
        let ok = matches_expect(&result, *expect);
        println!(
            "VERDICT {func}: {} (expected {expect:?})",
            match &result {
                Ok(VerifyResult::Counterexample {
                    obligation_name, ..
                }) => format!("Counterexample({obligation_name})"),
                Ok(other) => format!("{other:?}"),
                Err(e) => format!("Err({e})"),
            }
        );
        if !ok {
            mismatches.push(format!("{func}: expected {expect:?}, got {result:?}"));
        }
    }
    assert!(
        mismatches.is_empty(),
        "closure-body fact scoping mismatches:\n{}",
        mismatches.join("\n")
    );
}

#[test]
fn closure_body_assume_does_not_reach_the_enclosing_function() {
    check(
        SRC_UNINTERPRETED,
        &[
            ("liar_bare_assume_uncalled", Expect::Refuted("assertion_")),
            ("liar_expr_body_no_attrs", Expect::Refuted("assertion_")),
            ("liar_move_closure_assume", Expect::Refuted("assertion_")),
            ("liar_literal_arg_spec", Expect::Refuted("assertion_")),
            ("liar_option_map_uncalled", Expect::Refuted("assertion_")),
            ("liar_iter_map_uncalled", Expect::Refuted("assertion_")),
            ("liar_nested_closure", Expect::Refuted("assertion_")),
            ("liar_proof_block_in_closure", Expect::Refuted("assertion_")),
            ("liar_match_arms_in_closure", Expect::Refuted("assertion_")),
            ("liar_assume_false_uncalled", Expect::Refuted("assertion_")),
            (
                "liar_assert_forall_by_in_closure",
                Expect::Refuted("assert_forall_by_"),
            ),
            (
                "liar_closure_in_nested_block",
                Expect::Refuted("assertion_"),
            ),
            (
                "liar_filter_closure_uncalled",
                Expect::Refuted("assertion_"),
            ),
            (
                "ctrl_closure_defined_under_if",
                Expect::Refuted("assertion_"),
            ),
        ],
    );
}

#[test]
fn closure_body_helper_ensures_do_not_reach_the_enclosing_function() {
    check(
        SRC_UNINTERPRETED,
        &[
            ("liar_helper_uncalled", Expect::Refuted("assertion_")),
            ("liar_sibling_helper", Expect::Refuted("assertion_")),
        ],
    );
}

#[test]
fn closure_body_facts_do_not_discharge_a_requires_linked_goal() {
    check(
        SRC_UNINTERPRETED,
        &[
            ("liar_requires_linked_assert", Expect::Refuted("assertion_")),
            ("liar_requires_linked_helper", Expect::Refuted("assertion_")),
            (
                "liar_requires_linked_into_ensures",
                Expect::Refuted("postcondition"),
            ),
        ],
    );
}

#[test]
fn closure_body_loop_exit_facts_do_not_reach_the_enclosing_function() {
    check(
        SRC_UNINTERPRETED,
        &[
            (
                "liar_loop_marker_assert_false",
                Expect::Refuted("assertion_"),
            ),
            (
                "liar_loop_marker_into_ensures",
                Expect::Refuted("postcondition"),
            ),
            (
                "liar_while_exit_over_capture",
                Expect::Refuted("assertion_"),
            ),
            ("liar_while_true_in_closure", Expect::Refuted("assertion_")),
            ("liar_let_else_in_closure", Expect::Refuted("assertion_")),
            // Refuted at the invariant's base case today (see the residual
            // below); any refutation is the soundness requirement.
            (
                "liar_loop_invariant_from_body_assume",
                Expect::Refuted("loop_invariant_"),
            ),
        ],
    );
}

#[test]
fn closure_body_proof_conclusions_do_not_escape() {
    check(
        SRC_UNINTERPRETED,
        &[
            ("liar_carry_forward", Expect::Refuted("assertion_2")),
            (
                "liar_called_closure_no_callsite_fact",
                Expect::Refuted("assertion_"),
            ),
            ("liar_assert_by_in_closure", Expect::Refuted("assert_by_")),
            (
                "liar_assert_by_contradiction_in_closure",
                Expect::Refuted("assert_by_contradiction_"),
            ),
        ],
    );
}

#[test]
fn closure_body_runtime_grade_witnesses_are_refuted() {
    check(
        SRC_RUNTIME,
        &[
            ("runtime_opaque", Expect::Refuted("assertion_")),
            ("runtime_hide_callee", Expect::Refuted("assertion_")),
            ("runtime_hide_caller_one", Expect::Verified),
            ("runtime_hide_caller_zero", Expect::Refuted("")),
            (
                "runtime_contract_leak_assume",
                Expect::Refuted("postcondition"),
            ),
            (
                "runtime_contract_no_closure",
                Expect::Refuted("postcondition"),
            ),
        ],
    );
}

#[test]
fn straight_line_and_branch_controls_keep_their_verdicts() {
    check(
        SRC_UNINTERPRETED,
        &[
            ("ctrl_top_level_assume_then_assert", Expect::Verified),
            ("ctrl_top_level_helper_then_assert", Expect::Verified),
            ("ctrl_if_false_assume", Expect::Refuted("assertion_")),
            ("ctrl_if_false_infinite_loop", Expect::Refuted("assertion_")),
            (
                "ctrl_closure_after_assert_order",
                Expect::Refuted("assertion_"),
            ),
            ("ctrl_capture_free_inline_call", Expect::Verified),
        ],
    );
}

#[test]
fn a_closure_keeps_its_own_reasoning() {
    check(
        SRC_UNINTERPRETED,
        &[
            ("ctrl_own_capture_reasoning", Expect::Verified),
            ("ctrl_own_zero_ary_reasoning", Expect::Verified),
            ("ctrl_own_helper_reasoning", Expect::Verified),
            ("ctrl_own_assume_guards_div", Expect::Verified),
            ("ctrl_two_self_contained_siblings", Expect::Verified),
            ("ctrl_outer_requires_visible_in_closure", Expect::Verified),
            ("ctrl_closure_local_loop", Expect::Verified),
            ("ctrl_own_unreachable_after_loop", Expect::Verified),
            (
                "ctrl_closure_loop_invariant_from_outer_requires",
                Expect::Verified,
            ),
        ],
    );
}

#[test]
fn loop_invariant_under_a_path_condition_residual_is_pinned() {
    check(
        SRC_UNINTERPRETED,
        &[
            (
                "residual_if_loop_invariant_from_branch_assume",
                Expect::Refuted("loop_invariant_"),
            ),
            (
                "residual_closure_loop_invariant_from_body_assume",
                Expect::Refuted("loop_invariant_"),
            ),
        ],
    );
}

#[test]
fn in_closure_obligations_stay_real() {
    check(
        SRC_UNINTERPRETED,
        &[
            (
                "ctrl_sibling_assume_does_not_discharge",
                Expect::Refuted("assertion_"),
            ),
            (
                "ctrl_lone_closure_assert_is_real",
                Expect::Refuted("assertion_"),
            ),
            (
                "ctrl_in_closure_overflow_before_assume_false",
                Expect::Refuted("overflow_check_"),
            ),
            (
                "ctrl_in_closure_overflow_alone",
                Expect::Refuted("overflow_check_"),
            ),
            (
                "failclosed_closure_macro_block_body",
                Expect::FailsClosed("non-value"),
            ),
        ],
    );
}

#[test]
fn closure_body_loop_post_facts_do_not_reach_the_enclosing_function() {
    const REFUSED: Expect = Expect::FailsClosed("inside a closure body is unsupported");
    check(
        SRC_LOOP_POST_FACTS_AND_CAPTURES,
        &[
            ("liar_loop_ensures_break_site_uncalled", REFUSED),
            ("liar_loop_ensures_normal_exit_uncalled", REFUSED),
            ("liar_loop_ensures_into_postcondition", REFUSED),
            ("liar_loop_ensures_false_while_true_uncalled", REFUSED),
            ("failclosed_loop_ensures_used_inside_closure", REFUSED),
            ("failclosed_loop_ensures_then_assume_false", REFUSED),
            ("ctrl_top_level_loop_ensures_break_site", Expect::Verified),
            ("ctrl_top_level_loop_ensures_normal_exit", Expect::Verified),
        ],
    );
}

#[test]
fn a_mutated_capture_is_fresh_after_the_closure() {
    check(
        SRC_LOOP_POST_FACTS_AND_CAPTURES,
        &[
            (
                "liar_called_closure_mutation_keeps_requires",
                Expect::Refuted("assertion_"),
            ),
            (
                "liar_uncalled_invariant_over_mutated_capture_let",
                Expect::Refuted("assertion_"),
            ),
            (
                "liar_uncalled_invariant_over_mutated_capture_param",
                Expect::Refuted("assertion_"),
            ),
            (
                "liar_called_invariant_then_overwrite",
                Expect::Refuted("assertion_"),
            ),
            ("ctrl_closure_invariant_used_inside", Expect::Verified),
            ("ctrl_unmutated_capture_keeps_requires", Expect::Verified),
            (
                "ctrl_mutated_capture_reassigned_after_call",
                Expect::Verified,
            ),
        ],
    );
}

/// REVIEW ROUND 2, channel 1: a verified `invariant!` (and its exit-site copy)
/// inside a closure body is checked in full but is NOT republished as a
/// function-wide post-loop fact when the loop modifies a symbol the enclosing
/// function can name. The `ctrl_ensures_entry_*` pair fixes the lane's
/// semantics, the `ctrl_top_level_*` pair pins that the ordinary publication is
/// untouched, and `ctrl_closure_break_site_invariant_used_inside` pins that a
/// purely closure-local loop keeps its post-loop fact.
#[test]
fn in_closure_loop_facts_do_not_reach_the_postcondition() {
    check(
        SRC_ROUND2_LOOP_FACTS_AND_NESTED_CAPTURES,
        &[
            (
                "liar_uncalled_invariant_into_postcondition",
                Expect::Refuted("postcondition"),
            ),
            (
                "liar_requires_linked_uncalled_invariant_into_postcondition",
                Expect::Refuted("postcondition"),
            ),
            (
                "liar_shadowing_loop_local_invariant_hits_outer_param",
                Expect::Refuted("assertion_"),
            ),
            (
                "liar_break_site_invariant_copy_into_postcondition",
                Expect::Refuted("postcondition"),
            ),
            (
                "liar_break_site_invariant_copy_into_outer_assert",
                Expect::Refuted("assertion_"),
            ),
            (
                "ctrl_ensures_entry_empty_body",
                Expect::Refuted("postcondition"),
            ),
            (
                "ctrl_ensures_entry_straight_line_assign",
                Expect::Refuted("postcondition"),
            ),
            ("ctrl_top_level_invariant_post_fact", Expect::Verified),
            ("ctrl_top_level_loop_into_postcondition", Expect::Verified),
            (
                "ctrl_closure_break_site_invariant_used_inside",
                Expect::Verified,
            ),
        ],
    );
}

/// REVIEW ROUND 2, channel 2: a capture mutated inside a NESTED closure is
/// havocked after the outer closure, at every depth and through a method
/// argument. The three controls pin that a read-only capture, a nested
/// PARAMETER of the same name, and a nested closure's own local are all left
/// alone.
#[test]
fn a_capture_mutated_in_a_nested_closure_is_fresh_after_the_closure() {
    check(
        SRC_ROUND2_LOOP_FACTS_AND_NESTED_CAPTURES,
        &[
            (
                "liar_nested_closure_capture_mutation",
                Expect::Refuted("assertion_"),
            ),
            (
                "liar_nested_closure_capture_mutation_requires",
                Expect::Refuted("assertion_"),
            ),
            (
                "liar_three_level_closure_capture_mutation",
                Expect::Refuted("assertion_"),
            ),
            (
                "liar_nested_map_arg_capture_mutation",
                Expect::Refuted("assertion_"),
            ),
            (
                // See the MERGE NOTE on the fixture: the sv0 ladder freshens a
                // scoped-only scalar local, so this liar is refuted with a
                // model instead of failing closed on an unresolved name.
                "liar_nested_closure_let_capture_mutation",
                Expect::Refuted("assertion_"),
            ),
            ("ctrl_nested_closure_read_only", Expect::Verified),
            (
                "ctrl_nested_closure_param_shadows_capture",
                Expect::Verified,
            ),
            ("ctrl_nested_closure_local_mutation", Expect::Verified),
        ],
    );
}

/// REVIEW ROUND 2, channel 3: the reached-guard identifier namespace is
/// reserved. Naming it from source used to bind the engine's own free `Bool`
/// and re-admit every guarded closure-body fact.
#[test]
fn the_reached_guard_namespace_cannot_be_named_from_source() {
    const RESERVED: Expect = Expect::FailsClosed(
        "reserved for the verifier's closure-body reached guards and cannot be \
         named from source",
    );
    check(
        SRC_ROUND2_LOOP_FACTS_AND_NESTED_CAPTURES,
        &[
            ("liar_reached_guard_named_from_source", RESERVED),
            (
                "liar_reached_guard_second_index_named_from_source",
                RESERVED,
            ),
            ("liar_reached_guard_asserted_from_source", RESERVED),
            (
                "failclosed_nested_closure_loop_ensures",
                Expect::FailsClosed("inside a closure body is unsupported"),
            ),
        ],
    );
}
