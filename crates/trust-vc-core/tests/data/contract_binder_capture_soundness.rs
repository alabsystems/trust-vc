// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Fixture for `contract_binder_capture_soundness.rs`.
//!
//! Every `_must_refute` here is a program that MUST NOT verify; every
//! `_must_verify` is a capability pin that MUST keep verifying.
#![allow(dead_code, unused_variables)]

// ===================== THE CONFIRMED CARDINAL FALSE VERIFY =================
// `forall|m: int| m <= 100` is FALSE (`int` is unbounded), so NO call site can
// discharge it and every call to `cap_callee` is illegal. The postcondition
// claims `result == 1` while the body returns 0 — a claim only the
// contradictory precondition licenses. The call-site substituter used to
// rewrite the BOUND `m` with the argument, collapsing the clause to
// `forall|m: int| 5 <= 100` (a tautology) and letting the caller verify.
#[trust_vc::requires(forall|m: int| m <= 100)]
#[trust_vc::ensures(result == 1u64)]
fn cap_callee(m: u64) -> u64 {
    0u64
}

#[trust_vc::ensures(true)]
fn capture_literal_arg_must_refute() -> u64 {
    let r: u64 = cap_callee(5u64);
    trust_vc::assert!(r == 1u64);
    0u64
}

#[trust_vc::ensures(true)]
fn capture_local_arg_must_refute() -> u64 {
    let a: u64 = 5u64;
    let r: u64 = cap_callee(a);
    trust_vc::assert!(r == 1u64);
    0u64
}

// ARGUMENT-VALUE DEPENDENCE — the discriminator that identifies capture. An
// unprovable CLOSED clause cannot change verdict with the argument. Before the
// fix `5` verified and `200` was refuted; both must be refuted now.
#[trust_vc::requires(forall|m: int| m <= 100)]
#[trust_vc::ensures(true)]
fn dep_callee(m: u64) -> u64 {
    0u64
}

#[trust_vc::ensures(true)]
fn arg_value_small_must_refute() -> u64 {
    let a: u64 = 5u64;
    let r: u64 = dep_callee(a);
    0u64
}

#[trust_vc::ensures(true)]
fn arg_value_big_must_refute() -> u64 {
    let a: u64 = 200u64;
    let r: u64 = dep_callee(a);
    0u64
}

// CONTROL — the identical clause with the binder renamed so it collides with
// nothing. This one was ALWAYS refuted; it pins that the two above are decided
// by the shadowing and not by anything else in the shape.
#[trust_vc::requires(forall|w: int| w <= 100)]
#[trust_vc::ensures(result == 1u64)]
fn control_callee(m: u64) -> u64 {
    0u64
}

#[trust_vc::ensures(true)]
fn control_no_shadow_must_refute() -> u64 {
    let r: u64 = control_callee(5u64);
    trust_vc::assert!(r == 1u64);
    0u64
}

// ===== FREE AND BOUND OCCURRENCES OF THE SAME NAME IN ONE CLAUSE ==========
// `m > 0 && forall|m: int| m <= 100`: the first `m` is the PARAMETER (free, must
// be substituted with the argument), the second is BOUND (must not be). Get
// either one wrong and the clause becomes provable; correct handling leaves
// `5 > 0 && forall|m: int| m <= 100`, which is FALSE.
#[trust_vc::requires(m > 0 && forall|m: int| m <= 100)]
#[trust_vc::ensures(true)]
fn mixed_callee(m: u64) -> u64 {
    0u64
}

#[trust_vc::ensures(true)]
fn mixed_free_and_bound_must_refute() -> u64 {
    let r: u64 = mixed_callee(5u64);
    0u64
}

// ===== `ensures` SIDE: a binder shadowing a parameter used as an assumption ==
// `exists|a: int| a > 0` is TRUE, so it is assumed at the call site. Capturing
// the bound `a` with the argument `0` turns the assumption into
// `exists|a: int| 0 > 0` — FALSE — and every later assertion goes vacuous.
#[trust_vc::ensures(exists|a: int| a > 0)]
fn ens_callee(a: u64) -> u64 {
    0u64
}

#[trust_vc::ensures(true)]
fn ensures_binder_capture_must_refute() -> u64 {
    let z: u64 = 0u64;
    let r: u64 = ens_callee(z);
    trust_vc::assert!(1u64 == 2u64);
    0u64
}

// ========================= NARROWNESS PINS ================================
// The fix skips BOUND occurrences only. Skipping a FREE one would be unsound in
// the other direction, and skipping legitimate substitution would be a
// capability loss. Both are pinned below.

// (1) A shadowing binder over a clause that is TRUE: the call is legal and must
//     still verify. A blanket "decline on any shadowing binder" fails here.
#[trust_vc::requires(forall|m: int| m <= 100 || m > 100)]
#[trust_vc::ensures(true)]
fn taut_callee(m: u64) -> u64 {
    0u64
}

#[trust_vc::ensures(true)]
fn shadowed_binder_tautology_must_verify() -> u64 {
    let r: u64 = taut_callee(5u64);
    0u64
}

// (2) Substitution UNDER a non-colliding binder must still happen: `n` is free
//     inside the `forall|k|` and must be replaced by the argument.
#[trust_vc::requires(forall|k: int| k <= 0 || n >= 1)]
#[trust_vc::ensures(true)]
fn under_binder_callee(n: u64) -> u64 {
    0u64
}

#[trust_vc::ensures(true)]
fn substitution_under_binder_must_verify() -> u64 {
    let r: u64 = under_binder_callee(7u64);
    0u64
}

#[trust_vc::ensures(true)]
fn substitution_under_binder_must_refute() -> u64 {
    let r: u64 = under_binder_callee(0u64);
    0u64
}

// (3) THE OTHER UNSOUND DIRECTION. `requires(m <= 100)` has no binder, so `m` is
//     free and MUST be substituted. If it were left alone it would re-bind to
//     the CALLER's local `m` (= 5) and a call passing 200 would wrongly pass.
#[trust_vc::requires(m <= 100)]
#[trust_vc::ensures(true)]
fn caller_scope_callee(m: u64) -> u64 {
    0u64
}

#[trust_vc::ensures(true)]
fn caller_local_shadow_must_refute() -> u64 {
    let m: u64 = 5u64;
    let r: u64 = caller_scope_callee(200u64);
    0u64
}

#[trust_vc::ensures(true)]
fn caller_local_shadow_must_verify() -> u64 {
    let m: u64 = 5u64;
    let r: u64 = caller_scope_callee(50u64);
    0u64
}

// (4) The argument expression may itself name the callee's binder. Splicing it
//     under the binder would capture it; this lane was already correct and must
//     stay correct in both directions.
#[trust_vc::requires(forall|k: int| n >= 1)]
#[trust_vc::ensures(true)]
fn arg_named_like_binder_callee(n: u64) -> u64 {
    0u64
}

#[trust_vc::ensures(true)]
fn arg_named_like_binder_must_verify() -> u64 {
    let k: u64 = 7u64;
    let r: u64 = arg_named_like_binder_callee(k);
    0u64
}

#[trust_vc::ensures(true)]
fn arg_named_like_binder_must_refute() -> u64 {
    let k: u64 = 0u64;
    let r: u64 = arg_named_like_binder_callee(k);
    0u64
}

// (5) Plain unquantified contracts, both directions — the overwhelmingly common
//     shape must be untouched.
#[trust_vc::requires(n >= 1)]
#[trust_vc::ensures(true)]
fn plain_callee(n: u64) -> u64 {
    0u64
}

#[trust_vc::ensures(true)]
fn plain_requires_must_verify() -> u64 {
    let r: u64 = plain_callee(9u64);
    0u64
}

#[trust_vc::ensures(true)]
fn plain_requires_must_refute() -> u64 {
    let r: u64 = plain_callee(0u64);
    0u64
}

// (6) A plain `ensures` naming `result` must still substitute the call result.
#[trust_vc::ensures(result == 4u64)]
fn plain_ensures_callee(n: u64) -> u64 {
    4u64
}

#[trust_vc::ensures(true)]
fn plain_ensures_must_verify() -> u64 {
    let r: u64 = plain_ensures_callee(3u64);
    trust_vc::assert!(r == 4u64);
    0u64
}

#[trust_vc::ensures(true)]
fn plain_ensures_must_refute() -> u64 {
    let r: u64 = plain_ensures_callee(3u64);
    trust_vc::assert!(r == 5u64);
    0u64
}

// ===== `let` INSIDE A CONTRACT CLAUSE — the other binder form that occurs =====
// A block local scopes over the REST of the block, and its INITIALIZER is
// evaluated in the scope BEFORE the binding. Both halves are pinned.

// The local shadows the parameter: `{ let n = 0; n >= 1 }` is FALSE whatever the
// argument, so the call is illegal. Substituting the shadowed `n` would make it
// `{ let n = 0; 9 >= 1 }` — provable — which is the same capture one level down.
#[trust_vc::requires({ let n: u64 = 0u64; n >= 1 })]
#[trust_vc::ensures(true)]
fn let_shadow_callee(n: u64) -> u64 {
    0u64
}

#[trust_vc::ensures(true)]
fn let_local_shadow_must_refute() -> u64 {
    let r: u64 = let_shadow_callee(9u64);
    0u64
}

// The initializer reads the PARAMETER, which is still free there and must be
// substituted — pinned in both directions so a scope pushed one statement too
// early would be caught.
#[trust_vc::requires({ let q: u64 = n; q >= 1 })]
#[trust_vc::ensures(true)]
fn let_init_callee(n: u64) -> u64 {
    0u64
}

#[trust_vc::ensures(true)]
fn let_initializer_must_verify() -> u64 {
    let r: u64 = let_init_callee(9u64);
    0u64
}

#[trust_vc::ensures(true)]
fn let_initializer_must_refute() -> u64 {
    let r: u64 = let_init_callee(0u64);
    0u64
}
