// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Fixtures for the INCREMENT 2b (Fn-bound closure dispatch, cross-boundary
// PASS-SITE linkage) adversarial soundness suite
// (`fn_bound_closure_pass_site_soundness.rs`). Verified via
// verify_function_from_file, cache-OFF.
//
// A caller passes a concrete `trust_vc::closure!` literal `c` into an
// `F: Fn(u64) -> u64`-bounded callee `g` whose contract REFLECTS the closure:
//
//     requires f.requires((a,))
//     ensures  f.ensures((a,), result)
//
// At the pass site `g(c, 5)` the callee's `f.requires((a,))` / `f.ensures((a,),
// result)` clauses substitute to `c.requires((5,))` / `c.ensures((5,), g(c, 5))`,
// which lower to the OPAQUE reflection UFs `call_requires%` / `call_ensures%`.
// Increment 2b bridges those UF applications to `c`'s OWN concrete, arg-
// substituted requires/ensures with DEFINITIONAL ground facts, so the caller can
// PROVE `g`'s prove-`requires` (from `c`'s `5 < 10`) and USE `g`'s assumed
// `ensures` (`c`'s `y == 6`).
//
// SOUNDNESS.
//  * The ground fact is emitted ONLY for a bare-ident arg registered in
//    `closure_reflection_contracts` (⇔ `c`'s def-side obligation was emitted at
//    its `let c = …`). A lying closure sinks the DEFINING function via its
//    independent def-side check, so 2b needs no separate def-side check and
//    cannot mask that failure (LYING-CLOSURE trap).
//  * An Fn-bound PARAMETER re-passed as an arg is NOT registered ⇒ NO ground fact
//    ⇒ the callee's opaque `requires` stays undischargeable ⇒ fails closed
//    (PARAM-REPASS trap).
//  * The fact is CONSERVATIVE (fixes the opaque UF's value), so a false ensures
//    use (`assert!(y == 7)`) and a requires violation (`g(c, 50)`) both
//    counterexample.

// ===========================================================================
// SHARED CALLEE. An `F: Fn(u64) -> u64` value parameter used through its own
// spec (Increment 2a). Collected as a sibling helper contract by every caller
// below. `requires f.requires((a,))` (assumed at entry) + `ensures f.ensures((a,),
// result)`.
// ===========================================================================
#[trust_vc::contract(
    requires(f.requires((a,))),
    ensures(f.ensures((a,), result)),
    returns(result),
)]
fn fnbound_2b_apply_callee<F: Fn(u64) -> u64>(f: F, a: u64) -> u64 {
    f(a)
}

// ===========================================================================
// POSITIVE ROUND-TRIP — MUST VERIFY. The caller passes a concrete closure `c`
// (requires `x < 10`, ensures `r == x + 1`) into the callee at `g(c, 5)`. The
// pass-site linkage discharges `g`'s prove-`requires` from `c`'s `5 < 10` (true)
// and pins `g`'s assumed `ensures` to `c`'s `y == 5 + 1`, so `assert!(y == 6)`
// holds. The load-bearing success signal.
// ===========================================================================
#[trust_vc::ensures(true)]
fn fnbound_2b_positive_roundtrip() {
    let c = trust_vc::closure!(
        |x: u64| -> u64
        requires(x < 10u64)
        ensures(|r: u64| r == x + 1u64)
        x + 1u64
    );
    let y = fnbound_2b_apply_callee(c, 5u64);
    trust_vc::assert!(y == 6u64);
}

// ===========================================================================
// REQUIRES-VIOLATION TRAP — MUST COUNTEREXAMPLE. `c` requires `x < 10`, but the
// call passes `50`. The linkage pins `call_requires%(c, (50,)) == (50 < 10) ==
// false`, so `g`'s prove-`requires` obligation is false. A `Verified` here =
// admitting a call that violates the closure's precondition = UNSOUND.
// ===========================================================================
#[trust_vc::ensures(true)]
fn fnbound_2b_requires_violation_cx() {
    let c = trust_vc::closure!(
        |x: u64| -> u64
        requires(x < 10u64)
        ensures(|r: u64| r == x + 1u64)
        x + 1u64
    );
    let y = fnbound_2b_apply_callee(c, 50u64);
    trust_vc::assert!(y == 51u64);
}

// ===========================================================================
// FALSE-ENSURES-USE TRAP — MUST COUNTEREXAMPLE. The call is valid (`5 < 10`), so
// the ensures linkage fires and pins `y == 6`, but the caller asserts `y == 7`.
// A `Verified` here = the linked ensures did not actually constrain the result =
// UNSOUND.
// ===========================================================================
#[trust_vc::ensures(true)]
fn fnbound_2b_false_ensures_use_cx() {
    let c = trust_vc::closure!(
        |x: u64| -> u64
        requires(x < 10u64)
        ensures(|r: u64| r == x + 1u64)
        x + 1u64
    );
    let y = fnbound_2b_apply_callee(c, 5u64);
    trust_vc::assert!(y == 7u64);
}

// ===========================================================================
// LYING-CLOSURE TRAP — MUST COUNTEREXAMPLE. `c` CLAIMS `ensures r == x + 1` but
// its body returns `x + 2`. The closure's INDEPENDENT def-side obligation (run in
// an isolated child at `let c = …`) fails and sinks the DEFINING function
// `caller`, regardless of the pass site. The 2b linkage (which faithfully pins
// `c`'s WRITTEN ensures) must NOT mask that def-side counterexample.
// ===========================================================================
#[trust_vc::ensures(true)]
fn fnbound_2b_lying_closure_cx() {
    let c = trust_vc::closure!(
        |x: u64| -> u64
        requires(x < 10u64)
        ensures(|r: u64| r == x + 1u64)
        x + 2u64
    );
    let y = fnbound_2b_apply_callee(c, 5u64);
    trust_vc::assert!(y == 6u64);
}

// ===========================================================================
// FN-BOUND-PARAM-REPASS TRAP — MUST NOT VERIFY. The wrapper's Fn-bound parameter
// `f` is re-passed to the callee at `g(f, 5)`. `f` is NOT a registered closure
// literal, so NO pass-site ground fact is emitted; `g`'s prove-`requires`
// (`call_requires%(f, (5,))`) is the opaque UF with nothing to discharge it, and
// the ensures is never pinned to a concrete value. A `Verified` here = a
// re-passed param wrongly received a linkage = UNSOUND. Fails closed.
// ===========================================================================
#[trust_vc::ensures(true)]
fn fnbound_2b_param_repass_fail_closed<F: Fn(u64) -> u64>(f: F) {
    let y = fnbound_2b_apply_callee(f, 5u64);
    trust_vc::assert!(y == 6u64);
}

// ===========================================================================
// REGRESSION — determinism WITHOUT passing a closure still VERIFIES from the
// congruent `spec_fn_apply` term alone (Increment 1 intact). A local closure `c`
// exists in scope, but this caller does not pass it to a reflecting callee, so no
// pass-site fact is emitted and nothing is over-constrained. MUST VERIFY.
// ===========================================================================
#[trust_vc::ensures(true)]
fn fnbound_2b_determinism_regression<F: Fn(u64) -> u64>(f: F) {
    let a = f(3u64);
    let b = f(3u64);
    trust_vc::assert!(a == b);
}

// ===========================================================================
// SHADOW-RESTORATION TRAP — MUST NOT VERIFY. The inner `c` has a different,
// valid contract but leaves scope before the call. The call therefore passes
// the OUTER `c`, whose result is 6; proving 7 would witness a leaked inner
// `closure_reflection_contracts` entry being linked at the pass site.
// ===========================================================================
#[trust_vc::ensures(true)]
fn fnbound_2b_shadowed_contract_must_not_escape() {
    let c = trust_vc::closure!(
        |x: u64| -> u64
        requires(x < 10u64)
        ensures(|r: u64| r == x + 1u64)
        x + 1u64
    );
    {
        let c = trust_vc::closure!(
            |x: u64| -> u64
            requires(x < 10u64)
            ensures(|r: u64| r == x + 2u64)
            x + 2u64
        );
        let _ = c;
    }
    let y = fnbound_2b_apply_callee(c, 5u64);
    trust_vc::assert!(y == 7u64);
}

// ===========================================================================
// VALUE-SCOPE PARITY — MUST VERIFY. The inner closure binding shadows an outer
// scalar with the same Rust identifier. Inside the block, `c` must denote the
// SpecFn closure at the pass site; after the block, it must again denote 99.
// ===========================================================================
#[trust_vc::ensures(true)]
fn fnbound_2b_closure_shadows_outer_scalar() {
    let c = 99u64;
    {
        let c = trust_vc::closure!(
            |x: u64| -> u64
            requires(x < 10u64)
            ensures(|r: u64| r == x + 1u64)
            x + 1u64
        );
        let y = fnbound_2b_apply_callee(c, 5u64);
        trust_vc::assert!(y == 6u64);
    }
    trust_vc::assert!(c == 99u64);
}
