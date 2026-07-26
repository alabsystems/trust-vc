// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Fixtures for the INCREMENT 2a (Fn-bound closure dispatch, callee-side
// obligation model) adversarial soundness suite
// (`fn_bound_closure_obligation_soundness.rs`). Verified via
// verify_function_from_file, cache-OFF.
//
// At a Fn-bound call `let r = f(a)` (where `f: F`, `F: Fn(A) -> B` is typed
// `SpecFn` by Increment 1) the callee-side seam emits, over the OPAQUE reflection
// UFs `call_requires%` / `call_ensures%`, the SOUND conditional assumption
//
//     call_requires%(f, a)  ==>  call_ensures%(f, a, f(a))
//
// binding the REAL returned `spec_fn_apply(f, a)` term. This is the closure's own
// contract ("if the precondition holds for the args, the postcondition holds for
// the result") and is unconditionally valid for ANY closure satisfying `F: Fn`.
//
// SOUNDNESS (the crux — prove-requires GATES assume-ensures):
//  * `call_ensures%` is NEVER assumed unconditionally: it is derivable ONLY once
//    `call_requires%(f, a)` is independently established (from the callee's own
//    `requires f.requires((a,))`, which lowers to an ASSUMED `call_requires%`, or
//    an explicit `assume!`). A callee that USES `f.ensures` WITHOUT establishing
//    `f.requires` cannot derive the postcondition and fails closed (TRAP #2).
//  * `call_ensures%` stays OPAQUE: it pins NO concrete value, so a concrete claim
//    about the result (`assert!(f(a) == 5)`) is not provable (TRAP #1). The callee
//    never invents a def-side for the parameter.
//  * The Increment-1 congruent term is untouched: determinism (`f(3) == f(3)`)
//    verifies from congruence alone WITHOUT any obligation, and a concrete pin
//    (`f(3) == 3`) still counterexamples.

// ===========================================================================
// POSITIVE (tail form) — MUST VERIFY. The callee declares `requires
// f.requires((a,))` (assumed at entry) and `ensures f.ensures((a,), result)`.
// The call-site conditional assume, combined with the assumed precondition,
// derives `call_ensures%(f, a, f(a))`; the return binds `result == f(a)`, so the
// postcondition discharges. Sound for ANY `F: Fn`.
// ===========================================================================
#[trust_vc::contract(
    requires(f.requires((a,))),
    ensures(f.ensures((a,), result)),
    returns(result),
)]
fn fnbound_obligation_positive_tail<F: Fn(u64) -> u64>(f: F, a: u64) -> u64 {
    f(a)
}

// ===========================================================================
// POSITIVE (let form) — MUST VERIFY. Same as above with the application on a
// `let`-RHS (the straight-line `visit_expr_call` seam), returning the local.
// ===========================================================================
#[trust_vc::contract(
    requires(f.requires((a,))),
    ensures(f.ensures((a,), result)),
    returns(result),
)]
fn fnbound_obligation_positive_let<F: Fn(u64) -> u64>(f: F, a: u64) -> u64 {
    let observed = f(a);
    observed
}

// ===========================================================================
// FALSE-VERIFY TRAP #1 (opaque, not concrete) — MUST COUNTEREXAMPLE. The
// precondition is declared (so `call_requires%` is established and the ensures
// IS derivable), but `call_ensures%` is OPAQUE and pins no concrete value, so
// `r == 5` is not provable. A `Verified` here = inventing a concrete result =
// UNSOUND.
// ===========================================================================
#[trust_vc::requires(f.requires((a,)))]
fn fnbound_obligation_pins_concrete_result_cx<F: Fn(u64) -> u64>(f: F, a: u64) {
    let r = f(a);
    trust_vc::assert!(r == 5u64);
}

// ===========================================================================
// ANTI-VACUITY / binds-the-REAL-return — MUST COUNTEREXAMPLE. The callee declares
// BOTH the requires (so `call_ensures%(f, a, f(a))` IS derivable) AND the ensures,
// but RETURNS a value other than `f(a)`. The call-site assume pins
// `call_ensures%(f, a, f(a))`, NOT `call_ensures%(f, a, 5)`, so the postcondition
// `f.ensures((a,), result)` with `result == 5` is NOT derivable. A `Verified` here
// = the assume bound an arbitrary value / the ensures is trivially true = UNSOUND.
// ===========================================================================
#[trust_vc::contract(
    requires(f.requires((a,))),
    ensures(f.ensures((a,), result)),
    returns(result),
)]
fn fnbound_obligation_wrong_return_cx<F: Fn(u64) -> u64>(f: F, a: u64) -> u64 {
    let _ = f(a);
    5u64
}

// ===========================================================================
// FALSE-VERIFY TRAP #2 (missing prove-requires) — MUST COUNTEREXAMPLE /
// fail-closed. The callee USES `f.ensures` (as its postcondition) but does NOT
// declare `requires f.requires((a,))`. `call_requires%(f, a)` is unconstrained,
// so the conditional assume cannot fire and the postcondition
// `call_ensures%(f, a, result)` is underivable. If the ensures were usable
// WITHOUT establishing the (non-trivial, opaque) requires, that would be UNSOUND.
// ===========================================================================
#[trust_vc::contract(
    ensures(f.ensures((a,), result)),
    returns(result),
)]
fn fnbound_obligation_missing_requires_cx<F: Fn(u64) -> u64>(f: F, a: u64) -> u64 {
    f(a)
}

// ===========================================================================
// TRAP #2 companion (assert form) — MUST COUNTEREXAMPLE. Uses `f.ensures` in an
// assert without declaring the requires. Same gating: the ensures is underivable.
// ===========================================================================
#[trust_vc::ensures(true)]
fn fnbound_obligation_missing_requires_assert_cx<F: Fn(u64) -> u64>(f: F, a: u64) {
    let r = f(a);
    trust_vc::assert!(f.ensures((a,), r));
}

// ===========================================================================
// REGRESSION (Increment 1 intact): determinism WITHOUT a requires clause still
// VERIFIES from the congruent `spec_fn_apply` term alone — the callee-side seam
// adds ONLY a conditional assume (inert here, its result unused), NO standalone
// obligation that a requires-free call could fail. MUST VERIFY.
// ===========================================================================
#[trust_vc::ensures(true)]
fn fnbound_obligation_determinism_verified<F: Fn(u64) -> u64>(f: F) {
    let a = f(3u64);
    let b = f(3u64);
    trust_vc::assert!(a == b);
}

// ===========================================================================
// REGRESSION: a concrete pin of the result still COUNTEREXAMPLES (the result is
// unconstrained; the conditional assume pins no value without a matching
// `f.ensures`). MUST COUNTEREXAMPLE.
// ===========================================================================
#[trust_vc::ensures(true)]
fn fnbound_obligation_pins_concrete_no_requires_cx<F: Fn(u64) -> u64>(f: F) {
    let observed = f(3u64);
    trust_vc::assert!(observed == 3u64);
}

// ===========================================================================
// REGRESSION: `FnMut` stays fail-closed (non-deterministic; not typed `SpecFn`,
// so the call does not lower and no obligation is emitted). MUST NOT VERIFY.
// ===========================================================================
#[trust_vc::ensures(true)]
fn fnbound_obligation_fnmut_fail_closed<F: FnMut(u64) -> u64>(mut f: F) {
    let a = f(3u64);
    let b = f(3u64);
    trust_vc::assert!(a == b);
}

// ===========================================================================
// REGRESSION: `FnOnce` stays fail-closed. MUST NOT VERIFY.
// ===========================================================================
#[trust_vc::ensures(true)]
fn fnbound_obligation_fnonce_fail_closed<F: FnOnce(u64) -> u64>(f: F) {
    let observed = f(3u64);
    trust_vc::assert!(observed == observed);
}
