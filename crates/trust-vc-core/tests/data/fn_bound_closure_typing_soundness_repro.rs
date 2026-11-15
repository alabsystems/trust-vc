// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Fixtures for the INCREMENT 1 (Fn-bound closure typing foundation) adversarial
// soundness suite (`fn_bound_closure_typing_soundness.rs`). Verified via
// verify_function_from_file, cache-OFF.
//
// An `F: Fn(A..) -> B`-bounded value parameter `f: F` is typed as a first-class
// `SpecFn(A.., B)` value, so a call `f(x)` lowers to the opaque, congruent
// `spec_fn_apply` UF. So:
//   * reflexivity of one call (`let o = f(3); o == o`) VERIFIES;
//   * two calls with the same arguments are the same term, but an `Fn` closure
//     can read shared state (an atomic, a borrowed `Cell`), so `f(3) == f(3)`
//     is false at run time; the `Verified` answer is refused;
//   * the result is otherwise UNCONSTRAINED — `f(3) == 3` and `f(3) == f(4)`
//     are NOT provable and COUNTEREXAMPLE (the traps below).
// `FnMut`/`FnOnce` are non-deterministic across calls; they are NOT typed as a
// congruent `SpecFn` and stay fail-closed (H6: an application of one is rejected
// at extraction with a "function value" diagnostic).
//
// H6: an application `f(x)` PROVES `f.requires((x,))` at the call
// (Verus/vstd semantics — upstream `pass_closure_via_typ_param` / `takes_fn1`
// require it) and assumes `f.ensures((x,), f(x))` only under it. Before H6 the
// requires was folded into an assumed implication and never proven, so a
// requires-free callee verified and a caller passing a closure with a real
// precondition panicked. Every positive fixture therefore declares the
// `f.requires(..)` it applies under, and each has a requires-free twin
// (`*_no_requires_cx`) that counterexamples on the call-site requires.

// ---------------------------------------------------------------------------
// TARGET (Fn): reflexivity of a call through the bound. MUST VERIFY.
// The load-bearing witness that the `SpecFn` typing took effect: without it the
// call fails closed ("Undefined function: f").
// ---------------------------------------------------------------------------
#[trust_vc::requires(f.requires((3u64,)))]
fn fnbound_reflexive_verified<F: Fn(u64) -> u64>(f: F) {
    let observed = f(3u64);
    trust_vc::assert!(observed == observed);
}

// H6 twin: the same reflexive read without the requires — the call-site
// `f.requires((3,))` is unprovable. MUST COUNTEREXAMPLE on `__call_requires`.
#[trust_vc::ensures(true)]
fn fnbound_reflexive_no_requires_cx<F: Fn(u64) -> u64>(f: F) {
    let observed = f(3u64);
    trust_vc::assert!(observed == observed);
}

// ---------------------------------------------------------------------------
// TWO CALLS, SAME ARGUMENTS: false for a closure that returns a counter. The
// congruent UF would prove it, so the `Verified` answer MUST BE REFUSED. The
// refusal is produced only from a `Verified` answer, so it also witnesses that
// the call was typed and lowered.
// ---------------------------------------------------------------------------
#[trust_vc::requires(f.requires((3u64,)))]
fn fnbound_determinism_refused<F: Fn(u64) -> u64>(f: F) {
    let a = f(3u64);
    let b = f(3u64);
    trust_vc::assert!(a == b);
}

// H6 twin: requires-free determinism is refuted on the call-site requires.
#[trust_vc::ensures(true)]
fn fnbound_determinism_no_requires_cx<F: Fn(u64) -> u64>(f: F) {
    let a = f(3u64);
    let b = f(3u64);
    trust_vc::assert!(a == b);
}

// The same under the where-clause spelling of the bound (exercises the
// where-predicate recognition path). MUST BE REFUSED.
#[trust_vc::requires(f.requires((5u64,)))]
fn fnbound_determinism_where_clause_refused<F>(f: F)
where
    F: Fn(u64) -> u64,
{
    let a = f(5u64);
    let b = f(5u64);
    trust_vc::assert!(a == b);
}

// H6 twin (where-clause spelling): refuted on the call-site requires.
#[trust_vc::ensures(true)]
fn fnbound_determinism_where_clause_no_requires_cx<F>(f: F)
where
    F: Fn(u64) -> u64,
{
    let a = f(5u64);
    let b = f(5u64);
    trust_vc::assert!(a == b);
}

// ---------------------------------------------------------------------------
// FALSE-VERIFY TRAP #1: the result is UNCONSTRAINED, so pinning it to a concrete
// value is not provable. MUST COUNTEREXAMPLE (a `Verified` here = inventing
// behaviour = UNSOUND). A Counterexample (NOT an "Undefined function" error) is
// the load-bearing witness that the term is modeled but unconstrained.
// ---------------------------------------------------------------------------
#[trust_vc::requires(f.requires((3u64,)))]
fn fnbound_pins_concrete_result_cx<F: Fn(u64) -> u64>(f: F) {
    let observed = f(3u64);
    trust_vc::assert!(observed == 3u64);
}

// ---------------------------------------------------------------------------
// FALSE-VERIFY TRAP #2: DIFFERENT arguments — congruence gives nothing. MUST
// COUNTEREXAMPLE.
// ---------------------------------------------------------------------------
#[trust_vc::requires(f.requires((3u64,)) && f.requires((4u64,)))]
fn fnbound_distinct_args_cx<F: Fn(u64) -> u64>(f: F) {
    let a = f(3u64);
    let b = f(4u64);
    trust_vc::assert!(a == b);
}

// ---------------------------------------------------------------------------
// FnMut UNSOUNDNESS TRAP: `FnMut` is non-deterministic across calls (mutable
// captures), so `f(3) == f(3)` must NOT be provable via a congruent UF. `FnMut`
// is NOT typed as `SpecFn`, so the application fails closed at extraction
// ("function value"). MUST NOT VERIFY.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn fnmut_determinism_must_not_verify<F: FnMut(u64) -> u64>(mut f: F) {
    let a = f(3u64);
    let b = f(3u64);
    trust_vc::assert!(a == b);
}

// ---------------------------------------------------------------------------
// FnOnce companion: also non-deterministic / consumed; NOT typed as `SpecFn`.
// MUST NOT VERIFY (fails closed).
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn fnonce_reflexive_must_not_verify<F: FnOnce(u64) -> u64>(f: F) {
    let observed = f(3u64);
    trust_vc::assert!(observed == observed);
}
