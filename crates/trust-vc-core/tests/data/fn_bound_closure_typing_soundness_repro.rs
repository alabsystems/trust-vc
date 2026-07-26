// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Fixtures for the INCREMENT 1 (Fn-bound closure typing foundation) adversarial
// soundness suite (`fn_bound_closure_typing_soundness.rs`). Verified via
// verify_function_from_file, cache-OFF.
//
// An `F: Fn(A..) -> B`-bounded value parameter `f: F` is typed as a first-class
// `SpecFn(A.., B)` value, so a call `f(x)` lowers to the opaque, congruent
// `spec_fn_apply` UF. `Fn` captures immutably and is therefore DETERMINISTIC
// across calls, so:
//   * reflexivity `f(3) == f(3)` and determinism (same args) VERIFY (congruent
//     UF), and
//   * the result is otherwise UNCONSTRAINED — `f(3) == 3` and `f(3) == f(4)`
//     are NOT provable and COUNTEREXAMPLE (the traps below).
// `FnMut`/`FnOnce` are non-deterministic across calls; they are NOT typed as a
// congruent `SpecFn` and stay fail-closed (the call fails to lower). No obligation
// (`call_requires%`/`call_ensures%`) is emitted for a def-side-less parameter, so
// nothing is assumed about the result.

// ---------------------------------------------------------------------------
// TARGET (Fn): reflexivity of a call through the bound. MUST VERIFY.
// The load-bearing witness that the `SpecFn` typing took effect: without it the
// call fails closed ("Undefined function: f").
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn fnbound_reflexive_verified<F: Fn(u64) -> u64>(f: F) {
    let observed = f(3u64);
    trust_vc::assert!(observed == observed);
}

// ---------------------------------------------------------------------------
// DETERMINISM (Fn, non-tautological, SOUND): same arguments give the same result
// via the congruent UF. MUST VERIFY. This is the real capability the typing
// unlocks (NOT reflexivity of a single term).
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn fnbound_determinism_verified<F: Fn(u64) -> u64>(f: F) {
    let a = f(3u64);
    let b = f(3u64);
    trust_vc::assert!(a == b);
}

// The determinism property also holds under the where-clause spelling of the
// bound (exercises the where-predicate recognition path). MUST VERIFY.
#[trust_vc::ensures(true)]
fn fnbound_determinism_where_clause_verified<F>(f: F)
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
#[trust_vc::ensures(true)]
fn fnbound_pins_concrete_result_cx<F: Fn(u64) -> u64>(f: F) {
    let observed = f(3u64);
    trust_vc::assert!(observed == 3u64);
}

// ---------------------------------------------------------------------------
// FALSE-VERIFY TRAP #2: DIFFERENT arguments — congruence gives nothing. MUST
// COUNTEREXAMPLE.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn fnbound_distinct_args_cx<F: Fn(u64) -> u64>(f: F) {
    let a = f(3u64);
    let b = f(4u64);
    trust_vc::assert!(a == b);
}

// ---------------------------------------------------------------------------
// FnMut UNSOUNDNESS TRAP: `FnMut` is non-deterministic across calls (mutable
// captures), so `f(3) == f(3)` must NOT be provable via a congruent UF. `FnMut`
// is NOT typed as `SpecFn`, so the call fails closed. MUST NOT VERIFY.
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
