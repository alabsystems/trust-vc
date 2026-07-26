// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `hide!` battery (Verus `hide(f)` parity) + the full upstream basic.rs
//! `test_spec_fn` shape on the session (proc-macro) path.
//!
//! Semantics under test: `hide!(f)` makes a NON-opaque spec function's
//! defining body axiom unavailable for the current proof — the function
//! becomes strictly uninterpreted, exactly like an unrevealed
//! `#[trust_vc::opaque]` fn — and a `reveal!(f)` in the same proof wins over
//! the hide (the net effect of upstream Verus's flow-ordered
//! `hide(f); …; reveal(f)` sequence under trust-vc's query-granular model).
//!
//! SOUNDNESS PINS:
//!  * a hidden fn's body must not prove OR refute a goal (both cardinal
//!    directions), including via the demand-inline retry catalog and the
//!    concrete-compute evaluator;
//!  * `hide!` in one proof must not leak into another proof;
//!  * `hide!(typo)` fails closed (same guard class as `reveal!(typo)`,
//!    #2473).

mod common;

use trust_vc::{proof, spec};
use trust_vc_types::int;

// === Fixture spec fns ===

// Non-opaque: visible by default, the `hide!` target.
#[spec]
fn h_double(x: u64) -> u64 {
    x + x
}

// Upstream test_spec_fn trio (basic.rs:84-116).
#[spec]
fn tf1(i: int, j: int) -> bool {
    i <= j
}

// Upstream f2 has a let-bound body; the session-path spec expansion lowers a
// direct comparison body — the let-body variant is covered by the file-path
// battery (trust-vc-core/tests/opaque_reveal_definitional_ce.rs).
#[spec]
fn tf2(i: int, j: int) -> bool {
    i < j
}

// opaque must appear AFTER spec so spec expansion can detect it.
#[spec]
#[trust_vc::opaque]
fn tf3(i: int, j: int) -> bool {
    tf1(j, i)
}

// === (c) hide pins: hidden body must not prove ===

#[proof]
fn proof_hidden_fn_body_unavailable() {
    let _ = h_double(0u64);
    trust_vc::hide!(h_double);
    // Provable ONLY from the body (h_double(3) == 6): must NOT verify while
    // hidden. Also pins that the demand-inline retry does not inline a hidden
    // body and the compute evaluator does not unfold it.
    trust_vc::assert!(h_double(3u64) == 6u64);
}

/// Hidden fn: an assert provable only via the body must FAIL.
#[test]
fn test_hidden_fn_body_unavailable() {
    let _ = common::verify_should_fail(proof_hidden_fn_body_unavailable);
}

#[proof]
fn proof_visible_fn_control() {
    let _ = h_double(0u64);
    trust_vc::assert!(h_double(3u64) == 6u64);
}

/// Control: WITHOUT hide! the same assert verifies — proves the hide pin
/// above fails because of the hide, not for an unrelated reason.
#[test]
fn test_visible_fn_control_verifies() {
    let _ = common::verify_should_pass(proof_visible_fn_control);
}

// === hide-then-reveal: reveal wins (upstream hide(f2)+reveal(f2) net) ===

#[proof]
fn proof_hide_then_reveal_verifies() {
    let _ = h_double(0u64);
    trust_vc::hide!(h_double);
    trust_vc::reveal!(h_double);
    trust_vc::assert!(h_double(3u64) == 6u64);
}

/// hide! followed by reveal! in the same proof nets to revealed.
#[test]
fn test_hide_then_reveal_verifies() {
    let _ = common::verify_should_pass(proof_hide_then_reveal_verifies);
}

// === (d) hide scoping: hide! in one proof does not leak to another ===

#[proof]
fn proof_scope_a_hides() {
    let _ = h_double(0u64);
    trust_vc::hide!(h_double);
    // Trivial goal so this proof verifies while carrying the hide.
    trust_vc::assert!(true);
}

#[proof]
fn proof_scope_b_still_visible() {
    let _ = h_double(0u64);
    trust_vc::assert!(h_double(3u64) == 6u64);
}

/// hide! is proof-local: a hide in proof A must not affect proof B.
#[test]
fn test_hide_does_not_leak_across_proofs() {
    let _ = common::verify_should_pass(proof_scope_a_hides);
    let _ = common::verify_should_pass(proof_scope_b_still_visible);
}

// === hide!(typo) fails closed (mirror of the reveal! typo guard, #2473) ===

#[proof]
fn proof_hide_unknown_function() {
    let _ = h_double(0u64);
    trust_vc::hide!(no_such_function_anywhere);
    trust_vc::assert!(true);
}

/// hide! of an unknown function must fail (not silently no-op).
#[test]
fn test_hide_unknown_function_fails_closed() {
    let result = common::verify_should_fail(proof_hide_unknown_function);
    let text = format!("{result:?}");
    assert!(
        text.contains("hide!(no_such_function_anywhere)"),
        "hide! typo must fail through the prepare-context guard, got: {text}"
    );
}

// === (a) FULL upstream test_spec_fn shape (WITH hide!) ===
//
// upstream basic.rs:100-114: hide(f2); assume(f2(a,b)); proof { reveal(f2); }
// assert(f1(a,b)); proof { reveal(f3); } assert(f3(b,a)); assert(f3(a,b))
// => assert_one_fails: exactly the last assert fails.
//
// The session path binds concrete witnesses (a=1, b=2) satisfying the
// upstream assumption a < b, keeping all three asserts' upstream verdicts:
// f1(1,2) true; f3(2,1) = f1(1,2) true; f3(1,2) = f1(2,1) = 2<=1 FALSE.

#[proof]
fn proof_test_spec_fn_verified_prefix() {
    let a: int = 1;
    let b: int = 2;
    // Warm-up calls register each spec fn's typed signature with the session
    // (the established pattern — assert!/reveal! capture expressions without
    // executing them, so an uncalled spec fn would be unknown to the guard).
    let _ = tf1(a, b);
    let _ = tf2(a, b);
    let _ = tf3(a, b);
    trust_vc::hide!(tf2);
    trust_vc::assume!(tf2(a, b));
    trust_vc::reveal!(tf2);
    trust_vc::assert!(tf1(a, b));
    trust_vc::reveal!(tf3);
    trust_vc::assert!(tf3(b, a));
}

/// The verified prefix of the upstream sequence (through assert(f3(b,a)))
/// verifies with the hide!/reveal! directives in place.
#[test]
fn test_spec_fn_verified_prefix_passes() {
    let _ = common::verify_should_pass(proof_test_spec_fn_verified_prefix);
}

#[proof]
fn proof_test_spec_fn_full() {
    let a: int = 1;
    let b: int = 2;
    let _ = tf1(a, b);
    let _ = tf2(a, b);
    let _ = tf3(a, b);
    trust_vc::hide!(tf2);
    trust_vc::assume!(tf2(a, b));
    trust_vc::reveal!(tf2);
    trust_vc::assert!(tf1(a, b));
    trust_vc::reveal!(tf3);
    trust_vc::assert!(tf3(b, a));
    trust_vc::assert!(tf3(a, b)); // FAILS upstream (assert_one_fails)
}

/// The full upstream sequence fails on exactly the final assert, with a
/// genuine model-bearing assertion-failure verdict (upstream
/// assert_one_fails) — not a guard error and not a model-less Unknown.
#[test]
fn test_spec_fn_full_shape_fails() {
    let result = common::verify_should_fail(proof_test_spec_fn_full);
    let text = format!("{result:?}");
    assert!(
        !text.contains("references unknown function") && !text.contains("hide!("),
        "failure must be a verification verdict, not a guard error: {text}"
    );
    assert!(
        matches!(result, trust_vc_core::VerifyResult::Counterexample { .. }),
        "the final assert must fail with the genuine assertion-failure class \
         (upstream assert_one_fails), got: {text}"
    );
}

// === SOUNDNESS PIN (#2785): hide!/reveal! interleave must fail closed ===
//
// `hide!(f); assert!(<provable ONLY via f's body>); reveal!(f)`: Verus has f
// re-opaqued at the assert (the reveal is BELOW it) and REFUTES it. trust-vc's
// query-granular reveal-wins model would otherwise expose f's body at the
// bracketed assert and VERIFY it — proving MORE than Verus (a false-verify, the
// cardinal soundness violation). `reject_unsound_hide_reveal_interleave`
// (prepare()) fails the query closed. This must NEVER be Verified. Regression
// witness: before the guard + the positioned Hide obligation, this returned
// Verified.
#[proof]
fn proof_hide_reveal_interleave_bracketed_assert() {
    let _ = h_double(0u64);
    trust_vc::hide!(h_double);
    trust_vc::assert!(h_double(3u64) == 6u64); // provable ONLY via body; bracketed
    trust_vc::reveal!(h_double);
}

/// The bracketed-assert interleave must fail closed — never Verified.
#[test]
fn test_hide_reveal_interleave_fails_closed() {
    let result = common::verify_and_get_result(proof_hide_reveal_interleave_bracketed_assert);
    assert!(
        !matches!(result, trust_vc_core::VerifyResult::Verified),
        "hide!(f) … reveal!(f) bracketing a body-provable assert VERIFIED \
         (proves more than Verus — cardinal soundness violation), got {result:?}"
    );
}

// === (c) hidden fn must not refute from its body either ===

#[proof]
fn proof_hidden_fn_no_refutation_leak() {
    let _ = h_double(0u64);
    trust_vc::hide!(h_double);
    // FALSE only via the body (h_double(3) == 6 != 7): while hidden the
    // function is uninterpreted, so this must not VERIFY (h_double(3) could
    // be 7) — and it must also fail (the solver cannot prove it).
    trust_vc::assert!(h_double(3u64) == 7u64);
}

/// Hidden fn: a body-refutable assert must not verify (it fails, but only
/// because the claim is unprovable over an uninterpreted symbol — never
/// because the hidden body was consulted).
#[test]
fn test_hidden_fn_no_refutation_leak() {
    let _ = common::verify_should_fail(proof_hidden_fn_no_refutation_leak);
}
