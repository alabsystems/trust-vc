//! Arithmetic lemma specifications for integer types.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

// Mathematical-integer alias used by the opaque `vstd::arithmetic` spec
// surface below. The verifier maps the bare `int` spelling to its `MathInt`
// sort; a fully-qualified path (`trust_vc_types::int`) is NOT recognized.
use trust_vc_types::int;

// ---------------------------------------------------------------------------
// 4 required lemmas from issue #2741
// ---------------------------------------------------------------------------

/// Lemma: Euclidean division fundamental identity.
///
/// Property:
/// if `b != 0`, then `a == (a / b) * b + a % b`.
#[trust_vc::proof]
pub fn div_mod_fundamental(a: i64, b: i64) {
    trust_vc::requires!(b != 0);
    trust_vc::ensures!(a == (a / b) * b + a % b);
}

/// Lemma: multiplication is commutative for `i64`.
///
/// Property:
/// `a * b == b * a`.
#[trust_vc::proof]
#[allow(clippy::eq_op)]
pub fn mul_comm(a: i64, b: i64) {
    trust_vc::ensures!(a * b == b * a);
}

/// Lemma: multiplication distributes over addition for `i64`.
///
/// Property:
/// `a * (b + c) == a * b + a * c`.
#[trust_vc::proof]
pub fn mul_distrib_left(a: i64, b: i64, c: i64) {
    trust_vc::ensures!(a * (b + c) == a * b + a * c);
}

/// Lemma: powers of 2 are always positive.
///
/// Property:
/// if `0 <= n < 63`, then `1_i64 << n > 0`.
#[trust_vc::proof]
pub fn pow2_positive(n: u32) {
    trust_vc::requires!(n < 63);
    trust_vc::ensures!((1_i64 << n) > 0);
}

// ---------------------------------------------------------------------------
// Opaque mathematical-integer arithmetic spec functions (vstd::arithmetic).
//
// These mirror Verus's `vstd::arithmetic::{mul, add, sub}` wrappers: thin spec
// functions over mathematical integers (`int`, no overflow) that name the
// primitive arithmetic operators. They are deliberately **opaque** — the
// defining body axiom (`mul(x, y) == x * y`, etc.) is hidden from the solver
// until a proof explicitly reveals it (`reveal!(mul)` / a named reveal group),
// exactly as Verus requires `by(nonlinear_arith)` / a reveal before any
// reasoning about a wrapped nonlinear product is admitted.
//
// SOUNDNESS: an opaque spec function is an *uninterpreted* function symbol of
// the right arity/sort until revealed, so no goal mentioning it can be
// discharged from its (hidden) definition. This is strictly weaker than the
// transparent encoding — it can never prove a goal the transparent body could
// not — and it specifically avoids handing the solver a free nonlinear identity
// (`mul(x, y) == x * y`) in the default arithmetic mode, where ay's incomplete
// nonlinear reasoning could otherwise be coaxed into an unsound discharge. The
// body axiom itself is correct by definition, so revealing it (e.g. under
// `by(nonlinear_arith)`) is sound; the opacity is what keeps it Verus-faithful.
//
// NOTE: cross-crate use of these from a verified downstream file (i.e.
// `use trust_vc_std::arithmetic::mul;`) additionally requires the source spec
// catalog to resolve imported spec functions, which is not yet wired (see the
// frontend keystone in the internal Verus-replacement plan). The opacity semantics
// themselves are exercised in-crate by the `opaque_arith` test module below.
// ---------------------------------------------------------------------------

/// Opaque multiplication over mathematical integers (Verus `vstd::arithmetic::mul`).
///
/// Defining axiom (revealed only on demand): `mul(x, y) == x * y`.
#[trust_vc::spec]
#[trust_vc::opaque]
pub fn mul(x: int, y: int) -> int {
    x * y
}

/// Opaque addition over mathematical integers (Verus `vstd::arithmetic::add`).
///
/// Defining axiom (revealed only on demand): `add(x, y) == x + y`.
#[trust_vc::spec]
#[trust_vc::opaque]
pub fn add(x: int, y: int) -> int {
    x + y
}

/// Opaque subtraction over mathematical integers (Verus `vstd::arithmetic::sub`).
///
/// Defining axiom (revealed only on demand): `sub(x, y) == x - y`.
#[trust_vc::spec]
#[trust_vc::opaque]
pub fn sub(x: int, y: int) -> int {
    x - y
}

#[cfg(test)]
mod opaque_arith {
    //! End-to-end opacity tests for the surface `mul` / `add` / `sub` defined
    //! above. Because these are real `#[trust_vc::spec]` items in this crate,
    //! compiling under `cfg(test)` activates their proof-mode body so the
    //! `#[trust_vc::proof]` functions here drive the genuine encoder + ay
    //! pipeline (not a re-declared copy).

    use super::{add, mul, sub};

    /// Runs a `#[trust_vc::proof]` function with clean thread-local verification
    /// state, returning `Err(panic message)` when the proof is rejected (the
    /// `#[proof]` auto-verify boundary panics on a non-`Verified` outcome) and
    /// `Ok(())` when it verifies.
    fn run_proof<F: FnOnce() + std::panic::UnwindSafe>(proof_fn: F) -> Result<(), String> {
        clear_state();
        let outcome = std::panic::catch_unwind(proof_fn);
        clear_state();
        outcome.map_err(|payload| {
            payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|s| (*s).to_string()))
                .unwrap_or_else(|| "unknown panic".to_string())
        })
    }

    fn clear_state() {
        trust_vc_core::verify_macro::clear_all_thread_locals();
        trust_vc_core::verification_bridge::clear_registrations();
        trust_vc_core::clear_extern_contracts();
    }

    fn assert_verifies<F: FnOnce() + std::panic::UnwindSafe>(proof_fn: F) {
        if let Err(msg) = run_proof(proof_fn) {
            panic!("expected proof to verify, but it was rejected: {msg}");
        }
    }

    fn assert_rejected<F: FnOnce() + std::panic::UnwindSafe>(proof_fn: F) {
        match run_proof(proof_fn) {
            Ok(()) => panic!("expected proof to be rejected (opaque body hidden), but it verified"),
            Err(msg) => {
                // The rejection MUST be a genuine non-`Verified` verdict
                // (Counterexample / Unknown), NOT an infrastructure/context
                // error. Otherwise a malformed signature could make the proof
                // "fail" for the wrong reason and mask a real opacity break.
                let genuine = msg.contains("Proof verification failed")
                    || msg.contains("Proof verification returned Unknown");
                assert!(
                    genuine,
                    "proof was rejected, but NOT by a genuine verification verdict \
                     (possible infrastructure error): {msg}"
                );
            }
        }
    }

    // --- Opaque-by-default: hidden body cannot discharge concrete values. ---

    #[trust_vc::proof]
    fn mul_concrete_without_reveal_is_hidden() {
        let _ = mul(2, 3);
        trust_vc::assert!(mul(2, 3) == 6);
    }

    #[trust_vc::proof]
    fn add_concrete_without_reveal_is_hidden() {
        let _ = add(2, 3);
        trust_vc::assert!(add(2, 3) == 5);
    }

    #[trust_vc::proof]
    fn sub_concrete_without_reveal_is_hidden() {
        let _ = sub(5, 3);
        trust_vc::assert!(sub(5, 3) == 2);
    }

    // --- Revealed: defining body axiom evaluates concrete arguments. ---

    #[trust_vc::proof]
    fn mul_concrete_with_reveal_verifies() {
        let _ = mul(2, 3);
        trust_vc::reveal!(mul);
        trust_vc::assert!(mul(2, 3) == 6);
    }

    #[trust_vc::proof]
    fn add_concrete_with_reveal_verifies() {
        let _ = add(2, 3);
        trust_vc::reveal!(add);
        trust_vc::assert!(add(2, 3) == 5);
    }

    #[trust_vc::proof]
    fn sub_concrete_with_reveal_verifies() {
        let _ = sub(5, 3);
        trust_vc::reveal!(sub);
        trust_vc::assert!(sub(5, 3) == 2);
    }

    // --- Soundness: revealing the correct body must NOT prove a false goal. ---

    #[trust_vc::proof]
    fn mul_revealed_false_goal_is_rejected() {
        let _ = mul(2, 3);
        trust_vc::reveal!(mul);
        trust_vc::assert!(mul(2, 3) == 7);
    }

    // --- Reveal is exact: revealing `mul` leaves `add` opaque. ---

    #[trust_vc::proof]
    fn reveal_mul_does_not_reveal_add() {
        let _ = mul(2, 3);
        let _ = add(2, 3);
        trust_vc::reveal!(mul);
        trust_vc::assert!(add(2, 3) == 5);
    }

    // --- by(nonlinear_arith): revealed wrapper composes with the NIA mode. ---

    #[trust_vc::proof]
    fn mul_revealed_under_nonlinear_arith_verifies() {
        let _ = mul(3, 4);
        trust_vc::reveal!(mul);
        trust_vc::assert_by_nonlinear! { mul(3, 4) == 12 };
    }

    #[test]
    fn opaque_arithmetic_without_reveal_stays_hidden() {
        assert_rejected(mul_concrete_without_reveal_is_hidden);
        assert_rejected(add_concrete_without_reveal_is_hidden);
        assert_rejected(sub_concrete_without_reveal_is_hidden);
    }

    #[test]
    fn opaque_arithmetic_with_reveal_evaluates() {
        assert_verifies(mul_concrete_with_reveal_verifies);
        assert_verifies(add_concrete_with_reveal_verifies);
        assert_verifies(sub_concrete_with_reveal_verifies);
    }

    #[test]
    fn revealed_arithmetic_rejects_false_goal() {
        assert_rejected(mul_revealed_false_goal_is_rejected);
    }

    #[test]
    fn reveal_is_exact_per_function() {
        assert_rejected(reveal_mul_does_not_reveal_add);
    }

    #[test]
    fn revealed_arithmetic_under_nonlinear_arith() {
        assert_verifies(mul_revealed_under_nonlinear_arith_verifies);
    }
}
