// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! End-to-end coverage for the CONCRETE recursive-datatype REFUTATION recovery —
//! the completeness DUAL of the compute-mode `Some(true)` upgrade. A WRONG
//! closed/ground claim over a recursive datatype (e.g. `depth(Succ(Zero)) == 2`,
//! true value `1`) or a non-recursive selector (`is_zero(Zero) == false`)
//! previously bailed to `Unknown(Incompleteness, "quantifier-unhandled")`: ay's
//! native datatype theory case-splits constructors only at solver scope-depth 0,
//! but every obligation is discharged inside a `push` scope, so the
//! datatype-sorted defining-axiom `forall` is left in scope with no model. The
//! concrete evaluator (`try_compute_with_bindings`) unfolds the SAME defining body
//! the SMT axiom encodes; when it reduces a closed ground goal to `false` the
//! engine now synthesizes a `Counterexample` (mirroring the `Some(true)` →
//! `Verified` upgrade), GATED to a bare closed/ground goal with no constraining
//! hypotheses.
//!
//! This is FIRST a soundness battery (the critical risk is a FALSE counterexample
//! on a TRUE claim):
//!   * WRONG concrete recursive / selector claims      -> Counterexample;
//!   * TRUE concrete claims                             -> still Verified;
//!   * claims under a constraining / vacuous hypothesis -> NOT falsely cex'd (gated);
//!   * SUPPRESSED / ill-founded recursive fns           -> Unknown (no fabricated cex);
//!   * SYMBOLIC-parameter claims (assert AND postcond)  -> Unknown (no fabricated cex);
//!   * never a false `Verified` anywhere.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn path() -> String {
    format!(
        "{}/tests/data/recursive_datatype_refutation.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn ok(func: &str) -> VerifyResult {
    verify_function_from_file(&path(), func)
        .unwrap_or_else(|e| panic!("extract/verify {func} failed: {e:?}"))
}

// ─────────── WRONG concrete recursive claim -> Counterexample ────────────────

/// A wrong closed/ground recursive-datatype claim is now a definite
/// Counterexample, not `Unknown`. Covers a base-depth value, a value that
/// requires the unfolding axiom to fire twice, and a payload-carrying list.
#[test]
fn wrong_recursive_claims_are_counterexamples() {
    for func in [
        "wrong_depth_one", // depth(Succ(Zero)) == 2   (true value 1)
        "wrong_depth_two", // depth(Succ(Succ(Zero))) == 5 (true value 2)
        "wrong_len_one",   // len(Cons(7, Nil)) == 0   (true value 1)
    ] {
        assert!(
            matches!(ok(func), VerifyResult::Counterexample { .. }),
            "wrong recursive-datatype claim {func} must be a Counterexample, got {:?}",
            ok(func)
        );
    }
}

/// The non-recursive-selector dual: `is_zero(Zero) == false` (true value `true`)
/// is also refuted to a Counterexample.
#[test]
fn wrong_selector_claim_is_counterexample() {
    assert!(
        matches!(ok("wrong_is_zero"), VerifyResult::Counterexample { .. }),
        "is_zero(Zero) == false must be a Counterexample, got {:?}",
        ok("wrong_is_zero")
    );
}

// ──────────────── TRUE concrete claim -> still Verified ──────────────────────

/// The critical no-false-counterexample direction: a TRUE closed/ground claim
/// must still Verify (the refutation recovery must NEVER fire on a true goal).
#[test]
fn true_concrete_claims_still_verify() {
    for func in [
        "true_depth_one", // depth(Succ(Zero)) == 1
        "true_len_one",   // len(Cons(7, Nil)) == 1
        "true_is_zero",   // is_zero(Zero) == true
    ] {
        assert!(
            matches!(ok(func), VerifyResult::Verified),
            "TRUE concrete claim {func} must still Verify (no false counterexample), got {:?}",
            ok(func)
        );
    }
}

// ────── UNDER-HYPOTHESES: must NOT be falsely Counterexampled (gated) ─────────

/// SOUNDNESS: a goal under a CONTRADICTORY (cyclic) hypothesis is vacuously true.
/// A naive ground compute of the goal would say `false`; the engine must NOT
/// manufacture a counterexample (it is caught as vacuous / non-`Incompleteness`,
/// and the closed-ground gate would block it regardless). Never a Counterexample,
/// never a (real) Verified.
#[test]
fn vacuous_cyclic_hypothesis_is_not_counterexampled() {
    let result = ok("cex_blocked_under_cyclic_hyp");
    assert!(
        !matches!(result, VerifyResult::Counterexample { .. }),
        "UNSOUND: vacuously-true goal under a contradictory cyclic hypothesis must \
         NOT be a fabricated Counterexample, got {result:?}"
    );
    assert!(
        !matches!(result, VerifyResult::Verified),
        "a contradictory-hypothesis goal must not be a real Verified, got {result:?}"
    );
}

/// SOUNDNESS / gate predicate: whenever ANY hypothesis is in scope the
/// closed-ground gate withholds the refutation shortcut, even though the ground
/// goal here is genuinely false. The recovery path runs (Incompleteness +
/// compute `Some(false)`) but the gate blocks it — the claim stays `Unknown`,
/// never a Counterexample. This pins the bare-assert gate.
#[test]
fn constraining_hypothesis_blocks_the_shortcut() {
    let result = ok("cex_blocked_under_benign_hyp");
    assert!(
        !matches!(result, VerifyResult::Counterexample { .. }),
        "the closed-ground gate must withhold the cex shortcut under any hypothesis, \
         got {result:?}"
    );
    assert!(
        !matches!(result, VerifyResult::Verified),
        "a genuinely-false goal must never be a false Verified, got {result:?}"
    );
}

/// A TRUE claim under an equality hypothesis routes through the `Some(true)`
/// upgrade (binding `n -> Zero`, `depth(Zero) == 0`) and stays Verified — it must
/// never be a counterexample.
#[test]
fn true_claim_under_binding_hypothesis_verifies() {
    let result = ok("true_under_binding_hyp");
    assert!(
        matches!(result, VerifyResult::Verified),
        "TRUE claim under an equality hypothesis must Verify, got {result:?}"
    );
}

// ── SUPPRESSED / ill-founded recursive fn -> Unknown (no fabricated cex) ──────

/// A recursive spec fn WITHOUT `#[decreases]` has its defining axiom suppressed
/// and is therefore absent from the compute body catalog: the evaluator returns
/// `None`, so NO counterexample (and NO Verified) is fabricated — for either a
/// TRUE or a FALSE claim through it. This is the #50 soundness invariant viewed
/// from the refutation side.
#[test]
fn suppressed_recursion_stays_unknown() {
    for func in [
        "suppressed_bad_depth_true", // bad_depth(Succ(Zero)) == 1  (true, but suppressed)
        "suppressed_bad_depth_wrong", // bad_depth(Succ(Zero)) == 9  (false, but suppressed)
    ] {
        let result = ok(func);
        assert!(
            !matches!(
                result,
                VerifyResult::Verified | VerifyResult::Counterexample { .. }
            ),
            "suppressed/ill-founded recursive fn {func} must stay Unknown (uninterpreted \
             helper, no fabricated cex/Verified), got {result:?}"
        );
    }
}

// ──────── SYMBOLIC parameter -> Unknown (no fabricated cex) ───────────────────

/// A claim over a SYMBOLIC datatype parameter cannot be ground-evaluated
/// (`eval_match` returns `None` on a symbolic scrutinee), so the refutation
/// recovery never fires — both a bare assert and a postcondition stay Unknown,
/// never a fabricated Counterexample.
#[test]
fn symbolic_parameter_stays_unknown() {
    for func in [
        "symbolic_param_assert",   // assert!(depth(n) == 99), n symbolic
        "symbolic_param_postcond", // ensures(depth(n) == 99), n symbolic
    ] {
        let result = ok(func);
        assert!(
            !matches!(
                result,
                VerifyResult::Verified | VerifyResult::Counterexample { .. }
            ),
            "symbolic-parameter claim {func} must stay Unknown (no fabricated cex/Verified), \
             got {result:?}"
        );
    }
}
