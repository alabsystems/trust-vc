// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Drives trust-vc over the ay-pb cutting-planes OPTIMUM WHOLE-LOOP soundness
// fixture — the SCORE-CRITICAL dual of the refutation whole-loop lift. The
// floor-derivation REPLAY loop's invariant "every accumulated/derived constraint
// is entailed by the original input DB" is PRESERVED by each iteration (per rule,
// rule-agnostically, and across an arbitrary-length engine-verified `while` loop,
// including a strictly-richer TWO-CLAUSE conjunctive invariant), and the terminal
// `derived == target` (the objective form at degree F) makes F a VALID LOWER
// BOUND on the objective — so a feasible incumbent at F is OPTIMAL (LB == UB).
// Each soundness contract PROVES; each deliberately-unsound control is REFUTED or
// does not verify. See the fixture header for the entailment model, the
// per-step/whole-loop scope, and the preconditions-over-unmodified-vars toolchain
// capability it rides on.
//
// `tests/fixtures/ay_optimum_loop_realbody.rs` is a verbatim copy of
// `crates/ay-pb/proofs/trust_vc/optimum_loop_realbody.rs` in the `ay` repo.
// Override with `AY_PB_OPTIMUM_LOOP_PROOF_SRC` to verify directly against an
// `ay` checkout.

use trust_vc_core::verify_function_from_file;
use trust_vc_core::VerifyResult;

fn proof_source() -> String {
    std::env::var("AY_PB_OPTIMUM_LOOP_PROOF_SRC").unwrap_or_else(|_| {
        format!(
            "{}/tests/fixtures/ay_optimum_loop_realbody.rs",
            env!("CARGO_MANIFEST_DIR")
        )
    })
}

fn verify(name: &str) -> VerifyResult {
    verify_function_from_file(&proof_source(), name)
        .unwrap_or_else(|e| panic!("{name} should extract+verify, got error: {e}"))
}

fn assert_verified(name: &str) {
    let v = verify(name);
    assert!(
        matches!(v, VerifyResult::Verified),
        "{name} must PROVE its soundness contract; got {v:?}"
    );
}

fn assert_counterexample(name: &str) {
    let v = verify(name);
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "{name} (unsound control) MUST be refuted with a counterexample; got {v:?}"
    );
}

fn assert_not_verified(name: &str) {
    let v = verify(name);
    assert!(
        !matches!(v, VerifyResult::Verified),
        "{name} (unsound control) MUST NOT verify; got {v:?}"
    );
}

/// Unknown-as-failure relaxation (docs/design-unknown-as-failure.md): a genuine
/// verification FAILURE — a model-bearing `Counterexample` OR a model-less
/// `NotProved` (an incompleteness fail-close under the ay bump's wrong-SAT
/// closures). For unsound controls whose refutation must be a decisive failure
/// (never a soft `Unknown`), without demanding a fabricated model.
fn assert_fails(name: &str) {
    let v = verify(name);
    assert!(
        v.is_failure(),
        "{name} (unsound control) MUST be refuted — Counterexample or NotProved; got {v:?}"
    );
}

// ── (i) INVARIANT PRESERVATION — per rule ─────────────────────────────────────
#[test]
fn invariant_preserved_add_verified() {
    assert_verified("invariant_preserved_add");
}
#[test]
fn invariant_preserved_add_overclaim_refuted() {
    assert_counterexample("invariant_preserved_add_overclaim");
}
#[test]
fn invariant_preserved_scale_verified() {
    assert_verified("invariant_preserved_scale");
}
#[test]
fn invariant_preserved_scale_no_lemma_verified() {
    // Re-keyed to verified (docs/execution-plan §7 2026-07-19): the monotonicity
    // fact `k>=1 & a>=b ⟹ k*a>=k*b` is TRUE, and ay's improved NIA (pin 5665ac65)
    // derives it unaided — the explicit lemma is no longer load-bearing. The stale
    // "no-lemma-not-verified" control was a completeness gap, not a soundness hole
    // (mutation-verified sound: sign-drop mutants refute).
    assert_verified("invariant_preserved_scale_no_lemma");
}
#[test]
fn invariant_preserved_divide2_verified() {
    assert_verified("invariant_preserved_divide2");
}
#[test]
fn invariant_preserved_divide2_drop_domination_refuted() {
    assert_counterexample("invariant_preserved_divide2_drop_domination");
}

// ── (i') INVARIANT PRESERVATION — rule-agnostic crux ──────────────────────────
#[test]
fn invariant_preserved_general_verified() {
    assert_verified("invariant_preserved_general");
}
#[test]
fn invariant_preserved_general_drop_rule_refuted() {
    assert_counterexample("invariant_preserved_general_drop_rule");
}

// ── (ii) THE WHOLE FLOOR-DERIVATION LOOP — engine-verified inductive proof ─────
#[test]
fn accumulate_floor_entailed_verified() {
    // The entailment invariant `acc_eval >= floor` is maintained across an
    // arbitrary (symbolic n) number of ADD iterations by trust-vc's frame-
    // condition inductive step (carrying the step-entailment precondition over
    // the unmodified params — the capability built for the refutation lift).
    assert_verified("accumulate_floor_entailed");
}
#[test]
fn accumulate_floor_overstrong_not_verified() {
    // OVER-STRONG FLOOR: dropping the step-entailment precondition lets a cut
    // overcount the floor, breaking preservation — refuted at the inductive step.
    assert_not_verified("accumulate_floor_overstrong");
}
#[test]
fn accumulate_floor_monotone_verified() {
    // Strictly richer than the refutation loop: a TWO-CLAUSE conjunctive
    // invariant (entailment AND floor-strengthening) carried over an unmodified
    // `start_floor`.
    assert_verified("accumulate_floor_monotone");
}
#[test]
fn accumulate_floor_monotone_unsound_not_verified() {
    // Dropping the non-negative-contribution premise lets a step lower the floor
    // below `start_floor`, breaking the monotonicity clause.
    assert_not_verified("accumulate_floor_monotone_unsound");
}

// ── (ii-LIT) THE LITERAL Vec-PUSH FLOOR-DERIVATION LOOP — engine-verified over ──
// the actual heap mutation (dual of the refutation literal-push section), enabled
// by the new collection-push single-iteration transition capture.
#[test]
fn floor_push_db_grows_exact_verified() {
    assert_verified("floor_push_db_grows_exact");
}
#[test]
fn floor_push_db_grows_exact_overclaim_refuted() {
    assert_counterexample("floor_push_db_grows_exact_overclaim");
}
#[test]
fn floor_push_appends_entailed_verified() {
    // `db.index(db.len() - 1) == step` is a SAME-INDEX read-back of the
    // just-pushed cell — store and select alias the identical carrier cell, so
    // read-over-write discharges it independent of int2bv carrier
    // representability (same-index read-back recognizer,
    // `try_encode_push_same_index_readback`).
    assert_verified("floor_push_appends_entailed");
}
#[test]
fn floor_push_appends_entailed_unsound_not_verified() {
    assert_not_verified("floor_push_appends_entailed_unsound");
}

// ── (ii-FQ) FULLY-QUANTIFIED per-element entailment invariant ──────────────────
// The disclosed residual — `forall i. i < db.len() ==> entailed(db[i])` maintained
// across the floor-derivation push — now DISCHARGED via the ay-dpll forall-goal
// boundary fix, routed through the now-fixed Int-domain indexed-family carrier.
#[test]
fn fq_floor_invariant_preserved_append_verified() {
    assert_verified("fq_floor_invariant_preserved_append");
}
#[test]
fn fq_floor_invariant_preserved_append_unsound_refuted() {
    // Dropping the appended-cut entailment lets a non-entailed cut (negative slack,
    // which would falsely strengthen the floor) enter db; refuted with a concrete
    // counterexample (the per-step entailment is load-bearing — non-vacuous).
    assert_counterexample("fq_floor_invariant_preserved_append_unsound");
}
#[test]
fn fq_floor_invariant_implies_last_entailed_verified() {
    assert_verified("fq_floor_invariant_implies_last_entailed");
}
#[test]
fn fq_floor_invariant_implies_last_entailed_wrong_refuted() {
    // Unknown-as-failure (docs/design-unknown-as-failure.md): the out-of-range
    // instantiation refutation now fail-closes to a model-less NotProved.
    assert_fails("fq_floor_invariant_implies_last_entailed_wrong");
}

// ── (ii-FQ-LIT) FULLY-QUANTIFIED floor invariant over the LITERAL `Vec` carrier ─
// residual #2 CLOSED (dual of the refutation literal-carrier FQ): the SAME
// per-element universal as (ii-FQ), now with the quantifier body the literal
// `db.index(i)` (== `select db (int2bv_64 i)` over the real `db: Vec<i128>` floor
// DB), NOT the opaque `floor_slack_at`. Discharged via the landed ay-dpll fixes
// (forall-goal ground-strict-bound normalization folding `db.len() == old_len + 1`
// into the boundary bound — residual #2(a) — plus int2bv boundary injectivity).
#[test]
// Re-activated by the Vec/Seq length-boundedness lane: `db: Vec<i128>` now
// carries `len <= 2^64-1` (VariableDecl::bounded_len), which discharges the
// precondition/postcondition-side carrier-representability obligation that
// previously fired outside the quantifier and left this NotProved/Error.
fn fq_lit_floor_invariant_preserved_append_verified() {
    // PRESERVATION of the literal-Vec per-element floor invariant across one push,
    // over the REAL array read `select db (int2bv i)` — closing residual #2.
    assert_verified("fq_lit_floor_invariant_preserved_append");
}
#[test]
fn fq_lit_floor_invariant_preserved_append_unsound_not_verified() {
    // Dropping the appended-cut entailment lets a non-entailed cut enter the real db
    // at the boundary; the grown literal-carrier forall is then false, so it MUST
    // NOT verify. Over the int2bv array carrier ay returns Unknown (non-`Verified`),
    // a non-vacuous discharge.
    assert_not_verified("fq_lit_floor_invariant_preserved_append_unsound");
}
#[test]
// Re-activated by the Vec/Seq length-boundedness lane: `db: Vec<i128>` now
// carries `len <= 2^64-1` (VariableDecl::bounded_len), discharging the
// length-derived carrier-representability obligation. See the sibling
// `..._preserved_append_verified` note.
fn fq_lit_floor_invariant_implies_last_entailed_verified() {
    // Universal-elimination over the literal carrier: the whole-db invariant yields
    // the LAST derived cut (db.index(db.len()-1)) entailed.
    assert_verified("fq_lit_floor_invariant_implies_last_entailed");
}
#[test]
fn fq_lit_floor_invariant_implies_last_entailed_wrong_not_verified() {
    // Out-of-range instantiation (index db.len()) is not covered by the [0,db.len())
    // invariant AND the literal read is out of bounds; MUST NOT verify.
    assert_not_verified("fq_lit_floor_invariant_implies_last_entailed_wrong");
}

// ── TERMINAL — derived==target ⟹ valid floor ⟹ LB==UB (OPTIMUM) ───────────────
#[test]
fn optimum_terminal_lb_eq_ub_verified() {
    assert_verified("optimum_terminal_lb_eq_ub");
}
#[test]
fn optimum_terminal_wrong_form_refuted() {
    assert_counterexample("optimum_terminal_wrong_form");
}
#[test]
fn optimum_terminal_overcount_refuted() {
    assert_counterexample("optimum_terminal_overcount");
}
#[test]
fn optimum_terminal_drop_tightness_refuted() {
    assert_counterexample("optimum_terminal_drop_tightness");
}

// ── (iii) BOUNDED-N END-TO-END — Lean division OPTIMUM example ─────────────────
#[test]
fn division_example_derive_floor_verified() {
    assert_verified("division_example_derive_floor");
}
#[test]
fn division_example_derive_floor_overclaim_refuted() {
    assert_counterexample("division_example_derive_floor_overclaim");
}
#[test]
fn division_example_optimum_verified() {
    assert_verified("division_example_optimum");
}
#[test]
fn division_example_optimum_drop_input_refuted() {
    assert_counterexample("division_example_optimum_drop_input");
}
