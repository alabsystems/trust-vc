// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Drives trust-vc over the ay-pb cutting-planes REFUTATION WHOLE-LOOP soundness
// fixture: the loop invariant "every derived constraint is entailed by the
// original input DB" is PRESERVED by each iteration (per rule, rule-agnostically,
// and across an arbitrary-length engine-verified `while` loop), and the terminal
// `0 >= c (c>=1)` ENTAILS the inputs are UNSAT. Each soundness contract PROVES;
// each deliberately-unsound control is REFUTED or does not verify. See the fixture
// header for the entailment model, the per-step/whole-loop scope, and the
// preconditions-over-unmodified-vars toolchain capability it relies on.
//
// `tests/fixtures/ay_refutation_loop_realbody.rs` is a verbatim copy of
// `crates/ay-pb/proofs/trust_vc/refutation_loop_realbody.rs` in the `ay` repo.
// Override with `AY_PB_REFUTATION_LOOP_PROOF_SRC` to verify directly against an
// `ay` checkout.

use trust_vc_core::verify_function_from_file;
use trust_vc_core::VerifyResult;

fn proof_source() -> String {
    std::env::var("AY_PB_REFUTATION_LOOP_PROOF_SRC").unwrap_or_else(|_| {
        format!(
            "{}/tests/fixtures/ay_refutation_loop_realbody.rs",
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

// ── (ii) THE WHOLE LOOP — engine-verified inductive proof ─────────────────────
#[test]
fn replay_accumulate_entailed_verified() {
    // The entailment invariant `acc_eval >= acc_rhs` is maintained across an
    // arbitrary (symbolic n) number of ADD iterations by trust-vc's frame-
    // condition inductive step (carrying the step-entailment precondition over
    // the unmodified params — the capability built for this lift).
    assert_verified("replay_accumulate_entailed");
}
#[test]
fn replay_accumulate_unsound_not_verified() {
    // Dropping the step-entailment precondition breaks preservation: the loop
    // invariant is refuted at the inductive step (the fix is sound, not blanket).
    assert_not_verified("replay_accumulate_unsound");
}

// ── (ii-LIT) THE LITERAL Vec-PUSH LOOP — engine-verified over the actual heap ──
// These drive the frame-condition inductive step over the REAL growing `Vec` `db`
// mutated by `db.push(..)` (mirroring replay_derivation's `db.push(derived)`),
// enabled by the new collection-push single-iteration transition capture.
#[test]
fn replay_push_db_grows_exact_verified() {
    assert_verified("replay_push_db_grows_exact");
}
#[test]
fn replay_push_db_grows_exact_overclaim_refuted() {
    // Off-by-one growth claim about the literal Vec: refuted with a concrete model.
    assert_counterexample("replay_push_db_grows_exact_overclaim");
}
#[test]
fn replay_push_db_monotone_verified() {
    assert_verified("replay_push_db_monotone");
}
#[test]
fn replay_push_appends_entailed_verified() {
    // Each replay step appends an ENTAILED constraint (slack >= 0) at the new last
    // slot of the literal Vec. The `db.index(db.len() - 1) == step` obligation is a
    // SAME-INDEX read-back of the just-pushed cell: store and select alias the
    // identical carrier cell, so read-over-write discharges it independent of
    // int2bv carrier representability (same-index read-back recognizer,
    // `try_encode_push_same_index_readback`).
    assert_verified("replay_push_appends_entailed");
}
#[test]
fn replay_push_appends_entailed_unsound_not_verified() {
    // Dropping step >= 0 means a NON-entailed constraint may be pushed; the
    // appended-element entailment is then not provable.
    assert_not_verified("replay_push_appends_entailed_unsound");
}

// ── (ii-FQ) FULLY-QUANTIFIED per-element entailment invariant ──────────────────
// The disclosed residual — `forall i. i < db.len() ==> entailed(db[i])` maintained
// across the push — now DISCHARGED via the ay-dpll forall-goal boundary fix,
// routed through the now-fixed Int-domain indexed-family carrier.
#[test]
fn fq_invariant_preserved_append_verified() {
    // The fully-quantified per-element invariant is PRESERVED across one append
    // (IH over [0,old_len) + appended element entailed ==> forall over [0,old_len+1)).
    assert_verified("fq_invariant_preserved_append");
}
#[test]
fn fq_invariant_preserved_append_unsound_refuted() {
    // Dropping the appended-element entailment lets a non-entailed constraint
    // (negative slack) enter db; the grown forall is then refuted with a concrete
    // counterexample (the per-step entailment is load-bearing — non-vacuous).
    assert_counterexample("fq_invariant_preserved_append_unsound");
}
#[test]
fn fq_invariant_implies_last_entailed_verified() {
    // Universal-elimination: the whole-db invariant yields the LAST derived
    // constraint entailed (feeds the terminal UNSAT conclusion).
    assert_verified("fq_invariant_implies_last_entailed");
}
#[test]
fn fq_invariant_implies_last_entailed_wrong_refuted() {
    // Out-of-range instantiation (index len) is not covered by the [0,len)
    // invariant; refuted (the universal is used soundly).
    // Unknown-as-failure (docs/design-unknown-as-failure.md): this refutation now
    // fail-closes to a model-less NotProved — still a failure.
    assert_fails("fq_invariant_implies_last_entailed_wrong");
}

// ── (ii-FQ-LIT) FULLY-QUANTIFIED invariant over the LITERAL `Vec` carrier ──────
// residual #2 CLOSED: the SAME per-element universal as (ii-FQ), now with the
// quantifier body the literal `db.index(i)` (== `select db (int2bv_64 i)` over the
// real `db: Vec<i128>` array), NOT the opaque `db_slack_at`. Discharged via the
// landed ay-dpll fixes (forall-goal ground-strict-bound normalization folding the
// `db.len() == old_len + 1` equation into the boundary bound — residual #2(a) —
// plus int2bv boundary injectivity).
#[test]
// Re-activated by the Vec/Seq length-boundedness lane: `db: Vec<i128>` now
// carries `len <= 2^64-1` (VariableDecl::bounded_len), which discharges the
// length-derived carrier-representability obligation that fired outside the
// quantifier and previously left this NotProved/Error.
fn fq_lit_invariant_preserved_append_verified() {
    // PRESERVATION of the literal-Vec per-element invariant across one push: IH
    // over [0,old_len) + the just-appended element entailed (db.index(old_len)>=0)
    // + db.len()==old_len+1 ==> forall over [0,db.len()). The quantifier is over
    // the REAL array read `select db (int2bv i)`, closing residual #2.
    assert_verified("fq_lit_invariant_preserved_append");
}
#[test]
fn fq_lit_invariant_preserved_append_unsound_not_verified() {
    // Dropping the appended-element entailment lets a non-entailed constraint enter
    // the real db at the boundary; the grown literal-carrier forall is then false,
    // so it MUST NOT verify (the per-step entailment premise is load-bearing). Over
    // the int2bv array carrier ay returns Unknown (no concrete CE through int2bv),
    // which is still a non-`Verified` verdict — the discharge is non-vacuous.
    assert_not_verified("fq_lit_invariant_preserved_append_unsound");
}
#[test]
// Re-activated by the Vec/Seq length-boundedness lane: `db: Vec<i128>` now
// carries `len <= 2^64-1` (VariableDecl::bounded_len), discharging the
// length-derived carrier-representability obligation. See the sibling
// `..._preserved_append_verified` note.
fn fq_lit_invariant_implies_last_entailed_verified() {
    // Universal-elimination over the literal carrier: the whole-db invariant yields
    // the LAST derived constraint (db.index(db.len()-1)) entailed.
    assert_verified("fq_lit_invariant_implies_last_entailed");
}
#[test]
fn fq_lit_invariant_implies_last_entailed_wrong_not_verified() {
    // Out-of-range instantiation (index db.len()) is not covered by the [0,db.len())
    // invariant AND the literal read is out of bounds; MUST NOT verify (the index
    // bounds-check obligation cannot be discharged).
    assert_not_verified("fq_lit_invariant_implies_last_entailed_wrong");
}

// ── TERMINAL — 0 >= c (c>=1) entails UNSAT ────────────────────────────────────
#[test]
fn terminal_entails_unsat_verified() {
    assert_verified("terminal_entails_unsat");
}
#[test]
fn terminal_entails_unsat_wrong_refuted() {
    assert_counterexample("terminal_entails_unsat_wrong");
}

// ── (iii) BOUNDED-N END-TO-END — 3-cycle parity refutation ────────────────────
#[test]
fn three_cycle_derive_sum_ge_verified() {
    assert_verified("three_cycle_derive_sum_ge");
}
#[test]
fn three_cycle_derive_sum_ge_overclaim_refuted() {
    assert_counterexample("three_cycle_derive_sum_ge_overclaim");
}
#[test]
fn three_cycle_derive_sum_le_verified() {
    assert_verified("three_cycle_derive_sum_le");
}
#[test]
fn three_cycle_contradiction_verified() {
    assert_verified("three_cycle_contradiction");
}
#[test]
fn three_cycle_inputs_unsat_verified() {
    assert_verified("three_cycle_inputs_unsat");
}
#[test]
fn three_cycle_inputs_satisfiable_drop_one_refuted() {
    assert_counterexample("three_cycle_inputs_satisfiable_drop_one");
}
