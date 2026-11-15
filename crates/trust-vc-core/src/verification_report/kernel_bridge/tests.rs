// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use ay_core::{AletheRule, Proof, ProofStep, Sort, TermStore};

/// `x` and `not x` resolved to the empty clause.
fn simple_proof(terms: &mut TermStore) -> (Proof, TermId, TermId) {
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not_raw(x);
    let mut proof = Proof::new();
    let p0 = proof.add_step(ProofStep::Assume(x));
    let p1 = proof.add_step(ProofStep::Assume(not_x));
    proof.add_step(ProofStep::Resolution {
        clause: vec![],
        pivot: x,
        clause1: p0,
        clause2: p1,
    });
    (proof, x, not_x)
}

/// The measured collapse: `(assume false) (cl (not false)) :rule false`.
fn collapsed_false_proof(terms: &mut TermStore) -> Proof {
    let f = terms.false_term();
    let not_f = terms.mk_not_raw(f);
    let mut proof = Proof::new();
    let p0 = proof.add_step(ProofStep::Assume(f));
    let p1 = proof.add_step(ProofStep::Step {
        rule: AletheRule::False,
        clause: vec![not_f],
        premises: vec![],
        args: vec![],
    });
    proof.add_step(ProofStep::Resolution {
        clause: vec![],
        pivot: f,
        clause1: p0,
        clause2: p1,
    });
    proof
}

#[test]
fn simple_proof_is_kernel_checked_with_nothing_trusted() {
    let mut terms = TermStore::new();
    let (proof, ..) = simple_proof(&mut terms);
    let check = check_proof_with_kernel(&proof, &terms);
    assert!(check.skeleton_accepted, "{check:?}");
    assert_eq!(check.trusted_steps(), 0);
}

#[test]
fn empty_proof_is_refused() {
    let terms = TermStore::new();
    let check = check_proof_with_kernel(&Proof::new(), &terms);
    assert!(!check.skeleton_accepted);
}

/// Pre-fix the production call ran the kernel WITHOUT a term store and
/// learned polarity from the resolution steps it was checking: resolving
/// `{x}` against `{y}` on `x` recorded "`y` is `not x`" and accepted. The
/// premises `{x, y}` are satisfiable. Polarity is now read off the store.
#[test]
fn resolution_on_non_complementary_literals_is_refused() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);
    let mut proof = Proof::new();
    let p0 = proof.add_step(ProofStep::Assume(x));
    let p1 = proof.add_step(ProofStep::Assume(y));
    proof.add_step(ProofStep::Resolution {
        clause: vec![],
        pivot: x,
        clause1: p0,
        clause2: p1,
    });
    let check = check_proof_with_kernel(&proof, &terms);
    assert!(!check.skeleton_accepted, "{check:?}");
}

/// Pre-fix a generic step that merely CLAIMED `(cl)` was an input clause to
/// the kernel and the empty-clause witness at once, so any proof ending in
/// one was "kernel verified".
#[test]
fn unchecked_generic_empty_clause_is_not_a_witness() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(x));
    proof.add_step(ProofStep::Step {
        rule: AletheRule::Hole,
        clause: vec![],
        premises: vec![],
        args: vec![],
    });
    let check = check_proof_with_kernel(&proof, &terms);
    assert!(!check.skeleton_accepted, "{check:?}");
}

/// A generic `resolution` whose stated conclusion is wrong is not re-derived,
/// and the propositional check refuses it too, so it is not a witness.
#[test]
fn generic_resolution_with_a_wrong_conclusion_is_not_a_witness() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);
    let mut proof = Proof::new();
    let p0 = proof.add_step(ProofStep::Assume(x));
    let p1 = proof.add_step(ProofStep::Assume(y));
    proof.add_step(ProofStep::Step {
        rule: AletheRule::Resolution,
        clause: vec![],
        premises: vec![p0, p1],
        args: vec![],
    });
    assert!(!check_proof_with_kernel(&proof, &terms).skeleton_accepted);
}

/// A correct generic `resolution` is re-derived binary step by binary step
/// and counts as checked.
#[test]
fn generic_resolution_chain_is_rederived() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);
    let not_x = terms.mk_not_raw(x);
    let not_y = terms.mk_not_raw(y);
    let x_or_y = terms.mk_or(vec![x, y]);
    let mut proof = Proof::new();
    let p0 = proof.add_step(ProofStep::Assume(x_or_y));
    // (cl x y) from (or x y): propositionally entailed by its premise.
    let p1 = proof.add_step(ProofStep::Step {
        rule: AletheRule::Or,
        clause: vec![x, y],
        premises: vec![p0],
        args: vec![],
    });
    let p2 = proof.add_step(ProofStep::Assume(not_x));
    let p3 = proof.add_step(ProofStep::Assume(not_y));
    proof.add_step(ProofStep::Step {
        rule: AletheRule::Resolution,
        clause: vec![],
        premises: vec![p1, p2, p3],
        args: vec![],
    });
    let check = check_proof_with_kernel(&proof, &terms);
    assert!(check.skeleton_accepted, "{check:?}");
    assert_eq!(check.trusted_steps(), 0, "{check:?}");
}

/// Tseitin-style premise-free tautologies are checked by the bridge; a
/// premise-free clause that is not a tautology is counted as trusted.
#[test]
fn premise_free_rule_steps_are_checked_or_counted() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);
    let x_and_y = terms.mk_and(vec![x, y]);
    let not_and = terms.mk_not_raw(x_and_y);
    let not_x = terms.mk_not_raw(x);

    // (cl (not (and x y)) x) is `and_pos`: a tautology.
    let mut proof = Proof::new();
    let p0 = proof.add_step(ProofStep::Assume(x_and_y));
    let p1 = proof.add_step(ProofStep::Step {
        rule: AletheRule::AndPos(0),
        clause: vec![not_and, x],
        premises: vec![],
        args: vec![],
    });
    let p2 = proof.add_step(ProofStep::Resolution {
        clause: vec![x],
        pivot: x_and_y,
        clause1: p0,
        clause2: p1,
    });
    let p3 = proof.add_step(ProofStep::Assume(not_x));
    proof.add_step(ProofStep::Resolution {
        clause: vec![],
        pivot: x,
        clause1: p2,
        clause2: p3,
    });
    let check = check_proof_with_kernel(&proof, &terms);
    assert!(check.skeleton_accepted, "{check:?}");
    assert_eq!(check.trusted_steps(), 0, "{check:?}");

    // The same skeleton with (cl x) asserted by an unchecked rule instead.
    let mut proof = Proof::new();
    let p0 = proof.add_step(ProofStep::Step {
        rule: AletheRule::Hole,
        clause: vec![x],
        premises: vec![],
        args: vec![],
    });
    let p1 = proof.add_step(ProofStep::Assume(not_x));
    proof.add_step(ProofStep::Resolution {
        clause: vec![],
        pivot: x,
        clause1: p0,
        clause2: p1,
    });
    let check = check_proof_with_kernel(&proof, &terms);
    assert!(check.skeleton_accepted, "{check:?}");
    assert_eq!(check.trusted_rule_steps, 1, "{check:?}");
}

/// Theory lemmas go through `check_proof_with_theory` and are always counted
/// as trusted: its EUF/LRA checks are structural, not semantic.
#[test]
fn theory_lemmas_are_counted_as_trusted() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not_raw(x);
    let y = terms.mk_var("y", Sort::Bool);
    let not_y = terms.mk_not_raw(y);

    // (cl (not x) y): one positive literal, the shape of an EUF conflict.
    let mut proof = Proof::new();
    let p0 = proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_x, y],
        ay_core::TheoryLemmaKind::EufTransitive,
    );
    let p1 = proof.add_step(ProofStep::Assume(x));
    let p2 = proof.add_step(ProofStep::Resolution {
        clause: vec![y],
        pivot: x,
        clause1: p0,
        clause2: p1,
    });
    let p3 = proof.add_step(ProofStep::Assume(not_y));
    proof.add_step(ProofStep::Resolution {
        clause: vec![],
        pivot: y,
        clause1: p2,
        clause2: p3,
    });

    let converted = convert_proof_to_artifact(&proof, &terms).expect("converts");
    assert_eq!(converted.artifact.theory_lemmas.len(), 1);
    assert_eq!(converted.artifact.theory_lemmas[0].kind, AYTheoryKind::Euf);
    let check = check_proof_with_kernel(&proof, &terms);
    assert!(check.skeleton_accepted, "{check:?}");
    assert_eq!(check.trusted_theory_lemmas, 1, "{check:?}");
}

/// A structurally malformed theory lemma is a kernel refusal, not an axiom.
#[test]
fn malformed_theory_lemma_is_refused() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);
    let not_x = terms.mk_not_raw(x);
    let not_y = terms.mk_not_raw(y);
    // Two positive equalities: not the shape of any EUF conflict clause.
    let mut proof = Proof::new();
    let p0 = proof.add_theory_lemma_with_kind(
        "EUF",
        vec![x, y],
        ay_core::TheoryLemmaKind::EufTransitive,
    );
    let p1 = proof.add_step(ProofStep::Assume(not_x));
    let p2 = proof.add_step(ProofStep::Resolution {
        clause: vec![y],
        pivot: x,
        clause1: p0,
        clause2: p1,
    });
    let p3 = proof.add_step(ProofStep::Assume(not_y));
    proof.add_step(ProofStep::Resolution {
        clause: vec![],
        pivot: y,
        clause1: p2,
        clause2: p3,
    });
    // `x`, `y` are positive literals; a clause with both is refused by the
    // kernel's EUF shape check.
    let check = check_proof_with_kernel(&proof, &terms);
    assert!(!check.skeleton_accepted, "{check:?}");
}

#[test]
fn mismatched_resolution_clause_is_refused() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not_raw(x);
    let mut proof = Proof::new();
    let p0 = proof.add_step(ProofStep::Assume(x));
    let p1 = proof.add_step(ProofStep::Assume(not_x));
    proof.add_step(ProofStep::Resolution {
        clause: vec![x],
        pivot: x,
        clause1: p0,
        clause2: p1,
    });
    assert!(!check_proof_with_kernel(&proof, &terms).skeleton_accepted);
}

#[test]
fn a_proof_naming_terms_outside_its_store_is_refused() {
    let mut big = TermStore::new();
    let (proof, ..) = simple_proof(&mut big);
    let small = TermStore::new();
    let check = check_proof_with_kernel(&proof, &small);
    assert!(!check.skeleton_accepted);
    assert!(
        check
            .refusal
            .as_deref()
            .is_some_and(|r| r.contains("outside its term snapshot")),
        "{check:?}"
    );
}

#[test]
fn maps_current_ay_theory_kinds() {
    assert_eq!(
        map_theory_kind(&ay_core::TheoryLemmaKind::ArraySelectStore { index_eq: true }),
        AYTheoryKind::Array
    );
    assert_eq!(
        map_theory_kind(&ay_core::TheoryLemmaKind::ArrayExtensionality),
        AYTheoryKind::Array
    );
    assert_eq!(
        map_theory_kind(&ay_core::TheoryLemmaKind::BvBitBlastGate {
            gate_type: ay_core::BvGateType::And,
            width: 8,
        }),
        AYTheoryKind::BitVector
    );
    assert_eq!(
        map_theory_kind(&ay_core::TheoryLemmaKind::StringLengthAxiom),
        AYTheoryKind::Sequence
    );
}

#[test]
fn literals_follow_the_store() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not_raw(x);
    assert!(literal(&terms, x) > 0);
    assert_eq!(literal(&terms, not_x), -literal(&terms, x));
}

// ----- premise binding -----

#[test]
fn bound_premises_are_accepted() {
    let mut terms = TermStore::new();
    let (proof, x, not_x) = simple_proof(&mut terms);
    let posed = PosedQuery::from_terms([x, not_x]);
    assert_eq!(bind_premises(&proof, Some(&terms), &posed), Ok(()));
    assert!(!assumes_false(&proof, Some(&terms)));
}

/// The kernel accepts the derivation either way; only the binding sees that
/// `not x` was never asserted.
#[test]
fn a_premise_outside_the_posed_query_is_not_bound() {
    let mut terms = TermStore::new();
    let (proof, x, _) = simple_proof(&mut terms);
    let y = terms.mk_var("y", Sort::Bool);
    assert!(check_proof_with_kernel(&proof, &terms).skeleton_accepted);
    let err = bind_premises(&proof, Some(&terms), &PosedQuery::from_terms([x, y]))
        .expect_err("foreign premise");
    assert!(err.contains("not a term trust-vc asserted"), "{err}");
}

/// trust-vc asserted the `false` handle: it is what the term builder returned
/// for the negated goal. The certificate refutes the posed query, so it binds,
/// and the collapse is disclosed.
#[test]
fn a_collapsed_query_binds_and_is_disclosed() {
    let mut terms = TermStore::new();
    let proof = collapsed_false_proof(&mut terms);
    assert!(check_proof_with_kernel(&proof, &terms).skeleton_accepted);
    let posed = PosedQuery::from_terms([terms.false_term()]);
    assert_eq!(bind_premises(&proof, Some(&terms), &posed), Ok(()));
    assert!(assumes_false(&proof, Some(&terms)));
    // Recognized without the store as well.
    assert!(assumes_false(&proof, None));
}

/// A `false` premise trust-vc did not assert is a premise outside the posed
/// query like any other: the solver cannot collapse the query on its own.
#[test]
fn a_false_premise_trust_vc_did_not_assert_is_not_bound() {
    let mut terms = TermStore::new();
    let proof = collapsed_false_proof(&mut terms);
    let x = terms.mk_var("x", Sort::Bool);
    let err = bind_premises(&proof, Some(&terms), &PosedQuery::from_terms([x]))
        .expect_err("unposed `false`");
    assert!(err.contains("not a term trust-vc asserted"), "{err}");
}

#[test]
fn an_assumption_free_proof_is_not_bound() {
    assert!(bind_premises(&Proof::new(), None, &PosedQuery::default()).is_err());
}

// ----- posed query transcript -----

/// The posed query is the live assertion stack of trust-vc's own calls:
/// popped scopes leave it, a reset clears it, and the assumptions of a final
/// `check-sat-assuming` join it.
#[test]
fn posed_query_replays_the_api_transcript() {
    use ay_dpll::api::{Logic, Solver, Sort as ApiSort};
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let a = solver.declare_const("a", ApiSort::Bool);
    let b = solver.declare_const("b", ApiSort::Bool);
    let c = solver.declare_const("c", ApiSort::Bool);
    solver.try_assert_term(a).expect("assert a");
    solver.try_push().expect("push");
    solver.try_assert_term(b).expect("assert b");
    solver.try_pop().expect("pop");
    solver.try_push().expect("push");
    solver.try_assert_term(c).expect("assert c");

    let posed = PosedQuery::from_transcript(solver.native_replay_events()).expect("replays");
    assert!(posed.contains(a.id()));
    assert!(!posed.contains(b.id()), "a popped assertion is not posed");
    assert!(posed.contains(c.id()));

    let _ = solver.check_sat_assuming(&[b]);
    let posed = PosedQuery::from_transcript(solver.native_replay_events()).expect("replays");
    assert!(
        posed.contains(b.id()),
        "a final check-sat-assuming poses its assumptions"
    );
    let _ = solver.check_sat();
    let posed = PosedQuery::from_transcript(solver.native_replay_events()).expect("replays");
    assert!(!posed.contains(b.id()), "a later plain check-sat does not");
}

// ----- proof order: a step relies only on conclusions already checked -----

/// The circular proof: a native resolution derives the empty clause from
/// step 0 and the LATER step 2, and step 2 is a generic step concluding
/// `(cl (not x))` from step 1's claimed empty clause. Each step looks fine
/// against the other's claim; the premises `{x}` are satisfiable. Before the
/// proof was read in its own order, the kernel loaded step 2 as an input
/// clause up front and the bridge checked step 2 against step 1's unchecked
/// `(cl)`, so this came back accepted with nothing trusted.
fn circular_proof(terms: &mut TermStore, rule: AletheRule) -> Proof {
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not_raw(x);
    let mut proof = Proof::new();
    let p0 = proof.add_step(ProofStep::Assume(x));
    proof.add_step(ProofStep::Resolution {
        clause: vec![],
        pivot: x,
        clause1: p0,
        clause2: ProofId(2),
    });
    proof.add_step(ProofStep::Step {
        rule,
        clause: vec![not_x],
        premises: vec![ProofId(1)],
        args: vec![],
    });
    proof
}

fn refused_for_order(check: &KernelCheck) -> bool {
    !check.skeleton_accepted
        && check
            .refusal
            .as_deref()
            .is_some_and(|reason| reason.contains("not an earlier step"))
}

#[test]
fn a_resolution_citing_a_later_step_is_refused() {
    for rule in [AletheRule::Contraction, AletheRule::Hole] {
        let mut terms = TermStore::new();
        let proof = circular_proof(&mut terms, rule.clone());
        let check = check_proof_with_kernel(&proof, &terms);
        assert!(refused_for_order(&check), "{rule:?}: {check:?}");
    }
}

/// A resolution citing a LATER theory lemma: the kernel loads theory lemmas up
/// front too, so this was accepted (with the lemma disclosed as trusted).
#[test]
fn a_resolution_citing_a_later_theory_lemma_is_refused() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not_raw(x);
    let mut proof = Proof::new();
    let p0 = proof.add_step(ProofStep::Assume(x));
    proof.add_step(ProofStep::Resolution {
        clause: vec![],
        pivot: x,
        clause1: p0,
        clause2: ProofId(2),
    });
    proof.add_theory_lemma_with_kind("EUF", vec![not_x], ay_core::TheoryLemmaKind::EufTransitive);
    let check = check_proof_with_kernel(&proof, &terms);
    assert!(refused_for_order(&check), "{check:?}");
}

/// A `hole` citing a later step. It used to be counted as trusted and fed to
/// the kernel as an input clause, so the proof was accepted with one trusted
/// step; a premise that is not yet checked is no premise at all.
#[test]
fn a_hole_citing_a_later_step_is_refused() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not_raw(x);
    let mut proof = Proof::new();
    let p0 = proof.add_step(ProofStep::Assume(x));
    let p1 = proof.add_step(ProofStep::Step {
        rule: AletheRule::Hole,
        clause: vec![not_x],
        premises: vec![ProofId(2)],
        args: vec![],
    });
    proof.add_step(ProofStep::Resolution {
        clause: vec![],
        pivot: x,
        clause1: p0,
        clause2: p1,
    });
    let check = check_proof_with_kernel(&proof, &terms);
    assert!(refused_for_order(&check), "{check:?}");
}

/// Two generic steps that cite each other: neither conclusion is derived from
/// anything checked.
#[test]
fn a_cycle_between_generic_steps_is_refused() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not_raw(x);
    let mut proof = Proof::new();
    let p0 = proof.add_step(ProofStep::Assume(x));
    proof.add_step(ProofStep::Step {
        rule: AletheRule::Contraction,
        clause: vec![not_x],
        premises: vec![ProofId(2)],
        args: vec![],
    });
    let p2 = proof.add_step(ProofStep::Step {
        rule: AletheRule::Contraction,
        clause: vec![not_x],
        premises: vec![ProofId(1)],
        args: vec![],
    });
    proof.add_step(ProofStep::Resolution {
        clause: vec![],
        pivot: x,
        clause1: p0,
        clause2: p2,
    });
    let check = check_proof_with_kernel(&proof, &terms);
    assert!(refused_for_order(&check), "{check:?}");
}

/// A step citing itself, generic or native.
#[test]
fn a_self_citing_step_is_refused() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not_raw(x);
    let mut proof = Proof::new();
    let p0 = proof.add_step(ProofStep::Assume(x));
    let p1 = proof.add_step(ProofStep::Step {
        rule: AletheRule::Contraction,
        clause: vec![not_x],
        premises: vec![ProofId(1)],
        args: vec![],
    });
    proof.add_step(ProofStep::Resolution {
        clause: vec![],
        pivot: x,
        clause1: p0,
        clause2: p1,
    });
    let check = check_proof_with_kernel(&proof, &terms);
    assert!(refused_for_order(&check), "generic: {check:?}");

    let mut proof = Proof::new();
    let p0 = proof.add_step(ProofStep::Assume(x));
    proof.add_step(ProofStep::Resolution {
        clause: vec![],
        pivot: x,
        clause1: p0,
        clause2: ProofId(1),
    });
    let check = check_proof_with_kernel(&proof, &terms);
    assert!(refused_for_order(&check), "native: {check:?}");
}

/// Control: the same steps in their proper order. The generic step concludes
/// `(cl (not x))` from an earlier, checked premise, so it is checked by the
/// bridge, and nothing is trusted.
#[test]
fn the_same_steps_in_order_are_checked() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not_raw(x);
    let mut proof = Proof::new();
    let p0 = proof.add_step(ProofStep::Assume(x));
    let p1 = proof.add_step(ProofStep::Assume(not_x));
    let p2 = proof.add_step(ProofStep::Step {
        rule: AletheRule::Contraction,
        clause: vec![not_x],
        premises: vec![p1],
        args: vec![],
    });
    proof.add_step(ProofStep::Resolution {
        clause: vec![],
        pivot: x,
        clause1: p0,
        clause2: p2,
    });
    let check = check_proof_with_kernel(&proof, &terms);
    assert!(check.skeleton_accepted, "{check:?}");
    assert_eq!(check.trusted_steps(), 0, "{check:?}");
}

/// A `hole` or `trust` step is one the producer says it did not prove. It is
/// counted as trusted even when its conclusion happens to follow from its
/// premises, so `kernel_fully_checked` is never claimed across one.
#[test]
fn a_hole_is_trusted_even_when_its_conclusion_follows() {
    for rule in [AletheRule::Hole, AletheRule::Trust] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Bool);
        let not_x = terms.mk_not_raw(x);
        let mut proof = Proof::new();
        let p0 = proof.add_step(ProofStep::Assume(x));
        let p1 = proof.add_step(ProofStep::Step {
            rule: rule.clone(),
            clause: vec![x],
            premises: vec![p0],
            args: vec![],
        });
        let p2 = proof.add_step(ProofStep::Assume(not_x));
        proof.add_step(ProofStep::Resolution {
            clause: vec![],
            pivot: x,
            clause1: p1,
            clause2: p2,
        });
        let check = check_proof_with_kernel(&proof, &terms);
        assert!(check.skeleton_accepted, "{rule:?}: {check:?}");
        assert_eq!(check.trusted_rule_steps, 1, "{rule:?}: {check:?}");
    }
}

/// A step citing a subproof anchor cites a step that concludes no clause.
#[test]
fn a_step_citing_an_anchor_is_refused() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not_raw(x);
    let mut proof = Proof::new();
    let p0 = proof.add_step(ProofStep::Assume(x));
    let anchor = proof.add_step(ProofStep::Anchor {
        end_step: ProofId(2),
        variables: vec![],
    });
    let p2 = proof.add_step(ProofStep::Step {
        rule: AletheRule::Contraction,
        clause: vec![not_x],
        premises: vec![anchor],
        args: vec![],
    });
    proof.add_step(ProofStep::Resolution {
        clause: vec![],
        pivot: x,
        clause1: p0,
        clause2: p2,
    });
    let check = check_proof_with_kernel(&proof, &terms);
    assert!(!check.skeleton_accepted, "{check:?}");
    assert!(
        check
            .refusal
            .as_deref()
            .is_some_and(|reason| reason.contains("concludes no clause")),
        "{check:?}"
    );
}

/// The circular proof carried onto a public certificate: every claim it
/// used to make about its obligation is withheld.
#[test]
fn the_circular_proof_makes_no_claim_on_a_public_certificate() {
    use ay_dpll::api::{Logic, Solver, Sort as ApiSort};
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    solver.set_produce_proofs(true);
    let p = solver.declare_const("p", ApiSort::Bool);
    solver.try_assert_term(p).expect("p");
    let np = solver.not(p);
    solver.try_assert_term(np).expect("not p");
    let _ = solver.check_sat();
    let artifact = solver.export_last_unsat_artifact().expect("artifact");

    let mut terms = TermStore::new();
    let proof = circular_proof(&mut terms, AletheRule::Hole);
    let ProofStep::Assume(x) = proof.steps[0] else {
        panic!("step 0 is the premise");
    };
    let evidence = CertificateEvidence {
        binding: bind_premises(&proof, Some(&terms), &PosedQuery::from_terms([x])),
        kernel: check_proof_with_kernel(&proof, &terms),
        query_collapsed: assumes_false(&proof, Some(&terms)),
        assumed_lemma_premises: 0,
    };
    assert_eq!(evidence.binding, Ok(()), "the premises are the posed query");
    let cert = crate::verification_report::ProofCertificate::from_artifact(&artifact, "g")
        .with_evidence(&evidence);
    assert!(cert.premises_bound());
    assert!(!cert.kernel_skeleton_accepted(), "{cert:?}");
    assert!(!cert.kernel_verified(), "{cert:?}");
    assert!(!cert.kernel_fully_checked(), "{cert:?}");
}

// ----- premises that are instances of a posed `forall` -----

/// `forall x. f(x) = g(x, c)`, built with uninterpreted symbols only so no
/// builder rewrite reorders or folds it.
struct Definition {
    forall: TermId,
    c: TermId,
}

fn app(terms: &mut TermStore, name: &str, args: &[TermId]) -> TermId {
    terms.mk_app(ay_core::Symbol::named(name), args, Sort::Int)
}

fn definition(terms: &mut TermStore) -> Definition {
    let x = terms.mk_var("x", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let fx = app(terms, "f", &[x]);
    let gx = app(terms, "g", &[x, c]);
    let body = terms.mk_eq(fx, gx);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
    Definition { forall, c }
}

/// `f(lhs) = g(arg, c)`.
fn equation(terms: &mut TermStore, lhs: TermId, arg: TermId, c: TermId) -> TermId {
    let f = app(terms, "f", &[lhs]);
    let g = app(terms, "g", &[arg, c]);
    terms.mk_eq(f, g)
}

fn assuming(term: TermId) -> Proof {
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(term));
    proof
}

#[test]
fn an_exact_instance_of_a_posed_forall_binds() {
    let mut terms = TermStore::new();
    let def = definition(&mut terms);
    let a = terms.mk_var("a", Sort::Int);
    let instance = equation(&mut terms, a, a, def.c);
    let posed = PosedQuery::from_terms([def.forall]);
    assert_eq!(
        bind_premises(&assuming(instance), Some(&terms), &posed),
        Ok(())
    );
    // Without the store nothing but a posed term binds.
    assert!(bind_premises(&assuming(instance), None, &posed).is_err());
}

/// One binder, two different terms at its occurrences: not an instance.
#[test]
fn an_inconsistent_instance_does_not_bind() {
    let mut terms = TermStore::new();
    let def = definition(&mut terms);
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let not_instance = equation(&mut terms, a, b, def.c);
    let posed = PosedQuery::from_terms([def.forall]);
    assert!(bind_premises(&assuming(not_instance), Some(&terms), &posed).is_err());
}

/// The body's free symbol `c` must stay `c`.
#[test]
fn an_instance_that_changes_a_free_symbol_does_not_bind() {
    let mut terms = TermStore::new();
    let def = definition(&mut terms);
    let a = terms.mk_var("a", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);
    let not_instance = equation(&mut terms, a, a, d);
    let posed = PosedQuery::from_terms([def.forall]);
    assert!(bind_premises(&assuming(not_instance), Some(&terms), &posed).is_err());
}

/// The instance of a `forall` that is not posed binds nothing.
#[test]
fn an_instance_of_an_unposed_forall_does_not_bind() {
    let mut terms = TermStore::new();
    let def = definition(&mut terms);
    let a = terms.mk_var("a", Sort::Int);
    let instance = equation(&mut terms, a, a, def.c);
    let other = terms.mk_var("p", Sort::Bool);
    assert!(def.forall != other);
    let posed = PosedQuery::from_terms([other]);
    assert!(bind_premises(&assuming(instance), Some(&terms), &posed).is_err());
}

/// A body with a nested binder is not matched at all, so no instantiation
/// can capture a variable.
#[test]
fn a_forall_with_a_nested_binder_binds_no_instance() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let fx = app(&mut terms, "f", &[x]);
    let fy = app(&mut terms, "f", &[y]);
    let inner_body = terms.mk_eq(fx, fy);
    let inner = terms.mk_exists(vec![("y".to_string(), Sort::Int)], inner_body);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], inner);
    let a = terms.mk_var("a", Sort::Int);
    let fa = app(&mut terms, "f", &[a]);
    let instance_body = terms.mk_eq(fa, fy);
    let instance = terms.mk_exists(vec![("y".to_string(), Sort::Int)], instance_body);
    let posed = PosedQuery::from_terms([forall]);
    assert!(bind_premises(&assuming(instance), Some(&terms), &posed).is_err());
}

/// Definitional adoption through the real API: AY answers the asserted
/// `forall x. f(x) = x + 1` for an application `f(1)` built before it by
/// asserting the instance, and the proof assumes that instance. The query is
/// true and AY's strict checker accepts the proof; the certificate binds.
#[test]
fn definitional_adoption_certificate_binds() {
    use ay_dpll::api::{Logic, Solver, Sort as ApiSort};
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    solver.set_produce_proofs(true);
    let f = solver.declare_fun("f", &[ApiSort::Int], ApiSort::Int);
    let one = solver.int_const(1);
    let two = solver.int_const(2);
    let f1 = solver.apply(&f, &[one]);
    let xv = solver.fresh_var("x", ApiSort::Int);
    let fx = solver.apply(&f, &[xv]);
    let body = solver.add(xv, one);
    let eq = solver.eq(fx, body);
    let def = solver.forall(&[xv], eq);
    solver.try_assert_term(def).expect("assert the definition");
    solver.try_push().expect("push");
    let goal = solver.eq(f1, two);
    let negated = solver.not(goal);
    solver
        .try_assert_term(negated)
        .expect("assert the negated goal");
    assert!(solver.check_sat().result().is_unsat(), "the query is true");
    let evidence = certify_last_refutation(&solver, negated, &[]);
    assert_eq!(evidence.binding, Ok(()), "{evidence:?}");
    assert!(evidence.kernel.skeleton_accepted, "{evidence:?}");
}

/// Refuted twin: the goal `f(1) = 3` is false, so there is no refutation.
#[test]
fn definitional_adoption_refuted_twin_is_sat() {
    use ay_dpll::api::{Logic, Solver, Sort as ApiSort};
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    solver.set_produce_proofs(true);
    let f = solver.declare_fun("f", &[ApiSort::Int], ApiSort::Int);
    let one = solver.int_const(1);
    let three = solver.int_const(3);
    let f1 = solver.apply(&f, &[one]);
    let xv = solver.fresh_var("x", ApiSort::Int);
    let fx = solver.apply(&f, &[xv]);
    let body = solver.add(xv, one);
    let eq = solver.eq(fx, body);
    let def = solver.forall(&[xv], eq);
    solver.try_assert_term(def).expect("assert the definition");
    solver.try_push().expect("push");
    let goal = solver.eq(f1, three);
    let negated = solver.not(goal);
    solver
        .try_assert_term(negated)
        .expect("assert the negated goal");
    assert!(
        !solver.check_sat().result().is_unsat(),
        "the query is false"
    );
}
