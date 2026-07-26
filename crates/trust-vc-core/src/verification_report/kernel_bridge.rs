// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Bridge from ay-dpll proof artifacts to the trust-vc-kernel proof checker.
//!
//! Converts a `ay_core::Proof` into the trust-vc-kernel's [`AYProofArtifact`]
//! intermediate representation, then runs [`trust_vc_kernel::check_proof`] for
//! independent UNSAT verification.
//!
//! # Literal encoding
//!
//! ay-core proof clauses store `TermId` values. Negation is represented by
//! wrapping a term in `Not(inner)`, which is a *separate* `TermId` pointing
//! to a `TermData::Not(inner_id)` entry. To produce signed literals for the
//! kernel's resolution checker we need to detect negation.
//!
//! Two strategies are supported:
//!
//! 1. **With `TermStore`** (preferred): resolve `TermData::Not(inner)` via
//!    `terms.get(tid)`, producing `-(inner.0 + 1)` for negated literals.
//!
//! 2. **Without `TermStore`**: learn the negation map from Resolution pivots.
//!    For each Resolution step, the pivot TermId is the positive atom. One
//!    parent clause contains the pivot; the other contains its complement.
//!    By inspecting both parents, we discover which TermId is `Not(pivot)`.
//!
//! The primary entry point [`verify_proof_with_kernel`] accepts an optional
//! `TermStore` reference and falls back to the pivot-learning strategy when
//! it is `None`.

use std::collections::HashMap;

use ay_core::{Proof, ProofStep, TermData, TermId, TermStore};

use trust_vc_kernel::bridge::{
    AYClause, AYProofArtifact, AYResolutionStep, AYTheoryKind, AYTheoryLemma,
};
use trust_vc_kernel::types::CheckResult;

// ---------------------------------------------------------------------------
// TermId -> signed literal mapping
// ---------------------------------------------------------------------------

/// Convert a `TermId` to a signed literal using the term store.
///
/// - `Not(inner)` -> `-(inner.0 + 1)`
/// - anything else -> `(tid.0 + 1)`
fn term_to_literal_with_store(terms: &TermStore, tid: TermId) -> i64 {
    match terms.get(tid) {
        TermData::Not(inner) => -(inner.0 as i64 + 1),
        _ => tid.0 as i64 + 1,
    }
}

/// Convert a `TermId` to a signed literal using a learned negation map.
///
/// If `tid` appears in `neg_map` as a negation of some atom, returns the
/// negative literal. Otherwise returns a positive literal.
fn term_to_literal_with_map(neg_map: &HashMap<TermId, TermId>, tid: TermId) -> i64 {
    if let Some(&positive_atom) = neg_map.get(&tid) {
        -(positive_atom.0 as i64 + 1)
    } else {
        tid.0 as i64 + 1
    }
}

// ---------------------------------------------------------------------------
// Proof step clause extraction
// ---------------------------------------------------------------------------

/// Extract the clause (Vec<TermId>) from a proof step, or `None` for anchors.
fn clause_of_step(step: &ProofStep) -> Option<Vec<TermId>> {
    match step {
        ProofStep::Assume(term_id) => Some(vec![*term_id]),
        ProofStep::Resolution { clause, .. }
        | ProofStep::TheoryLemma { clause, .. }
        | ProofStep::Step { clause, .. } => Some(clause.clone()),
        ProofStep::Anchor { .. } => None,
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Negation map learning (no TermStore needed)
// ---------------------------------------------------------------------------

/// Build a negation map from Resolution pivots.
///
/// For each `Resolution { pivot, clause1, clause2, .. }`:
/// - The pivot TermId is the positive atom.
/// - One parent clause contains the pivot; the other contains its complement.
/// - The complement TermId is mapped to the pivot as its "positive atom".
fn learn_negation_map(proof: &Proof) -> HashMap<TermId, TermId> {
    // Step index -> clause TermIds
    let step_clauses: Vec<Option<Vec<TermId>>> = proof.steps.iter().map(clause_of_step).collect();

    let mut neg_map: HashMap<TermId, TermId> = HashMap::new();

    for step in &proof.steps {
        if let ProofStep::Resolution {
            pivot,
            clause1,
            clause2,
            ..
        } = step
        {
            let c1 = step_clauses
                .get(clause1.0 as usize)
                .and_then(|c| c.as_ref());
            let c2 = step_clauses
                .get(clause2.0 as usize)
                .and_then(|c| c.as_ref());

            if let (Some(c1_lits), Some(c2_lits)) = (c1, c2) {
                // The pivot appears in exactly one parent; its complement in the other.
                let pivot_in_c1 = c1_lits.contains(pivot);
                let pivot_in_c2 = c2_lits.contains(pivot);

                if pivot_in_c1 && !pivot_in_c2 {
                    // Complement is in c2. Find the TermId in c2 that is
                    // Not(pivot) — it's any TermId in c2 not in c1 and not the pivot.
                    // Heuristic: pick a TermId from c2 that we haven't seen as positive.
                    for &tid in c2_lits {
                        if tid != *pivot && !neg_map.contains_key(&tid) {
                            // Conservative: only learn if this TermId hasn't been seen
                            // as a positive atom in another resolution step.
                            neg_map.entry(tid).or_insert(*pivot);
                            break;
                        }
                    }
                } else if pivot_in_c2 && !pivot_in_c1 {
                    for &tid in c1_lits {
                        if tid != *pivot && !neg_map.contains_key(&tid) {
                            neg_map.entry(tid).or_insert(*pivot);
                            break;
                        }
                    }
                }
                // If pivot is in both or neither, we can't learn — skip.
            }
        }
    }

    neg_map
}

// ---------------------------------------------------------------------------
// Theory kind mapping
// ---------------------------------------------------------------------------

/// Map a `ay_core::TheoryLemmaKind` to the kernel bridge's `AYTheoryKind`.
fn map_theory_kind(kind: &ay_core::TheoryLemmaKind) -> AYTheoryKind {
    use ay_core::TheoryLemmaKind;
    match kind {
        TheoryLemmaKind::EufTransitive
        | TheoryLemmaKind::EufCongruent
        | TheoryLemmaKind::EufCongruentPred => AYTheoryKind::Euf,
        TheoryLemmaKind::LraFarkas => AYTheoryKind::Lra,
        TheoryLemmaKind::LiaGeneric => AYTheoryKind::Nia,
        TheoryLemmaKind::BvBitBlast
        | TheoryLemmaKind::BvBitBlastGate { .. }
        | TheoryLemmaKind::FpToBv { .. } => AYTheoryKind::BitVector,
        TheoryLemmaKind::ArraySelectStore { .. } | TheoryLemmaKind::ArrayExtensionality => {
            AYTheoryKind::Array
        }
        TheoryLemmaKind::StringLengthAxiom
        | TheoryLemmaKind::StringContentAxiom
        | TheoryLemmaKind::StringNormalForm => AYTheoryKind::Sequence,
        _ => AYTheoryKind::Other,
    }
}

// ---------------------------------------------------------------------------
// Proof -> AYProofArtifact conversion
// ---------------------------------------------------------------------------

/// Convert a `ay_core::Proof` into a `AYProofArtifact` suitable for the
/// kernel's resolution checker.
///
/// When `terms` is `Some`, uses the term store for precise negation detection.
/// When `None`, falls back to learning negation from Resolution pivots.
///
/// Returns `None` if the proof is empty or has no empty-clause candidate.
#[must_use]
pub(crate) fn convert_proof_to_artifact(
    proof: &Proof,
    terms: Option<&TermStore>,
) -> Option<AYProofArtifact> {
    if proof.steps.is_empty() {
        return None;
    }

    // Build the literal converter based on available data.
    let learned_neg_map = learn_negation_map(proof);

    let to_lit = |tid: TermId| -> i64 {
        if let Some(ts) = terms {
            term_to_literal_with_store(ts, tid)
        } else {
            term_to_literal_with_map(&learned_neg_map, tid)
        }
    };

    let mut input_clauses = Vec::new();
    let mut resolution_steps = Vec::new();
    let mut theory_lemmas = Vec::new();
    let mut last_empty_candidate: Option<u64> = None;

    for (idx, step) in proof.steps.iter().enumerate() {
        let step_id = idx as u64;
        match step {
            ProofStep::Assume(term_id) => {
                let lit = to_lit(*term_id);
                input_clauses.push(AYClause {
                    id: step_id,
                    literals: vec![lit],
                });
            }
            ProofStep::Resolution {
                clause,
                pivot,
                clause1,
                clause2,
            } => {
                let pivot_lit = to_lit(*pivot);
                resolution_steps.push(AYResolutionStep {
                    result_id: step_id,
                    pivot: pivot_lit,
                    antecedent_a: clause1.0 as u64,
                    antecedent_b: clause2.0 as u64,
                    result_literals: Some(clause.iter().map(|t| to_lit(*t)).collect()),
                });
                if clause.is_empty() {
                    last_empty_candidate = Some(step_id);
                }
            }
            ProofStep::TheoryLemma { clause, kind, .. } => {
                let literals: Vec<i64> = clause.iter().map(|t| to_lit(*t)).collect();
                theory_lemmas.push(AYTheoryLemma {
                    id: step_id,
                    kind: map_theory_kind(kind),
                    literals,
                });
            }
            ProofStep::Step { clause, .. } => {
                // Generic Alethe steps (Tseitin clausification, simplification, etc.)
                // are treated as trusted input clauses for the kernel checker.
                let literals: Vec<i64> = clause.iter().map(|t| to_lit(*t)).collect();
                if literals.is_empty() {
                    last_empty_candidate = Some(step_id);
                }
                input_clauses.push(AYClause {
                    id: step_id,
                    literals,
                });
            }
            ProofStep::Anchor { .. } => {
                // Subproof anchors do not produce clauses; skip.
            }
            // ay_core::ProofStep is #[non_exhaustive]; ignore unknown variants.
            _ => {}
        }
    }

    let empty_clause_id = last_empty_candidate?;

    Some(AYProofArtifact {
        input_clauses,
        resolution_steps,
        theory_lemmas,
        empty_clause_id,
    })
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Verify a ay proof through the trust-vc-kernel independent checker.
///
/// Accepts an optional `TermStore` for precise literal encoding. When
/// `terms` is `None`, negation is inferred from Resolution pivots.
///
/// Returns `true` if the kernel's resolution checker accepts the proof trace,
/// `false` if the proof cannot be converted or the checker rejects it.
#[must_use]
pub(crate) fn verify_proof_with_kernel(proof: &Proof, terms: Option<&TermStore>) -> bool {
    let Some(artifact) = convert_proof_to_artifact(proof, terms) else {
        tracing::debug!("kernel bridge: proof could not be converted to AYProofArtifact");
        return false;
    };

    let trace = trust_vc_kernel::bridge::convert_ay_artifact(&artifact);
    let result = trust_vc_kernel::check_proof(&trace);

    match &result {
        CheckResult::Valid => {
            tracing::debug!("kernel bridge: proof verified by independent checker");
            true
        }
        CheckResult::Invalid { step, reason } => {
            tracing::debug!(
                step = step,
                reason = reason.as_str(),
                "kernel bridge: independent checker rejected proof"
            );
            false
        }
        _ => {
            tracing::debug!("kernel bridge: unknown CheckResult variant");
            false
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::{Proof, ProofStep, Sort, TermStore};

    /// Build a minimal valid proof: two unit clauses resolved to empty clause.
    fn build_simple_proof() -> (Proof, TermStore) {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Bool);
        let not_x = terms.mk_not_raw(x);

        let mut proof = Proof::new();
        let p0 = proof.add_step(ProofStep::Assume(x));
        let p1 = proof.add_step(ProofStep::Assume(not_x));
        let _p2 = proof.add_step(ProofStep::Resolution {
            clause: vec![],
            pivot: x,
            clause1: p0,
            clause2: p1,
        });

        (proof, terms)
    }

    #[test]
    fn test_kernel_bridge_simple_proof_verifies_with_store() {
        let (proof, terms) = build_simple_proof();
        assert!(
            verify_proof_with_kernel(&proof, Some(&terms)),
            "simple two-clause resolution proof should be kernel-verified (with store)"
        );
    }

    #[test]
    fn test_kernel_bridge_simple_proof_verifies_without_store() {
        let (proof, _terms) = build_simple_proof();
        assert!(
            verify_proof_with_kernel(&proof, None),
            "simple two-clause resolution proof should be kernel-verified (without store)"
        );
    }

    #[test]
    fn test_kernel_bridge_empty_proof_rejects() {
        let proof = Proof::new();
        assert!(
            !verify_proof_with_kernel(&proof, None),
            "empty proof should not be kernel-verified"
        );
    }

    #[test]
    fn test_kernel_bridge_convert_proof_to_artifact_basic() {
        let (proof, terms) = build_simple_proof();
        let artifact = convert_proof_to_artifact(&proof, Some(&terms))
            .expect("simple proof should convert to artifact");
        assert_eq!(artifact.input_clauses.len(), 2, "two Assume steps");
        assert_eq!(artifact.resolution_steps.len(), 1, "one Resolution step");
        assert_eq!(artifact.empty_clause_id, 2, "empty clause is step 2");
    }

    #[test]
    fn test_kernel_bridge_term_to_literal_positive() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Bool);
        let lit = term_to_literal_with_store(&terms, x);
        assert!(lit > 0, "positive term should map to positive literal");
    }

    #[test]
    fn test_kernel_bridge_term_to_literal_negative() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Bool);
        let not_x = terms.mk_not_raw(x);
        let lit = term_to_literal_with_store(&terms, not_x);
        assert!(lit < 0, "negated term should map to negative literal");
        let pos_lit = term_to_literal_with_store(&terms, x);
        assert_eq!(
            lit, -pos_lit,
            "negated literal should be the sign-complement of positive"
        );
    }

    #[test]
    fn test_kernel_bridge_negation_map_learning() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Bool);
        let not_x = terms.mk_not_raw(x);

        let mut proof = Proof::new();
        let p0 = proof.add_step(ProofStep::Assume(x));
        let p1 = proof.add_step(ProofStep::Assume(not_x));
        let _p2 = proof.add_step(ProofStep::Resolution {
            clause: vec![],
            pivot: x,
            clause1: p0,
            clause2: p1,
        });

        let neg_map = learn_negation_map(&proof);
        assert!(
            neg_map.contains_key(&not_x),
            "negation map should learn that not_x is the complement of x"
        );
        assert_eq!(
            neg_map[&not_x], x,
            "not_x should map to x as its positive atom"
        );
    }

    #[test]
    fn test_kernel_bridge_theory_lemma_included() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Bool);
        let not_x = terms.mk_not_raw(x);
        let y = terms.mk_var("y", Sort::Bool);
        let not_y = terms.mk_not_raw(y);

        let mut proof = Proof::new();
        // Step 0: Theory lemma {x, y}
        let p0 = proof.add_theory_lemma_with_kind(
            "EUF",
            vec![x, y],
            ay_core::TheoryLemmaKind::EufTransitive,
        );
        // Step 1: Assume(not_x)
        let p1 = proof.add_step(ProofStep::Assume(not_x));
        // Step 2: Resolution of p0 and p1 on x -> {y}
        let p2 = proof.add_step(ProofStep::Resolution {
            clause: vec![y],
            pivot: x,
            clause1: p0,
            clause2: p1,
        });
        // Step 3: Assume(not_y)
        let p3 = proof.add_step(ProofStep::Assume(not_y));
        // Step 4: Resolution of p2 and p3 on y -> {}
        let _p4 = proof.add_step(ProofStep::Resolution {
            clause: vec![],
            pivot: y,
            clause1: p2,
            clause2: p3,
        });

        let artifact = convert_proof_to_artifact(&proof, Some(&terms))
            .expect("proof with theory lemma should convert");
        assert_eq!(artifact.theory_lemmas.len(), 1);
        assert_eq!(artifact.theory_lemmas[0].kind, AYTheoryKind::Euf);
        assert!(
            verify_proof_with_kernel(&proof, Some(&terms)),
            "proof with theory lemma should be kernel-verified"
        );
    }

    #[test]
    fn test_kernel_bridge_maps_current_ay_theory_kinds() {
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
    fn test_kernel_bridge_rejects_mismatched_resolution_clause() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Bool);
        let not_x = terms.mk_not_raw(x);

        let mut proof = Proof::new();
        let p0 = proof.add_step(ProofStep::Assume(x));
        let p1 = proof.add_step(ProofStep::Assume(not_x));
        let _p2 = proof.add_step(ProofStep::Resolution {
            clause: vec![x],
            pivot: x,
            clause1: p0,
            clause2: p1,
        });

        assert!(
            !verify_proof_with_kernel(&proof, Some(&terms)),
            "mismatched resolution clause should be rejected by the kernel bridge"
        );
    }
}
