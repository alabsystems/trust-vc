// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Resolution proof checker.
//!
//! Verifies that each resolution step correctly derives its resolvent
//! from two parent clauses, and that the proof terminates in an empty clause.

use std::collections::{BTreeSet, HashMap};

use crate::error::KernelError;
use crate::theory_check::check_all_theory_lemmas;
use crate::types::{CheckResult, CheckResultWithStats, ClauseId, LiteralId, ProofTrace};

/// Check a resolution proof trace for validity, including theory lemma
/// verification.
///
/// Returns a [`CheckResultWithStats`] containing both the overall proof
/// validity and statistics on theory lemma checking (verified, trusted,
/// invalid counts).
///
/// Theory lemmas are checked by theory-specific validators where available
/// (EUF, LRA). Theories without checkers are accepted on trust.
#[must_use]
pub fn check_proof_with_theory(trace: &ProofTrace) -> CheckResultWithStats {
    // First, check all theory lemmas.
    let (theory_stats, first_invalid) = check_all_theory_lemmas(&trace.theory_lemmas);

    // If any theory lemma is invalid, report failure.
    if let Some((lemma_id, result)) = first_invalid {
        let reason = match result {
            crate::types::TheoryCheckResult::Invalid { reason } => reason,
            _ => "unknown theory check failure".to_string(),
        };
        return CheckResultWithStats {
            result: CheckResult::Invalid {
                step: lemma_id,
                reason: format!("theory lemma {lemma_id}: {reason}"),
            },
            theory_stats,
        };
    }

    // Then run the standard resolution checker.
    let result = check_proof(trace);

    CheckResultWithStats {
        result,
        theory_stats,
    }
}

/// Check a resolution proof trace for validity.
///
/// Returns `CheckResult::Valid` if every resolution step is correct and
/// the final clause is empty. Returns `CheckResult::Invalid` on the
/// first detected error.
///
/// Theory lemmas are trusted in this phase — their clauses are accepted
/// without further verification. Use [`check_proof_with_theory`] for
/// theory-aware checking.
#[must_use]
pub fn check_proof(trace: &ProofTrace) -> CheckResult {
    // Build clause map: ClauseId -> set of literals.
    let mut clause_map: HashMap<ClauseId, BTreeSet<LiteralId>> = HashMap::new();

    // Check for duplicate clause IDs across all sources.
    for clause in &trace.input_clauses {
        if clause_map.contains_key(&clause.id) {
            return CheckResult::Invalid {
                step: clause.id,
                reason: KernelError::DuplicateClauseId(clause.id).to_string(),
            };
        }
        clause_map.insert(clause.id, clause.literals.iter().copied().collect());
    }

    for lemma in &trace.theory_lemmas {
        if clause_map.contains_key(&lemma.id) {
            return CheckResult::Invalid {
                step: lemma.id,
                reason: KernelError::DuplicateClauseId(lemma.id).to_string(),
            };
        }
        clause_map.insert(lemma.id, lemma.clause.literals.iter().copied().collect());
    }

    // Process each resolution step in order.
    for step in &trace.resolution_steps {
        if clause_map.contains_key(&step.id) {
            return CheckResult::Invalid {
                step: step.id,
                reason: KernelError::DuplicateClauseId(step.id).to_string(),
            };
        }

        // Look up parent clauses.
        let parent1_lits = match clause_map.get(&step.parent1) {
            Some(lits) => lits,
            None => {
                return CheckResult::Invalid {
                    step: step.id,
                    reason: KernelError::MissingClause {
                        step: step.id,
                        clause_id: step.parent1,
                    }
                    .to_string(),
                };
            }
        };

        let parent2_lits = match clause_map.get(&step.parent2) {
            Some(lits) => lits,
            None => {
                return CheckResult::Invalid {
                    step: step.id,
                    reason: KernelError::MissingClause {
                        step: step.id,
                        clause_id: step.parent2,
                    }
                    .to_string(),
                };
            }
        };

        // Verify pivot appears correctly: +pivot in parent1, -pivot in parent2
        // (or vice versa — we accept either polarity arrangement).
        let pivot = step.pivot;
        let neg_pivot = -pivot;

        let (pos_parent, neg_parent) =
            if parent1_lits.contains(&pivot) && parent2_lits.contains(&neg_pivot) {
                (parent1_lits, parent2_lits)
            } else if parent1_lits.contains(&neg_pivot) && parent2_lits.contains(&pivot) {
                (parent2_lits, parent1_lits)
            } else {
                // Determine which parent is missing the pivot.
                let missing_parent =
                    if !parent1_lits.contains(&pivot) && !parent1_lits.contains(&neg_pivot) {
                        step.parent1
                    } else {
                        step.parent2
                    };
                return CheckResult::Invalid {
                    step: step.id,
                    reason: KernelError::PivotNotInParent {
                        step: step.id,
                        pivot,
                        parent: missing_parent,
                    }
                    .to_string(),
                };
            };

        // Compute resolvent: union of both parents minus the pivot literals.
        let mut resolvent = BTreeSet::new();
        for &lit in pos_parent {
            if lit != pivot {
                resolvent.insert(lit);
            }
        }
        for &lit in neg_parent {
            if lit != neg_pivot {
                resolvent.insert(lit);
            }
        }

        if let Some(expected_literals) = &step.result_literals {
            let expected: BTreeSet<LiteralId> = expected_literals.iter().copied().collect();
            if expected != resolvent {
                return CheckResult::Invalid {
                    step: step.id,
                    reason: KernelError::ResultClauseMismatch {
                        step: step.id,
                        expected: expected.into_iter().collect(),
                        actual: resolvent.iter().copied().collect(),
                    }
                    .to_string(),
                };
            }
        }

        clause_map.insert(step.id, resolvent);
    }

    // Verify the empty clause exists and is indeed empty.
    match clause_map.get(&trace.empty_clause_id) {
        None => CheckResult::Invalid {
            step: trace.empty_clause_id,
            reason: KernelError::EmptyClauseNotFound(trace.empty_clause_id).to_string(),
        },
        Some(lits) if !lits.is_empty() => CheckResult::Invalid {
            step: trace.empty_clause_id,
            reason: KernelError::FinalClauseNotEmpty {
                id: trace.empty_clause_id,
                count: lits.len(),
            }
            .to_string(),
        },
        Some(_) => CheckResult::Valid,
    }
}
