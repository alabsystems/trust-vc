// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::collections::{HashMap, HashSet};

use super::atom_registry::{ContractLiteral, ContractVariable};
use super::bcp_decision::ContractAssignmentValue;

// =========================================================================
// CDCL Conflict Analysis Contracts
// =========================================================================

/// Result of 1-UIP conflict analysis in CDCL.
///
/// After a conflict is detected during BCP, the solver performs resolution
/// starting from the conflict clause, resolving against reason clauses until
/// a single literal at the current decision level remains (the UIP). The
/// learned clause is asserting: it has exactly one literal at the current
/// decision level, so after backjumping it becomes unit and propagates.
///
/// Reference: Marques-Silva & Sakallah, "GRASP: A Search Procedure for
/// Propositional Satisfiability", IEEE TC 1999.
#[derive(Debug)]
pub(crate) struct ConflictAnalysisResult {
    /// The learned clause derived by resolution from the conflict.
    pub(crate) learned_clause: Vec<ContractLiteral>,
    /// Decision level to backtrack to (second-highest level in learned clause).
    pub(crate) backjump_level: usize,
    /// The unique implication point literal (the one literal at current level).
    pub(crate) uip_literal: ContractLiteral,
}

/// Validates the result of CDCL 1-UIP conflict analysis.
///
/// Checks the following contract postconditions:
/// 1. The learned clause is asserting: exactly 1 literal at the current decision level.
/// 2. The UIP literal is present in the learned clause.
/// 3. Backjump level equals the second-highest decision level in the learned clause
///    (or 0 if the learned clause has only one literal).
/// 4. All literals in the learned clause are assigned false under the current assignment.
/// 5. The learned clause is not tautological (no variable appears both positive and negative).
#[must_use]
pub(crate) fn validate_conflict_analysis(
    result: &ConflictAnalysisResult,
    current_level: usize,
    decision_levels: &HashMap<ContractVariable, usize>,
    assignment: &HashMap<u32, ContractAssignmentValue>,
) -> bool {
    let clause = &result.learned_clause;

    // Empty learned clause is invalid (would mean UNSAT at level 0, handled separately).
    if clause.is_empty() {
        return false;
    }

    // (1) Asserting: exactly 1 literal at the current decision level.
    let at_current: Vec<&ContractLiteral> = clause
        .iter()
        .filter(|lit| decision_levels.get(&lit.variable()).copied().unwrap_or(0) == current_level)
        .collect();
    if at_current.len() != 1 {
        return false;
    }

    // (2) UIP literal is in the learned clause.
    if !clause.contains(&result.uip_literal) {
        return false;
    }

    // The UIP literal must be the one at the current decision level.
    let uip_level = decision_levels
        .get(&result.uip_literal.variable())
        .copied()
        .unwrap_or(0);
    if uip_level != current_level {
        return false;
    }

    // (3) Backjump level = second-highest decision level in learned clause.
    let expected_backjump = if clause.len() == 1 {
        0
    } else {
        clause
            .iter()
            .filter_map(|lit| {
                let lvl = decision_levels.get(&lit.variable()).copied().unwrap_or(0);
                if lvl < current_level {
                    Some(lvl)
                } else {
                    None
                }
            })
            .max()
            .unwrap_or(0)
    };
    if result.backjump_level != expected_backjump {
        return false;
    }

    // (4) All literals in learned clause are assigned false.
    for lit in clause {
        match assignment.get(&lit.raw()) {
            Some(ContractAssignmentValue::False) => {}
            _ => return false,
        }
    }

    // (5) Not tautological: no variable appears both positive and negative.
    let mut pos_vars = HashSet::new();
    let mut neg_vars = HashSet::new();
    for lit in clause {
        if lit.is_positive() {
            pos_vars.insert(lit.variable());
        } else {
            neg_vars.insert(lit.variable());
        }
    }
    if pos_vars.intersection(&neg_vars).next().is_some() {
        return false;
    }

    true
}

/// Snapshot of solver state before and after a backtrack operation.
///
/// During CDCL backtracking, the solver undoes all assignments above the target
/// decision level while preserving assignments at and below it. The trail is
/// truncated to remove undone assignments, and the assignment map is updated
/// to mark those variables as unassigned.
#[derive(Debug)]
pub(crate) struct BacktrackSnapshot {
    /// The decision level we are backtracking to.
    pub(crate) target_level: usize,
    /// Trail contents before backtracking.
    pub(crate) trail_before: Vec<ContractLiteral>,
    /// Trail contents after backtracking.
    pub(crate) trail_after: Vec<ContractLiteral>,
    /// Decision level of each literal on the trail (indexed by trail position).
    pub(crate) trail_levels: Vec<usize>,
    /// Assignment map after backtracking.
    pub(crate) assignment_after: HashMap<u32, ContractAssignmentValue>,
}

/// Validates that a backtrack operation satisfies its contract.
///
/// Checks:
/// 1. All assignments above target_level are removed (unassigned in result).
/// 2. All assignments at or below target_level are preserved in the trail.
/// 3. The trail after is a prefix-consistent subset of the trail before.
#[must_use]
pub(crate) fn validate_backtrack(snap: &BacktrackSnapshot) -> bool {
    // Trail_levels and trail_before must have the same length.
    if snap.trail_levels.len() != snap.trail_before.len() {
        return false;
    }

    // (1) All literals above target_level must not be in trail_after and must
    //     be unassigned.
    for (i, lit) in snap.trail_before.iter().enumerate() {
        if snap.trail_levels[i] > snap.target_level {
            if snap.trail_after.contains(lit) {
                return false;
            }
            match snap.assignment_after.get(&lit.raw()) {
                Some(ContractAssignmentValue::Unassigned) | None => {}
                _ => return false,
            }
        }
    }

    // (2) All literals at or below target_level must be preserved in trail_after.
    let kept: Vec<&ContractLiteral> = snap
        .trail_before
        .iter()
        .enumerate()
        .filter(|(i, _)| snap.trail_levels[*i] <= snap.target_level)
        .map(|(_, lit)| lit)
        .collect();
    for lit in &kept {
        if !snap.trail_after.contains(lit) {
            return false;
        }
    }

    // (3) Trail after must not be longer than trail before.
    if snap.trail_after.len() > snap.trail_before.len() {
        return false;
    }

    // (3b) Trail after must be order-consistent: each literal in trail_after
    //      appears in the same relative order as in trail_before.
    let mut prev_idx: Option<usize> = None;
    for after_lit in &snap.trail_after {
        let pos = snap.trail_before.iter().position(|l| l == after_lit);
        match pos {
            Some(idx) => {
                if let Some(pi) = prev_idx {
                    if idx <= pi {
                        return false;
                    }
                }
                prev_idx = Some(idx);
            }
            None => return false,
        }
    }

    true
}

/// Validates the quality of a learned clause.
///
/// Checks:
/// 1. No redundant literals (no duplicate variables).
/// 2. Clause is non-empty.
/// 3. Not tautological (no variable appears both positive and negative).
#[must_use]
pub(crate) fn validate_learned_clause_quality(clause: &[ContractLiteral]) -> bool {
    // (1) Non-empty.
    if clause.is_empty() {
        return false;
    }

    // (2) No redundant literals: each variable appears at most once.
    let mut seen_vars = HashSet::new();
    for lit in clause {
        if !seen_vars.insert(lit.variable()) {
            return false;
        }
    }

    // (3) Not tautological.
    let mut pos_vars = HashSet::new();
    let mut neg_vars = HashSet::new();
    for lit in clause {
        if lit.is_positive() {
            pos_vars.insert(lit.variable());
        } else {
            neg_vars.insert(lit.variable());
        }
    }
    if pos_vars.intersection(&neg_vars).next().is_some() {
        return false;
    }

    true
}
