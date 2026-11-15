// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashSet;

use super::atom_registry::ContractLiteral;

// =========================================================================
// Contract 6: DPLL(T) Restart Policy
// =========================================================================

/// Decision returned by the restart policy.
///
/// Models the postconditions of the restart decision function in DPLL(T).
/// Reference: Luby, Sinclair, Zuckerman, "Optimal Speedup of Las Vegas
/// Algorithms", Information Processing Letters 1993.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct RestartDecision {
    /// Whether the solver should restart now.
    pub(crate) should_restart: bool,
    /// The next conflict threshold before considering restart again.
    pub(crate) next_threshold: usize,
}

/// Computes the i-th element of the Luby sequence (1-indexed).
///
/// The Luby sequence is: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
///
/// Algorithm: find the smallest k such that 2^k - 1 >= i, then walk down
/// the complete binary tree of that size. At each node, if i lands exactly
/// at the root of the current subtree (i == size), return 2^(k-1).
/// Otherwise descend into the left half (i <= half) or right half (i -= half).
///
/// Reference: Luby, Sinclair, Zuckerman 1993; Huang, IJCAI 2007.
#[must_use]
pub(crate) fn luby(i: usize) -> usize {
    assert!(i >= 1, "luby sequence is 1-indexed");

    // Find smallest k such that (2^k - 1) >= i.
    let mut k: u32 = 1;
    while (1_usize << k) - 1 < i {
        k += 1;
    }

    // Walk down the tree.
    let mut remaining = i;
    let mut depth = k;
    loop {
        let size = (1_usize << depth) - 1; // size of current complete tree
        if remaining == size {
            // We are at the root of a complete tree of this depth.
            return 1_usize << (depth - 1);
        }
        // The left and right subtrees each have size = (size - 1) / 2 = 2^(depth-1) - 1.
        depth -= 1;
        let half = (1_usize << depth) - 1;
        if remaining <= half {
            // Descend into left subtree.
            continue;
        }
        // Descend into right subtree: subtract the left subtree size.
        remaining -= half;
    }
}

/// Contract abstraction for restart policy.
///
/// Models the restart decision postconditions:
///
/// ```text
/// fn restart_after_conflicts(num_conflicts: usize, luby_index: usize) -> RestartDecision
///
/// requires: luby_index >= 1
///
/// ensures |result|:
///   result.should_restart ==> num_conflicts >= luby(luby_index) * base_interval
///   result.next_threshold == luby(luby_index + 1) * base_interval
///   // After restart, the solver decision level returns to 0.
///   // All learned clauses are preserved (modeled externally).
/// ```
pub(crate) struct ContractRestart {
    /// Base interval multiplied by Luby sequence value to get the threshold.
    pub(crate) base_interval: usize,
    /// Current Luby sequence index (1-indexed).
    pub(crate) luby_index: usize,
    /// Number of learned clauses before restart (for preservation check).
    pub(crate) learned_count_before: usize,
}

impl ContractRestart {
    /// Create a new restart contract with the given base interval.
    #[must_use]
    pub(crate) fn new(base_interval: usize) -> Self {
        Self {
            base_interval,
            luby_index: 1,
            learned_count_before: 0,
        }
    }

    /// Evaluate whether a restart should occur given the current conflict count.
    #[must_use]
    pub(crate) fn restart_after_conflicts(
        &self,
        num_conflicts: usize,
        luby_sequence_index: usize,
    ) -> RestartDecision {
        assert!(luby_sequence_index >= 1, "Luby index must be >= 1");
        let threshold = luby(luby_sequence_index) * self.base_interval;
        let should_restart = num_conflicts >= threshold;
        let next_threshold = luby(luby_sequence_index + 1) * self.base_interval;
        RestartDecision {
            should_restart,
            next_threshold,
        }
    }
}

/// Validates restart decision postconditions.
///
/// Checks:
/// 1. If should_restart, num_conflicts >= current Luby threshold.
/// 2. next_threshold follows Luby sequence for index + 1.
/// 3. After restart, decision level should be 0 (checked via `decision_level_after`).
/// 4. Learned clause count should not decrease (checked via counts).
#[must_use]
pub(crate) fn validate_restart_decision(
    decision: &RestartDecision,
    num_conflicts: usize,
    luby_index: usize,
    base_interval: usize,
    decision_level_after: Option<usize>,
    learned_count_before: usize,
    learned_count_after: usize,
) -> bool {
    let current_threshold = luby(luby_index) * base_interval;
    let expected_next = luby(luby_index + 1) * base_interval;

    // (1) If should_restart, conflicts must be >= threshold.
    if decision.should_restart && num_conflicts < current_threshold {
        return false;
    }

    // (2) next_threshold must match Luby(index + 1) * base.
    if decision.next_threshold != expected_next {
        return false;
    }

    // (3) If restart occurred, decision level must be 0.
    if decision.should_restart {
        if let Some(level) = decision_level_after {
            if level != 0 {
                return false;
            }
        }
    }

    // (4) Learned clauses must be preserved (count does not decrease).
    learned_count_after >= learned_count_before
}

// =========================================================================
// Contract 7: Phase Saving / Polarity Caching
// =========================================================================

/// Contract abstraction for DPLL(T) phase saving (polarity caching).
///
/// Phase saving records the last polarity a variable was assigned before
/// backtracking, so the solver can prefer the same polarity on re-decision.
///
/// Reference: Pipatsrisawat & Darwiche, "A Lightweight Component Caching
/// Scheme for Satisfiability Solvers", SAT 2007.
///
/// Postconditions:
/// 1. After `save_phase(var, pol)`, `get_phase(var) == Some(pol)`.
/// 2. `get_phase(var)` returns `None` for variables never saved.
/// 3. Phase respects variable bounds (var < num_vars).
/// 4. `clear_phases()` resets all phases to `None`.
pub(crate) struct ContractPhaseSaving {
    /// Per-variable polarity cache. Index = variable id.
    pub(crate) saved_phases: Vec<Option<bool>>,
}

impl ContractPhaseSaving {
    /// Create a new phase saving structure for `num_vars` variables.
    #[must_use]
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            saved_phases: vec![None; num_vars],
        }
    }

    /// Save the polarity for a variable.
    ///
    /// # Panics
    ///
    /// Panics if `var >= self.saved_phases.len()`.
    pub(crate) fn save_phase(&mut self, var: usize, polarity: bool) {
        assert!(var < self.saved_phases.len(), "variable out of bounds");
        self.saved_phases[var] = Some(polarity);
    }

    /// Get the saved phase for a variable, or `None` if not saved.
    #[must_use]
    pub(crate) fn get_phase(&self, var: usize) -> Option<bool> {
        self.saved_phases.get(var).copied().flatten()
    }

    /// Clear all saved phases.
    pub(crate) fn clear_phases(&mut self) {
        self.saved_phases.fill(None);
    }

    /// Number of variables this structure tracks.
    #[must_use]
    pub(crate) fn num_vars(&self) -> usize {
        self.saved_phases.len()
    }
}

/// Validates phase saving postconditions.
///
/// After a `save_phase(var, pol)` call, the saved phase must equal `pol`.
#[must_use]
pub(crate) fn validate_phase_save(ps: &ContractPhaseSaving, var: usize, expected: bool) -> bool {
    match ps.get_phase(var) {
        Some(pol) => pol == expected,
        None => false,
    }
}

/// Validates that all phases are cleared.
#[must_use]
pub(crate) fn validate_phases_cleared(ps: &ContractPhaseSaving) -> bool {
    ps.saved_phases.iter().all(|p| p.is_none())
}

// =========================================================================
// Contract 8: Clause Database Invariants
// =========================================================================

/// Contract abstraction for clause database management.
///
/// Models the invariants maintained by a clause database with activity-based
/// deletion. This covers learned clause lifecycle: insertion, activity bump,
/// decay, and deletion.
///
/// Invariants:
/// 1. Learned clause count <= max budget.
/// 2. Activity decay is applied uniformly (all activities multiplied by same factor).
/// 3. Clause deletion preserves unit clauses (never deletes a clause that is
///    currently a reason for a propagated literal).
/// 4. No exact-duplicate clauses in the database.
pub(crate) struct ContractClauseDatabase {
    /// All learned clauses, stored as sorted literal vectors for dedup comparison.
    pub(crate) clauses: Vec<Vec<ContractLiteral>>,
    /// Activity score for each clause (indexed same as `clauses`).
    pub(crate) activities: Vec<f64>,
    /// Maximum number of learned clauses allowed.
    pub(crate) max_budget: usize,
    /// Set of clause indices that are unit reasons (cannot be deleted).
    pub(crate) unit_reason_indices: HashSet<usize>,
}

impl ContractClauseDatabase {
    /// Create a new clause database with the given budget.
    #[must_use]
    pub(crate) fn new(max_budget: usize) -> Self {
        Self {
            clauses: Vec::new(),
            activities: Vec::new(),
            max_budget,
            unit_reason_indices: HashSet::new(),
        }
    }

    /// Add a learned clause to the database.
    ///
    /// Returns the index of the newly added clause.
    pub(crate) fn add_clause(&mut self, clause: Vec<ContractLiteral>) -> usize {
        let idx = self.clauses.len();
        self.clauses.push(clause);
        self.activities.push(0.0);
        idx
    }

    /// Bump the activity of a clause by the given increment.
    pub(crate) fn bump_activity(&mut self, idx: usize, increment: f64) {
        if idx < self.activities.len() {
            self.activities[idx] += increment;
        }
    }

    /// Apply uniform decay to all clause activities.
    pub(crate) fn decay_activities(&mut self, factor: f64) {
        for activity in &mut self.activities {
            *activity *= factor;
        }
    }

    /// Mark a clause index as a unit reason (protected from deletion).
    pub(crate) fn mark_unit_reason(&mut self, idx: usize) {
        self.unit_reason_indices.insert(idx);
    }

    /// Remove the unit reason mark from a clause.
    pub(crate) fn unmark_unit_reason(&mut self, idx: usize) {
        self.unit_reason_indices.remove(&idx);
    }

    /// Current number of learned clauses.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.clauses.len()
    }

    /// Check if the database is within budget.
    #[must_use]
    pub(crate) fn within_budget(&self) -> bool {
        self.clauses.len() <= self.max_budget
    }
}

/// Validates clause database budget invariant.
#[must_use]
pub(crate) fn validate_clause_db_budget(db: &ContractClauseDatabase) -> bool {
    db.clauses.len() <= db.max_budget
}

/// Validates that activity decay was applied uniformly.
///
/// Given `before` and `after` activity vectors and a `factor`, checks that
/// each `after[i] == before[i] * factor` (within floating-point tolerance).
#[must_use]
pub(crate) fn validate_uniform_decay(before: &[f64], after: &[f64], factor: f64) -> bool {
    if before.len() != after.len() {
        return false;
    }
    for (b, a) in before.iter().zip(after.iter()) {
        let expected = b * factor;
        if (a - expected).abs() > 1e-12 {
            return false;
        }
    }
    true
}

/// Validates that clause deletion preserved all unit reason clauses.
///
/// Given the set of clause indices that were unit reasons before deletion,
/// and a mapping from old indices to new indices (None = deleted), checks
/// that no unit reason was deleted.
#[must_use]
pub(crate) fn validate_unit_reasons_preserved(
    unit_reasons: &HashSet<usize>,
    old_to_new: &[Option<usize>],
) -> bool {
    for &idx in unit_reasons {
        if idx < old_to_new.len() && old_to_new[idx].is_none() {
            return false;
        }
    }
    true
}

/// Validates that the clause database contains no duplicate clauses.
///
/// Two clauses are considered duplicates if they contain exactly the same
/// set of literals (order-independent).
#[must_use]
pub(crate) fn validate_no_duplicate_clauses(db: &ContractClauseDatabase) -> bool {
    let mut seen: HashSet<Vec<u32>> = HashSet::new();
    for clause in &db.clauses {
        let mut sorted: Vec<u32> = clause.iter().map(|l| l.raw()).collect();
        sorted.sort_unstable();
        if !seen.insert(sorted) {
            return false;
        }
    }
    true
}

/// Registers the restart policy contract as an extern_spec entry.
pub(crate) fn register_ay_restart_contract() {
    crate::extern_spec_verify::register_extern_spec(
        "ay_sat::Solver::restart",
        &["self.luby_index >= 1".to_string()],
        &[
            "result.should_restart ==> self.num_conflicts >= threshold".to_string(),
            "self.decision_level == 0".to_string(),
            "self.learned_clauses.len() >= old(self.learned_clauses.len())".to_string(),
        ],
    );
}

/// Registers the phase saving contract as an extern_spec entry.
pub(crate) fn register_ay_phase_saving_contract() {
    crate::extern_spec_verify::register_extern_spec(
        "ay_sat::Solver::save_phase",
        &["var < self.num_vars".to_string()],
        &["self.saved_phases[var] == Some(polarity)".to_string()],
    );
}

/// Registers the clause database contract as an extern_spec entry.
pub(crate) fn register_ay_clause_db_contract() {
    crate::extern_spec_verify::register_extern_spec(
        "ay_sat::ClauseDb::reduce",
        &["true".to_string()],
        &[
            "self.len() <= self.max_budget".to_string(),
            "unit_reasons_preserved(old(self.unit_reasons), self.mapping)".to_string(),
            "no_duplicate_clauses(self)".to_string(),
        ],
    );
}
