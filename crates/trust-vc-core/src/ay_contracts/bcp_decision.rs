// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::collections::{HashMap, HashSet};

use super::atom_registry::{ContractLiteral, ContractVariable};

// ---------------------------------------------------------------------------
// Contract 3: BCP propagation (propagate_bcp / search_propagate)
// ---------------------------------------------------------------------------

/// Assignment value for a literal in the partial assignment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ContractAssignmentValue {
    Unassigned,
    True,
    False,
}

/// A clause reference in the contract model.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ContractClauseRef(pub(crate) u32);

/// Snapshot of solver state before and after BCP propagation.
#[derive(Debug)]
pub(crate) struct PropagationSnapshot {
    pub(crate) trail_before: Vec<ContractLiteral>,
    pub(crate) trail_after: Vec<ContractLiteral>,
    pub(crate) qhead_before: usize,
    pub(crate) qhead_after: usize,
    pub(crate) clauses: Vec<Vec<ContractLiteral>>,
    pub(crate) assignment: HashMap<u32, ContractAssignmentValue>,
    pub(crate) conflict: Option<ContractClauseRef>,
}

/// Contract trait for BCP propagation.
pub(crate) trait BcpPropagation {
    fn snapshot(&self) -> PropagationSnapshot;
    fn propagate(&mut self) -> PropagationSnapshot;
}

/// Validates BCP propagation postconditions.
#[must_use]
pub(crate) fn validate_propagation_postcondition(snap: &PropagationSnapshot) -> bool {
    if snap.conflict.is_none() && snap.qhead_after != snap.trail_after.len() {
        return false;
    }
    if let Some(cref) = snap.conflict {
        let idx = cref.0 as usize;
        if idx < snap.clauses.len() {
            for lit in &snap.clauses[idx] {
                match snap.assignment.get(&lit.raw()) {
                    Some(ContractAssignmentValue::False) => {}
                    _ => return false,
                }
            }
        }
    }
    if snap.trail_after.len() < snap.trail_before.len() {
        return false;
    }
    let new_lits = &snap.trail_after[snap.trail_before.len()..];
    let mut seen_vars = HashSet::new();
    for lit in new_lits {
        if !seen_vars.insert(lit.variable()) {
            return false;
        }
    }
    let pre_vars: HashSet<ContractVariable> =
        snap.trail_before.iter().map(|l| l.variable()).collect();
    for lit in new_lits {
        if pre_vars.contains(&lit.variable()) {
            return false;
        }
    }
    for lit in new_lits {
        let mut found = false;
        for clause in &snap.clauses {
            if !clause.contains(lit) {
                continue;
            }
            let ok = clause.iter().all(|cl| {
                *cl == *lit
                    || matches!(
                        snap.assignment.get(&cl.raw()),
                        Some(ContractAssignmentValue::False)
                    )
            });
            if ok {
                found = true;
                break;
            }
        }
        if !found {
            return false;
        }
    }
    true
}

// ---------------------------------------------------------------------------
// Contract 4: Decision (decide / pick_next_decision_variable)
// ---------------------------------------------------------------------------

/// Snapshot of solver state before and after a decision.
#[derive(Debug, Clone)]
pub(crate) struct DecisionSnapshot {
    pub(crate) level_before: u32,
    pub(crate) level_after: u32,
    pub(crate) decision_literal: ContractLiteral,
    pub(crate) trail_len_before: usize,
    pub(crate) trail_len_after: usize,
    pub(crate) assigned_vars_before: HashSet<u32>,
    pub(crate) removed_vars: HashSet<u32>,
    pub(crate) num_vars: u32,
    pub(crate) qhead_at_decision: usize,
}

/// Contract trait for decision.
pub(crate) trait DecisionOperation {
    fn decide(&mut self, lit: ContractLiteral) -> DecisionSnapshot;
}

/// Validates decision preconditions.
#[must_use]
pub(crate) fn validate_decision_precondition(snap: &DecisionSnapshot) -> bool {
    let v = snap.decision_literal.variable().0;
    snap.qhead_at_decision == snap.trail_len_before
        && !snap.removed_vars.contains(&v)
        && !snap.assigned_vars_before.contains(&v)
        && v < snap.num_vars
}

/// Validates decision postconditions.
#[must_use]
pub(crate) fn validate_decision_postcondition(snap: &DecisionSnapshot) -> bool {
    snap.level_after == snap.level_before + 1 && snap.trail_len_after == snap.trail_len_before + 1
}

// ---------------------------------------------------------------------------
// Reference implementations
// ---------------------------------------------------------------------------

pub(crate) struct ReferenceBcp {
    clauses: Vec<Vec<ContractLiteral>>,
    vals: HashMap<u32, ContractAssignmentValue>,
    trail: Vec<ContractLiteral>,
    qhead: usize,
}

impl ReferenceBcp {
    #[must_use]
    pub(crate) fn new(num_vars: u32) -> Self {
        let mut vals = HashMap::new();
        for v in 0..num_vars {
            let p = ContractLiteral::positive(ContractVariable(v));
            let n = ContractLiteral::negative(ContractVariable(v));
            vals.insert(p.raw(), ContractAssignmentValue::Unassigned);
            vals.insert(n.raw(), ContractAssignmentValue::Unassigned);
        }
        Self {
            clauses: Vec::new(),
            vals,
            trail: Vec::new(),
            qhead: 0,
        }
    }
    pub(crate) fn add_clause(&mut self, clause: Vec<ContractLiteral>) {
        self.clauses.push(clause);
    }
    pub(crate) fn assign(&mut self, lit: ContractLiteral) {
        self.vals.insert(lit.raw(), ContractAssignmentValue::True);
        self.vals
            .insert(lit.negated().raw(), ContractAssignmentValue::False);
        self.trail.push(lit);
    }
    #[must_use]
    pub(crate) fn lit_value(&self, lit: ContractLiteral) -> ContractAssignmentValue {
        self.vals
            .get(&lit.raw())
            .copied()
            .unwrap_or(ContractAssignmentValue::Unassigned)
    }
}

impl BcpPropagation for ReferenceBcp {
    fn snapshot(&self) -> PropagationSnapshot {
        PropagationSnapshot {
            trail_before: Vec::new(),
            trail_after: self.trail.clone(),
            qhead_before: 0,
            qhead_after: self.qhead,
            clauses: self.clauses.clone(),
            assignment: self.vals.clone(),
            conflict: None,
        }
    }
    fn propagate(&mut self) -> PropagationSnapshot {
        let trail_before = self.trail.clone();
        let qhead_before = self.qhead;
        // Naive BCP: scan all clauses, assign one unit literal, re-scan.
        // Returns immediately on conflict (all literals false in a clause).
        'outer: loop {
            let num_clauses = self.clauses.len();
            for ci in 0..num_clauses {
                let clause = &self.clauses[ci];
                let mut fc = 0;
                let mut uc = 0;
                let mut last_u = None;
                let mut sat = false;
                for &l in clause {
                    match self.lit_value(l) {
                        ContractAssignmentValue::True => {
                            sat = true;
                            break;
                        }
                        ContractAssignmentValue::False => {
                            fc += 1;
                        }
                        ContractAssignmentValue::Unassigned => {
                            uc += 1;
                            last_u = Some(l);
                        }
                    }
                }
                if sat {
                    continue;
                }
                if uc == 0 && fc == clause.len() {
                    self.qhead = self.trail.len();
                    return PropagationSnapshot {
                        trail_before,
                        trail_after: self.trail.clone(),
                        qhead_before,
                        qhead_after: self.qhead,
                        clauses: self.clauses.clone(),
                        assignment: self.vals.clone(),
                        conflict: Some(ContractClauseRef(u32::try_from(ci).unwrap_or(u32::MAX))),
                    };
                }
                if let (1, Some(lit)) = (uc, last_u) {
                    if self.lit_value(lit) == ContractAssignmentValue::Unassigned {
                        self.assign(lit);
                        continue 'outer;
                    }
                }
            }
            // No unit clause found — fixpoint reached.
            break;
        }
        self.qhead = self.trail.len();
        PropagationSnapshot {
            trail_before,
            trail_after: self.trail.clone(),
            qhead_before,
            qhead_after: self.qhead,
            clauses: self.clauses.clone(),
            assignment: self.vals.clone(),
            conflict: None,
        }
    }
}

pub(crate) struct ReferenceDecision {
    level: u32,
    pub(crate) trail: Vec<ContractLiteral>,
    assigned_vars: HashSet<u32>,
    removed_vars: HashSet<u32>,
    num_vars: u32,
    qhead: usize,
}

impl ReferenceDecision {
    #[must_use]
    pub(crate) fn new(num_vars: u32) -> Self {
        Self {
            level: 0,
            trail: Vec::new(),
            assigned_vars: HashSet::new(),
            removed_vars: HashSet::new(),
            num_vars,
            qhead: 0,
        }
    }
    pub(crate) fn remove_var(&mut self, v: u32) {
        self.removed_vars.insert(v);
    }
    pub(crate) fn assign_propagated(&mut self, lit: ContractLiteral) {
        self.assigned_vars.insert(lit.variable().0);
        self.trail.push(lit);
        self.qhead = self.trail.len();
    }
    pub(crate) fn set_qhead(&mut self, q: usize) {
        self.qhead = q;
    }
}

impl DecisionOperation for ReferenceDecision {
    fn decide(&mut self, lit: ContractLiteral) -> DecisionSnapshot {
        let lb = self.level;
        let tb = self.trail.len();
        let ab = self.assigned_vars.clone();
        self.level += 1;
        self.trail.push(lit);
        self.assigned_vars.insert(lit.variable().0);
        DecisionSnapshot {
            level_before: lb,
            level_after: self.level,
            decision_literal: lit,
            trail_len_before: tb,
            trail_len_after: self.trail.len(),
            assigned_vars_before: ab,
            removed_vars: self.removed_vars.clone(),
            num_vars: self.num_vars,
            qhead_at_decision: self.qhead,
        }
    }
}

/// Registers the BCP propagation contract as an extern_spec entry.
pub(crate) fn register_ay_propagation_contract() {
    crate::extern_spec_verify::register_extern_spec(
        "ay_sat::Solver::propagate_bcp",
        &["self.qhead <= self.trail.len()".to_string()],
        &[
            "result.is_none() ==> self.qhead == self.trail.len()".to_string(),
            "result.is_some() ==> all_false(clause_lits, &self.vals)".to_string(),
            "self.trail.len() >= old(self.trail.len())".to_string(),
        ],
    );
}

/// Registers the decision contract as an extern_spec entry.
pub(crate) fn register_ay_decision_contract() {
    crate::extern_spec_verify::register_extern_spec(
        "ay_sat::Solver::decide",
        &[
            "self.qhead == self.trail.len()".to_string(),
            "!self.var_lifecycle.is_removed(lit.variable().index())".to_string(),
        ],
        &[
            "self.decision_level == old(self.decision_level) + 1".to_string(),
            "self.trail.len() == old(self.trail.len()) + 1".to_string(),
        ],
    );
}
