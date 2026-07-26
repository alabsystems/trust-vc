//! Solver statistics types for verification reports.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::BTreeMap;

use ay_dpll::api::SolveDetails;
use ay_dpll::{StatValue, Statistics};

/// Public copy of ay `StatValue`.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum SolverStatValue {
    Int(u64),
    Float(f64),
    String(String),
}

impl std::fmt::Display for SolverStatValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Int(value) => write!(f, "{value}"),
            Self::Float(value) => write!(f, "{value:.2}"),
            Self::String(value) => write!(f, "{value}"),
        }
    }
}

/// Public copy of solver statistics relevant to diagnostics.
#[derive(Debug, Clone, PartialEq)]
#[must_use]
pub struct SolverStats {
    pub(super) conflicts: u64,
    pub(super) decisions: u64,
    pub(super) propagations: u64,
    pub(super) restarts: u64,
    pub(super) learned_clauses: u64,
    pub(super) deleted_clauses: u64,
    pub(super) theory_conflicts: u64,
    pub(super) theory_propagations: u64,
    pub(super) num_vars: u64,
    pub(super) num_clauses: u64,
    pub(super) num_assertions: u64,
    pub(super) extra: BTreeMap<String, SolverStatValue>,
    pub(super) verification_level: String,
    pub(super) sat_model_validated: bool,
    pub(super) term_bytes: Option<usize>,
}

impl SolverStats {
    #[must_use]
    pub const fn conflicts(&self) -> u64 {
        self.conflicts
    }

    #[must_use]
    pub const fn decisions(&self) -> u64 {
        self.decisions
    }

    #[must_use]
    pub const fn propagations(&self) -> u64 {
        self.propagations
    }

    #[must_use]
    pub const fn restarts(&self) -> u64 {
        self.restarts
    }

    #[must_use]
    pub const fn learned_clauses(&self) -> u64 {
        self.learned_clauses
    }

    #[must_use]
    pub const fn deleted_clauses(&self) -> u64 {
        self.deleted_clauses
    }

    #[must_use]
    pub const fn theory_conflicts(&self) -> u64 {
        self.theory_conflicts
    }

    #[must_use]
    pub const fn theory_propagations(&self) -> u64 {
        self.theory_propagations
    }

    #[must_use]
    pub const fn num_vars(&self) -> u64 {
        self.num_vars
    }

    #[must_use]
    pub const fn num_clauses(&self) -> u64 {
        self.num_clauses
    }

    #[must_use]
    pub const fn num_assertions(&self) -> u64 {
        self.num_assertions
    }

    /// Returns additional solver statistics not captured by the fixed fields,
    /// keyed by the ay statistic name (e.g. `"quantifier.instantiations.total"`).
    #[must_use]
    pub fn extra(&self) -> &BTreeMap<String, SolverStatValue> {
        &self.extra
    }

    /// Returns the verification level label used for this solve
    /// (e.g. `"default"`, `"bv-mode"`, `"int-mode"`, `"debug-checked"`).
    #[must_use]
    pub fn verification_level(&self) -> &str {
        &self.verification_level
    }

    #[must_use]
    pub const fn sat_model_validated(&self) -> bool {
        self.sat_model_validated
    }

    #[must_use]
    pub const fn term_bytes(&self) -> Option<usize> {
        self.term_bytes
    }

    pub(crate) fn from_statistics(
        statistics: &Statistics,
        verification_level: String,
        sat_model_validated: bool,
        term_bytes: Option<usize>,
    ) -> Self {
        Self {
            conflicts: statistics.conflicts,
            decisions: statistics.decisions,
            propagations: statistics.propagations,
            restarts: statistics.restarts,
            learned_clauses: statistics.learned_clauses,
            deleted_clauses: statistics.deleted_clauses,
            theory_conflicts: statistics.theory_conflicts,
            theory_propagations: statistics.theory_propagations,
            num_vars: statistics.num_vars,
            num_clauses: statistics.num_clauses,
            num_assertions: statistics.num_assertions,
            extra: statistics
                .extra
                .iter()
                .map(|(name, value)| (name.clone(), solver_stat_value(value)))
                .collect(),
            verification_level,
            sat_model_validated,
            term_bytes,
        }
    }

    pub(crate) fn from_solve_details(details: &SolveDetails, term_bytes: Option<usize>) -> Self {
        Self::from_statistics(
            &details.statistics,
            details.verification_level.to_string(),
            details.verification.sat_model_validated,
            term_bytes,
        )
    }
}

fn solver_stat_value(value: &StatValue) -> SolverStatValue {
    match value {
        StatValue::Int(value) => SolverStatValue::Int(*value),
        StatValue::Float(value) => SolverStatValue::Float(*value),
        StatValue::String(value) => SolverStatValue::String(value.clone()),
        _ => SolverStatValue::String(value.to_string()),
    }
}
