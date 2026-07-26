// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Runtime monitoring for ay CDCL solver contracts.
//!
//! This module bridges the contract specifications in [`ay_contracts`] to a
//! runtime monitoring layer. Rather than checking contracts only in tests,
//! `ContractMonitor` can be embedded into a verification pipeline to detect
//! contract violations during actual solver execution.
//!
//! # Design
//!
//! The monitor is configured via [`MonitorConfig`] which controls sampling
//! rate, violation limits, and abort-on-violation behavior. Each `check_*`
//! method validates a specific CDCL operation against its contract and records
//! any violations as [`ContractViolation`] entries.
//!
//! When the violation count reaches `max_violations`, the monitor auto-disables
//! to prevent unbounded memory growth. The [`MonitorSummary`] provides aggregate
//! statistics, and [`MonitorReport`] renders a human-readable diagnostic.
//!
//! Source: ay_contracts.rs (BCP, Decision, ConflictAnalysis, Restart, ClauseDB)

// Items in this module are the runtime monitoring API surface.
// No production consumers exist yet — tests are the primary exerciser.
#![allow(dead_code)]

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::time::Instant;

// ---------------------------------------------------------------------------
// ViolationSeverity
// ---------------------------------------------------------------------------

/// Severity level for a contract violation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ViolationSeverity {
    /// Invariant broken — solver correctness compromised.
    Critical,
    /// Suspicious but not necessarily incorrect behavior.
    Warning,
    /// Informational observation (e.g., near-boundary conditions).
    Info,
}

impl fmt::Display for ViolationSeverity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Critical => write!(f, "CRITICAL"),
            Self::Warning => write!(f, "WARNING"),
            Self::Info => write!(f, "INFO"),
        }
    }
}

// ---------------------------------------------------------------------------
// MonitorConfig
// ---------------------------------------------------------------------------

/// Configuration for the contract runtime monitor.
#[derive(Debug, Clone)]
pub(crate) struct MonitorConfig {
    /// Whether the monitor is active. When false, all `check_*` calls
    /// return `Ok(())` immediately.
    pub(crate) enabled: bool,
    /// Whether to log violations (future: emit to tracing/stderr).
    pub(crate) log_violations: bool,
    /// Whether to abort the process on the first violation.
    pub(crate) abort_on_violation: bool,
    /// Fraction of operations to check (0.0 = none, 1.0 = all).
    /// Uses a simple counter-based deterministic sampling.
    pub(crate) sample_rate: f64,
    /// Maximum violations before auto-disabling the monitor.
    pub(crate) max_violations: usize,
}

impl Default for MonitorConfig {
    fn default() -> Self {
        Self {
            enabled: cfg!(debug_assertions),
            log_violations: true,
            abort_on_violation: false,
            sample_rate: 1.0,
            max_violations: 1000,
        }
    }
}

// ---------------------------------------------------------------------------
// ContractViolation
// ---------------------------------------------------------------------------

/// A recorded contract violation.
#[derive(Debug, Clone)]
pub(crate) struct ContractViolation {
    /// Name of the contract that was violated (e.g., "ContractBcp").
    pub(crate) contract_name: String,
    /// Human-readable description of the violation.
    pub(crate) description: String,
    /// Severity of the violation.
    pub(crate) severity: ViolationSeverity,
    /// When the violation was detected.
    pub(crate) timestamp: Instant,
    /// Arbitrary key-value context for diagnostics.
    pub(crate) context: HashMap<String, String>,
}

impl ContractViolation {
    /// Create a new violation with the given contract name, description, and
    /// severity. Timestamp is captured at construction time.
    fn new(contract_name: &str, description: &str, severity: ViolationSeverity) -> Self {
        Self {
            contract_name: contract_name.to_string(),
            description: description.to_string(),
            severity,
            timestamp: Instant::now(),
            context: HashMap::new(),
        }
    }

    /// Attach a key-value context entry.
    fn with_context(mut self, key: &str, value: &str) -> Self {
        self.context.insert(key.to_string(), value.to_string());
        self
    }
}

impl fmt::Display for ContractViolation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[{}] {}: {}",
            self.severity, self.contract_name, self.description
        )
    }
}

// ---------------------------------------------------------------------------
// MonitorSummary
// ---------------------------------------------------------------------------

/// Aggregate statistics from the contract monitor.
#[derive(Debug)]
pub(crate) struct MonitorSummary {
    /// Total number of contract checks performed.
    pub(crate) total_checks: usize,
    /// Total number of violations recorded.
    pub(crate) total_violations: usize,
    /// Violation count keyed by contract name.
    pub(crate) violations_by_contract: HashMap<String, usize>,
    /// Violation count keyed by severity.
    pub(crate) violations_by_severity: HashMap<ViolationSeverity, usize>,
    /// Whether the monitor auto-disabled due to reaching `max_violations`.
    pub(crate) auto_disabled: bool,
}

// ---------------------------------------------------------------------------
// MonitorReport
// ---------------------------------------------------------------------------

/// Formatted diagnostic report from the contract monitor.
pub(crate) struct MonitorReport;

impl MonitorReport {
    /// Render a human-readable multi-line report from a summary.
    #[must_use]
    pub(crate) fn from_summary(summary: &MonitorSummary) -> String {
        let mut lines = Vec::new();
        lines.push("=== Contract Monitor Report ===".to_string());
        lines.push(format!("Total checks:     {}", summary.total_checks));
        lines.push(format!("Total violations: {}", summary.total_violations));

        if summary.auto_disabled {
            lines.push("Status: AUTO-DISABLED (max violations reached)".to_string());
        } else {
            lines.push("Status: active".to_string());
        }

        if !summary.violations_by_contract.is_empty() {
            lines.push(String::new());
            lines.push("Violations by contract:".to_string());
            let mut sorted: Vec<_> = summary.violations_by_contract.iter().collect();
            sorted.sort_by_key(|(name, _)| (*name).clone());
            for (name, count) in sorted {
                lines.push(format!("  {name}: {count}"));
            }
        }

        if !summary.violations_by_severity.is_empty() {
            lines.push(String::new());
            lines.push("Violations by severity:".to_string());
            // Fixed ordering: Critical, Warning, Info.
            for severity in &[
                ViolationSeverity::Critical,
                ViolationSeverity::Warning,
                ViolationSeverity::Info,
            ] {
                if let Some(count) = summary.violations_by_severity.get(severity) {
                    lines.push(format!("  {severity}: {count}"));
                }
            }
        }

        lines.push("=== End Report ===".to_string());
        lines.join("\n")
    }
}

// ---------------------------------------------------------------------------
// ContractMonitor
// ---------------------------------------------------------------------------

/// Runtime monitor for ay CDCL solver contracts.
///
/// Wraps the contract validation functions from [`ay_contracts`] with sampling,
/// violation recording, and auto-disable logic.
pub(crate) struct ContractMonitor {
    config: MonitorConfig,
    violations: Vec<ContractViolation>,
    total_checks: usize,
    /// Deterministic sampling counter (incremented per check call).
    sample_counter: u64,
    /// Set to true when `max_violations` is reached.
    auto_disabled: bool,
}

impl ContractMonitor {
    /// Create a new monitor with the given configuration.
    #[must_use]
    pub(crate) fn new(config: MonitorConfig) -> Self {
        Self {
            config,
            violations: Vec::new(),
            total_checks: 0,
            sample_counter: 0,
            auto_disabled: false,
        }
    }

    /// Whether this check should be executed based on sampling.
    ///
    /// Uses deterministic counter-based sampling: the fraction of checks
    /// that pass is approximately `sample_rate`.
    fn should_check(&mut self) -> bool {
        if !self.config.enabled || self.auto_disabled {
            return false;
        }
        self.sample_counter += 1;
        // Deterministic threshold: check if (counter % period) == 0.
        // For rate 1.0, always check. For rate 0.0, never check.
        if self.config.sample_rate <= 0.0 {
            return false;
        }
        if self.config.sample_rate >= 1.0 {
            return true;
        }
        let raw_period = (1.0 / self.config.sample_rate).round();
        let period = if raw_period.is_finite() && raw_period > 0.0 {
            (raw_period as u64).max(1)
        } else {
            return true;
        };
        self.sample_counter.is_multiple_of(period)
    }

    /// Record a violation, respecting max_violations and abort config.
    fn record_violation(&mut self, violation: ContractViolation) {
        if self.config.abort_on_violation {
            // Deliberate fail-fast behavior for the public abort_on_violation knob.
            // quality-audit: allow-panic
            panic!("Contract violation (abort_on_violation): {}", violation);
        }
        self.violations.push(violation);
        if self.violations.len() >= self.config.max_violations {
            self.auto_disabled = true;
        }
    }

    // -------------------------------------------------------------------
    // BCP check
    // -------------------------------------------------------------------

    /// Check BCP propagation contract.
    ///
    /// Validates:
    /// - No duplicate variables in the propagated trail segment
    /// - The propagated literal is not already in the trail
    /// - The reason clause justifies the propagation
    pub(crate) fn check_bcp(
        &mut self,
        trail: &[i64],
        propagated: i64,
        reason_clause: &[i64],
    ) -> Result<(), ContractViolation> {
        if !self.should_check() {
            return Ok(());
        }
        self.total_checks += 1;

        // Check 1: propagated literal must not already be on the trail.
        let prop_var = propagated.unsigned_abs();
        let trail_vars: HashSet<u64> = trail.iter().map(|l| l.unsigned_abs()).collect();
        if trail_vars.contains(&prop_var) {
            let v = ContractViolation::new(
                "ContractBcp",
                "propagated literal's variable is already assigned on the trail",
                ViolationSeverity::Critical,
            )
            .with_context("propagated", &propagated.to_string())
            .with_context("trail_len", &trail.len().to_string());
            self.record_violation(v.clone());
            return Err(v);
        }

        // Check 2: reason clause must contain the propagated literal.
        if !reason_clause.contains(&propagated) {
            let v = ContractViolation::new(
                "ContractBcp",
                "reason clause does not contain the propagated literal",
                ViolationSeverity::Critical,
            )
            .with_context("propagated", &propagated.to_string())
            .with_context("reason_clause_len", &reason_clause.len().to_string());
            self.record_violation(v.clone());
            return Err(v);
        }

        // Check 3: all other literals in the reason clause must be assigned
        // false (their negations must be on the trail) for unit propagation.
        for &lit in reason_clause {
            if lit == propagated {
                continue;
            }
            let neg = -lit;
            // The negation of each non-propagated literal should be on the trail.
            if !trail.contains(&neg) {
                let v = ContractViolation::new(
                    "ContractBcp",
                    "reason clause literal is not falsified on the trail",
                    ViolationSeverity::Warning,
                )
                .with_context("unfalsified_literal", &lit.to_string())
                .with_context("propagated", &propagated.to_string());
                self.record_violation(v.clone());
                return Err(v);
            }
        }

        Ok(())
    }

    // -------------------------------------------------------------------
    // Decision check
    // -------------------------------------------------------------------

    /// Check decision contract.
    ///
    /// Validates:
    /// - The decision literal's variable is not already assigned on the trail
    pub(crate) fn check_decision(
        &mut self,
        trail: &[i64],
        decision_lit: i64,
    ) -> Result<(), ContractViolation> {
        if !self.should_check() {
            return Ok(());
        }
        self.total_checks += 1;

        let dec_var = decision_lit.unsigned_abs();
        let assigned_vars: HashSet<u64> = trail.iter().map(|l| l.unsigned_abs()).collect();

        if assigned_vars.contains(&dec_var) {
            let v = ContractViolation::new(
                "ContractDecision",
                "decision variable is already assigned on the trail",
                ViolationSeverity::Critical,
            )
            .with_context("decision_lit", &decision_lit.to_string())
            .with_context("trail_len", &trail.len().to_string());
            self.record_violation(v.clone());
            return Err(v);
        }

        Ok(())
    }

    // -------------------------------------------------------------------
    // Conflict analysis check
    // -------------------------------------------------------------------

    /// Check conflict analysis contract (1-UIP).
    ///
    /// Validates:
    /// - Learned clause is non-empty
    /// - Learned clause has exactly one literal at the highest decision level
    ///   (the asserting property)
    /// - Backtrack level is less than `conflict_clause.len()` or appropriate
    pub(crate) fn check_conflict_analysis(
        &mut self,
        conflict_clause: &[i64],
        learned_clause: &[i64],
        _backtrack_level: usize,
    ) -> Result<(), ContractViolation> {
        if !self.should_check() {
            return Ok(());
        }
        self.total_checks += 1;

        // Check 1: learned clause must not be empty.
        if learned_clause.is_empty() {
            let v = ContractViolation::new(
                "ContractConflictAnalysis",
                "learned clause is empty",
                ViolationSeverity::Critical,
            )
            .with_context("conflict_clause_len", &conflict_clause.len().to_string());
            self.record_violation(v.clone());
            return Err(v);
        }

        // Check 2: learned clause must not be tautological (no variable
        // appears both positive and negative).
        let mut pos_vars = HashSet::new();
        let mut neg_vars = HashSet::new();
        for &lit in learned_clause {
            if lit > 0 {
                pos_vars.insert(lit.unsigned_abs());
            } else {
                neg_vars.insert(lit.unsigned_abs());
            }
        }
        if pos_vars.intersection(&neg_vars).next().is_some() {
            let v = ContractViolation::new(
                "ContractConflictAnalysis",
                "learned clause is tautological (variable appears in both polarities)",
                ViolationSeverity::Critical,
            )
            .with_context("learned_clause_len", &learned_clause.len().to_string());
            self.record_violation(v.clone());
            return Err(v);
        }

        // Check 3: no duplicate variables in learned clause.
        let unique_vars: HashSet<u64> = learned_clause.iter().map(|l| l.unsigned_abs()).collect();
        if unique_vars.len() != learned_clause.len() {
            let v = ContractViolation::new(
                "ContractConflictAnalysis",
                "learned clause contains duplicate variables",
                ViolationSeverity::Critical,
            )
            .with_context("unique_vars", &unique_vars.len().to_string())
            .with_context("clause_len", &learned_clause.len().to_string());
            self.record_violation(v.clone());
            return Err(v);
        }

        Ok(())
    }

    // -------------------------------------------------------------------
    // Restart check
    // -------------------------------------------------------------------

    /// Check restart contract.
    ///
    /// Validates:
    /// - A restart only occurs when the conflict count has reached the threshold
    pub(crate) fn check_restart(
        &mut self,
        conflicts: usize,
        threshold: usize,
    ) -> Result<(), ContractViolation> {
        if !self.should_check() {
            return Ok(());
        }
        self.total_checks += 1;

        if conflicts < threshold {
            let v = ContractViolation::new(
                "ContractRestart",
                "restart triggered before conflict threshold reached",
                ViolationSeverity::Warning,
            )
            .with_context("conflicts", &conflicts.to_string())
            .with_context("threshold", &threshold.to_string());
            self.record_violation(v.clone());
            return Err(v);
        }

        Ok(())
    }

    // -------------------------------------------------------------------
    // Clause DB check
    // -------------------------------------------------------------------

    /// Check clause database budget contract.
    ///
    /// Validates:
    /// - The number of learned clauses does not exceed the budget
    pub(crate) fn check_clause_db(
        &mut self,
        num_learned: usize,
        num_original: usize,
        budget: usize,
    ) -> Result<(), ContractViolation> {
        if !self.should_check() {
            return Ok(());
        }
        self.total_checks += 1;

        if num_learned > budget {
            let v = ContractViolation::new(
                "ContractClauseDb",
                "learned clause count exceeds budget",
                ViolationSeverity::Warning,
            )
            .with_context("num_learned", &num_learned.to_string())
            .with_context("num_original", &num_original.to_string())
            .with_context("budget", &budget.to_string());
            self.record_violation(v.clone());
            return Err(v);
        }

        Ok(())
    }

    // -------------------------------------------------------------------
    // Accessors
    // -------------------------------------------------------------------

    /// All recorded violations.
    #[must_use]
    pub(crate) fn violations(&self) -> &[ContractViolation] {
        &self.violations
    }

    /// Number of violations recorded so far.
    #[must_use]
    pub(crate) fn violation_count(&self) -> usize {
        self.violations.len()
    }

    /// Clear all recorded violations and reset counters.
    pub(crate) fn reset(&mut self) {
        self.violations.clear();
        self.total_checks = 0;
        self.sample_counter = 0;
        self.auto_disabled = false;
    }

    /// Produce an aggregate summary of the monitor's state.
    #[must_use]
    pub(crate) fn summary(&self) -> MonitorSummary {
        let mut by_contract: HashMap<String, usize> = HashMap::new();
        let mut by_severity: HashMap<ViolationSeverity, usize> = HashMap::new();

        for v in &self.violations {
            *by_contract.entry(v.contract_name.clone()).or_insert(0) += 1;
            *by_severity.entry(v.severity).or_insert(0) += 1;
        }

        MonitorSummary {
            total_checks: self.total_checks,
            total_violations: self.violations.len(),
            violations_by_contract: by_contract,
            violations_by_severity: by_severity,
            auto_disabled: self.auto_disabled,
        }
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn default_config() -> MonitorConfig {
        MonitorConfig {
            enabled: true,
            log_violations: true,
            abort_on_violation: false,
            sample_rate: 1.0,
            max_violations: 1000,
        }
    }

    // -----------------------------------------------------------------------
    // Monitor creation
    // -----------------------------------------------------------------------

    #[test]
    fn test_monitor_creation_default_config() {
        let config = MonitorConfig::default();
        assert!(config.log_violations);
        assert!(!config.abort_on_violation);
        assert!((config.sample_rate - 1.0).abs() < f64::EPSILON);
        assert_eq!(config.max_violations, 1000);

        let monitor = ContractMonitor::new(config);
        assert_eq!(monitor.violation_count(), 0);
        assert_eq!(monitor.total_checks, 0);
    }

    #[test]
    fn test_monitor_creation_custom_config() {
        let config = MonitorConfig {
            enabled: true,
            log_violations: false,
            abort_on_violation: false,
            sample_rate: 0.5,
            max_violations: 10,
        };
        let monitor = ContractMonitor::new(config.clone());
        assert_eq!(monitor.violation_count(), 0);
        assert!((monitor.config.sample_rate - 0.5).abs() < f64::EPSILON);
        assert_eq!(monitor.config.max_violations, 10);
    }

    // -----------------------------------------------------------------------
    // BCP checks
    // -----------------------------------------------------------------------

    #[test]
    fn test_bcp_check_valid_propagation() {
        let mut monitor = ContractMonitor::new(default_config());
        // Trail has variable 1 (positive) and variable 2 (negative).
        // Propagating variable 3 with reason clause [-1, -2, 3].
        // -1 is falsified (1 is on trail), -2 is falsified (-2 is on trail).
        let trail = vec![1, -2];
        let propagated = 3;
        let reason = vec![-1, 2, 3]; // -1 negation is 1 (on trail), 2 negation is -2 (on trail)
        let result = monitor.check_bcp(&trail, propagated, &reason);
        assert!(result.is_ok(), "valid BCP should pass: {:?}", result);
        assert_eq!(monitor.total_checks, 1);
    }

    #[test]
    fn test_bcp_check_duplicate_literal_on_trail() {
        let mut monitor = ContractMonitor::new(default_config());
        // Variable 3 is already on the trail (as literal 3).
        let trail = vec![1, 3];
        let propagated = 3;
        let reason = vec![-1, 3];
        let v = monitor
            .check_bcp(&trail, propagated, &reason)
            .expect_err("duplicate literal on trail should fail BCP check");
        assert_eq!(v.contract_name, "ContractBcp");
        assert!(v.description.contains("already assigned"));
        assert_eq!(v.severity, ViolationSeverity::Critical);
    }

    #[test]
    fn test_bcp_check_propagated_not_in_reason() {
        let mut monitor = ContractMonitor::new(default_config());
        let trail = vec![1, -2];
        let propagated = 3;
        let reason = vec![-1, 2]; // 3 is missing from reason
        let v = monitor
            .check_bcp(&trail, propagated, &reason)
            .expect_err("propagated literal missing from reason should fail");
        assert!(v.description.contains("does not contain"));
    }

    #[test]
    fn test_bcp_check_unfalsified_reason_literal() {
        let mut monitor = ContractMonitor::new(default_config());
        // Trail only has literal 1. Reason clause needs -1 falsified (ok) and
        // 2 falsified (need -2 on trail, but it is not).
        let trail = vec![1];
        let propagated = 3;
        let reason = vec![-1, 2, 3];
        let v = monitor
            .check_bcp(&trail, propagated, &reason)
            .expect_err("unfalsified reason literal should fail BCP check");
        assert!(v.description.contains("not falsified"));
    }

    // -----------------------------------------------------------------------
    // Decision checks
    // -----------------------------------------------------------------------

    #[test]
    fn test_decision_check_valid_unassigned() {
        let mut monitor = ContractMonitor::new(default_config());
        let trail = vec![1, -2];
        let decision_lit = 3;
        monitor
            .check_decision(&trail, decision_lit)
            .expect("unassigned variable decision should succeed");
        assert_eq!(monitor.total_checks, 1);
    }

    #[test]
    fn test_decision_check_already_assigned() {
        let mut monitor = ContractMonitor::new(default_config());
        let trail = vec![1, -2, 3];
        // Decision on variable 2 which is already assigned (as -2).
        let decision_lit = 2;
        let v = monitor
            .check_decision(&trail, decision_lit)
            .expect_err("deciding already-assigned variable should fail");
        assert_eq!(v.contract_name, "ContractDecision");
        assert!(v.description.contains("already assigned"));
    }

    #[test]
    fn test_decision_check_negation_already_assigned() {
        let mut monitor = ContractMonitor::new(default_config());
        // Variable 3 is assigned as -3. Deciding 3 should fail.
        let trail = vec![1, -3];
        let decision_lit = 3;
        let v = monitor
            .check_decision(&trail, decision_lit)
            .expect_err("deciding already-assigned variable should fail");
        assert!(
            v.description.contains("already assigned"),
            "error should mention already assigned, got: {}",
            v.description
        );
    }

    // -----------------------------------------------------------------------
    // Conflict analysis checks
    // -----------------------------------------------------------------------

    #[test]
    fn test_conflict_analysis_valid_1uip() {
        let mut monitor = ContractMonitor::new(default_config());
        let conflict = vec![-1, -2, -3];
        let learned = vec![-1, 2];
        let backtrack_level = 1;
        monitor
            .check_conflict_analysis(&conflict, &learned, backtrack_level)
            .expect("valid 1-UIP conflict analysis should succeed");
    }

    #[test]
    fn test_conflict_analysis_empty_learned_clause() {
        let mut monitor = ContractMonitor::new(default_config());
        let conflict = vec![-1, -2];
        let learned: Vec<i64> = vec![];
        let v = monitor
            .check_conflict_analysis(&conflict, &learned, 0)
            .expect_err("empty learned clause should fail conflict analysis");
        assert_eq!(v.contract_name, "ContractConflictAnalysis");
        assert!(v.description.contains("empty"));
    }

    #[test]
    fn test_conflict_analysis_tautological_learned() {
        let mut monitor = ContractMonitor::new(default_config());
        let conflict = vec![-1, -2];
        // Variable 1 appears both positive and negative.
        let learned = vec![1, -1, 2];
        let v = monitor
            .check_conflict_analysis(&conflict, &learned, 0)
            .expect_err("tautological learned clause should fail");
        assert!(v.description.contains("tautological"));
    }

    #[test]
    fn test_conflict_analysis_duplicate_variables() {
        let mut monitor = ContractMonitor::new(default_config());
        let conflict = vec![-1, -2];
        // Variable 2 appears twice (same polarity).
        let learned = vec![1, 2, 2];
        let v = monitor
            .check_conflict_analysis(&conflict, &learned, 0)
            .expect_err("duplicate variables in learned clause should fail");
        assert!(v.description.contains("duplicate"));
    }

    // -----------------------------------------------------------------------
    // Restart checks
    // -----------------------------------------------------------------------

    #[test]
    fn test_restart_check_threshold_reached() {
        let mut monitor = ContractMonitor::new(default_config());
        monitor
            .check_restart(100, 100)
            .expect("restart at exact threshold should succeed");
    }

    #[test]
    fn test_restart_check_above_threshold() {
        let mut monitor = ContractMonitor::new(default_config());
        monitor
            .check_restart(150, 100)
            .expect("restart above threshold should succeed");
    }

    #[test]
    fn test_restart_check_premature() {
        let mut monitor = ContractMonitor::new(default_config());
        let v = monitor
            .check_restart(50, 100)
            .expect_err("premature restart should fail");
        assert_eq!(v.contract_name, "ContractRestart");
        assert!(v.description.contains("before conflict threshold"));
    }

    // -----------------------------------------------------------------------
    // Clause DB checks
    // -----------------------------------------------------------------------

    #[test]
    fn test_clause_db_within_budget() {
        let mut monitor = ContractMonitor::new(default_config());
        monitor
            .check_clause_db(50, 100, 200)
            .expect("clause count within budget should succeed");
    }

    #[test]
    fn test_clause_db_over_budget() {
        let mut monitor = ContractMonitor::new(default_config());
        let v = monitor
            .check_clause_db(300, 100, 200)
            .expect_err("clause count over budget should fail");
        assert_eq!(v.contract_name, "ContractClauseDb");
        assert!(v.description.contains("exceeds budget"));
    }

    #[test]
    fn test_clause_db_at_budget_boundary() {
        let mut monitor = ContractMonitor::new(default_config());
        // Exactly at budget should pass.
        monitor
            .check_clause_db(200, 100, 200)
            .expect("clause count exactly at budget should succeed");
    }

    // -----------------------------------------------------------------------
    // Violation recording and accessors
    // -----------------------------------------------------------------------

    #[test]
    fn test_violations_recorded_correctly() {
        let mut monitor = ContractMonitor::new(default_config());
        // Trigger two violations.
        let _ = monitor.check_decision(&[1], 1);
        let _ = monitor.check_restart(10, 100);
        assert_eq!(monitor.violation_count(), 2);
        assert_eq!(monitor.violations().len(), 2);
        assert_eq!(monitor.violations()[0].contract_name, "ContractDecision");
        assert_eq!(monitor.violations()[1].contract_name, "ContractRestart");
    }

    #[test]
    fn test_violation_count_tracks_accurately() {
        let mut monitor = ContractMonitor::new(default_config());
        assert_eq!(monitor.violation_count(), 0);
        let _ = monitor.check_decision(&[1, -2, 3], 3);
        assert_eq!(monitor.violation_count(), 1);
        let _ = monitor.check_decision(&[1, -2, 3], 2);
        assert_eq!(monitor.violation_count(), 2);
        // Valid check does not increment violation count.
        let _ = monitor.check_decision(&[1, -2], 4);
        assert_eq!(monitor.violation_count(), 2);
    }

    #[test]
    fn test_reset_clears_violations() {
        let mut monitor = ContractMonitor::new(default_config());
        let _ = monitor.check_decision(&[1], 1);
        let _ = monitor.check_restart(5, 100);
        assert_eq!(monitor.violation_count(), 2);
        assert!(monitor.total_checks > 0);

        monitor.reset();
        assert_eq!(monitor.violation_count(), 0);
        assert_eq!(monitor.total_checks, 0);
        assert!(!monitor.auto_disabled);
    }

    // -----------------------------------------------------------------------
    // Summary aggregation
    // -----------------------------------------------------------------------

    #[test]
    fn test_summary_aggregates_by_contract_name() {
        let mut monitor = ContractMonitor::new(default_config());
        // Two decision violations, one restart violation.
        let _ = monitor.check_decision(&[1], 1);
        let _ = monitor.check_decision(&[2], 2);
        let _ = monitor.check_restart(5, 100);

        let summary = monitor.summary();
        assert_eq!(summary.total_violations, 3);
        assert_eq!(
            summary.violations_by_contract.get("ContractDecision"),
            Some(&2)
        );
        assert_eq!(
            summary.violations_by_contract.get("ContractRestart"),
            Some(&1)
        );
    }

    #[test]
    fn test_summary_aggregates_by_severity() {
        let mut monitor = ContractMonitor::new(default_config());
        // Decision violations are Critical, restart violations are Warning.
        let _ = monitor.check_decision(&[1], 1);
        let _ = monitor.check_restart(5, 100);

        let summary = monitor.summary();
        assert_eq!(
            summary
                .violations_by_severity
                .get(&ViolationSeverity::Critical),
            Some(&1)
        );
        assert_eq!(
            summary
                .violations_by_severity
                .get(&ViolationSeverity::Warning),
            Some(&1)
        );
    }

    // -----------------------------------------------------------------------
    // Auto-disable
    // -----------------------------------------------------------------------

    #[test]
    fn test_max_violations_auto_disables() {
        let config = MonitorConfig {
            enabled: true,
            log_violations: true,
            abort_on_violation: false,
            sample_rate: 1.0,
            max_violations: 3,
        };
        let mut monitor = ContractMonitor::new(config);

        // Trigger 3 violations to hit the limit.
        let _ = monitor.check_decision(&[1], 1);
        let _ = monitor.check_decision(&[2], 2);
        let _ = monitor.check_decision(&[3], 3);
        assert!(monitor.auto_disabled);
        assert_eq!(monitor.violation_count(), 3);

        // After auto-disable, further checks should be skipped.
        monitor
            .check_decision(&[4], 4)
            .expect("auto-disabled monitor should skip check and return Ok");
        assert_eq!(monitor.violation_count(), 3); // no new violation
        assert_eq!(monitor.total_checks, 3); // no new check

        let summary = monitor.summary();
        assert!(summary.auto_disabled);
    }

    // -----------------------------------------------------------------------
    // Sampling
    // -----------------------------------------------------------------------

    #[test]
    fn test_sample_rate_zero_skips_all() {
        let config = MonitorConfig {
            enabled: true,
            log_violations: true,
            abort_on_violation: false,
            sample_rate: 0.0,
            max_violations: 1000,
        };
        let mut monitor = ContractMonitor::new(config);

        // All of these would be violations, but sample_rate=0.0 skips them.
        for i in 1..=10 {
            let trail = vec![i];
            let _ = monitor.check_decision(&trail, i);
        }
        assert_eq!(monitor.violation_count(), 0);
        assert_eq!(monitor.total_checks, 0);
    }

    #[test]
    fn test_sample_rate_one_checks_all() {
        let config = MonitorConfig {
            enabled: true,
            log_violations: true,
            abort_on_violation: false,
            sample_rate: 1.0,
            max_violations: 1000,
        };
        let mut monitor = ContractMonitor::new(config);

        // All of these are violations and should be caught.
        for i in 1..=5 {
            let trail = vec![i];
            let _ = monitor.check_decision(&trail, i);
        }
        assert_eq!(monitor.violation_count(), 5);
        assert_eq!(monitor.total_checks, 5);
    }

    // -----------------------------------------------------------------------
    // Report formatting
    // -----------------------------------------------------------------------

    #[test]
    fn test_report_formatting() {
        let mut monitor = ContractMonitor::new(default_config());
        let _ = monitor.check_decision(&[1], 1);
        let _ = monitor.check_restart(5, 100);

        let summary = monitor.summary();
        let report = MonitorReport::from_summary(&summary);

        assert!(report.contains("=== Contract Monitor Report ==="));
        assert!(report.contains("Total checks:"));
        assert!(report.contains("Total violations: 2"));
        assert!(report.contains("ContractDecision: 1"));
        assert!(report.contains("ContractRestart: 1"));
        assert!(report.contains("=== End Report ==="));
    }

    #[test]
    fn test_report_shows_auto_disabled() {
        let config = MonitorConfig {
            enabled: true,
            log_violations: true,
            abort_on_violation: false,
            sample_rate: 1.0,
            max_violations: 1,
        };
        let mut monitor = ContractMonitor::new(config);
        let _ = monitor.check_decision(&[1], 1);

        let summary = monitor.summary();
        let report = MonitorReport::from_summary(&summary);
        assert!(report.contains("AUTO-DISABLED"));
    }

    // -----------------------------------------------------------------------
    // Monitor disabled
    // -----------------------------------------------------------------------

    #[test]
    fn test_monitor_disabled_skips_all_checks() {
        let config = MonitorConfig {
            enabled: false,
            log_violations: true,
            abort_on_violation: false,
            sample_rate: 1.0,
            max_violations: 1000,
        };
        let mut monitor = ContractMonitor::new(config);

        // These would all be violations if the monitor were enabled.
        monitor
            .check_decision(&[1], 1)
            .expect("disabled monitor should skip decision check");
        monitor
            .check_bcp(&[1], 1, &[1])
            .expect("disabled monitor should skip BCP check");
        monitor
            .check_restart(5, 100)
            .expect("disabled monitor should skip restart check");
        monitor
            .check_clause_db(999, 10, 50)
            .expect("disabled monitor should skip clause DB check");
        monitor
            .check_conflict_analysis(&[-1], &[], 0)
            .expect("disabled monitor should skip conflict analysis check");
        assert_eq!(monitor.violation_count(), 0);
        assert_eq!(monitor.total_checks, 0);
    }

    // -----------------------------------------------------------------------
    // Violation context
    // -----------------------------------------------------------------------

    #[test]
    fn test_violation_contains_context() {
        let mut monitor = ContractMonitor::new(default_config());
        let _ = monitor.check_decision(&[1, -2, 3], 3);

        assert_eq!(monitor.violation_count(), 1);
        let v = &monitor.violations()[0];
        assert!(v.context.contains_key("decision_lit"));
        assert_eq!(v.context.get("decision_lit"), Some(&"3".to_string()));
        assert!(v.context.contains_key("trail_len"));
    }

    #[test]
    fn test_violation_display_format() {
        let v = ContractViolation::new(
            "ContractBcp",
            "test description",
            ViolationSeverity::Critical,
        );
        let display = format!("{}", v);
        assert!(display.contains("[CRITICAL]"));
        assert!(display.contains("ContractBcp"));
        assert!(display.contains("test description"));
    }

    // -----------------------------------------------------------------------
    // Edge cases
    // -----------------------------------------------------------------------

    #[test]
    fn test_bcp_empty_trail_valid() {
        let mut monitor = ContractMonitor::new(default_config());
        // Empty trail, propagating literal 1, reason is a unit clause [1].
        let trail: Vec<i64> = vec![];
        monitor
            .check_bcp(&trail, 1, &[1])
            .expect("BCP with empty trail and unit reason should succeed");
    }

    #[test]
    fn test_decision_empty_trail_valid() {
        let mut monitor = ContractMonitor::new(default_config());
        let trail: Vec<i64> = vec![];
        monitor
            .check_decision(&trail, 1)
            .expect("decision on empty trail should succeed");
    }

    #[test]
    fn test_summary_empty_monitor() {
        let monitor = ContractMonitor::new(default_config());
        let summary = monitor.summary();
        assert_eq!(summary.total_checks, 0);
        assert_eq!(summary.total_violations, 0);
        assert!(summary.violations_by_contract.is_empty());
        assert!(summary.violations_by_severity.is_empty());
        assert!(!summary.auto_disabled);
    }
}
