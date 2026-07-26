// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Encoder instrumentation — integration layer between [`super::encoder`] and
//! [`super::monitor_hooks`].
//!
//! This module provides normalized solver event capture, per-function
//! instrumentation sessions, and a registry for tracking instrumentation
//! across multiple verification targets. Unlike `monitor_hooks` which validates
//! CDCL contract compliance, this module focuses on aggregate solver behavior
//! statistics and performance anomaly detection.
//!
//! # Overview
//!
//! [`InstrumentationConfig`] controls whether instrumentation is active, the
//! sampling rate, violation limits, and whether solver statistics are collected.
//! [`InstrumentationSession`] is instantiated per-function to capture
//! [`SolverEvent`] values and produce an [`InstrumentationReport`] at the end.
//! [`InstrumentationRegistry`] manages sessions across all functions in a
//! verification run and produces a [`GlobalInstrumentationReport`].
//!
//! Source: monitor_hooks.rs, encoder.rs

#![allow(dead_code)]

use std::collections::HashMap;
use std::fmt;

// ---------------------------------------------------------------------------
// InstrumentationConfig
// ---------------------------------------------------------------------------

/// Configuration for encoder instrumentation.
#[derive(Debug, Clone)]
pub(crate) struct InstrumentationConfig {
    /// Whether instrumentation is active. When false, events are discarded.
    pub(crate) monitoring_enabled: bool,
    /// Fraction of events to record (0.0 = none, 1.0 = all).
    /// Uses deterministic counter-based sampling.
    pub(crate) sample_rate: f64,
    /// Maximum violations per session before auto-disabling.
    pub(crate) max_violations: usize,
    /// Whether to collect aggregate solver statistics.
    pub(crate) collect_solver_stats: bool,
    /// Whether to log events to stderr.
    pub(crate) log_events: bool,
}

impl Default for InstrumentationConfig {
    fn default() -> Self {
        Self {
            monitoring_enabled: false,
            sample_rate: 0.01,
            max_violations: 100,
            collect_solver_stats: true,
            log_events: false,
        }
    }
}

// ---------------------------------------------------------------------------
// SolverEventType
// ---------------------------------------------------------------------------

/// Discriminant for normalized solver events.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum SolverEventType {
    /// Literal propagation step.
    Propagation { literals: usize },
    /// A branching decision was made.
    Decision { variable_id: u32, level: usize },
    /// A conflict was detected.
    Conflict {
        clause_size: usize,
        backjump_level: usize,
    },
    /// The solver triggered a restart.
    Restart { conflict_count: usize },
    /// A clause was learned.
    Learn { clause_size: usize },
    /// Clauses were forgotten (garbage collected).
    Forget { clause_count: usize },
}

impl SolverEventType {
    /// Short tag for aggregation keys.
    fn tag(&self) -> &'static str {
        match self {
            Self::Propagation { .. } => "Propagation",
            Self::Decision { .. } => "Decision",
            Self::Conflict { .. } => "Conflict",
            Self::Restart { .. } => "Restart",
            Self::Learn { .. } => "Learn",
            Self::Forget { .. } => "Forget",
        }
    }
}

impl fmt::Display for SolverEventType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Propagation { literals } => {
                write!(f, "Propagation(literals={literals})")
            }
            Self::Decision { variable_id, level } => {
                write!(f, "Decision(var={variable_id}, level={level})")
            }
            Self::Conflict {
                clause_size,
                backjump_level,
            } => write!(
                f,
                "Conflict(clause_size={clause_size}, backjump={backjump_level})"
            ),
            Self::Restart { conflict_count } => {
                write!(f, "Restart(conflicts={conflict_count})")
            }
            Self::Learn { clause_size } => write!(f, "Learn(size={clause_size})"),
            Self::Forget { clause_count } => {
                write!(f, "Forget(count={clause_count})")
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SolverEvent
// ---------------------------------------------------------------------------

/// A normalized solver event captured from ay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SolverEvent {
    /// The type and payload of this event.
    pub(crate) event_type: SolverEventType,
    /// Timestamp in nanoseconds (monotonic, relative to session start).
    pub(crate) timestamp_ns: u64,
    /// Name of the function being verified when this event occurred.
    pub(crate) function_name: String,
    /// Additional context string for diagnostics.
    pub(crate) context: String,
}

impl fmt::Display for SolverEvent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[{}ns] {} in {}: {}",
            self.timestamp_ns, self.event_type, self.function_name, self.context
        )
    }
}

// ---------------------------------------------------------------------------
// AlertSeverity
// ---------------------------------------------------------------------------

/// Severity level for an instrumentation alert.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum AlertSeverity {
    /// A critical issue that may compromise verification correctness.
    Critical,
    /// A suspicious condition worth investigating.
    Warning,
    /// Informational observation.
    Info,
}

impl fmt::Display for AlertSeverity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Critical => write!(f, "CRITICAL"),
            Self::Warning => write!(f, "WARNING"),
            Self::Info => write!(f, "INFO"),
        }
    }
}

// ---------------------------------------------------------------------------
// AlertType
// ---------------------------------------------------------------------------

/// Category of instrumentation alert.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum AlertType {
    /// A contract or invariant was violated.
    ContractViolation,
    /// A performance anomaly was detected (e.g., excessive restarts).
    PerformanceAnomaly,
    /// A resource limit was reached (e.g., max violations).
    ResourceLimit,
}

impl fmt::Display for AlertType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ContractViolation => write!(f, "ContractViolation"),
            Self::PerformanceAnomaly => write!(f, "PerformanceAnomaly"),
            Self::ResourceLimit => write!(f, "ResourceLimit"),
        }
    }
}

// ---------------------------------------------------------------------------
// InstrumentationAlert
// ---------------------------------------------------------------------------

/// An alert emitted during instrumentation.
#[derive(Debug, Clone)]
pub(crate) struct InstrumentationAlert {
    /// Category of this alert.
    pub(crate) alert_type: AlertType,
    /// Human-readable description.
    pub(crate) message: String,
    /// Severity level.
    pub(crate) severity: AlertSeverity,
}

impl fmt::Display for InstrumentationAlert {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[{}] {}: {}",
            self.severity, self.alert_type, self.message
        )
    }
}

// ---------------------------------------------------------------------------
// SolverRunStats
// ---------------------------------------------------------------------------

/// Aggregate solver behavior statistics for a single function verification.
#[derive(Debug, Clone)]
pub(crate) struct SolverRunStats {
    /// Total decision events.
    pub(crate) total_decisions: usize,
    /// Total conflict events.
    pub(crate) total_conflicts: usize,
    /// Total restart events.
    pub(crate) total_restarts: usize,
    /// Total propagation events.
    pub(crate) total_propagations: usize,
    /// Total learned clauses.
    pub(crate) learned_clauses: usize,
    /// Total forgotten clauses.
    pub(crate) forgotten_clauses: usize,
    /// Maximum decision level observed.
    pub(crate) max_decision_level: usize,
    /// Average conflict clause size (0.0 if no conflicts).
    pub(crate) avg_conflict_clause_size: f64,
}

impl Default for SolverRunStats {
    fn default() -> Self {
        Self {
            total_decisions: 0,
            total_conflicts: 0,
            total_restarts: 0,
            total_propagations: 0,
            learned_clauses: 0,
            forgotten_clauses: 0,
            max_decision_level: 0,
            avg_conflict_clause_size: 0.0,
        }
    }
}

impl SolverRunStats {
    /// Merge another stats instance into this one (additive).
    fn merge(&mut self, other: &SolverRunStats) {
        let prev_total = self.total_conflicts;
        self.total_decisions += other.total_decisions;
        self.total_conflicts += other.total_conflicts;
        self.total_restarts += other.total_restarts;
        self.total_propagations += other.total_propagations;
        self.learned_clauses += other.learned_clauses;
        self.forgotten_clauses += other.forgotten_clauses;
        if other.max_decision_level > self.max_decision_level {
            self.max_decision_level = other.max_decision_level;
        }
        // Weighted average of conflict clause sizes.
        let new_total = self.total_conflicts;
        if new_total > 0 {
            self.avg_conflict_clause_size = (self.avg_conflict_clause_size * prev_total as f64
                + other.avg_conflict_clause_size * other.total_conflicts as f64)
                / new_total as f64;
        }
    }
}

// ---------------------------------------------------------------------------
// InstrumentationReport
// ---------------------------------------------------------------------------

/// Per-function instrumentation summary produced when a session finishes.
#[derive(Debug, Clone)]
pub(crate) struct InstrumentationReport {
    /// Name of the function that was verified.
    pub(crate) function_name: String,
    /// Total events received (including those skipped by sampling).
    pub(crate) total_events: usize,
    /// Event counts keyed by event type tag.
    pub(crate) events_by_type: HashMap<String, usize>,
    /// Total violations detected.
    pub(crate) violations: usize,
    /// All alerts emitted during the session.
    pub(crate) alerts: Vec<InstrumentationAlert>,
    /// Aggregate solver statistics.
    pub(crate) solver_stats: SolverRunStats,
    /// Whether the session completed without critical violations.
    pub(crate) healthy: bool,
}

// ---------------------------------------------------------------------------
// InstrumentationSession
// ---------------------------------------------------------------------------

/// Per-function verification instrumentation session.
///
/// Records solver events, detects anomalies, and produces a summary report
/// when the session finishes.
pub(crate) struct InstrumentationSession {
    config: InstrumentationConfig,
    function_name: String,
    /// Total events received (pre-sampling).
    total_events: usize,
    /// Deterministic sampling counter.
    sample_counter: u64,
    /// Events that passed the sampling filter.
    sampled_events: usize,
    /// Event counts by type tag.
    events_by_type: HashMap<String, usize>,
    /// Alerts emitted during this session.
    alerts: Vec<InstrumentationAlert>,
    /// Running solver statistics.
    stats: SolverRunStats,
    /// Total conflict clause size accumulator (for computing average).
    conflict_clause_size_sum: usize,
    /// Whether a critical violation has been recorded.
    has_critical: bool,
    /// Whether the session has been auto-disabled due to max violations.
    auto_disabled: bool,
    /// Number of violations recorded.
    violation_count: usize,
}

impl InstrumentationSession {
    /// Create a new instrumentation session for the named function.
    #[must_use]
    pub(crate) fn new(config: InstrumentationConfig, function_name: &str) -> Self {
        Self {
            config,
            function_name: function_name.to_string(),
            total_events: 0,
            sample_counter: 0,
            sampled_events: 0,
            events_by_type: HashMap::new(),
            alerts: Vec::new(),
            stats: SolverRunStats::default(),
            conflict_clause_size_sum: 0,
            has_critical: false,
            auto_disabled: false,
            violation_count: 0,
        }
    }

    /// Whether this event passes the deterministic sampling filter.
    fn should_sample(&mut self) -> bool {
        if !self.config.monitoring_enabled || self.auto_disabled {
            return false;
        }
        self.sample_counter += 1;
        if self.config.sample_rate <= 0.0 {
            return false;
        }
        if self.config.sample_rate >= 1.0 {
            return true;
        }
        let raw_period = (1.0 / self.config.sample_rate).ceil();
        let period = if raw_period.is_finite() && raw_period > 0.0 {
            (raw_period as u64).max(1)
        } else {
            return true;
        };
        self.sample_counter.is_multiple_of(period)
    }

    /// Record a solver event and optionally return an alert.
    ///
    /// Events are always counted. Sampling determines whether the event is
    /// fully processed for anomaly detection and statistics collection.
    pub(crate) fn record(&mut self, event: SolverEvent) -> Option<InstrumentationAlert> {
        self.total_events += 1;
        let tag = event.event_type.tag().to_string();
        *self.events_by_type.entry(tag).or_insert(0) += 1;

        if self.config.log_events && self.config.monitoring_enabled {
            eprintln!("[encoder_instrumentation] {event}");
        }

        if !self.should_sample() {
            return None;
        }
        self.sampled_events += 1;

        // Collect solver stats if configured.
        if self.config.collect_solver_stats {
            self.update_stats(&event.event_type);
        }

        // Check for anomalies.
        self.check_anomalies(&event)
    }

    /// Update running statistics from an event.
    fn update_stats(&mut self, event_type: &SolverEventType) {
        match event_type {
            SolverEventType::Propagation { .. } => {
                self.stats.total_propagations += 1;
            }
            SolverEventType::Decision { level, .. } => {
                self.stats.total_decisions += 1;
                if *level > self.stats.max_decision_level {
                    self.stats.max_decision_level = *level;
                }
            }
            SolverEventType::Conflict { clause_size, .. } => {
                self.stats.total_conflicts += 1;
                self.conflict_clause_size_sum += clause_size;
                self.stats.avg_conflict_clause_size =
                    self.conflict_clause_size_sum as f64 / self.stats.total_conflicts as f64;
            }
            SolverEventType::Restart { .. } => {
                self.stats.total_restarts += 1;
            }
            SolverEventType::Learn { .. } => {
                self.stats.learned_clauses += 1;
            }
            SolverEventType::Forget { clause_count } => {
                self.stats.forgotten_clauses += clause_count;
            }
        }
    }

    /// Check for anomalous patterns in the event stream.
    fn check_anomalies(&mut self, event: &SolverEvent) -> Option<InstrumentationAlert> {
        // Detect excessive restarts (more restarts than decisions is suspicious).
        if self.stats.total_restarts > 0
            && self.stats.total_decisions > 0
            && self.stats.total_restarts > self.stats.total_decisions
        {
            let alert = InstrumentationAlert {
                alert_type: AlertType::PerformanceAnomaly,
                message: format!(
                    "restarts ({}) exceed decisions ({}) in {}",
                    self.stats.total_restarts, self.stats.total_decisions, self.function_name,
                ),
                severity: AlertSeverity::Warning,
            };
            self.record_alert(alert.clone());
            return Some(alert);
        }

        // Detect zero-size conflict clauses (contract violation).
        if let SolverEventType::Conflict { clause_size: 0, .. } = &event.event_type {
            let alert = InstrumentationAlert {
                alert_type: AlertType::ContractViolation,
                message: format!("zero-size conflict clause in {}", self.function_name,),
                severity: AlertSeverity::Critical,
            };
            self.record_alert(alert.clone());
            return Some(alert);
        }

        // Detect zero-size learned clauses.
        if let SolverEventType::Learn { clause_size: 0 } = &event.event_type {
            let alert = InstrumentationAlert {
                alert_type: AlertType::ContractViolation,
                message: format!("zero-size learned clause in {}", self.function_name,),
                severity: AlertSeverity::Critical,
            };
            self.record_alert(alert.clone());
            return Some(alert);
        }

        None
    }

    /// Record an alert, respecting max-violations auto-disable.
    fn record_alert(&mut self, alert: InstrumentationAlert) {
        if alert.severity == AlertSeverity::Critical {
            self.has_critical = true;
        }
        self.violation_count += 1;
        self.alerts.push(alert);
        if self.violation_count >= self.config.max_violations {
            self.auto_disabled = true;
            self.alerts.push(InstrumentationAlert {
                alert_type: AlertType::ResourceLimit,
                message: format!(
                    "max violations ({}) reached for {}; session auto-disabled",
                    self.config.max_violations, self.function_name,
                ),
                severity: AlertSeverity::Warning,
            });
        }
    }

    /// Consume the session and produce a summary report.
    #[must_use]
    pub(crate) fn finish(self) -> InstrumentationReport {
        InstrumentationReport {
            function_name: self.function_name,
            total_events: self.total_events,
            events_by_type: self.events_by_type,
            violations: self.violation_count,
            alerts: self.alerts,
            solver_stats: self.stats,
            healthy: !self.has_critical,
        }
    }

    /// Whether this session has no critical violations.
    #[must_use]
    pub(crate) fn is_healthy(&self) -> bool {
        !self.has_critical
    }
}

// ---------------------------------------------------------------------------
// GlobalInstrumentationReport
// ---------------------------------------------------------------------------

/// Aggregate instrumentation report across all verified functions.
#[derive(Debug, Clone)]
pub(crate) struct GlobalInstrumentationReport {
    /// Number of functions that were instrumented.
    pub(crate) functions_instrumented: usize,
    /// Total events across all sessions.
    pub(crate) total_events: usize,
    /// Total violations across all sessions.
    pub(crate) total_violations: usize,
    /// Functions with critical violations.
    pub(crate) unhealthy_functions: Vec<String>,
    /// Aggregate solver statistics across all functions.
    pub(crate) aggregate_stats: SolverRunStats,
}

// ---------------------------------------------------------------------------
// InstrumentationRegistry
// ---------------------------------------------------------------------------

/// Registry tracking instrumentation sessions across multiple functions.
pub(crate) struct InstrumentationRegistry {
    config: InstrumentationConfig,
    /// Active sessions keyed by function name.
    active_sessions: HashMap<String, InstrumentationSession>,
    /// Completed reports keyed by function name.
    completed_reports: HashMap<String, InstrumentationReport>,
}

impl InstrumentationRegistry {
    /// Create a new registry with the given configuration.
    #[must_use]
    pub(crate) fn new(config: InstrumentationConfig) -> Self {
        Self {
            config,
            active_sessions: HashMap::new(),
            completed_reports: HashMap::new(),
        }
    }

    /// Start or return an existing session for the named function.
    pub(crate) fn start_session(&mut self, function_name: &str) -> &mut InstrumentationSession {
        self.active_sessions
            .entry(function_name.to_string())
            .or_insert_with(|| InstrumentationSession::new(self.config.clone(), function_name))
    }

    /// Finish and remove the session for the named function, returning the
    /// report. Returns `None` if no active session exists for that function.
    pub(crate) fn finish_session(&mut self, function_name: &str) -> Option<InstrumentationReport> {
        let session = self.active_sessions.remove(function_name)?;
        let report = session.finish();
        self.completed_reports
            .insert(function_name.to_string(), report.clone());
        Some(report)
    }

    /// Produce a global summary across all completed sessions.
    #[must_use]
    pub(crate) fn global_report(&self) -> GlobalInstrumentationReport {
        let mut total_events = 0;
        let mut total_violations = 0;
        let mut unhealthy_functions = Vec::new();
        let mut aggregate_stats = SolverRunStats::default();

        for (name, report) in &self.completed_reports {
            total_events += report.total_events;
            total_violations += report.violations;
            if !report.healthy {
                unhealthy_functions.push(name.clone());
            }
            aggregate_stats.merge(&report.solver_stats);
        }

        unhealthy_functions.sort();

        GlobalInstrumentationReport {
            functions_instrumented: self.completed_reports.len(),
            total_events,
            total_violations,
            unhealthy_functions,
            aggregate_stats,
        }
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: create an enabled config that samples all events.
    fn enabled_config() -> InstrumentationConfig {
        InstrumentationConfig {
            monitoring_enabled: true,
            sample_rate: 1.0,
            max_violations: 100,
            collect_solver_stats: true,
            log_events: false,
        }
    }

    /// Helper: create a valid propagation event.
    fn propagation_event(function_name: &str, literals: usize) -> SolverEvent {
        SolverEvent {
            event_type: SolverEventType::Propagation { literals },
            timestamp_ns: 0,
            function_name: function_name.to_string(),
            context: String::new(),
        }
    }

    /// Helper: create a valid decision event.
    fn decision_event(function_name: &str, variable_id: u32, level: usize) -> SolverEvent {
        SolverEvent {
            event_type: SolverEventType::Decision { variable_id, level },
            timestamp_ns: 0,
            function_name: function_name.to_string(),
            context: String::new(),
        }
    }

    /// Helper: create a valid conflict event.
    fn conflict_event(
        function_name: &str,
        clause_size: usize,
        backjump_level: usize,
    ) -> SolverEvent {
        SolverEvent {
            event_type: SolverEventType::Conflict {
                clause_size,
                backjump_level,
            },
            timestamp_ns: 0,
            function_name: function_name.to_string(),
            context: String::new(),
        }
    }

    /// Helper: create a restart event.
    fn restart_event(function_name: &str, conflict_count: usize) -> SolverEvent {
        SolverEvent {
            event_type: SolverEventType::Restart { conflict_count },
            timestamp_ns: 0,
            function_name: function_name.to_string(),
            context: String::new(),
        }
    }

    /// Helper: create a learn event.
    fn learn_event(function_name: &str, clause_size: usize) -> SolverEvent {
        SolverEvent {
            event_type: SolverEventType::Learn { clause_size },
            timestamp_ns: 0,
            function_name: function_name.to_string(),
            context: String::new(),
        }
    }

    /// Helper: create a forget event.
    fn forget_event(function_name: &str, clause_count: usize) -> SolverEvent {
        SolverEvent {
            event_type: SolverEventType::Forget { clause_count },
            timestamp_ns: 0,
            function_name: function_name.to_string(),
            context: String::new(),
        }
    }

    // -----------------------------------------------------------------------
    // 1. Default config values
    // -----------------------------------------------------------------------

    #[test]
    fn test_default_config_values() {
        let config = InstrumentationConfig::default();
        assert!(!config.monitoring_enabled);
        assert!((config.sample_rate - 0.01).abs() < f64::EPSILON);
        assert_eq!(config.max_violations, 100);
        assert!(config.collect_solver_stats);
        assert!(!config.log_events);
    }

    // -----------------------------------------------------------------------
    // 2. SolverEventType tag strings
    // -----------------------------------------------------------------------

    #[test]
    fn test_solver_event_type_tags() {
        assert_eq!(
            SolverEventType::Propagation { literals: 5 }.tag(),
            "Propagation"
        );
        assert_eq!(
            SolverEventType::Decision {
                variable_id: 1,
                level: 2
            }
            .tag(),
            "Decision"
        );
        assert_eq!(
            SolverEventType::Conflict {
                clause_size: 3,
                backjump_level: 1
            }
            .tag(),
            "Conflict"
        );
        assert_eq!(
            SolverEventType::Restart { conflict_count: 10 }.tag(),
            "Restart"
        );
        assert_eq!(SolverEventType::Learn { clause_size: 4 }.tag(), "Learn");
        assert_eq!(SolverEventType::Forget { clause_count: 2 }.tag(), "Forget");
    }

    // -----------------------------------------------------------------------
    // 3. SolverEventType display
    // -----------------------------------------------------------------------

    #[test]
    fn test_solver_event_type_display() {
        let ty = SolverEventType::Propagation { literals: 7 };
        assert_eq!(format!("{ty}"), "Propagation(literals=7)");

        let ty = SolverEventType::Decision {
            variable_id: 42,
            level: 3,
        };
        assert_eq!(format!("{ty}"), "Decision(var=42, level=3)");

        let ty = SolverEventType::Conflict {
            clause_size: 5,
            backjump_level: 2,
        };
        assert_eq!(format!("{ty}"), "Conflict(clause_size=5, backjump=2)");
    }

    // -----------------------------------------------------------------------
    // 4. SolverEvent display
    // -----------------------------------------------------------------------

    #[test]
    fn test_solver_event_display() {
        let event = SolverEvent {
            event_type: SolverEventType::Decision {
                variable_id: 1,
                level: 4,
            },
            timestamp_ns: 12345,
            function_name: "verify_add".to_string(),
            context: "initial".to_string(),
        };
        let display = format!("{event}");
        assert!(display.contains("12345ns"));
        assert!(display.contains("verify_add"));
        assert!(display.contains("initial"));
    }

    // -----------------------------------------------------------------------
    // 5. AlertSeverity display
    // -----------------------------------------------------------------------

    #[test]
    fn test_alert_severity_display() {
        assert_eq!(format!("{}", AlertSeverity::Critical), "CRITICAL");
        assert_eq!(format!("{}", AlertSeverity::Warning), "WARNING");
        assert_eq!(format!("{}", AlertSeverity::Info), "INFO");
    }

    // -----------------------------------------------------------------------
    // 6. AlertType display
    // -----------------------------------------------------------------------

    #[test]
    fn test_alert_type_display() {
        assert_eq!(
            format!("{}", AlertType::ContractViolation),
            "ContractViolation"
        );
        assert_eq!(
            format!("{}", AlertType::PerformanceAnomaly),
            "PerformanceAnomaly"
        );
        assert_eq!(format!("{}", AlertType::ResourceLimit), "ResourceLimit");
    }

    // -----------------------------------------------------------------------
    // 7. InstrumentationAlert display
    // -----------------------------------------------------------------------

    #[test]
    fn test_instrumentation_alert_display() {
        let alert = InstrumentationAlert {
            alert_type: AlertType::ContractViolation,
            message: "zero-size clause".to_string(),
            severity: AlertSeverity::Critical,
        };
        let display = format!("{alert}");
        assert!(display.contains("CRITICAL"));
        assert!(display.contains("ContractViolation"));
        assert!(display.contains("zero-size clause"));
    }

    // -----------------------------------------------------------------------
    // 8. SolverRunStats default
    // -----------------------------------------------------------------------

    #[test]
    fn test_solver_run_stats_default() {
        let stats = SolverRunStats::default();
        assert_eq!(stats.total_decisions, 0);
        assert_eq!(stats.total_conflicts, 0);
        assert_eq!(stats.total_restarts, 0);
        assert_eq!(stats.total_propagations, 0);
        assert_eq!(stats.learned_clauses, 0);
        assert_eq!(stats.forgotten_clauses, 0);
        assert_eq!(stats.max_decision_level, 0);
        assert!((stats.avg_conflict_clause_size - 0.0).abs() < f64::EPSILON);
    }

    // -----------------------------------------------------------------------
    // 9. SolverRunStats merge
    // -----------------------------------------------------------------------

    #[test]
    fn test_solver_run_stats_merge() {
        let mut a = SolverRunStats {
            total_decisions: 10,
            total_conflicts: 5,
            total_restarts: 1,
            total_propagations: 100,
            learned_clauses: 3,
            forgotten_clauses: 1,
            max_decision_level: 8,
            avg_conflict_clause_size: 4.0,
        };
        let b = SolverRunStats {
            total_decisions: 20,
            total_conflicts: 10,
            total_restarts: 2,
            total_propagations: 200,
            learned_clauses: 7,
            forgotten_clauses: 3,
            max_decision_level: 12,
            avg_conflict_clause_size: 6.0,
        };
        a.merge(&b);
        assert_eq!(a.total_decisions, 30);
        assert_eq!(a.total_conflicts, 15);
        assert_eq!(a.total_restarts, 3);
        assert_eq!(a.total_propagations, 300);
        assert_eq!(a.learned_clauses, 10);
        assert_eq!(a.forgotten_clauses, 4);
        assert_eq!(a.max_decision_level, 12);
        // Weighted average: (4.0 * 5 + 6.0 * 10) / 15 = 80/15 ≈ 5.333
        assert!((a.avg_conflict_clause_size - 80.0 / 15.0).abs() < 1e-10);
    }

    // -----------------------------------------------------------------------
    // 10. Disabled session records nothing
    // -----------------------------------------------------------------------

    #[test]
    fn test_disabled_session_records_no_alerts() {
        let config = InstrumentationConfig {
            monitoring_enabled: false,
            sample_rate: 1.0,
            max_violations: 100,
            collect_solver_stats: true,
            log_events: false,
        };
        let mut session = InstrumentationSession::new(config, "fn_disabled");

        // Zero-size conflict would normally trigger an alert.
        let result = session.record(conflict_event("fn_disabled", 0, 0));
        assert!(result.is_none());
        assert_eq!(session.total_events, 1);
        assert!(session.is_healthy());
    }

    // -----------------------------------------------------------------------
    // 11. Enabled session records events and updates stats
    // -----------------------------------------------------------------------

    #[test]
    fn test_enabled_session_records_propagation() {
        let mut session = InstrumentationSession::new(enabled_config(), "fn_prop");

        let result = session.record(propagation_event("fn_prop", 10));
        assert!(result.is_none());
        assert_eq!(session.total_events, 1);
        assert_eq!(session.stats.total_propagations, 1);
    }

    // -----------------------------------------------------------------------
    // 12. Decision events update max_decision_level
    // -----------------------------------------------------------------------

    #[test]
    fn test_decision_updates_max_level() {
        let mut session = InstrumentationSession::new(enabled_config(), "fn_dec");

        session.record(decision_event("fn_dec", 1, 3));
        session.record(decision_event("fn_dec", 2, 7));
        session.record(decision_event("fn_dec", 3, 5));

        assert_eq!(session.stats.total_decisions, 3);
        assert_eq!(session.stats.max_decision_level, 7);
    }

    // -----------------------------------------------------------------------
    // 13. Conflict events update avg_conflict_clause_size
    // -----------------------------------------------------------------------

    #[test]
    fn test_conflict_updates_avg_clause_size() {
        let mut session = InstrumentationSession::new(enabled_config(), "fn_conflict");

        session.record(conflict_event("fn_conflict", 4, 1));
        session.record(conflict_event("fn_conflict", 6, 0));

        assert_eq!(session.stats.total_conflicts, 2);
        // Average: (4 + 6) / 2 = 5.0
        assert!((session.stats.avg_conflict_clause_size - 5.0).abs() < f64::EPSILON);
    }

    // -----------------------------------------------------------------------
    // 14. Restart events counted
    // -----------------------------------------------------------------------

    #[test]
    fn test_restart_events_counted() {
        let mut session = InstrumentationSession::new(enabled_config(), "fn_restart");

        session.record(restart_event("fn_restart", 50));
        session.record(restart_event("fn_restart", 30));

        assert_eq!(session.stats.total_restarts, 2);
    }

    // -----------------------------------------------------------------------
    // 15. Learn events counted
    // -----------------------------------------------------------------------

    #[test]
    fn test_learn_events_counted() {
        let mut session = InstrumentationSession::new(enabled_config(), "fn_learn");

        session.record(learn_event("fn_learn", 3));
        session.record(learn_event("fn_learn", 5));

        assert_eq!(session.stats.learned_clauses, 2);
    }

    // -----------------------------------------------------------------------
    // 16. Forget events accumulate clause_count
    // -----------------------------------------------------------------------

    #[test]
    fn test_forget_events_accumulate_counts() {
        let mut session = InstrumentationSession::new(enabled_config(), "fn_forget");

        session.record(forget_event("fn_forget", 10));
        session.record(forget_event("fn_forget", 5));

        assert_eq!(session.stats.forgotten_clauses, 15);
    }

    // -----------------------------------------------------------------------
    // 17. Zero-size conflict triggers critical alert
    // -----------------------------------------------------------------------

    #[test]
    fn test_zero_size_conflict_triggers_alert() {
        let mut session = InstrumentationSession::new(enabled_config(), "fn_zero_conflict");

        let result = session.record(conflict_event("fn_zero_conflict", 0, 0));

        assert!(result.is_some());
        let alert = result.expect("should have alert");
        assert_eq!(alert.alert_type, AlertType::ContractViolation);
        assert_eq!(alert.severity, AlertSeverity::Critical);
        assert!(!session.is_healthy());
    }

    // -----------------------------------------------------------------------
    // 18. Zero-size learn triggers critical alert
    // -----------------------------------------------------------------------

    #[test]
    fn test_zero_size_learn_triggers_alert() {
        let mut session = InstrumentationSession::new(enabled_config(), "fn_zero_learn");

        let result = session.record(learn_event("fn_zero_learn", 0));

        assert!(result.is_some());
        let alert = result.expect("should have alert");
        assert_eq!(alert.alert_type, AlertType::ContractViolation);
        assert_eq!(alert.severity, AlertSeverity::Critical);
    }

    // -----------------------------------------------------------------------
    // 19. Excessive restarts trigger performance anomaly
    // -----------------------------------------------------------------------

    #[test]
    fn test_excessive_restarts_trigger_anomaly() {
        let mut session = InstrumentationSession::new(enabled_config(), "fn_restarts");

        // 1 decision, then 2 restarts → restarts > decisions.
        session.record(decision_event("fn_restarts", 1, 1));
        session.record(restart_event("fn_restarts", 10));
        let result = session.record(restart_event("fn_restarts", 5));

        assert!(result.is_some());
        let alert = result.expect("should have alert");
        assert_eq!(alert.alert_type, AlertType::PerformanceAnomaly);
        assert_eq!(alert.severity, AlertSeverity::Warning);
    }

    // -----------------------------------------------------------------------
    // 20. Session finish produces report
    // -----------------------------------------------------------------------

    #[test]
    fn test_session_finish_produces_report() {
        let mut session = InstrumentationSession::new(enabled_config(), "fn_report");

        session.record(propagation_event("fn_report", 5));
        session.record(decision_event("fn_report", 1, 2));
        session.record(conflict_event("fn_report", 3, 1));

        let report = session.finish();
        assert_eq!(report.function_name, "fn_report");
        assert_eq!(report.total_events, 3);
        assert_eq!(report.violations, 0);
        assert!(report.healthy);
        assert_eq!(report.solver_stats.total_propagations, 1);
        assert_eq!(report.solver_stats.total_decisions, 1);
        assert_eq!(report.solver_stats.total_conflicts, 1);
    }

    // -----------------------------------------------------------------------
    // 21. Report events_by_type populated
    // -----------------------------------------------------------------------

    #[test]
    fn test_report_events_by_type() {
        let mut session = InstrumentationSession::new(enabled_config(), "fn_by_type");

        session.record(propagation_event("fn_by_type", 3));
        session.record(propagation_event("fn_by_type", 5));
        session.record(decision_event("fn_by_type", 1, 1));

        let report = session.finish();
        assert_eq!(report.events_by_type.get("Propagation"), Some(&2));
        assert_eq!(report.events_by_type.get("Decision"), Some(&1));
        assert_eq!(report.events_by_type.get("Conflict"), None);
    }

    // -----------------------------------------------------------------------
    // 22. Sample rate filtering
    // -----------------------------------------------------------------------

    #[test]
    fn test_sample_rate_filtering() {
        let config = InstrumentationConfig {
            monitoring_enabled: true,
            sample_rate: 0.1,
            max_violations: 10000,
            collect_solver_stats: true,
            log_events: false,
        };
        let mut session = InstrumentationSession::new(config, "fn_sampling");

        for _ in 0..1000 {
            session.record(propagation_event("fn_sampling", 1));
        }

        assert_eq!(session.total_events, 1000);
        // With period = ceil(1/0.1) = 10, exactly 100 events sampled.
        assert_eq!(session.sampled_events, 100);
        assert_eq!(session.stats.total_propagations, 100);
    }

    // -----------------------------------------------------------------------
    // 23. Max violations auto-disable
    // -----------------------------------------------------------------------

    #[test]
    fn test_max_violations_auto_disable() {
        let config = InstrumentationConfig {
            monitoring_enabled: true,
            sample_rate: 1.0,
            max_violations: 3,
            collect_solver_stats: true,
            log_events: false,
        };
        let mut session = InstrumentationSession::new(config, "fn_max_viol");

        // Send 5 zero-size learn events (each triggers a critical alert).
        for _ in 0..5 {
            session.record(learn_event("fn_max_viol", 0));
        }

        // Should have 3 violation alerts + 1 resource-limit alert = 4 total,
        // then auto-disabled so remaining events produce no more alerts.
        assert_eq!(session.violation_count, 3);
        assert!(session.auto_disabled);
    }

    // -----------------------------------------------------------------------
    // 24. is_healthy reflects critical violations
    // -----------------------------------------------------------------------

    #[test]
    fn test_is_healthy_reflects_critical() {
        let mut session = InstrumentationSession::new(enabled_config(), "fn_health");

        assert!(session.is_healthy());
        session.record(learn_event("fn_health", 0)); // critical
        assert!(!session.is_healthy());
    }

    // -----------------------------------------------------------------------
    // 25. Registry start_session creates session
    // -----------------------------------------------------------------------

    #[test]
    fn test_registry_start_session() {
        let mut registry = InstrumentationRegistry::new(enabled_config());
        let session = registry.start_session("func_a");
        session.record(propagation_event("func_a", 5));

        assert!(registry.active_sessions.contains_key("func_a"));
    }

    // -----------------------------------------------------------------------
    // 26. Registry finish_session returns report
    // -----------------------------------------------------------------------

    #[test]
    fn test_registry_finish_session() {
        let mut registry = InstrumentationRegistry::new(enabled_config());
        {
            let session = registry.start_session("func_b");
            session.record(decision_event("func_b", 1, 3));
            session.record(decision_event("func_b", 2, 5));
        }

        let report = registry
            .finish_session("func_b")
            .expect("session should exist");
        assert_eq!(report.function_name, "func_b");
        assert_eq!(report.total_events, 2);
        assert_eq!(report.solver_stats.total_decisions, 2);
        assert!(report.healthy);
    }

    // -----------------------------------------------------------------------
    // 27. Registry finish_session for unknown returns None
    // -----------------------------------------------------------------------

    #[test]
    fn test_registry_finish_unknown_returns_none() {
        let mut registry = InstrumentationRegistry::new(enabled_config());
        assert!(registry.finish_session("nonexistent").is_none());
    }

    // -----------------------------------------------------------------------
    // 28. Registry global_report aggregates
    // -----------------------------------------------------------------------

    #[test]
    fn test_registry_global_report_aggregates() {
        let mut registry = InstrumentationRegistry::new(enabled_config());

        // Function A: healthy, 3 events.
        {
            let session = registry.start_session("func_a");
            session.record(propagation_event("func_a", 1));
            session.record(decision_event("func_a", 1, 2));
            session.record(conflict_event("func_a", 4, 1));
        }
        registry.finish_session("func_a");

        // Function B: unhealthy (zero-size learn), 2 events.
        {
            let session = registry.start_session("func_b");
            session.record(propagation_event("func_b", 3));
            session.record(learn_event("func_b", 0)); // critical
        }
        registry.finish_session("func_b");

        let global = registry.global_report();
        assert_eq!(global.functions_instrumented, 2);
        assert_eq!(global.total_events, 5);
        assert_eq!(global.total_violations, 1);
        assert_eq!(global.unhealthy_functions, vec!["func_b".to_string()]);
        assert_eq!(global.aggregate_stats.total_propagations, 2);
        assert_eq!(global.aggregate_stats.total_decisions, 1);
    }

    // -----------------------------------------------------------------------
    // 29. Global report with no sessions
    // -----------------------------------------------------------------------

    #[test]
    fn test_global_report_empty() {
        let registry = InstrumentationRegistry::new(enabled_config());
        let global = registry.global_report();
        assert_eq!(global.functions_instrumented, 0);
        assert_eq!(global.total_events, 0);
        assert_eq!(global.total_violations, 0);
        assert!(global.unhealthy_functions.is_empty());
    }

    // -----------------------------------------------------------------------
    // 30. Multiple sessions interleaved
    // -----------------------------------------------------------------------

    #[test]
    fn test_multiple_sessions_interleaved() {
        let mut registry = InstrumentationRegistry::new(enabled_config());

        // Start two sessions concurrently.
        {
            let s1 = registry.start_session("f1");
            s1.record(decision_event("f1", 1, 1));
        }
        {
            let s2 = registry.start_session("f2");
            s2.record(decision_event("f2", 2, 2));
            s2.record(decision_event("f2", 3, 4));
        }

        let r1 = registry
            .finish_session("f1")
            .expect("f1 session should exist");
        let r2 = registry
            .finish_session("f2")
            .expect("f2 session should exist");

        assert_eq!(r1.total_events, 1);
        assert_eq!(r1.solver_stats.max_decision_level, 1);
        assert_eq!(r2.total_events, 2);
        assert_eq!(r2.solver_stats.max_decision_level, 4);
    }

    // -----------------------------------------------------------------------
    // 31. Collect solver stats disabled
    // -----------------------------------------------------------------------

    #[test]
    fn test_collect_solver_stats_disabled() {
        let config = InstrumentationConfig {
            monitoring_enabled: true,
            sample_rate: 1.0,
            max_violations: 100,
            collect_solver_stats: false,
            log_events: false,
        };
        let mut session = InstrumentationSession::new(config, "fn_no_stats");

        session.record(decision_event("fn_no_stats", 1, 5));
        session.record(conflict_event("fn_no_stats", 4, 2));

        // Stats should not have been updated.
        assert_eq!(session.stats.total_decisions, 0);
        assert_eq!(session.stats.total_conflicts, 0);
    }

    // -----------------------------------------------------------------------
    // 32. SolverEventType equality
    // -----------------------------------------------------------------------

    #[test]
    fn test_solver_event_type_equality() {
        let a = SolverEventType::Decision {
            variable_id: 1,
            level: 2,
        };
        let b = SolverEventType::Decision {
            variable_id: 1,
            level: 2,
        };
        let c = SolverEventType::Decision {
            variable_id: 1,
            level: 3,
        };
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    // -----------------------------------------------------------------------
    // 33. SolverEvent with context
    // -----------------------------------------------------------------------

    #[test]
    fn test_solver_event_context_preserved() {
        let event = SolverEvent {
            event_type: SolverEventType::Restart { conflict_count: 42 },
            timestamp_ns: 999,
            function_name: "fn_ctx".to_string(),
            context: "after-bcp-phase".to_string(),
        };
        assert_eq!(event.context, "after-bcp-phase");
        assert_eq!(event.timestamp_ns, 999);
    }

    // -----------------------------------------------------------------------
    // 34. Report healthy flag propagated from session
    // -----------------------------------------------------------------------

    #[test]
    fn test_report_healthy_flag() {
        let mut session = InstrumentationSession::new(enabled_config(), "fn_healthy");
        session.record(propagation_event("fn_healthy", 5));
        let report = session.finish();
        assert!(report.healthy);

        let mut session2 = InstrumentationSession::new(enabled_config(), "fn_unhealthy");
        session2.record(learn_event("fn_unhealthy", 0)); // critical
        let report2 = session2.finish();
        assert!(!report2.healthy);
    }

    // -----------------------------------------------------------------------
    // 35. Registry idempotent start_session
    // -----------------------------------------------------------------------

    #[test]
    fn test_registry_start_session_idempotent() {
        let mut registry = InstrumentationRegistry::new(enabled_config());

        {
            let s = registry.start_session("func_x");
            s.record(propagation_event("func_x", 1));
        }
        {
            // Second call returns the same session, not a new one.
            let s = registry.start_session("func_x");
            s.record(propagation_event("func_x", 2));
        }

        let report = registry
            .finish_session("func_x")
            .expect("session should exist");
        assert_eq!(report.total_events, 2);
    }

    // -----------------------------------------------------------------------
    // 36. Zero sample rate records no sampled events
    // -----------------------------------------------------------------------

    #[test]
    fn test_zero_sample_rate() {
        let config = InstrumentationConfig {
            monitoring_enabled: true,
            sample_rate: 0.0,
            max_violations: 100,
            collect_solver_stats: true,
            log_events: false,
        };
        let mut session = InstrumentationSession::new(config, "fn_zero_rate");

        for _ in 0..100 {
            session.record(propagation_event("fn_zero_rate", 1));
        }

        assert_eq!(session.total_events, 100);
        assert_eq!(session.sampled_events, 0);
        assert_eq!(session.stats.total_propagations, 0);
    }

    // -----------------------------------------------------------------------
    // 37. SolverRunStats merge with zero conflicts
    // -----------------------------------------------------------------------

    #[test]
    fn test_stats_merge_zero_conflicts() {
        let mut a = SolverRunStats::default();
        let b = SolverRunStats {
            total_decisions: 5,
            total_conflicts: 0,
            total_restarts: 0,
            total_propagations: 10,
            learned_clauses: 0,
            forgotten_clauses: 0,
            max_decision_level: 3,
            avg_conflict_clause_size: 0.0,
        };
        a.merge(&b);
        assert_eq!(a.total_decisions, 5);
        assert_eq!(a.max_decision_level, 3);
        assert!((a.avg_conflict_clause_size - 0.0).abs() < f64::EPSILON);
    }

    // -----------------------------------------------------------------------
    // 38. Global report unhealthy_functions sorted
    // -----------------------------------------------------------------------

    #[test]
    fn test_global_report_unhealthy_sorted() {
        let mut registry = InstrumentationRegistry::new(enabled_config());

        // Create two unhealthy sessions with names that sort differently.
        for name in &["zebra", "alpha"] {
            let s = registry.start_session(name);
            s.record(learn_event(name, 0)); // critical
            registry.finish_session(name);
        }

        let global = registry.global_report();
        assert_eq!(
            global.unhealthy_functions,
            vec!["alpha".to_string(), "zebra".to_string()]
        );
    }

    // -----------------------------------------------------------------------
    // 39. Report alerts include resource limit on auto-disable
    // -----------------------------------------------------------------------

    #[test]
    fn test_auto_disable_emits_resource_limit_alert() {
        let config = InstrumentationConfig {
            monitoring_enabled: true,
            sample_rate: 1.0,
            max_violations: 2,
            collect_solver_stats: true,
            log_events: false,
        };
        let mut session = InstrumentationSession::new(config, "fn_rl");

        session.record(learn_event("fn_rl", 0));
        session.record(learn_event("fn_rl", 0));

        let report = session.finish();
        // 2 contract violations + 1 resource-limit alert.
        let rl_alerts: Vec<_> = report
            .alerts
            .iter()
            .filter(|a| a.alert_type == AlertType::ResourceLimit)
            .collect();
        assert_eq!(rl_alerts.len(), 1);
        assert!(rl_alerts[0].message.contains("auto-disabled"));
    }

    // -----------------------------------------------------------------------
    // 40. Full end-to-end registry workflow
    // -----------------------------------------------------------------------

    #[test]
    fn test_full_registry_workflow() {
        let mut registry = InstrumentationRegistry::new(enabled_config());

        // Simulate verification of three functions.
        for (i, name) in ["verify_add", "verify_sub", "verify_mul"]
            .iter()
            .enumerate()
        {
            let s = registry.start_session(name);
            for j in 0..10 {
                s.record(propagation_event(name, j));
                s.record(decision_event(name, j as u32, j + 1));
            }
            if i == 2 {
                // Inject a critical violation in verify_mul.
                s.record(learn_event(name, 0));
            }
            registry.finish_session(name);
        }

        let global = registry.global_report();
        assert_eq!(global.functions_instrumented, 3);
        // 10 propagations + 10 decisions each = 20 per function, +1 learn for mul.
        assert_eq!(global.total_events, 61);
        assert_eq!(global.total_violations, 1);
        assert_eq!(global.unhealthy_functions, vec!["verify_mul".to_string()]);
        assert_eq!(global.aggregate_stats.total_decisions, 30);
        assert_eq!(global.aggregate_stats.total_propagations, 30);
    }
}
