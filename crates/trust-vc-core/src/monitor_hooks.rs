// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Instrumentation hooks for the contract monitor.
//!
//! This module provides an optional monitoring layer that the encoder can use to
//! observe ay solver contract compliance during verification. Unlike the
//! [`contract_monitor`] which checks CDCL invariants directly, `monitor_hooks`
//! operates at the event level: callers emit [`HookEvent`] values and the
//! [`MonitorHookState`] validates each event against lightweight contract rules.
//!
//! # Design
//!
//! [`MonitorHookConfig`] controls whether monitoring is active, the
//! deterministic sampling rate, violation limits, and diagnostic behavior.
//! [`MonitorHookState`] is instantiated per-function so that independent
//! verification tasks do not interfere with each other.
//!
//! Contract rules per event type:
//! - **BCP**: `watch_count >= 2 * clause_count` (two-watched-literal invariant)
//! - **Decision**: decision level must monotonically increase
//! - **Conflict**: `backtrack_level < current_max_level`
//! - **Restart**: `conflicts_since_last > 0`
//! - **ClauseAdded**: `size > 0`
//! - **ClauseRemoved**: `reason` must be non-empty
//!
//! Source: contract_monitor.rs, ay_contracts.rs

#![allow(dead_code)]

use std::collections::HashMap;
use std::fmt;

// ---------------------------------------------------------------------------
// HookSeverity
// ---------------------------------------------------------------------------

/// Severity level for a hook violation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum HookSeverity {
    /// Invariant broken — solver correctness compromised.
    Critical,
    /// Suspicious but not necessarily incorrect behavior.
    Warning,
    /// Informational observation.
    Info,
}

impl fmt::Display for HookSeverity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Critical => write!(f, "CRITICAL"),
            Self::Warning => write!(f, "WARNING"),
            Self::Info => write!(f, "INFO"),
        }
    }
}

// ---------------------------------------------------------------------------
// MonitorHookConfig
// ---------------------------------------------------------------------------

/// Configuration for the monitor hook layer.
#[derive(Debug, Clone)]
pub(crate) struct MonitorHookConfig {
    /// Whether hook monitoring is active. When false, all events are ignored.
    pub(crate) enabled: bool,
    /// Fraction of events to check (0.0 = none, 1.0 = all).
    /// Uses deterministic counter-based sampling.
    pub(crate) sample_rate: f64,
    /// Maximum violations before auto-disabling per function.
    pub(crate) max_violations_per_function: usize,
    /// Whether to log violations to stderr.
    pub(crate) log_to_stderr: bool,
    /// Whether to set an abort flag on critical violations (does not actually
    /// abort — sets `abort_requested` for the caller to inspect).
    pub(crate) abort_on_critical: bool,
}

impl Default for MonitorHookConfig {
    fn default() -> Self {
        Self {
            enabled: false,
            sample_rate: 0.01,
            max_violations_per_function: 100,
            log_to_stderr: false,
            abort_on_critical: false,
        }
    }
}

impl MonitorHookConfig {
    /// Create a builder starting from default values.
    #[must_use]
    pub(crate) fn builder() -> MonitorHookConfigBuilder {
        MonitorHookConfigBuilder {
            config: Self::default(),
        }
    }
}

// ---------------------------------------------------------------------------
// MonitorHookConfigBuilder
// ---------------------------------------------------------------------------

/// Builder for [`MonitorHookConfig`].
#[derive(Debug, Clone)]
pub(crate) struct MonitorHookConfigBuilder {
    config: MonitorHookConfig,
}

impl MonitorHookConfigBuilder {
    #[must_use]
    pub(crate) fn enabled(mut self, enabled: bool) -> Self {
        self.config.enabled = enabled;
        self
    }

    #[must_use]
    pub(crate) fn sample_rate(mut self, rate: f64) -> Self {
        self.config.sample_rate = rate;
        self
    }

    #[must_use]
    pub(crate) fn max_violations_per_function(mut self, max: usize) -> Self {
        self.config.max_violations_per_function = max;
        self
    }

    #[must_use]
    pub(crate) fn log_to_stderr(mut self, log: bool) -> Self {
        self.config.log_to_stderr = log;
        self
    }

    #[must_use]
    pub(crate) fn abort_on_critical(mut self, abort: bool) -> Self {
        self.config.abort_on_critical = abort;
        self
    }

    #[must_use]
    pub(crate) fn build(self) -> MonitorHookConfig {
        self.config
    }
}

// ---------------------------------------------------------------------------
// HookEvent
// ---------------------------------------------------------------------------

/// A monitorable solver event.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum HookEvent {
    /// Boolean Constraint Propagation step.
    BcpPropagation {
        clause_count: usize,
        watch_count: usize,
    },
    /// A branching decision was made.
    DecisionMade {
        variable: u32,
        phase: bool,
        level: usize,
    },
    /// A conflict was detected during propagation.
    ConflictDetected {
        conflict_clause_size: usize,
        backtrack_level: usize,
    },
    /// The solver triggered a restart.
    RestartTriggered {
        conflicts_since_last: usize,
        total_conflicts: usize,
    },
    /// A clause was added to the clause database.
    ClauseAdded {
        clause_id: usize,
        size: usize,
        is_learned: bool,
    },
    /// A clause was removed from the clause database.
    ClauseRemoved { clause_id: usize, reason: String },
}

impl HookEvent {
    /// Return a short type tag for aggregation.
    fn type_tag(&self) -> &'static str {
        match self {
            Self::BcpPropagation { .. } => "BcpPropagation",
            Self::DecisionMade { .. } => "DecisionMade",
            Self::ConflictDetected { .. } => "ConflictDetected",
            Self::RestartTriggered { .. } => "RestartTriggered",
            Self::ClauseAdded { .. } => "ClauseAdded",
            Self::ClauseRemoved { .. } => "ClauseRemoved",
        }
    }
}

impl fmt::Display for HookEvent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BcpPropagation {
                clause_count,
                watch_count,
            } => write!(
                f,
                "BcpPropagation(clauses={clause_count}, watches={watch_count})"
            ),
            Self::DecisionMade {
                variable,
                phase,
                level,
            } => write!(
                f,
                "DecisionMade(var={variable}, phase={phase}, level={level})"
            ),
            Self::ConflictDetected {
                conflict_clause_size,
                backtrack_level,
            } => write!(
                f,
                "ConflictDetected(size={conflict_clause_size}, bt_level={backtrack_level})"
            ),
            Self::RestartTriggered {
                conflicts_since_last,
                total_conflicts,
            } => write!(
                f,
                "RestartTriggered(since_last={conflicts_since_last}, total={total_conflicts})"
            ),
            Self::ClauseAdded {
                clause_id,
                size,
                is_learned,
            } => write!(
                f,
                "ClauseAdded(id={clause_id}, size={size}, learned={is_learned})"
            ),
            Self::ClauseRemoved { clause_id, reason } => {
                write!(f, "ClauseRemoved(id={clause_id}, reason={reason})")
            }
        }
    }
}

// ---------------------------------------------------------------------------
// HookViolation
// ---------------------------------------------------------------------------

/// A recorded hook violation.
#[derive(Debug, Clone)]
pub(crate) struct HookViolation {
    /// The event that triggered the violation.
    pub(crate) event: HookEvent,
    /// Human-readable description of the violation.
    pub(crate) description: String,
    /// Severity of the violation.
    pub(crate) severity: HookSeverity,
    /// Additional context for diagnostics.
    pub(crate) context: String,
}

impl fmt::Display for HookViolation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[{}] {}: {} ({})",
            self.severity, self.event, self.description, self.context
        )
    }
}

// ---------------------------------------------------------------------------
// HookSummary
// ---------------------------------------------------------------------------

/// Aggregate statistics from a [`MonitorHookState`].
#[derive(Debug, Clone)]
pub(crate) struct HookSummary {
    /// Total events received (including those skipped by sampling).
    pub(crate) events_recorded: usize,
    /// Events that passed the sampling filter and were checked.
    pub(crate) events_sampled: usize,
    /// Total violations detected.
    pub(crate) violations_detected: usize,
    /// Violation count keyed by severity.
    pub(crate) by_severity: HashMap<HookSeverity, usize>,
    /// Event count keyed by event type tag.
    pub(crate) by_event_type: HashMap<String, usize>,
}

// ---------------------------------------------------------------------------
// MonitorHookState
// ---------------------------------------------------------------------------

/// Per-function monitoring state for hook events.
///
/// Tracks events, applies deterministic sampling, validates contract rules,
/// and records violations up to the configured limit.
pub(crate) struct MonitorHookState {
    config: MonitorHookConfig,
    /// All recorded violations.
    violations: Vec<HookViolation>,
    /// Total events received (pre-sampling).
    events_recorded: usize,
    /// Events that passed the sampling filter.
    events_sampled: usize,
    /// Deterministic sampling counter.
    sample_counter: u64,
    /// Set to true when `max_violations_per_function` is reached.
    auto_disabled: bool,
    /// Set to true when `abort_on_critical` fires.
    pub(crate) abort_requested: bool,
    /// Highest decision level seen so far (for monotonicity checking).
    max_decision_level: usize,
    /// Current max decision level for conflict backtrack validation.
    current_max_level: usize,
    /// Count of events by type tag.
    event_type_counts: HashMap<String, usize>,
}

impl MonitorHookState {
    /// Create a new per-function monitoring state with the given configuration.
    #[must_use]
    pub(crate) fn new(config: MonitorHookConfig) -> Self {
        Self {
            config,
            violations: Vec::new(),
            events_recorded: 0,
            events_sampled: 0,
            sample_counter: 0,
            auto_disabled: false,
            abort_requested: false,
            max_decision_level: 0,
            current_max_level: 0,
            event_type_counts: HashMap::new(),
        }
    }

    /// Whether this event should be checked based on sampling and state.
    ///
    /// Uses deterministic counter-based sampling: the fraction of events
    /// that pass is approximately `sample_rate`.
    fn should_check(&mut self) -> bool {
        if !self.config.enabled || self.auto_disabled {
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

    /// Record a violation, respecting max violations and abort-on-critical.
    fn record_violation(&mut self, violation: HookViolation) {
        if self.config.abort_on_critical && violation.severity == HookSeverity::Critical {
            self.abort_requested = true;
        }
        if self.config.log_to_stderr {
            eprintln!("[monitor_hook] {}", violation);
        }
        self.violations.push(violation);
        if self.violations.len() >= self.config.max_violations_per_function {
            self.auto_disabled = true;
        }
    }

    /// Record an event and check its contract.
    ///
    /// Returns `Some(violation)` if the event violates a contract rule,
    /// `None` if the event is valid or was skipped by sampling.
    pub(crate) fn record_event(&mut self, event: HookEvent) -> Option<HookViolation> {
        self.events_recorded += 1;
        *self
            .event_type_counts
            .entry(event.type_tag().to_string())
            .or_insert(0) += 1;

        if !self.should_check() {
            return None;
        }
        self.events_sampled += 1;

        self.check_contract(&event)
    }

    /// Validate the contract for a specific event.
    fn check_contract(&mut self, event: &HookEvent) -> Option<HookViolation> {
        match event {
            HookEvent::BcpPropagation {
                clause_count,
                watch_count,
            } => self.check_bcp(*clause_count, *watch_count, event),
            HookEvent::DecisionMade {
                variable: _,
                phase: _,
                level,
            } => self.check_decision(*level, event),
            HookEvent::ConflictDetected {
                conflict_clause_size: _,
                backtrack_level,
            } => self.check_conflict(*backtrack_level, event),
            HookEvent::RestartTriggered {
                conflicts_since_last,
                total_conflicts: _,
            } => self.check_restart(*conflicts_since_last, event),
            HookEvent::ClauseAdded {
                clause_id: _,
                size,
                is_learned: _,
            } => self.check_clause_added(*size, event),
            HookEvent::ClauseRemoved {
                clause_id: _,
                reason,
            } => self.check_clause_removed(reason, event),
        }
    }

    /// BCP: watch_count should be >= 2 * clause_count (two-watched-literal).
    fn check_bcp(
        &mut self,
        clause_count: usize,
        watch_count: usize,
        event: &HookEvent,
    ) -> Option<HookViolation> {
        let min_watches = 2 * clause_count;
        if watch_count < min_watches {
            let violation = HookViolation {
                event: event.clone(),
                description: format!(
                    "watch_count ({watch_count}) < 2 * clause_count ({min_watches}): \
                     two-watched-literal invariant violated"
                ),
                severity: HookSeverity::Critical,
                context: format!("clause_count={clause_count}, watch_count={watch_count}"),
            };
            self.record_violation(violation.clone());
            return Some(violation);
        }
        None
    }

    /// Decision: level should monotonically increase during decision phase.
    fn check_decision(&mut self, level: usize, event: &HookEvent) -> Option<HookViolation> {
        if level < self.max_decision_level {
            let violation = HookViolation {
                event: event.clone(),
                description: format!(
                    "decision level ({level}) < max seen level ({}): \
                     monotonicity violated",
                    self.max_decision_level
                ),
                severity: HookSeverity::Warning,
                context: format!(
                    "level={level}, max_decision_level={}",
                    self.max_decision_level
                ),
            };
            self.record_violation(violation.clone());
            return Some(violation);
        }
        // Update max level trackers.
        self.max_decision_level = level;
        if level > self.current_max_level {
            self.current_max_level = level;
        }
        None
    }

    /// Conflict: backtrack_level should be < current max level.
    fn check_conflict(
        &mut self,
        backtrack_level: usize,
        event: &HookEvent,
    ) -> Option<HookViolation> {
        if self.current_max_level > 0 && backtrack_level >= self.current_max_level {
            let violation = HookViolation {
                event: event.clone(),
                description: format!(
                    "backtrack_level ({backtrack_level}) >= current_max_level ({}): \
                     backtrack must reduce level",
                    self.current_max_level
                ),
                severity: HookSeverity::Critical,
                context: format!(
                    "backtrack_level={backtrack_level}, current_max_level={}",
                    self.current_max_level
                ),
            };
            self.record_violation(violation.clone());
            // Reset decision tracking after conflict.
            self.max_decision_level = backtrack_level;
            return Some(violation);
        }
        // Reset decision tracking to the backtrack level.
        self.max_decision_level = backtrack_level;
        None
    }

    /// Restart: conflicts_since_last should be > 0.
    fn check_restart(
        &mut self,
        conflicts_since_last: usize,
        event: &HookEvent,
    ) -> Option<HookViolation> {
        if conflicts_since_last == 0 {
            let violation = HookViolation {
                event: event.clone(),
                description: "restart triggered with zero conflicts since last restart".to_string(),
                severity: HookSeverity::Warning,
                context: "conflicts_since_last=0".to_string(),
            };
            self.record_violation(violation.clone());
            return Some(violation);
        }
        // Reset decision level tracking after restart.
        self.max_decision_level = 0;
        self.current_max_level = 0;
        None
    }

    /// ClauseAdded: size should be > 0.
    fn check_clause_added(&mut self, size: usize, event: &HookEvent) -> Option<HookViolation> {
        if size == 0 {
            let violation = HookViolation {
                event: event.clone(),
                description: "clause added with size 0".to_string(),
                severity: HookSeverity::Critical,
                context: "size=0".to_string(),
            };
            self.record_violation(violation.clone());
            return Some(violation);
        }
        None
    }

    /// ClauseRemoved: reason should be non-empty.
    fn check_clause_removed(&mut self, reason: &str, event: &HookEvent) -> Option<HookViolation> {
        if reason.is_empty() {
            let violation = HookViolation {
                event: event.clone(),
                description: "clause removed with empty reason".to_string(),
                severity: HookSeverity::Info,
                context: "reason=<empty>".to_string(),
            };
            self.record_violation(violation.clone());
            return Some(violation);
        }
        None
    }

    // -------------------------------------------------------------------
    // Accessors
    // -------------------------------------------------------------------

    /// Total number of events received (including those skipped by sampling).
    #[must_use]
    pub(crate) fn event_count(&self) -> usize {
        self.events_recorded
    }

    /// Number of violations recorded so far.
    #[must_use]
    pub(crate) fn violation_count(&self) -> usize {
        self.violations.len()
    }

    /// Whether the monitor is currently active (enabled, not auto-disabled).
    #[must_use]
    pub(crate) fn is_active(&self) -> bool {
        self.config.enabled && !self.auto_disabled
    }

    /// All recorded violations.
    #[must_use]
    pub(crate) fn violations(&self) -> &[HookViolation] {
        &self.violations
    }

    /// Produce an aggregate summary.
    #[must_use]
    pub(crate) fn summary(&self) -> HookSummary {
        let mut by_severity: HashMap<HookSeverity, usize> = HashMap::new();
        for v in &self.violations {
            *by_severity.entry(v.severity).or_insert(0) += 1;
        }

        HookSummary {
            events_recorded: self.events_recorded,
            events_sampled: self.events_sampled,
            violations_detected: self.violations.len(),
            by_severity,
            by_event_type: self.event_type_counts.clone(),
        }
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: create an enabled config that checks all events.
    fn enabled_config() -> MonitorHookConfig {
        MonitorHookConfig {
            enabled: true,
            sample_rate: 1.0,
            max_violations_per_function: 100,
            log_to_stderr: false,
            abort_on_critical: false,
        }
    }

    // -----------------------------------------------------------------------
    // 1. Default config construction
    // -----------------------------------------------------------------------

    #[test]
    fn test_default_config_values() {
        let config = MonitorHookConfig::default();
        assert!(!config.enabled);
        assert!((config.sample_rate - 0.01).abs() < f64::EPSILON);
        assert_eq!(config.max_violations_per_function, 100);
        assert!(!config.log_to_stderr);
        assert!(!config.abort_on_critical);
    }

    // -----------------------------------------------------------------------
    // 2. Config builder pattern
    // -----------------------------------------------------------------------

    #[test]
    fn test_config_builder() {
        let config = MonitorHookConfig::builder()
            .enabled(true)
            .sample_rate(0.5)
            .max_violations_per_function(50)
            .log_to_stderr(true)
            .abort_on_critical(true)
            .build();
        assert!(config.enabled);
        assert!((config.sample_rate - 0.5).abs() < f64::EPSILON);
        assert_eq!(config.max_violations_per_function, 50);
        assert!(config.log_to_stderr);
        assert!(config.abort_on_critical);
    }

    // -----------------------------------------------------------------------
    // 3. HookEvent creation for each variant
    // -----------------------------------------------------------------------

    #[test]
    fn test_hook_event_bcp_creation() {
        let event = HookEvent::BcpPropagation {
            clause_count: 10,
            watch_count: 20,
        };
        assert_eq!(event.type_tag(), "BcpPropagation");
        let display = format!("{event}");
        assert!(display.contains("clauses=10"));
        assert!(display.contains("watches=20"));
    }

    #[test]
    fn test_hook_event_decision_creation() {
        let event = HookEvent::DecisionMade {
            variable: 42,
            phase: true,
            level: 5,
        };
        assert_eq!(event.type_tag(), "DecisionMade");
        let display = format!("{event}");
        assert!(display.contains("var=42"));
    }

    #[test]
    fn test_hook_event_conflict_creation() {
        let event = HookEvent::ConflictDetected {
            conflict_clause_size: 3,
            backtrack_level: 1,
        };
        assert_eq!(event.type_tag(), "ConflictDetected");
    }

    #[test]
    fn test_hook_event_restart_creation() {
        let event = HookEvent::RestartTriggered {
            conflicts_since_last: 50,
            total_conflicts: 200,
        };
        assert_eq!(event.type_tag(), "RestartTriggered");
    }

    #[test]
    fn test_hook_event_clause_added_creation() {
        let event = HookEvent::ClauseAdded {
            clause_id: 7,
            size: 3,
            is_learned: true,
        };
        assert_eq!(event.type_tag(), "ClauseAdded");
    }

    #[test]
    fn test_hook_event_clause_removed_creation() {
        let event = HookEvent::ClauseRemoved {
            clause_id: 7,
            reason: "activity decay".to_string(),
        };
        assert_eq!(event.type_tag(), "ClauseRemoved");
    }

    // -----------------------------------------------------------------------
    // 4. Disabled monitor records nothing
    // -----------------------------------------------------------------------

    #[test]
    fn test_disabled_monitor_records_nothing() {
        let config = MonitorHookConfig {
            enabled: false,
            sample_rate: 1.0,
            max_violations_per_function: 100,
            log_to_stderr: false,
            abort_on_critical: false,
        };
        let mut state = MonitorHookState::new(config);

        // These would all be violations if enabled.
        let result = state.record_event(HookEvent::BcpPropagation {
            clause_count: 10,
            watch_count: 5,
        });
        assert!(result.is_none());
        // Events are still counted even when disabled.
        assert_eq!(state.event_count(), 1);
        assert_eq!(state.violation_count(), 0);
        assert!(!state.is_active());
    }

    // -----------------------------------------------------------------------
    // 5. Enabled monitor records events
    // -----------------------------------------------------------------------

    #[test]
    fn test_enabled_monitor_records_events() {
        let mut state = MonitorHookState::new(enabled_config());

        let result = state.record_event(HookEvent::BcpPropagation {
            clause_count: 10,
            watch_count: 20,
        });
        assert!(result.is_none()); // valid event
        assert_eq!(state.event_count(), 1);
        assert_eq!(state.violation_count(), 0);
        assert!(state.is_active());
    }

    // -----------------------------------------------------------------------
    // 6. Sample rate filtering
    // -----------------------------------------------------------------------

    #[test]
    fn test_sample_rate_filtering() {
        let config = MonitorHookConfig {
            enabled: true,
            sample_rate: 0.1, // 10%
            max_violations_per_function: 10000,
            log_to_stderr: false,
            abort_on_critical: false,
        };
        let mut state = MonitorHookState::new(config);

        // Send 1000 valid events; ~10% should be sampled.
        for _ in 0..1000 {
            state.record_event(HookEvent::BcpPropagation {
                clause_count: 5,
                watch_count: 10,
            });
        }

        assert_eq!(state.event_count(), 1000);
        // With period = ceil(1/0.1) = 10, exactly 100 events sampled.
        assert_eq!(state.events_sampled, 100);
    }

    // -----------------------------------------------------------------------
    // 7. Max violations auto-disable
    // -----------------------------------------------------------------------

    #[test]
    fn test_max_violations_auto_disable() {
        let config = MonitorHookConfig {
            enabled: true,
            sample_rate: 1.0,
            max_violations_per_function: 3,
            log_to_stderr: false,
            abort_on_critical: false,
        };
        let mut state = MonitorHookState::new(config);

        // Each clause-added with size=0 is a violation.
        for i in 0..5 {
            state.record_event(HookEvent::ClauseAdded {
                clause_id: i,
                size: 0,
                is_learned: false,
            });
        }

        assert_eq!(state.violation_count(), 3);
        assert!(!state.is_active());
    }

    // -----------------------------------------------------------------------
    // 8. BCP contract violation detection
    // -----------------------------------------------------------------------

    #[test]
    fn test_bcp_contract_violation() {
        let mut state = MonitorHookState::new(enabled_config());

        let result = state.record_event(HookEvent::BcpPropagation {
            clause_count: 10,
            watch_count: 15, // needs >= 20
        });
        let v = result.expect("BCP violation should produce a diagnostic");
        assert_eq!(v.severity, HookSeverity::Critical);
        assert!(v.description.contains("two-watched-literal"));
    }

    // -----------------------------------------------------------------------
    // 9. Decision level monotonicity check
    // -----------------------------------------------------------------------

    #[test]
    fn test_decision_level_monotonicity_violation() {
        let mut state = MonitorHookState::new(enabled_config());

        // Level 5 first.
        let r1 = state.record_event(HookEvent::DecisionMade {
            variable: 1,
            phase: true,
            level: 5,
        });
        assert!(r1.is_none());

        // Level 3 — violation (not monotonically increasing).
        let r2 = state.record_event(HookEvent::DecisionMade {
            variable: 2,
            phase: false,
            level: 3,
        });
        let v = r2.expect("monotonicity violation should produce a diagnostic");
        assert_eq!(v.severity, HookSeverity::Warning);
        assert!(v.description.contains("monotonicity"));
    }

    // -----------------------------------------------------------------------
    // 10. Conflict backtrack level check
    // -----------------------------------------------------------------------

    #[test]
    fn test_conflict_backtrack_level_violation() {
        let mut state = MonitorHookState::new(enabled_config());

        // Establish decision level 5.
        state.record_event(HookEvent::DecisionMade {
            variable: 1,
            phase: true,
            level: 5,
        });

        // Backtrack to level 5 (not less than current max = 5) — violation.
        let result = state.record_event(HookEvent::ConflictDetected {
            conflict_clause_size: 3,
            backtrack_level: 5,
        });
        let v = result.expect("backtrack violation should produce a diagnostic");
        assert_eq!(v.severity, HookSeverity::Critical);
        assert!(v.description.contains("backtrack"));
    }

    // -----------------------------------------------------------------------
    // 11. Restart zero-conflicts violation
    // -----------------------------------------------------------------------

    #[test]
    fn test_restart_zero_conflicts_violation() {
        let mut state = MonitorHookState::new(enabled_config());

        let result = state.record_event(HookEvent::RestartTriggered {
            conflicts_since_last: 0,
            total_conflicts: 100,
        });
        let v = result.expect("zero-conflicts restart should produce a diagnostic");
        assert_eq!(v.severity, HookSeverity::Warning);
        assert!(v.description.contains("zero conflicts"));
    }

    // -----------------------------------------------------------------------
    // 12. ClauseAdded zero-size violation
    // -----------------------------------------------------------------------

    #[test]
    fn test_clause_added_zero_size_violation() {
        let mut state = MonitorHookState::new(enabled_config());

        let result = state.record_event(HookEvent::ClauseAdded {
            clause_id: 1,
            size: 0,
            is_learned: true,
        });
        let v = result.expect("zero-size clause should produce a diagnostic");
        assert_eq!(v.severity, HookSeverity::Critical);
        assert!(v.description.contains("size 0"));
    }

    // -----------------------------------------------------------------------
    // 13. ClauseRemoved empty-reason violation
    // -----------------------------------------------------------------------

    #[test]
    fn test_clause_removed_empty_reason_violation() {
        let mut state = MonitorHookState::new(enabled_config());

        let result = state.record_event(HookEvent::ClauseRemoved {
            clause_id: 1,
            reason: String::new(),
        });
        let v = result.expect("empty-reason removal should produce a diagnostic");
        assert_eq!(v.severity, HookSeverity::Info);
        assert!(v.description.contains("empty reason"));
    }

    // -----------------------------------------------------------------------
    // 14. Summary event counting
    // -----------------------------------------------------------------------

    #[test]
    fn test_summary_event_counting() {
        let mut state = MonitorHookState::new(enabled_config());

        state.record_event(HookEvent::BcpPropagation {
            clause_count: 5,
            watch_count: 10,
        });
        state.record_event(HookEvent::BcpPropagation {
            clause_count: 3,
            watch_count: 6,
        });
        state.record_event(HookEvent::RestartTriggered {
            conflicts_since_last: 10,
            total_conflicts: 50,
        });

        let summary = state.summary();
        assert_eq!(summary.events_recorded, 3);
        assert_eq!(summary.events_sampled, 3);
    }

    // -----------------------------------------------------------------------
    // 15. Summary violation counting
    // -----------------------------------------------------------------------

    #[test]
    fn test_summary_violation_counting() {
        let mut state = MonitorHookState::new(enabled_config());

        // Two violations.
        state.record_event(HookEvent::ClauseAdded {
            clause_id: 1,
            size: 0,
            is_learned: false,
        });
        state.record_event(HookEvent::RestartTriggered {
            conflicts_since_last: 0,
            total_conflicts: 0,
        });
        // One valid event.
        state.record_event(HookEvent::BcpPropagation {
            clause_count: 5,
            watch_count: 10,
        });

        let summary = state.summary();
        assert_eq!(summary.violations_detected, 2);
        assert_eq!(summary.events_recorded, 3);
    }

    // -----------------------------------------------------------------------
    // 16. Summary by-severity breakdown
    // -----------------------------------------------------------------------

    #[test]
    fn test_summary_by_severity() {
        let mut state = MonitorHookState::new(enabled_config());

        // Critical: clause added with size 0.
        state.record_event(HookEvent::ClauseAdded {
            clause_id: 1,
            size: 0,
            is_learned: false,
        });
        // Warning: restart with zero conflicts.
        state.record_event(HookEvent::RestartTriggered {
            conflicts_since_last: 0,
            total_conflicts: 0,
        });
        // Info: clause removed with empty reason.
        state.record_event(HookEvent::ClauseRemoved {
            clause_id: 2,
            reason: String::new(),
        });

        let summary = state.summary();
        assert_eq!(summary.by_severity.get(&HookSeverity::Critical), Some(&1));
        assert_eq!(summary.by_severity.get(&HookSeverity::Warning), Some(&1));
        assert_eq!(summary.by_severity.get(&HookSeverity::Info), Some(&1));
    }

    // -----------------------------------------------------------------------
    // 17. Summary by-event-type breakdown
    // -----------------------------------------------------------------------

    #[test]
    fn test_summary_by_event_type() {
        let mut state = MonitorHookState::new(enabled_config());

        state.record_event(HookEvent::BcpPropagation {
            clause_count: 5,
            watch_count: 10,
        });
        state.record_event(HookEvent::BcpPropagation {
            clause_count: 3,
            watch_count: 6,
        });
        state.record_event(HookEvent::DecisionMade {
            variable: 1,
            phase: true,
            level: 1,
        });

        let summary = state.summary();
        assert_eq!(summary.by_event_type.get("BcpPropagation"), Some(&2));
        assert_eq!(summary.by_event_type.get("DecisionMade"), Some(&1));
    }

    // -----------------------------------------------------------------------
    // 18. No violation for valid BCP
    // -----------------------------------------------------------------------

    #[test]
    fn test_no_violation_valid_bcp() {
        let mut state = MonitorHookState::new(enabled_config());

        let result = state.record_event(HookEvent::BcpPropagation {
            clause_count: 10,
            watch_count: 20, // exactly 2 * 10
        });
        assert!(result.is_none());
        assert_eq!(state.violation_count(), 0);
    }

    // -----------------------------------------------------------------------
    // 19. No violation for valid decision
    // -----------------------------------------------------------------------

    #[test]
    fn test_no_violation_valid_decision() {
        let mut state = MonitorHookState::new(enabled_config());

        // Monotonically increasing levels.
        let r1 = state.record_event(HookEvent::DecisionMade {
            variable: 1,
            phase: true,
            level: 1,
        });
        let r2 = state.record_event(HookEvent::DecisionMade {
            variable: 2,
            phase: false,
            level: 2,
        });
        let r3 = state.record_event(HookEvent::DecisionMade {
            variable: 3,
            phase: true,
            level: 3,
        });

        assert!(r1.is_none());
        assert!(r2.is_none());
        assert!(r3.is_none());
        assert_eq!(state.violation_count(), 0);
    }

    // -----------------------------------------------------------------------
    // 20. No violation for valid conflict
    // -----------------------------------------------------------------------

    #[test]
    fn test_no_violation_valid_conflict() {
        let mut state = MonitorHookState::new(enabled_config());

        // Establish level 5.
        state.record_event(HookEvent::DecisionMade {
            variable: 1,
            phase: true,
            level: 5,
        });

        // Backtrack to level 2 (< 5) — valid.
        let result = state.record_event(HookEvent::ConflictDetected {
            conflict_clause_size: 3,
            backtrack_level: 2,
        });
        assert!(result.is_none());
        assert_eq!(state.violation_count(), 0);
    }

    // -----------------------------------------------------------------------
    // 21. No violation for valid restart
    // -----------------------------------------------------------------------

    #[test]
    fn test_no_violation_valid_restart() {
        let mut state = MonitorHookState::new(enabled_config());

        let result = state.record_event(HookEvent::RestartTriggered {
            conflicts_since_last: 50,
            total_conflicts: 200,
        });
        assert!(result.is_none());
        assert_eq!(state.violation_count(), 0);
    }

    // -----------------------------------------------------------------------
    // 22. Mixed events sequence
    // -----------------------------------------------------------------------

    #[test]
    fn test_mixed_events_sequence() {
        let mut state = MonitorHookState::new(enabled_config());

        // Valid BCP.
        state.record_event(HookEvent::BcpPropagation {
            clause_count: 5,
            watch_count: 10,
        });
        // Valid decision.
        state.record_event(HookEvent::DecisionMade {
            variable: 1,
            phase: true,
            level: 1,
        });
        // Valid clause add.
        state.record_event(HookEvent::ClauseAdded {
            clause_id: 1,
            size: 3,
            is_learned: true,
        });
        // Invalid restart (zero conflicts).
        let r = state.record_event(HookEvent::RestartTriggered {
            conflicts_since_last: 0,
            total_conflicts: 10,
        });
        assert!(r.is_some());
        // Valid clause remove.
        state.record_event(HookEvent::ClauseRemoved {
            clause_id: 1,
            reason: "activity decay".to_string(),
        });

        assert_eq!(state.event_count(), 5);
        assert_eq!(state.violation_count(), 1);
    }

    // -----------------------------------------------------------------------
    // 23. High violation rate triggers auto-disable
    // -----------------------------------------------------------------------

    #[test]
    fn test_high_violation_rate_auto_disable() {
        let config = MonitorHookConfig {
            enabled: true,
            sample_rate: 1.0,
            max_violations_per_function: 5,
            log_to_stderr: false,
            abort_on_critical: false,
        };
        let mut state = MonitorHookState::new(config);

        // Send 10 violation-causing events (clause added with size 0).
        for i in 0..10 {
            state.record_event(HookEvent::ClauseAdded {
                clause_id: i,
                size: 0,
                is_learned: false,
            });
        }

        // Should have stopped at 5.
        assert_eq!(state.violation_count(), 5);
        assert!(!state.is_active());

        let summary = state.summary();
        assert_eq!(summary.violations_detected, 5);
    }

    // -----------------------------------------------------------------------
    // 24. Critical violation with abort_on_critical
    // -----------------------------------------------------------------------

    #[test]
    fn test_abort_on_critical_sets_flag() {
        let config = MonitorHookConfig {
            enabled: true,
            sample_rate: 1.0,
            max_violations_per_function: 100,
            log_to_stderr: false,
            abort_on_critical: true,
        };
        let mut state = MonitorHookState::new(config);
        assert!(!state.abort_requested);

        // BCP violation is Critical severity.
        state.record_event(HookEvent::BcpPropagation {
            clause_count: 10,
            watch_count: 5,
        });
        assert!(state.abort_requested);
    }

    // -----------------------------------------------------------------------
    // 25. Log to stderr with log_to_stderr flag
    // -----------------------------------------------------------------------

    #[test]
    fn test_log_to_stderr_does_not_panic() {
        let config = MonitorHookConfig {
            enabled: true,
            sample_rate: 1.0,
            max_violations_per_function: 100,
            log_to_stderr: true,
            abort_on_critical: false,
        };
        let mut state = MonitorHookState::new(config);

        // This should write to stderr but not panic.
        let result = state.record_event(HookEvent::ClauseAdded {
            clause_id: 1,
            size: 0,
            is_learned: false,
        });
        assert!(result.is_some());
        assert!(state.config.log_to_stderr);
    }

    // -----------------------------------------------------------------------
    // 26. Multiple functions independent state
    // -----------------------------------------------------------------------

    #[test]
    fn test_multiple_functions_independent_state() {
        let config = enabled_config();
        let mut state_a = MonitorHookState::new(config.clone());
        let mut state_b = MonitorHookState::new(config);

        // Violation in A.
        state_a.record_event(HookEvent::ClauseAdded {
            clause_id: 1,
            size: 0,
            is_learned: false,
        });

        // Valid event in B.
        state_b.record_event(HookEvent::BcpPropagation {
            clause_count: 5,
            watch_count: 10,
        });

        assert_eq!(state_a.violation_count(), 1);
        assert_eq!(state_b.violation_count(), 0);
        assert_eq!(state_a.event_count(), 1);
        assert_eq!(state_b.event_count(), 1);
    }

    // -----------------------------------------------------------------------
    // 27. Event ordering preserved
    // -----------------------------------------------------------------------

    #[test]
    fn test_event_ordering_preserved() {
        let mut state = MonitorHookState::new(enabled_config());

        // Three violations in order.
        state.record_event(HookEvent::ClauseAdded {
            clause_id: 1,
            size: 0,
            is_learned: false,
        });
        state.record_event(HookEvent::RestartTriggered {
            conflicts_since_last: 0,
            total_conflicts: 0,
        });
        state.record_event(HookEvent::ClauseRemoved {
            clause_id: 2,
            reason: String::new(),
        });

        let violations = state.violations();
        assert_eq!(violations.len(), 3);
        assert_eq!(violations[0].event.type_tag(), "ClauseAdded");
        assert_eq!(violations[1].event.type_tag(), "RestartTriggered");
        assert_eq!(violations[2].event.type_tag(), "ClauseRemoved");
    }

    // -----------------------------------------------------------------------
    // 28. is_active transitions
    // -----------------------------------------------------------------------

    #[test]
    fn test_is_active_transitions() {
        let config = MonitorHookConfig {
            enabled: true,
            sample_rate: 1.0,
            max_violations_per_function: 2,
            log_to_stderr: false,
            abort_on_critical: false,
        };
        let mut state = MonitorHookState::new(config);

        assert!(state.is_active());

        // First violation.
        state.record_event(HookEvent::ClauseAdded {
            clause_id: 1,
            size: 0,
            is_learned: false,
        });
        assert!(state.is_active());

        // Second violation — reaches max_violations_per_function.
        state.record_event(HookEvent::ClauseAdded {
            clause_id: 2,
            size: 0,
            is_learned: false,
        });
        assert!(!state.is_active());
    }

    // -----------------------------------------------------------------------
    // 29. Summary after auto-disable
    // -----------------------------------------------------------------------

    #[test]
    fn test_summary_after_auto_disable() {
        let config = MonitorHookConfig {
            enabled: true,
            sample_rate: 1.0,
            max_violations_per_function: 2,
            log_to_stderr: false,
            abort_on_critical: false,
        };
        let mut state = MonitorHookState::new(config);

        // Two violations to trigger auto-disable.
        state.record_event(HookEvent::ClauseAdded {
            clause_id: 1,
            size: 0,
            is_learned: false,
        });
        state.record_event(HookEvent::ClauseAdded {
            clause_id: 2,
            size: 0,
            is_learned: false,
        });

        // Additional events after disable.
        state.record_event(HookEvent::BcpPropagation {
            clause_count: 5,
            watch_count: 10,
        });
        state.record_event(HookEvent::BcpPropagation {
            clause_count: 3,
            watch_count: 6,
        });

        let summary = state.summary();
        assert_eq!(summary.violations_detected, 2);
        assert_eq!(summary.events_recorded, 4); // all 4 counted
        assert_eq!(summary.events_sampled, 2); // only the first 2 sampled
    }

    // -----------------------------------------------------------------------
    // 30. Large event batch (1000+)
    // -----------------------------------------------------------------------

    #[test]
    fn test_large_event_batch() {
        let mut state = MonitorHookState::new(enabled_config());

        // 1500 valid BCP events.
        for i in 0..1500 {
            state.record_event(HookEvent::BcpPropagation {
                clause_count: i + 1,
                watch_count: 2 * (i + 1),
            });
        }

        assert_eq!(state.event_count(), 1500);
        assert_eq!(state.violation_count(), 0);
        assert!(state.is_active());

        let summary = state.summary();
        assert_eq!(summary.events_recorded, 1500);
        assert_eq!(summary.events_sampled, 1500);
        assert_eq!(summary.by_event_type.get("BcpPropagation"), Some(&1500));
    }

    // -----------------------------------------------------------------------
    // Additional edge case tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_abort_on_critical_not_triggered_by_warning() {
        let config = MonitorHookConfig {
            enabled: true,
            sample_rate: 1.0,
            max_violations_per_function: 100,
            log_to_stderr: false,
            abort_on_critical: true,
        };
        let mut state = MonitorHookState::new(config);

        // Restart with zero conflicts is Warning severity.
        state.record_event(HookEvent::RestartTriggered {
            conflicts_since_last: 0,
            total_conflicts: 10,
        });
        assert!(!state.abort_requested);
        assert_eq!(state.violation_count(), 1);
    }

    #[test]
    fn test_decision_same_level_not_violation() {
        let mut state = MonitorHookState::new(enabled_config());

        // Same level twice — not a decrease, so not a violation.
        let r1 = state.record_event(HookEvent::DecisionMade {
            variable: 1,
            phase: true,
            level: 3,
        });
        let r2 = state.record_event(HookEvent::DecisionMade {
            variable: 2,
            phase: false,
            level: 3,
        });

        assert!(r1.is_none());
        assert!(r2.is_none());
        assert_eq!(state.violation_count(), 0);
    }

    #[test]
    fn test_conflict_at_level_zero_no_violation() {
        let mut state = MonitorHookState::new(enabled_config());

        // No decisions made — current_max_level is 0. Backtrack to 0 is fine
        // because the check only fires when current_max_level > 0.
        let result = state.record_event(HookEvent::ConflictDetected {
            conflict_clause_size: 1,
            backtrack_level: 0,
        });
        assert!(result.is_none());
    }

    #[test]
    fn test_conflict_resets_decision_tracking() {
        let mut state = MonitorHookState::new(enabled_config());

        // Build up to level 5.
        state.record_event(HookEvent::DecisionMade {
            variable: 1,
            phase: true,
            level: 5,
        });

        // Valid conflict backtracks to level 2.
        state.record_event(HookEvent::ConflictDetected {
            conflict_clause_size: 3,
            backtrack_level: 2,
        });

        // Decision at level 3 is valid (3 > 2, the backtrack level).
        let r = state.record_event(HookEvent::DecisionMade {
            variable: 3,
            phase: true,
            level: 3,
        });
        assert!(r.is_none());
        assert_eq!(state.violation_count(), 0);
    }

    #[test]
    fn test_restart_resets_decision_tracking() {
        let mut state = MonitorHookState::new(enabled_config());

        // Build up to level 5.
        state.record_event(HookEvent::DecisionMade {
            variable: 1,
            phase: true,
            level: 5,
        });

        // Valid restart.
        state.record_event(HookEvent::RestartTriggered {
            conflicts_since_last: 10,
            total_conflicts: 50,
        });

        // Decision at level 1 is valid (restart reset to 0).
        let r = state.record_event(HookEvent::DecisionMade {
            variable: 2,
            phase: true,
            level: 1,
        });
        assert!(r.is_none());
        assert_eq!(state.violation_count(), 0);
    }

    #[test]
    fn test_hook_violation_display() {
        let violation = HookViolation {
            event: HookEvent::ClauseAdded {
                clause_id: 1,
                size: 0,
                is_learned: false,
            },
            description: "clause added with size 0".to_string(),
            severity: HookSeverity::Critical,
            context: "size=0".to_string(),
        };
        let display = format!("{violation}");
        assert!(display.contains("[CRITICAL]"));
        assert!(display.contains("ClauseAdded"));
        assert!(display.contains("clause added with size 0"));
    }

    #[test]
    fn test_severity_display() {
        assert_eq!(format!("{}", HookSeverity::Critical), "CRITICAL");
        assert_eq!(format!("{}", HookSeverity::Warning), "WARNING");
        assert_eq!(format!("{}", HookSeverity::Info), "INFO");
    }

    #[test]
    fn test_valid_clause_added_no_violation() {
        let mut state = MonitorHookState::new(enabled_config());

        let result = state.record_event(HookEvent::ClauseAdded {
            clause_id: 42,
            size: 5,
            is_learned: true,
        });
        assert!(result.is_none());
        assert_eq!(state.violation_count(), 0);
    }

    #[test]
    fn test_valid_clause_removed_no_violation() {
        let mut state = MonitorHookState::new(enabled_config());

        let result = state.record_event(HookEvent::ClauseRemoved {
            clause_id: 42,
            reason: "activity decay".to_string(),
        });
        assert!(result.is_none());
        assert_eq!(state.violation_count(), 0);
    }
}
