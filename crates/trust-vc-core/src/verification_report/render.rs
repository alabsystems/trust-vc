//! Rendering helpers for verification reports.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::io::{self, Write};

use super::*;

impl VerificationReport {
    /// Render this report as a human-readable string.
    ///
    /// When `options.verbose()` is true, includes per-step diagnostics,
    /// solver statistics, and assumption usage.
    #[must_use]
    pub fn format_with_options(&self, options: VerificationReportOptions) -> String {
        let mut lines = Vec::new();
        lines.push(format!("result: {}", verify_result_kind(self.result())));
        lines.push(format!(
            "total elapsed: {}",
            format_duration(self.total_elapsed())
        ));
        match self.result() {
            VerifyResult::Counterexample {
                obligation_name,
                model,
                ..
            } => {
                lines.push(format!("obligation: {obligation_name}"));
                if let Some(model) = model {
                    lines.push(format!("model: {model}"));
                }
            }
            // Deliberately renders NO "model:" line: this outcome has no model
            // and none may be invented for it.
            VerifyResult::NotProved { reason, .. } => {
                lines.push(format!("not proved (no model): {reason}"));
                if let Some(unknown) = unknown_from_verify_result(self.result()) {
                    lines.push(format!("category: {:?}", unknown.category()));
                    lines.push(format!("suggestion: {}", unknown.suggestion()));
                }
            }
            VerifyResult::Unknown { reason, .. } => {
                lines.push(format!("reason: {reason}"));
                if let Some(unknown) = unknown_from_verify_result(self.result()) {
                    lines.push(format!("category: {:?}", unknown.category()));
                    lines.push(format!("suggestion: {}", unknown.suggestion()));
                }
            }
            VerifyResult::Error { message } => {
                lines.push(format!("message: {message}"));
            }
            VerifyResult::Verified => {}
        }

        if options.verbose() {
            if let Some(pipeline) = self.pipeline() {
                lines.push(format!(
                    "pipeline: obligations={}, variables={}, assertions={}, assumptions={}",
                    pipeline.num_obligations(),
                    pipeline.num_variables(),
                    pipeline.has_assertions(),
                    pipeline.has_assumptions(),
                ));
            }

            if !self.steps().is_empty() {
                lines.push("steps:".to_string());
                for step in self.steps() {
                    lines.push(format!(
                        "  - {} [{}] {} {}",
                        step.label(),
                        step.phase(),
                        step.result(),
                        format_duration(step.elapsed()),
                    ));
                    if let Some(location) = step.location() {
                        lines.push(format!("    location: {location}"));
                    }
                    if let Some(unknown) = step.unknown() {
                        lines.push(format!("    category: {:?}", unknown.category()));
                        lines.push(format!("    suggestion: {}", unknown.suggestion()));
                    }
                    if let Some(recovery) = step.demand_inline_recovery() {
                        lines.push(format!(
                            "    note: {}",
                            format_demand_inline_recovery(recovery)
                        ));
                    }
                    if !step.used_assumptions().is_empty() {
                        lines.push(format!(
                            "    used assumptions: {}",
                            step.used_assumptions().join(", ")
                        ));
                    }
                    if let Some(solver) = step.solver() {
                        lines.push(format!(
                            "    solver: level={}, model_validated={}, term_bytes={}",
                            solver.verification_level(),
                            solver.sat_model_validated(),
                            solver
                                .term_bytes()
                                .map_or_else(|| "n/a".to_string(), |bytes| bytes.to_string()),
                        ));
                        lines.push(format!(
                            "    stats: conflicts={}, decisions={}, propagations={}, restarts={}, learned_clauses={}, deleted_clauses={}, theory_conflicts={}, theory_propagations={}, num_vars={}, num_clauses={}, num_assertions={}",
                            solver.conflicts(),
                            solver.decisions(),
                            solver.propagations(),
                            solver.restarts(),
                            solver.learned_clauses(),
                            solver.deleted_clauses(),
                            solver.theory_conflicts(),
                            solver.theory_propagations(),
                            solver.num_vars(),
                            solver.num_clauses(),
                            solver.num_assertions(),
                        ));
                        if !solver.extra().is_empty() {
                            lines.push("    extra:".to_string());
                            for (name, value) in solver.extra() {
                                lines.push(format!("      {name}={value}"));
                            }
                        }
                    }
                }
            }
        }

        lines.join("\n")
    }
}

impl std::fmt::Display for VerificationReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.format_with_options(VerificationReportOptions::new().with_verbose(true))
        )
    }
}

pub(crate) fn write_verbose_report_if_enabled<W: Write>(
    writer: &mut W,
    report: &VerificationReport,
    options: VerificationReportOptions,
) -> io::Result<()> {
    if options.verbose() {
        writer.write_all(report.format_with_options(options).as_bytes())?;
        writer.write_all(b"\n")?;
    }
    Ok(())
}

pub(crate) fn emit_verbose_report_if_enabled(
    report: &VerificationReport,
    options: VerificationReportOptions,
) {
    let mut stderr = io::stderr().lock();
    let _ = write_verbose_report_if_enabled(&mut stderr, report, options);
}

fn verify_result_kind(result: &VerifyResult) -> &'static str {
    match result {
        VerifyResult::Verified => "verified",
        VerifyResult::Counterexample { .. } => "counterexample",
        VerifyResult::NotProved { .. } => "not-proved",
        VerifyResult::Unknown { .. } => "unknown",
        VerifyResult::Error { .. } => "error",
    }
}

fn format_duration(duration: Duration) -> String {
    let seconds = duration.as_secs_f64();
    if seconds >= 1.0 {
        format!("{seconds:.2}s")
    } else if seconds >= 0.001 {
        format!("{:.2}ms", seconds * 1000.0)
    } else if seconds >= 0.000_001 {
        format!("{:.2}us", seconds * 1_000_000.0)
    } else {
        format!("{}ns", duration.as_nanos())
    }
}

fn format_demand_inline_recovery(recovery: &DemandInlineRecovery) -> String {
    let inlined = recovery.inlined_functions().join(", ");
    let contract_hint = if recovery.inlined_functions().len() == 1 {
        format!("consider strengthening {inlined}'s contract")
    } else {
        "consider strengthening those contracts".to_string()
    };
    format!(
        "verified after inlining {inlined} (depth {}); {contract_hint}",
        recovery.depth_used()
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_report_options_from_env_truthy_value() {
        // Serialized behind the process-wide env lock; TRUST_VC_VERBOSE is set
        // for the closure and its previous value restored on exit (also on panic).
        crate::env::with_serialized_env_vars(&[("TRUST_VC_VERBOSE", "true")], || {
            assert!(VerificationReportOptions::from_env().verbose());
        });
    }

    #[test]
    fn test_format_with_options_renders_extra_solver_stats() {
        let mut extra = BTreeMap::new();
        extra.insert(
            "quantifier.instantiations.total".to_string(),
            SolverStatValue::Int(12),
        );
        extra.insert(
            "time.dpll.sat_solve".to_string(),
            SolverStatValue::Float(0.25),
        );
        let report = VerificationReport {
            result: VerifyResult::unknown(
                "Solver returned unknown (timeout) for 'lemma'",
                Some(UnknownCategory::Timeout),
            ),
            pipeline: Some(PipelineSummary {
                num_obligations: 1,
                num_variables: 2,
                has_assertions: true,
                has_assumptions: false,
            }),
            steps: vec![StepDiagnostic {
                label: "lemma".to_string(),
                condition: None,
                location: Some("src/lib.rs:10:5".to_string()),
                phase: VerificationPhase::Assertion,
                elapsed: Duration::from_millis(12),
                result: StepResultKind::Unknown,
                unknown: Some(UnknownDiagnostic {
                    category: UnknownCategory::Timeout,
                    suggestion: UnknownCategory::Timeout.actionable_suggestion(),
                }),
                demand_inline_recovery: None,
                used_assumptions: vec!["positive".to_string()],
                solver: Some(SolverStats {
                    conflicts: 1,
                    decisions: 2,
                    propagations: 3,
                    restarts: 4,
                    learned_clauses: 5,
                    deleted_clauses: 6,
                    theory_conflicts: 7,
                    theory_propagations: 8,
                    num_vars: 9,
                    num_clauses: 10,
                    num_assertions: 11,
                    extra,
                    verification_level: "debug-checked".to_string(),
                    sat_model_validated: false,
                    term_bytes: Some(99),
                }),
                #[cfg(feature = "proof-certificates")]
                proof: None,
            }],
            total_elapsed: Duration::from_millis(15),
            #[cfg(feature = "proof-certificates")]
            proof: None,
        };

        let rendered =
            report.format_with_options(VerificationReportOptions::new().with_verbose(true));
        assert!(rendered.contains("quantifier.instantiations.total=12"));
        assert!(rendered.contains("time.dpll.sat_solve=0.25"));
        assert!(rendered.contains("category: Timeout"));
        assert!(rendered.contains("used assumptions: positive"));
    }

    #[test]
    fn test_write_verbose_report_if_enabled() {
        let report = VerificationReport::from_parts(
            VerifyResult::Verified,
            None,
            Vec::new(),
            Duration::from_millis(1),
        );
        let mut buffer = Vec::new();
        write_verbose_report_if_enabled(
            &mut buffer,
            &report,
            VerificationReportOptions::new().with_verbose(true),
        )
        .expect("verbose report should write to buffer");
        let rendered = String::from_utf8(buffer).expect("buffer should contain utf8");
        assert!(rendered.contains("result: verified"));
    }
}
