//! Compilation-oriented proven-fact extraction from verification reports.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::fmt::Write as _;

use thiserror::Error;

use crate::json_escape;
use crate::verification_report::{
    StepDiagnostic, StepResultKind, VerificationPhase, VerificationReport,
};
use crate::VerifyResult;

/// A single proven fact that can drive compilation-oriented optimization.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use]
pub struct CompilationProvenFact {
    condition: String,
    step_label: String,
    source_location: Option<String>,
    phase: VerificationPhase,
}

impl CompilationProvenFact {
    fn from_step(step: &StepDiagnostic) -> Self {
        Self {
            condition: step
                .condition()
                .filter(|condition| !condition.trim().is_empty())
                .unwrap_or(step.label())
                .to_string(),
            step_label: step.label().to_string(),
            source_location: step.location().map(str::to_string),
            phase: step.phase(),
        }
    }

    /// Returns the proven condition expression text.
    #[must_use]
    pub fn condition(&self) -> &str {
        &self.condition
    }

    /// Returns the verification step label that proved this fact.
    #[must_use]
    pub fn step_label(&self) -> &str {
        &self.step_label
    }

    /// Returns the source location of the proven assertion, if available.
    #[must_use]
    pub fn source_location(&self) -> Option<&str> {
        self.source_location.as_deref()
    }

    /// Returns the verification phase that produced this fact.
    #[must_use]
    pub const fn phase(&self) -> VerificationPhase {
        self.phase
    }
}

/// Compilation-facing proven facts extracted from a verified report.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[must_use]
pub struct CompilationProvenFacts {
    bounds: Vec<CompilationProvenFact>,
    nonzero: Vec<CompilationProvenFact>,
    overflow_free: Vec<CompilationProvenFact>,
    safe_indexing: Vec<CompilationProvenFact>,
    dead_branches: Vec<CompilationProvenFact>,
}

/// Extraction failure for compilation-oriented proven facts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum CompilationProvenFactsError {
    #[error("cannot extract compilation proven facts from a non-verified verification report")]
    ReportNotVerified,
}

impl CompilationProvenFacts {
    /// Extract compilation-oriented proven facts from a verified report.
    pub fn try_from_report(
        report: &VerificationReport,
    ) -> Result<Self, CompilationProvenFactsError> {
        if !matches!(report.result(), VerifyResult::Verified) {
            return Err(CompilationProvenFactsError::ReportNotVerified);
        }

        let mut facts = Self::default();
        for step in report
            .steps()
            .iter()
            .filter(|step| step.result() == StepResultKind::Verified)
            .filter(|step| is_extractable_phase(step.phase()))
        {
            let fact = CompilationProvenFact::from_step(step);
            let safe_indexing = step_matches(step, is_safe_indexing_text);
            let bounds = safe_indexing || step_matches(step, is_bounds_text);

            if bounds {
                facts.bounds.push(fact.clone());
            }
            if step_matches(step, is_nonzero_text) {
                facts.nonzero.push(fact.clone());
            }
            if step_matches(step, is_overflow_free_text) {
                facts.overflow_free.push(fact.clone());
            }
            if safe_indexing {
                facts.safe_indexing.push(fact.clone());
            }
            if step_matches(step, is_dead_branch_text) {
                facts.dead_branches.push(fact);
            }
        }

        Ok(facts)
    }

    /// Returns proven bounds-related facts (range checks, capacity, length).
    pub fn bounds(&self) -> &[CompilationProvenFact] {
        &self.bounds
    }

    /// Returns proven non-zero facts.
    pub fn nonzero(&self) -> &[CompilationProvenFact] {
        &self.nonzero
    }

    /// Returns proven overflow-freedom facts (checked/saturating arithmetic).
    pub fn overflow_free(&self) -> &[CompilationProvenFact] {
        &self.overflow_free
    }

    /// Returns proven safe-indexing facts (in-bounds array/slice access).
    pub fn safe_indexing(&self) -> &[CompilationProvenFact] {
        &self.safe_indexing
    }

    /// Returns proven dead-branch facts (unreachable code paths).
    pub fn dead_branches(&self) -> &[CompilationProvenFact] {
        &self.dead_branches
    }

    /// Returns `true` if no proven facts were extracted.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.bounds.is_empty()
            && self.nonzero.is_empty()
            && self.overflow_free.is_empty()
            && self.safe_indexing.is_empty()
            && self.dead_branches.is_empty()
    }

    /// Returns the total number of proven facts across all categories.
    #[must_use]
    pub fn total_matches(&self) -> usize {
        self.bounds.len()
            + self.nonzero.len()
            + self.overflow_free.len()
            + self.safe_indexing.len()
            + self.dead_branches.len()
    }

    /// Export the extracted facts as JSON.
    #[must_use]
    pub fn to_json(&self) -> String {
        let buckets = [
            ("bounds", self.bounds()),
            ("nonzero", self.nonzero()),
            ("overflow_free", self.overflow_free()),
            ("safe_indexing", self.safe_indexing()),
            ("dead_branches", self.dead_branches()),
        ];

        let mut out = String::new();
        out.push_str("{\n");
        out.push_str("  \"counts\": {\n");
        let _ = writeln!(out, "    \"bounds\": {},", self.bounds.len());
        let _ = writeln!(out, "    \"nonzero\": {},", self.nonzero.len());
        let _ = writeln!(out, "    \"overflow_free\": {},", self.overflow_free.len());
        let _ = writeln!(out, "    \"safe_indexing\": {},", self.safe_indexing.len());
        let _ = writeln!(out, "    \"dead_branches\": {},", self.dead_branches.len());
        let _ = writeln!(out, "    \"total_matches\": {}", self.total_matches());
        out.push_str("  },\n");

        for (index, (name, facts)) in buckets.iter().enumerate() {
            let _ = writeln!(out, "  \"{name}\": [");
            for (fact_index, fact) in facts.iter().enumerate() {
                append_json_fact(&mut out, fact);
                if fact_index + 1 < facts.len() {
                    out.push_str(",\n");
                } else {
                    out.push('\n');
                }
            }
            out.push_str("  ]");
            if index + 1 < buckets.len() {
                out.push_str(",\n");
            } else {
                out.push('\n');
            }
        }

        out.push_str("}\n");
        out
    }
}

fn is_extractable_phase(phase: VerificationPhase) -> bool {
    !matches!(
        phase,
        VerificationPhase::ParallelProof | VerificationPhase::VacuousPrecheck
    )
}

fn step_matches(step: &StepDiagnostic, predicate: fn(&str) -> bool) -> bool {
    step.condition().is_some_and(predicate) || predicate(step.label())
}

fn is_bounds_text(text: &str) -> bool {
    let text = text.to_ascii_lowercase();
    let keywords = [
        "bounds",
        "within_bounds",
        ".len()",
        "capacity",
        "range",
        "offset",
        "limit",
    ];
    keywords.iter().any(|keyword| text.contains(keyword))
}

fn is_nonzero_text(text: &str) -> bool {
    let text = text.to_ascii_lowercase();
    let keywords = ["nonzero", "is_nonzero", "non_zero", "!= 0", "> 0", "< 0"];
    keywords.iter().any(|keyword| text.contains(keyword))
}

fn is_overflow_free_text(text: &str) -> bool {
    let text = text.to_ascii_lowercase();
    let keywords = [
        "overflow_free",
        "no_overflow",
        "no overflow",
        "checked_add",
        "checked_sub",
        "checked_mul",
        "overflowing",
        "saturating",
        "wrapping",
    ];
    if keywords.iter().any(|keyword| text.contains(keyword)) {
        return true;
    }

    let has_arithmetic = text.contains(" + ") || text.contains(" - ") || text.contains(" * ");
    let has_range = text.contains("max") || text.contains("min");
    has_arithmetic && has_range
}

fn is_safe_indexing_text(text: &str) -> bool {
    let text = text.to_ascii_lowercase();
    let keywords = [
        "safe_indexing",
        "safe_index",
        "index",
        "idx",
        ".len()",
        "in_bounds",
        "within_bounds",
        "subscript",
    ];
    keywords.iter().any(|keyword| text.contains(keyword))
        || (text.contains('[') && text.contains(']'))
}

fn is_dead_branch_text(text: &str) -> bool {
    let text = text.to_ascii_lowercase();
    let trimmed = text.trim();
    let keywords = [
        "dead_branch",
        "dead_branches",
        "dead code",
        "dead_code",
        "unreachable",
        "false_branch",
    ];
    trimmed == "false" || keywords.iter().any(|keyword| text.contains(keyword))
}

fn append_json_fact(out: &mut String, fact: &CompilationProvenFact) {
    out.push_str("    {\n");
    let _ = writeln!(
        out,
        "      \"condition\": \"{}\",",
        json_escape(fact.condition())
    );
    let _ = writeln!(
        out,
        "      \"step_label\": \"{}\",",
        json_escape(fact.step_label())
    );
    match fact.source_location() {
        Some(location) => {
            let _ = writeln!(
                out,
                "      \"source_location\": \"{}\",",
                json_escape(location)
            );
        }
        None => out.push_str("      \"source_location\": null,\n"),
    }
    let _ = writeln!(out, "      \"phase\": \"{}\"", fact.phase());
    out.push_str("    }");
}

#[cfg(test)]
mod tests;
