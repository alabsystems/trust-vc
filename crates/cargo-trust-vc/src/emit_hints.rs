// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Emit-hints pipeline: generates verified optimization hints from proof results.
//!
//! This module provides [`HintEmitter`], the main pipeline that converts
//! proven verification facts into structured [`EmittedHint`] records. Each hint
//! carries a source location, classification, rendered directive, confidence
//! score, and optional proof reference.
//!
//! Four output formats are supported via [`HintFormat`]:
//!
//! - **RustComment** — `// SAFETY: Verified by trust_vc — <assertion>`
//! - **CompilerDirective** — `#[trust_vc::verified(<kind>)]`
//! - **Json** — structured JSON object per hint
//! - **Llvm** — `; !trust_vc.verified {kind: "...", proof: "..."}`
//!
//! The pipeline integrates with [`FactStrength`] from `crate::fact_strength` to
//! filter hints by minimum optimization strength and with
//! [`VerificationReport`] from `trust_vc_core` to extract proven facts directly
//! from verification results.

use std::collections::BTreeMap;
use std::fmt::Write as FmtWrite;
use std::io::{self, Write};

use trust_vc_core::json_escape;

use trust_vc_core::proven_facts::{extract_proven_facts, ProvenFact};
use trust_vc_core::VerificationReport;

use crate::fact_strength::{classify_fact, FactStrength};
use crate::format_types::HintFormat;

// ---------------------------------------------------------------------------
// SourceLocation
// ---------------------------------------------------------------------------

/// Source location of an emitted hint.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct SourceLocation {
    pub(crate) file: String,
    pub(crate) line: usize,
    pub(crate) column: usize,
}

impl SourceLocation {
    /// Parse a location string like `"src/lib.rs:42:5"` into structured form.
    ///
    /// Returns `None` if the string does not match the expected pattern.
    #[must_use]
    fn parse(s: &str) -> Option<Self> {
        let trimmed = s.trim();
        // Find the last two colons to split file:line:column.
        let last_colon = trimmed.rfind(':')?;
        let column: usize = trimmed[last_colon + 1..].parse().ok()?;
        let rest = &trimmed[..last_colon];
        let second_colon = rest.rfind(':')?;
        let line: usize = rest[second_colon + 1..].parse().ok()?;
        let file = rest[..second_colon].to_string();
        if file.is_empty() {
            return None;
        }
        Some(Self { file, line, column })
    }
}

impl std::fmt::Display for SourceLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}:{}", self.file, self.line, self.column)
    }
}

// ---------------------------------------------------------------------------
// HintKind
// ---------------------------------------------------------------------------

/// Classification of an optimization hint.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum HintKind {
    /// Dead-branch elimination via `unreachable_unchecked()`.
    Unreachable,
    /// Bounds check can be elided (proven in-bounds).
    BoundsCheckElim,
    /// Overflow check can be elided (proven non-overflowing).
    OverflowCheckElim,
    /// Null/Option check can be elided (proven Some/Ok).
    NullCheckElim,
    /// Assertion can be strengthened (e.g., `debug_assert!` to `assert!`).
    AssertionStrength,
    /// Function is proven pure (no side effects).
    PurityHint,
    /// Aliasing constraint proven (enables better register allocation).
    AliasingHint,
}

impl std::fmt::Display for HintKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let label = match self {
            Self::Unreachable => "unreachable",
            Self::BoundsCheckElim => "bounds_check_elim",
            Self::OverflowCheckElim => "overflow_check_elim",
            Self::NullCheckElim => "null_check_elim",
            Self::AssertionStrength => "assertion_strength",
            Self::PurityHint => "purity",
            Self::AliasingHint => "aliasing",
        };
        write!(f, "{label}")
    }
}

// ---------------------------------------------------------------------------
// EmitConfig
// ---------------------------------------------------------------------------

/// Configuration for the emit-hints pipeline.
#[derive(Debug, Clone)]
pub(crate) struct EmitConfig {
    /// Output format.
    pub(crate) format: HintFormat,
    /// Minimum fact strength to emit (default: Strong).
    pub(crate) min_strength: FactStrength,
    /// Include source location in output (default: true).
    pub(crate) include_source_location: bool,
    /// Include proof reference in output (default: false).
    pub(crate) include_proof_reference: bool,
    /// Group hints by file in output (default: true).
    pub(crate) group_by_file: bool,
}

impl Default for EmitConfig {
    fn default() -> Self {
        Self {
            format: HintFormat::RustComment,
            min_strength: FactStrength::Strong,
            include_source_location: true,
            include_proof_reference: false,
            group_by_file: true,
        }
    }
}

// ---------------------------------------------------------------------------
// EmittedHint
// ---------------------------------------------------------------------------

/// A single emitted optimization hint.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct EmittedHint {
    /// Source location where the hint applies.
    pub(crate) location: SourceLocation,
    /// Classification of the optimization.
    pub(crate) kind: HintKind,
    /// The rendered directive text.
    pub(crate) directive: String,
    /// Confidence score in [0.0, 1.0].
    pub(crate) confidence: f64,
    /// Optional proof obligation identifier.
    pub(crate) proof_id: Option<String>,
}

// ---------------------------------------------------------------------------
// ProvenFact (pipeline input — wraps trust_vc_core::ProvenFact)
// ---------------------------------------------------------------------------

/// Input fact for the emit-hints pipeline.
///
/// This is a locally-owned representation that carries the fields the pipeline
/// needs without coupling to the `VerificationReport` extraction path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PipelineFact {
    pub(crate) name: String,
    pub(crate) assertion: String,
    pub(crate) strength: FactStrength,
    pub(crate) source_file: String,
    pub(crate) source_line: usize,
    pub(crate) variables: Vec<(String, String)>,
}

impl PipelineFact {
    /// Convert a `trust_vc_core::ProvenFact` into a pipeline fact.
    #[must_use]
    fn from_proven_fact(fact: &ProvenFact) -> Self {
        let strength = classify_fact(fact.expression());
        let (source_file, source_line) = fact
            .source_location()
            .and_then(|loc| {
                let parts: Vec<&str> = loc.rsplitn(3, ':').collect();
                if parts.len() >= 3 {
                    let line: usize = parts[1].parse().ok()?;
                    Some((parts[2].to_string(), line))
                } else {
                    None
                }
            })
            .unwrap_or_else(|| ("<unknown>".to_string(), 0));
        Self {
            name: fact.step_label().to_string(),
            assertion: fact.expression().to_string(),
            strength,
            source_file,
            source_line,
            variables: Vec::new(),
        }
    }
}

// ---------------------------------------------------------------------------
// Format renderers
// ---------------------------------------------------------------------------

/// Render a hint as a Rust safety comment.
#[must_use]
pub(crate) fn render_rust_comment(hint: &EmittedHint) -> String {
    let mut out = String::new();
    let _ = write!(out, "// SAFETY: Verified by trust_vc — {}", hint.directive);
    if let Some(ref proof_id) = hint.proof_id {
        let _ = write!(out, " (proof: {proof_id})");
    }
    out
}

/// Render a hint as a compiler directive attribute.
#[must_use]
pub(crate) fn render_compiler_directive(hint: &EmittedHint) -> String {
    format!("#[trust_vc::verified({})]", hint.kind)
}

/// Render a hint as a JSON annotation object.
#[must_use]
pub(crate) fn render_json_annotation(hint: &EmittedHint) -> String {
    let proof_field = match &hint.proof_id {
        Some(id) => format!(", \"proof_id\": \"{}\"", json_escape(id)),
        None => String::new(),
    };
    format!(
        "{{\"location\": \"{loc}\", \"kind\": \"{kind}\", \"directive\": \"{directive}\", \"confidence\": {confidence:.2}{proof}}}",
        loc = json_escape(&hint.location.to_string()),
        kind = hint.kind,
        directive = json_escape(&hint.directive),
        confidence = hint.confidence,
        proof = proof_field,
    )
}

/// Render a hint as an LLVM metadata attribute.
#[must_use]
pub(crate) fn render_llvm_attribute(hint: &EmittedHint) -> String {
    let proof_part = match &hint.proof_id {
        Some(id) => format!(", proof: \"{id}\""),
        None => String::new(),
    };
    format!(
        "; !trust_vc.verified {{kind: \"{kind}\"{proof}}}",
        kind = hint.kind,
        proof = proof_part,
    )
}

// ---------------------------------------------------------------------------
// HintKind classification
// ---------------------------------------------------------------------------

/// Classify an assertion expression into a `HintKind`.
#[must_use]
fn classify_hint_kind(assertion: &str) -> HintKind {
    let expr = assertion.trim();

    // Debug-assert strengthening takes priority.
    if expr.contains("debug_assert") {
        return HintKind::AssertionStrength;
    }

    // Bounds-check patterns.
    let bounds_keywords = [
        ".len()", "index", "offset", "capacity", "bound", "range", "size",
    ];
    let has_bounds_kw = bounds_keywords.iter().any(|kw| expr.contains(kw));
    let has_comparison = expr.contains('<') || expr.contains("<=") || expr.contains(">=");
    if has_bounds_kw && has_comparison {
        return HintKind::BoundsCheckElim;
    }

    // Null/Option check patterns.
    let null_patterns = [
        "is_some()",
        "is_none()",
        "!= None",
        "!= null",
        "!= std::ptr::null",
        ".is_null()",
        "is_ok()",
    ];
    if null_patterns.iter().any(|pat| expr.contains(pat)) {
        return HintKind::NullCheckElim;
    }

    // Overflow check patterns.
    let overflow_keywords = [
        "no_overflow",
        "checked_add",
        "checked_sub",
        "checked_mul",
        "overflowing",
        "saturating",
        "wrapping",
    ];
    if overflow_keywords.iter().any(|kw| expr.contains(kw)) {
        return HintKind::OverflowCheckElim;
    }
    // Arithmetic + range bound patterns.
    let arith = [" + ", " - ", " * "];
    let range_bounds = ["<= MAX", ">= MIN", "< MAX", "< u", "< i"];
    let has_arith = arith.iter().any(|pat| expr.contains(pat));
    let has_range = range_bounds.iter().any(|pat| expr.contains(pat));
    if has_arith && has_range {
        return HintKind::OverflowCheckElim;
    }

    // Purity patterns.
    if expr.contains("pure") || expr.contains("no_side_effect") {
        return HintKind::PurityHint;
    }

    // Aliasing patterns.
    if expr.contains("noalias") || expr.contains("no_alias") || expr.contains("unique_ref") {
        return HintKind::AliasingHint;
    }

    HintKind::Unreachable
}

/// Map a `FactStrength` to a confidence score.
#[must_use]
fn strength_to_confidence(strength: FactStrength) -> f64 {
    match strength {
        FactStrength::Critical => 1.0,
        FactStrength::Strong => 0.95,
        FactStrength::Moderate => 0.8,
        FactStrength::Weak => 0.5,
        FactStrength::Informational => 0.3,
    }
}

// ---------------------------------------------------------------------------
// HintEmitter
// ---------------------------------------------------------------------------

/// Main pipeline for emitting verified optimization hints.
pub(crate) struct HintEmitter {
    config: EmitConfig,
}

impl HintEmitter {
    /// Create a new emitter with the given configuration.
    #[must_use]
    pub(crate) fn new(config: EmitConfig) -> Self {
        Self { config }
    }

    /// Emit hints from a slice of pipeline facts.
    ///
    /// Facts below `config.min_strength` are filtered out. Facts at the same
    /// location are deduplicated (keeping the highest-confidence hint).
    #[must_use]
    pub(crate) fn emit_from_facts(&self, facts: &[PipelineFact]) -> Vec<EmittedHint> {
        let mut hints: Vec<EmittedHint> = facts
            .iter()
            .filter(|f| f.strength >= self.config.min_strength)
            .filter_map(|f| self.fact_to_hint(f))
            .collect();

        self.deduplicate(&mut hints);

        if self.config.group_by_file {
            hints.sort_by(|a, b| {
                a.location
                    .file
                    .cmp(&b.location.file)
                    .then_with(|| a.location.line.cmp(&b.location.line))
                    .then_with(|| a.location.column.cmp(&b.location.column))
            });
        }

        hints
    }

    /// Emit hints from a `VerificationReport` by extracting proven facts.
    #[must_use]
    pub(crate) fn emit_from_report(&self, report: &VerificationReport) -> Vec<EmittedHint> {
        let core_facts = extract_proven_facts(report);
        let pipeline_facts: Vec<PipelineFact> = core_facts
            .iter()
            .map(PipelineFact::from_proven_fact)
            .collect();
        self.emit_from_facts(&pipeline_facts)
    }

    /// Write hints to the given writer using the configured format.
    pub(crate) fn write_hints(
        &self,
        hints: &[EmittedHint],
        output: &mut dyn Write,
    ) -> io::Result<()> {
        if self.config.group_by_file {
            let grouped = group_hints_by_file(hints);
            for (file, file_hints) in &grouped {
                writeln!(output, "// File: {file}")?;
                for hint in file_hints {
                    self.write_single_hint(hint, output)?;
                }
                writeln!(output)?;
            }
        } else {
            for hint in hints {
                self.write_single_hint(hint, output)?;
            }
        }
        Ok(())
    }

    /// Convert a single pipeline fact into an emitted hint.
    fn fact_to_hint(&self, fact: &PipelineFact) -> Option<EmittedHint> {
        let location = SourceLocation {
            file: fact.source_file.clone(),
            line: fact.source_line,
            column: 0,
        };
        let kind = classify_hint_kind(&fact.assertion);
        let confidence = strength_to_confidence(fact.strength);
        let directive = fact.assertion.clone();
        let proof_id = if self.config.include_proof_reference {
            Some(fact.name.clone())
        } else {
            None
        };

        Some(EmittedHint {
            location,
            kind,
            directive,
            confidence,
            proof_id,
        })
    }

    /// Deduplicate hints at the same location, keeping the highest confidence.
    fn deduplicate(&self, hints: &mut Vec<EmittedHint>) {
        // Group by (file, line, column, kind) and keep highest confidence.
        let mut seen: BTreeMap<(String, usize, usize, String), usize> = BTreeMap::new();
        let mut to_remove = Vec::new();

        for (i, hint) in hints.iter().enumerate() {
            let key = (
                hint.location.file.clone(),
                hint.location.line,
                hint.location.column,
                hint.kind.to_string(),
            );
            if let Some(&existing_idx) = seen.get(&key) {
                if hints[existing_idx].confidence >= hint.confidence {
                    to_remove.push(i);
                } else {
                    to_remove.push(existing_idx);
                    seen.insert(key, i);
                }
            } else {
                seen.insert(key, i);
            }
        }

        to_remove.sort_unstable();
        to_remove.dedup();
        for idx in to_remove.into_iter().rev() {
            hints.remove(idx);
        }
    }

    /// Write a single hint in the configured format.
    fn write_single_hint(&self, hint: &EmittedHint, output: &mut dyn Write) -> io::Result<()> {
        if self.config.include_source_location {
            writeln!(output, "// At {}", hint.location)?;
        }
        let rendered = match self.config.format {
            HintFormat::RustComment | HintFormat::All => render_rust_comment(hint),
            HintFormat::CompilerDirective => render_compiler_directive(hint),
            HintFormat::Json => render_json_annotation(hint),
            HintFormat::Llvm => render_llvm_attribute(hint),
        };
        writeln!(output, "{rendered}")
    }
}

/// Group hints by their source file, preserving order within each file.
fn group_hints_by_file(hints: &[EmittedHint]) -> BTreeMap<String, Vec<&EmittedHint>> {
    let mut groups: BTreeMap<String, Vec<&EmittedHint>> = BTreeMap::new();
    for hint in hints {
        groups
            .entry(hint.location.file.clone())
            .or_default()
            .push(hint);
    }
    groups
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_vc_core::proven_facts::ProvenFactKind;

    // ---- Helper constructors ----

    fn make_fact(
        name: &str,
        assertion: &str,
        strength: FactStrength,
        file: &str,
        line: usize,
    ) -> PipelineFact {
        PipelineFact {
            name: name.to_string(),
            assertion: assertion.to_string(),
            strength,
            source_file: file.to_string(),
            source_line: line,
            variables: Vec::new(),
        }
    }

    fn default_emitter() -> HintEmitter {
        HintEmitter::new(EmitConfig::default())
    }

    // ---- 1. EmitConfig defaults ----

    #[test]
    fn test_emit_config_default_values() {
        let config = EmitConfig::default();
        assert_eq!(config.format, HintFormat::RustComment);
        assert_eq!(config.min_strength, FactStrength::Strong);
        assert!(config.include_source_location);
        assert!(!config.include_proof_reference);
        assert!(config.group_by_file);
    }

    // ---- 2. emit_from_facts with empty input ----

    #[test]
    fn test_emit_from_facts_empty_input_returns_empty() {
        let emitter = default_emitter();
        let hints = emitter.emit_from_facts(&[]);
        assert!(hints.is_empty(), "empty facts should produce no hints");
    }

    // ---- 3. emit_from_facts with single bounds check ----

    #[test]
    fn test_emit_from_facts_single_bounds_check() {
        let emitter = HintEmitter::new(EmitConfig {
            min_strength: FactStrength::Informational,
            ..EmitConfig::default()
        });
        let facts = vec![make_fact(
            "loop_bound",
            "i < arr.len()",
            FactStrength::Critical,
            "src/lib.rs",
            42,
        )];
        let hints = emitter.emit_from_facts(&facts);
        assert_eq!(hints.len(), 1);
        assert_eq!(hints[0].kind, HintKind::BoundsCheckElim);
        assert_eq!(hints[0].location.file, "src/lib.rs");
        assert_eq!(hints[0].location.line, 42);
        assert_eq!(hints[0].confidence, 1.0);
    }

    // ---- 4. emit_from_facts with mixed strengths filters by min_strength ----

    #[test]
    fn test_emit_from_facts_filters_by_min_strength() {
        let emitter = HintEmitter::new(EmitConfig {
            min_strength: FactStrength::Strong,
            ..EmitConfig::default()
        });
        let facts = vec![
            make_fact("s1", "i < arr.len()", FactStrength::Critical, "a.rs", 1),
            make_fact("s2", "x.is_some()", FactStrength::Strong, "a.rs", 2),
            make_fact("s3", "x > 0", FactStrength::Moderate, "a.rs", 3),
            make_fact("s4", "debug_assert!(x)", FactStrength::Weak, "a.rs", 4),
            make_fact(
                "s5",
                "result == old(x)",
                FactStrength::Informational,
                "a.rs",
                5,
            ),
        ];
        let hints = emitter.emit_from_facts(&facts);
        // Only Critical and Strong should pass (>= Strong).
        assert_eq!(hints.len(), 2, "only Strong and above should be emitted");
        assert!(hints.iter().all(|h| h.confidence >= 0.95));
    }

    // ---- 5. RustComment format rendering ----

    #[test]
    fn test_render_rust_comment_format() {
        let hint = EmittedHint {
            location: SourceLocation {
                file: "src/lib.rs".to_string(),
                line: 10,
                column: 5,
            },
            kind: HintKind::BoundsCheckElim,
            directive: "i < arr.len()".to_string(),
            confidence: 1.0,
            proof_id: None,
        };
        let output = render_rust_comment(&hint);
        assert!(output.starts_with("// SAFETY: Verified by trust_vc"));
        assert!(output.contains("i < arr.len()"));
        assert!(!output.contains("proof:"));
    }

    // ---- 6. CompilerDirective format rendering ----

    #[test]
    fn test_render_compiler_directive_format() {
        let hint = EmittedHint {
            location: SourceLocation {
                file: "src/lib.rs".to_string(),
                line: 10,
                column: 5,
            },
            kind: HintKind::NullCheckElim,
            directive: "x.is_some()".to_string(),
            confidence: 0.95,
            proof_id: None,
        };
        let output = render_compiler_directive(&hint);
        assert_eq!(output, "#[trust_vc::verified(null_check_elim)]");
    }

    // ---- 7. Json format rendering ----

    #[test]
    fn test_render_json_annotation_format() {
        let hint = EmittedHint {
            location: SourceLocation {
                file: "src/lib.rs".to_string(),
                line: 10,
                column: 5,
            },
            kind: HintKind::OverflowCheckElim,
            directive: "x + y < MAX".to_string(),
            confidence: 0.95,
            proof_id: Some("arith_safe".to_string()),
        };
        let output = render_json_annotation(&hint);
        assert!(output.starts_with('{'));
        assert!(output.ends_with('}'));
        assert!(output.contains("\"kind\": \"overflow_check_elim\""));
        assert!(output.contains("\"confidence\": 0.95"));
        assert!(output.contains("\"proof_id\": \"arith_safe\""));
    }

    // ---- 8. Llvm format rendering ----

    #[test]
    fn test_render_llvm_attribute_format() {
        let hint = EmittedHint {
            location: SourceLocation {
                file: "src/lib.rs".to_string(),
                line: 10,
                column: 5,
            },
            kind: HintKind::Unreachable,
            directive: "x > 0".to_string(),
            confidence: 0.8,
            proof_id: Some("guard_1".to_string()),
        };
        let output = render_llvm_attribute(&hint);
        assert!(output.starts_with("; !trust_vc.verified"));
        assert!(output.contains("kind: \"unreachable\""));
        assert!(output.contains("proof: \"guard_1\""));
    }

    // ---- 9. write_hints produces valid output ----

    #[test]
    fn test_write_hints_produces_valid_output() {
        let emitter = HintEmitter::new(EmitConfig {
            format: HintFormat::RustComment,
            min_strength: FactStrength::Informational,
            group_by_file: false,
            ..EmitConfig::default()
        });
        let facts = vec![make_fact(
            "s1",
            "x > 0",
            FactStrength::Strong,
            "src/lib.rs",
            10,
        )];
        let hints = emitter.emit_from_facts(&facts);

        let mut buf = Vec::new();
        emitter
            .write_hints(&hints, &mut buf)
            .expect("write_hints should succeed");
        let output = String::from_utf8(buf).expect("output should be valid UTF-8");
        assert!(output.contains("SAFETY: Verified by trust_vc"));
        assert!(output.contains("At src/lib.rs:10:0"));
    }

    // ---- 10. group_by_file groups correctly ----

    #[test]
    fn test_group_by_file_groups_correctly() {
        let emitter = HintEmitter::new(EmitConfig {
            min_strength: FactStrength::Informational,
            group_by_file: true,
            ..EmitConfig::default()
        });
        let facts = vec![
            make_fact("s1", "x > 0", FactStrength::Strong, "a.rs", 1),
            make_fact("s2", "y > 0", FactStrength::Strong, "b.rs", 1),
            make_fact("s3", "z > 0", FactStrength::Strong, "a.rs", 5),
        ];
        let hints = emitter.emit_from_facts(&facts);
        // With group_by_file, hints from a.rs should be adjacent.
        assert_eq!(hints.len(), 3);
        assert_eq!(hints[0].location.file, "a.rs");
        assert_eq!(hints[1].location.file, "a.rs");
        assert_eq!(hints[2].location.file, "b.rs");
    }

    // ---- 11. Source location included when configured ----

    #[test]
    fn test_source_location_included_when_configured() {
        let emitter = HintEmitter::new(EmitConfig {
            include_source_location: true,
            min_strength: FactStrength::Informational,
            group_by_file: false,
            ..EmitConfig::default()
        });
        let facts = vec![make_fact(
            "s1",
            "x > 0",
            FactStrength::Strong,
            "src/lib.rs",
            42,
        )];
        let hints = emitter.emit_from_facts(&facts);

        let mut buf = Vec::new();
        emitter
            .write_hints(&hints, &mut buf)
            .expect("write should succeed");
        let output = String::from_utf8(buf).expect("valid UTF-8");
        assert!(
            output.contains("// At src/lib.rs:42:0"),
            "source location should appear in output"
        );
    }

    // ---- 12. Proof reference included when configured ----

    #[test]
    fn test_proof_reference_included_when_configured() {
        let emitter = HintEmitter::new(EmitConfig {
            include_proof_reference: true,
            min_strength: FactStrength::Informational,
            group_by_file: false,
            ..EmitConfig::default()
        });
        let facts = vec![make_fact(
            "my_proof_step",
            "x > 0",
            FactStrength::Strong,
            "src/lib.rs",
            10,
        )];
        let hints = emitter.emit_from_facts(&facts);
        assert_eq!(hints.len(), 1);
        assert_eq!(hints[0].proof_id, Some("my_proof_step".to_string()));

        let rendered = render_rust_comment(&hints[0]);
        assert!(
            rendered.contains("proof: my_proof_step"),
            "proof reference should appear in rendered output"
        );
    }

    // ---- 13. Multiple facts same location deduplicated ----

    #[test]
    fn test_multiple_facts_same_location_deduplicated() {
        let emitter = HintEmitter::new(EmitConfig {
            min_strength: FactStrength::Informational,
            ..EmitConfig::default()
        });
        let facts = vec![
            make_fact("s1", "x > 0", FactStrength::Strong, "a.rs", 10),
            make_fact("s2", "x > 0", FactStrength::Moderate, "a.rs", 10),
        ];
        let hints = emitter.emit_from_facts(&facts);
        // Both map to Unreachable at a.rs:10:0. The higher-confidence one survives.
        assert_eq!(hints.len(), 1);
        assert_eq!(
            hints[0].confidence, 0.95,
            "higher confidence should survive"
        );
    }

    // ---- 14. Confidence scoring based on fact strength ----

    #[test]
    fn test_confidence_scoring_based_on_fact_strength() {
        assert_eq!(strength_to_confidence(FactStrength::Critical), 1.0);
        assert_eq!(strength_to_confidence(FactStrength::Strong), 0.95);
        assert_eq!(strength_to_confidence(FactStrength::Moderate), 0.8);
        assert_eq!(strength_to_confidence(FactStrength::Weak), 0.5);
        assert_eq!(strength_to_confidence(FactStrength::Informational), 0.3);
    }

    // ---- 15. HintKind classification from assertion patterns ----

    #[test]
    fn test_hint_kind_classification_from_assertion_patterns() {
        assert_eq!(
            classify_hint_kind("i < arr.len()"),
            HintKind::BoundsCheckElim
        );
        assert_eq!(classify_hint_kind("x.is_some()"), HintKind::NullCheckElim);
        assert_eq!(
            classify_hint_kind("no_overflow(a + b)"),
            HintKind::OverflowCheckElim
        );
        assert_eq!(
            classify_hint_kind("debug_assert!(x > 0)"),
            HintKind::AssertionStrength
        );
        assert_eq!(classify_hint_kind("x > 0"), HintKind::Unreachable);
        assert_eq!(classify_hint_kind("pure function"), HintKind::PurityHint);
        assert_eq!(classify_hint_kind("noalias ptr"), HintKind::AliasingHint);
    }

    // ---- 16. emit_from_report path via PipelineFact::from_proven_fact ----

    #[test]
    fn test_emit_from_report_path_via_pipeline_fact() {
        // We cannot construct a VerificationReport from outside trust-vc-core
        // (from_parts is pub(crate)). Instead, test the delegation path by
        // verifying that PipelineFact::from_proven_fact + emit_from_facts
        // produces correct results -- this is exactly what emit_from_report does.
        let core_facts = [
            ProvenFact::new(
                ProvenFactKind::Invariant,
                "i < arr.len()",
                Some("src/loop.rs:10:5".to_string()),
                "loop_bound",
            ),
            ProvenFact::new(
                ProvenFactKind::Assertion,
                "x > 0",
                Some("src/lib.rs:42:5".to_string()),
                "positive_guard",
            ),
        ];
        let pipeline_facts: Vec<PipelineFact> = core_facts
            .iter()
            .map(PipelineFact::from_proven_fact)
            .collect();

        let emitter = HintEmitter::new(EmitConfig {
            min_strength: FactStrength::Informational,
            ..EmitConfig::default()
        });
        let hints = emitter.emit_from_facts(&pipeline_facts);
        assert_eq!(hints.len(), 2);
        // The bounds check (Critical) comes first when grouped by file.
        let bounds_hint = hints.iter().find(|h| h.kind == HintKind::BoundsCheckElim);
        assert!(
            bounds_hint.is_some(),
            "should classify 'i < arr.len()' as BoundsCheckElim"
        );
    }

    // ---- 17. SourceLocation parsing ----

    #[test]
    fn test_source_location_parse_valid() {
        let loc = SourceLocation::parse("src/lib.rs:42:5").expect("should parse");
        assert_eq!(loc.file, "src/lib.rs");
        assert_eq!(loc.line, 42);
        assert_eq!(loc.column, 5);
    }

    #[test]
    fn test_source_location_parse_invalid() {
        assert!(SourceLocation::parse("no-colons").is_none());
        assert!(SourceLocation::parse("").is_none());
        assert!(SourceLocation::parse(":1:1").is_none());
    }

    // ---- 18. SourceLocation display ----

    #[test]
    fn test_source_location_display() {
        let loc = SourceLocation {
            file: "src/main.rs".to_string(),
            line: 100,
            column: 8,
        };
        assert_eq!(loc.to_string(), "src/main.rs:100:8");
    }

    // ---- 19. HintFormat default ----

    #[test]
    fn test_hint_format_default_is_rust_comment() {
        assert_eq!(HintFormat::default(), HintFormat::RustComment);
    }

    // ---- 20. Write hints with JSON format ----

    #[test]
    fn test_write_hints_json_format() {
        let emitter = HintEmitter::new(EmitConfig {
            format: HintFormat::Json,
            min_strength: FactStrength::Informational,
            group_by_file: false,
            include_source_location: false,
            ..EmitConfig::default()
        });
        let facts = vec![make_fact(
            "s1",
            "i < arr.len()",
            FactStrength::Critical,
            "src/lib.rs",
            10,
        )];
        let hints = emitter.emit_from_facts(&facts);

        let mut buf = Vec::new();
        emitter
            .write_hints(&hints, &mut buf)
            .expect("write should succeed");
        let output = String::from_utf8(buf).expect("valid UTF-8");
        assert!(output.contains("\"kind\": \"bounds_check_elim\""));
        assert!(output.contains("\"confidence\": 1.00"));
    }

    // ---- 21. Llvm without proof_id ----

    #[test]
    fn test_llvm_attribute_without_proof_id() {
        let hint = EmittedHint {
            location: SourceLocation {
                file: "a.rs".to_string(),
                line: 1,
                column: 0,
            },
            kind: HintKind::BoundsCheckElim,
            directive: "i < n".to_string(),
            confidence: 1.0,
            proof_id: None,
        };
        let output = render_llvm_attribute(&hint);
        assert_eq!(output, "; !trust_vc.verified {kind: \"bounds_check_elim\"}");
        assert!(!output.contains("proof:"));
    }

    // ---- 22. RustComment with proof reference ----

    #[test]
    fn test_rust_comment_with_proof_reference() {
        let hint = EmittedHint {
            location: SourceLocation {
                file: "a.rs".to_string(),
                line: 1,
                column: 0,
            },
            kind: HintKind::Unreachable,
            directive: "x > 0".to_string(),
            confidence: 0.95,
            proof_id: Some("step_42".to_string()),
        };
        let output = render_rust_comment(&hint);
        assert!(output.contains("(proof: step_42)"));
    }

    // ---- 23. group_hints_by_file helper ----

    #[test]
    fn test_group_hints_by_file_helper() {
        let hints = vec![
            EmittedHint {
                location: SourceLocation {
                    file: "b.rs".to_string(),
                    line: 1,
                    column: 0,
                },
                kind: HintKind::Unreachable,
                directive: "x".to_string(),
                confidence: 0.5,
                proof_id: None,
            },
            EmittedHint {
                location: SourceLocation {
                    file: "a.rs".to_string(),
                    line: 1,
                    column: 0,
                },
                kind: HintKind::Unreachable,
                directive: "y".to_string(),
                confidence: 0.5,
                proof_id: None,
            },
        ];
        let grouped = group_hints_by_file(&hints);
        assert_eq!(grouped.len(), 2);
        // BTreeMap keys are sorted, so "a.rs" comes first.
        let keys: Vec<&String> = grouped.keys().collect();
        assert_eq!(keys[0], "a.rs");
        assert_eq!(keys[1], "b.rs");
    }

    // ---- 24. HintKind display ----

    #[test]
    fn test_hint_kind_display_all_variants() {
        assert_eq!(HintKind::Unreachable.to_string(), "unreachable");
        assert_eq!(HintKind::BoundsCheckElim.to_string(), "bounds_check_elim");
        assert_eq!(
            HintKind::OverflowCheckElim.to_string(),
            "overflow_check_elim"
        );
        assert_eq!(HintKind::NullCheckElim.to_string(), "null_check_elim");
        assert_eq!(
            HintKind::AssertionStrength.to_string(),
            "assertion_strength"
        );
        assert_eq!(HintKind::PurityHint.to_string(), "purity");
        assert_eq!(HintKind::AliasingHint.to_string(), "aliasing");
    }

    // ---- 25. PipelineFact from ProvenFact ----

    #[test]
    fn test_pipeline_fact_from_proven_fact() {
        let proven = ProvenFact::new(
            ProvenFactKind::Invariant,
            "i < arr.len()",
            Some("src/loop.rs:10:5".to_string()),
            "loop_bound",
        );
        let pf = PipelineFact::from_proven_fact(&proven);
        assert_eq!(pf.name, "loop_bound");
        assert_eq!(pf.assertion, "i < arr.len()");
        assert_eq!(pf.strength, FactStrength::Critical);
        assert_eq!(pf.source_file, "src/loop.rs");
        assert_eq!(pf.source_line, 10);
    }

    // ---- 26. Write hints with grouped output ----

    #[test]
    fn test_write_hints_grouped_output() {
        let emitter = HintEmitter::new(EmitConfig {
            format: HintFormat::CompilerDirective,
            min_strength: FactStrength::Informational,
            group_by_file: true,
            include_source_location: false,
            ..EmitConfig::default()
        });
        let facts = vec![
            make_fact("s1", "x > 0", FactStrength::Strong, "a.rs", 1),
            make_fact("s2", "y > 0", FactStrength::Strong, "b.rs", 1),
        ];
        let hints = emitter.emit_from_facts(&facts);

        let mut buf = Vec::new();
        emitter
            .write_hints(&hints, &mut buf)
            .expect("write should succeed");
        let output = String::from_utf8(buf).expect("valid UTF-8");
        assert!(output.contains("// File: a.rs"));
        assert!(output.contains("// File: b.rs"));
        assert!(output.contains("#[trust_vc::verified(unreachable)]"));
    }
}
