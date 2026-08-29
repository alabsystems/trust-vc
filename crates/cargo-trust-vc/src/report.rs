// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Output formatting for verification results (human-readable and JSON).

use crate::scan::UnscannableFile;
use crate::verify::{FunctionVerdict, LocalizedFailure, VerdictKind};
use serde::Serialize;
use std::fmt::Write as _;
use std::path::Path;

fn is_zero(n: &usize) -> bool {
    *n == 0
}

/// Summary counts across all verified functions.
#[derive(Debug, Default, Serialize)]
pub struct Summary {
    pub verified: usize,
    pub counterexample: usize,
    pub unknown: usize,
    pub error: usize,
    pub skipped: usize,
    /// Functions the scan saw but never verified — see [`VerdictKind::NotAnalyzed`].
    pub not_analyzed: usize,
    /// Input FILES that produced no buckets at all — see [`UnscannableFile`].
    ///
    /// Serialized only when nonzero, so the report for a scannable file is
    /// byte-identical to the one that predates this bucket. Its presence is the
    /// signal; a run with nothing to report says nothing new.
    #[serde(skip_serializing_if = "is_zero")]
    pub file_error: usize,
}

impl Summary {
    /// Tally verification outcomes from a slice of function verdicts.
    ///
    /// Equivalent to [`Summary::from_parts`] with no unscannable files. Callers
    /// that HAVE a scan must use `from_parts`: a file that could not be read is
    /// not represented by any verdict, so tallying verdicts alone would drop it.
    pub fn from_verdicts(verdicts: &[FunctionVerdict]) -> Self {
        Self::from_parts(verdicts, &[])
    }

    /// Tally BOTH halves of what a run accounted for: the per-function verdicts
    /// and the per-file scan failures.
    pub fn from_parts(verdicts: &[FunctionVerdict], unscannable: &[UnscannableFile]) -> Self {
        let mut s = Summary::default();
        for v in verdicts {
            match v.result {
                VerdictKind::Verified => s.verified += 1,
                VerdictKind::Counterexample => s.counterexample += 1,
                VerdictKind::Unknown => s.unknown += 1,
                VerdictKind::Error => s.error += 1,
                VerdictKind::Skipped => s.skipped += 1,
                VerdictKind::NotAnalyzed => s.not_analyzed += 1,
            }
        }
        s.file_error = unscannable.len();
        s
    }

    /// Total check targets accounted for — every bucket, summed.
    ///
    /// # The invariant
    ///
    /// ```text
    /// verified + counterexample + unknown + error + skipped + not_analyzed
    ///     + file_error
    ///     == number of check targets the scan produced
    /// ```
    ///
    /// "Check targets" is every `fn` item the scan saw, PLUS the trait-impl
    /// conformance obligations the scan enumerates as targets in their own right
    /// (see `scan::TRAIT_CONFORMANCE_ATTR` — an obligation of the impl, not of
    /// any one function, so it is counted separately and is not a `fn` item),
    /// PLUS one target for each file the scan could not read or parse, whose
    /// function count is not zero but UNKNOWN.
    /// For a file that declares no `#[trust_vc::trait_spec]`/`trait_impl` and
    /// parses, the counts coincide.
    ///
    /// This is the whole point of the `not_analyzed` and `file_error` buckets. A
    /// function whose only contract was spelled in a way discovery failed to
    /// recognize used to appear in NO bucket, and so did EVERY function in a file
    /// with a syntax error: the summary read all-zero, the exit code was 0, and
    /// the output was indistinguishable from a clean pass over a file with
    /// nothing in it. Making the buckets a PARTITION of the scanned set turns
    /// that silence into an arithmetic impossibility — a dropped function now
    /// breaks the sum, and the sum is pinned by
    /// `report::tests::every_scanned_function_lands_in_exactly_one_bucket` and
    /// by `tests/not_analyzed_count_invariant.rs` end to end.
    pub fn total(&self) -> usize {
        self.verified
            + self.counterexample
            + self.unknown
            + self.error
            + self.skipped
            + self.not_analyzed
            + self.file_error
    }

    /// Returns `true` if any function had a counterexample, unknown, or error
    /// result, or if any input file could not be scanned at all.
    ///
    /// `not_analyzed` is deliberately NOT a failure: an uncontracted helper is
    /// legitimate and common, and turning a crate full of them red would make
    /// the honest report unusable. The signal is the reported entry, not the
    /// exit code.
    ///
    /// `file_error` IS a failure, and the asymmetry is deliberate. "This helper
    /// carries no contract" is a complete, true statement about a function we
    /// read. "This file did not parse" is an admission that we do not know what
    /// the file claims — every contract in it, true or false, went unexamined.
    /// Exiting 0 on that is the fail-silent shape itself.
    pub fn has_failures(&self) -> bool {
        self.counterexample > 0 || self.unknown > 0 || self.error > 0 || self.file_error > 0
    }
}

/// Prints human-readable verification results to stdout.
pub fn print_human(
    verdicts: &[FunctionVerdict],
    unscannable: &[UnscannableFile],
    crate_root: &Path,
    show_localization: bool,
) {
    println!(
        "{}",
        format_human(verdicts, unscannable, crate_root, show_localization)
    );
}

pub(crate) fn print_progress(function_name: &str, index: usize, total: usize) {
    println!("[{index}/{total}] Verifying {function_name}...");
}

pub(crate) fn print_progress_result(function_name: &str, index: usize, total: usize, result: &str) {
    println!("[{index}/{total}] {function_name}: {result}");
}

fn display_path(path: &Path, crate_root: &Path) -> String {
    path.strip_prefix(crate_root)
        .unwrap_or(path)
        .display()
        .to_string()
}

fn format_human(
    verdicts: &[FunctionVerdict],
    unscannable: &[UnscannableFile],
    crate_root: &Path,
    show_localization: bool,
) -> String {
    let total = verdicts.len();
    let mut output = String::new();
    // The count is qualified the moment a file went unread: "0 functions found"
    // over a file that did not parse is the exact sentence this bucket exists to
    // stop the tool from saying on its own.
    let unscanned_note = if unscannable.is_empty() {
        String::new()
    } else {
        format!(
            " ({} file{} not scanned, so this count is incomplete)",
            unscannable.len(),
            if unscannable.len() == 1 { "" } else { "s" }
        )
    };
    let _ = writeln!(
        output,
        "trust_vc check: {total} function{} found{unscanned_note}\n",
        if total == 1 { "" } else { "s" }
    );

    for verdict in verdicts {
        let file_display = verdict
            .function
            .file_path
            .strip_prefix(crate_root)
            .unwrap_or(&verdict.function.file_path)
            .display();
        let status = match verdict.result {
            VerdictKind::Verified => "Verified",
            VerdictKind::Counterexample => "Counterexample",
            VerdictKind::Unknown => "Unknown",
            VerdictKind::Error => "Error",
            VerdictKind::Skipped => "Skipped",
            VerdictKind::NotAnalyzed => "NotAnalyzed",
        };
        let _ = writeln!(
            output,
            "  {file_display}:{:<4}  {:<24} {:<16} {}ms",
            verdict.function.line, verdict.function.name, status, verdict.duration_ms,
        );
        let counterexample_explanation =
            if verdict.result == VerdictKind::Counterexample && !verdict.bindings.is_empty() {
                let bindings: Vec<(String, String)> = verdict
                    .bindings
                    .iter()
                    .map(|binding| (binding.display_name.clone(), binding.value.clone()))
                    .collect();
                Some(explain_counterexample(
                    &bindings,
                    &counterexample_assertion_name(
                        verdict.detail.as_deref(),
                        verdict.localized_failure.as_ref(),
                    ),
                ))
            } else {
                None
            };
        if counterexample_explanation.is_none() {
            if let Some(detail) = &verdict.detail {
                let _ = writeln!(output, "    {detail}");
            }
        }
        if let Some(explanation) = &counterexample_explanation {
            append_indented_block(&mut output, explanation, "    ");
        } else {
            append_binding_lines(&mut output, &verdict.bindings, verdict.detail.as_deref());
        }
        if show_localization {
            if let Some(localized) = &verdict.localized_failure {
                append_localized_failure_lines(&mut output, localized);
            }
        }
    }

    // Stated as its own section rather than folded into the function list: these
    // are not functions, and their function count is unknown rather than zero.
    for failure in unscannable {
        let _ = writeln!(
            output,
            "  {}:{:<4}  {:<24} {}",
            display_path(&failure.file_path, crate_root),
            failure.line,
            "FileError",
            failure.reason,
        );
    }

    let summary = Summary::from_parts(verdicts, unscannable);
    let _ = writeln!(output);
    let _ = write!(output, "{}", format_summary_line(&summary));
    output
}

fn format_summary_line(s: &Summary) -> String {
    let mut parts = Vec::new();
    if s.verified > 0 {
        parts.push(format!("{} verified", s.verified));
    }
    if s.counterexample > 0 {
        parts.push(format!("{} counterexample", s.counterexample));
    }
    if s.unknown > 0 {
        parts.push(format!("{} unknown", s.unknown));
    }
    if s.error > 0 {
        parts.push(format!("{} error", s.error));
    }
    if s.skipped > 0 {
        parts.push(format!("{} skipped", s.skipped));
    }
    if s.not_analyzed > 0 {
        parts.push(format!("{} not analyzed", s.not_analyzed));
    }
    if s.file_error > 0 {
        parts.push(format!(
            "{} file{} not scanned",
            s.file_error,
            if s.file_error == 1 { "" } else { "s" }
        ));
    }
    format!("Summary: {}", parts.join(", "))
}

fn counterexample_assertion_name(
    detail: Option<&str>,
    localized: Option<&LocalizedFailure>,
) -> String {
    if let Some(localized) = localized {
        let label = localized.label.trim();
        if !label.is_empty() {
            return label.to_string();
        }
    }

    if let Some(detail) = detail {
        let detail = detail.trim();
        if let Some((assertion_name, _)) = detail.rsplit_once(": ") {
            let assertion_name = assertion_name.trim();
            if !assertion_name.is_empty() {
                return assertion_name.to_string();
            }
        }
        if !detail.is_empty() {
            return detail.to_string();
        }
    }

    "the assertion".to_string()
}

fn append_indented_block(output: &mut String, block: &str, indent: &str) {
    for line in block.lines() {
        let _ = writeln!(output, "{indent}{line}");
    }
}

/// Generate a plain-English explanation of a counterexample.
///
/// Instead of only showing "x = -1, y = 5", this produces a short explanation
/// of why the reported values are interesting and what to inspect next.
pub(crate) fn explain_counterexample(
    bindings: &[(String, String)],
    assertion_name: &str,
) -> String {
    let assertion_name = assertion_name.trim();
    let assertion_name = if assertion_name.is_empty() {
        "the assertion"
    } else {
        assertion_name
    };

    let mut output = String::new();
    let _ = writeln!(
        output,
        "The verifier found concrete values that violate {assertion_name}:"
    );

    if bindings.is_empty() {
        let _ = writeln!(output, "  (no concrete bindings were reported)");
    } else {
        for (name, value) in bindings {
            let _ = write!(output, "  {name} = {value}");
            if let Some(hint) = counterexample_hint(name, value, assertion_name) {
                let _ = write!(output, " ({hint})");
            }
            let _ = writeln!(output);
        }
    }

    let _ = writeln!(
        output,
        "These values satisfy the current preconditions but still make {assertion_name} false."
    );
    let _ = write!(
        output,
        "Suggestion: tighten the relevant requires! clause or add an explicit guard for the failing boundary case."
    );
    output
}

fn counterexample_hint(name: &str, value: &str, assertion_name: &str) -> Option<&'static str> {
    if looks_like_negative_integer(value) {
        return Some(
            "a negative value; if this should be unsigned or nonnegative, add a requires! guard",
        );
    }

    if value.trim() == "0" && looks_like_division_context(name, assertion_name) {
        return Some("zero; division and modulo usually need an explicit nonzero precondition");
    }

    if looks_like_max_int(value) {
        return Some(
            "a maximum integer value; arithmetic here often needs an overflow check or tighter bound",
        );
    }

    None
}

fn looks_like_negative_integer(value: &str) -> bool {
    let value = value.trim();
    let Some(rest) = value.strip_prefix('-') else {
        return false;
    };
    !rest.is_empty() && rest.chars().all(|ch| ch.is_ascii_digit())
}

fn looks_like_division_context(name: &str, assertion_name: &str) -> bool {
    let name = name.to_ascii_lowercase();
    let assertion_name = assertion_name.to_ascii_lowercase();
    const NEEDLES: &[&str] = &[
        "div",
        "divisor",
        "denom",
        "divide",
        "division",
        "mod",
        "quotient",
        "remainder",
        "/",
        "%",
    ];
    NEEDLES
        .iter()
        .any(|needle| name.contains(needle) || assertion_name.contains(needle))
}

fn looks_like_max_int(value: &str) -> bool {
    matches!(
        value.trim(),
        "127"
            | "255"
            | "32767"
            | "65535"
            | "2147483647"
            | "4294967295"
            | "9223372036854775807"
            | "18446744073709551615"
            | "170141183460469231731687303715884105727"
            | "340282366920938463463374607431768211455"
            | "MAX_INT"
            | "i8::MAX"
            | "u8::MAX"
            | "i16::MAX"
            | "u16::MAX"
            | "i32::MAX"
            | "u32::MAX"
            | "i64::MAX"
            | "u64::MAX"
            | "i128::MAX"
            | "u128::MAX"
            | "isize::MAX"
            | "usize::MAX"
    )
}

fn append_localized_failure_lines(output: &mut String, localized: &LocalizedFailure) {
    let mut bottleneck = format!("    bottleneck: {} [{}]", localized.label, localized.phase);
    if let Some(location) = &localized.location {
        let _ = write!(bottleneck, " at {location}");
    }
    let _ = write!(bottleneck, " ({}ms)", localized.duration_ms);
    let _ = writeln!(output, "{bottleneck}");
    if !localized.used_assumptions.is_empty() {
        let _ = writeln!(
            output,
            "    used assumptions: {}",
            localized.used_assumptions.join(", ")
        );
    }
    if let Some(category) = &localized.unknown_category {
        let _ = writeln!(output, "    category: {category}");
    }
    if let Some(suggestion) = &localized.suggestion {
        let _ = writeln!(output, "    suggestion: {suggestion}");
    }
}

fn append_binding_lines(
    output: &mut String,
    bindings: &[trust_vc_core::CounterexampleBinding],
    detail: Option<&str>,
) {
    if bindings.is_empty() {
        return;
    }
    // Suppress when a single binding adds no information beyond the detail string.
    if bindings.len() == 1 {
        if let Some(detail) = detail {
            if detail.contains(&bindings[0].display_name) && detail.contains(&bindings[0].value) {
                return;
            }
        }
    }
    for binding in bindings {
        let _ = write!(
            output,
            "    binding: {}: {} = {}",
            binding.display_name, binding.ty, binding.value
        );
        if binding.raw_name != binding.display_name {
            let _ = write!(output, " [raw: {}]", binding.raw_name);
        }
        let _ = writeln!(output);
    }
}

/// JSON output schema.
#[derive(Debug, Serialize)]
struct JsonReport {
    #[serde(rename = "crate")]
    crate_name: String,
    functions: Vec<JsonFunction>,
    /// Input files that produced no `functions` entries because they could not
    /// be read or parsed.
    ///
    /// Serialized only when non-empty, so a report over scannable input is
    /// byte-identical to the schema that predates this key. When it IS present,
    /// `summary.file_error` is nonzero and the process exits nonzero: an
    /// all-zero report and exit 0 can no longer mean "your syntax error was
    /// invisible".
    #[serde(skip_serializing_if = "Vec::is_empty")]
    file_errors: Vec<JsonFileError>,
    summary: Summary,
}

/// A file-level failure entry: the report's statement that it has NOTHING to say
/// about this file, and why.
#[derive(Debug, Serialize)]
struct JsonFileError {
    file: String,
    line: usize,
    /// Always `"error"` — a fixed discriminator so a consumer filtering on
    /// `result` treats these uniformly with failing function entries.
    result: &'static str,
    detail: String,
}

#[derive(Debug, Serialize)]
struct JsonFunction {
    file: String,
    line: usize,
    name: String,
    result: VerdictKind,
    duration_ms: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    detail: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    localized_failure: Option<LocalizedFailure>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    bindings: Vec<JsonBinding>,
}

#[derive(Debug, Serialize)]
struct JsonBinding {
    display_name: String,
    raw_name: String,
    ty: String,
    value: String,
}

/// Prints JSON verification results to stdout.
pub fn print_json(
    verdicts: &[FunctionVerdict],
    unscannable: &[UnscannableFile],
    crate_root: &Path,
    show_localization: bool,
) {
    let report = json_report(verdicts, unscannable, crate_root, show_localization);
    match serde_json::to_string_pretty(&report) {
        Ok(json) => println!("{json}"),
        Err(err) => eprintln!("failed to serialize verification report: {err}"),
    }
}

fn json_report(
    verdicts: &[FunctionVerdict],
    unscannable: &[UnscannableFile],
    crate_root: &Path,
    show_localization: bool,
) -> JsonReport {
    let crate_name = crate_root
        .file_name()
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_else(|| ".".into());

    let functions: Vec<JsonFunction> = verdicts
        .iter()
        .map(|v| {
            let file = display_path(&v.function.file_path, crate_root);
            JsonFunction {
                file,
                line: v.function.line,
                name: v.function.name.clone(),
                result: v.result.clone(),
                duration_ms: v.duration_ms,
                detail: v.detail.clone(),
                localized_failure: if show_localization {
                    v.localized_failure.clone()
                } else {
                    None
                },
                bindings: v
                    .bindings
                    .iter()
                    .map(|b| JsonBinding {
                        display_name: b.display_name.clone(),
                        raw_name: b.raw_name.clone(),
                        ty: b.ty.clone(),
                        value: b.value.clone(),
                    })
                    .collect(),
            }
        })
        .collect();

    let file_errors: Vec<JsonFileError> = unscannable
        .iter()
        .map(|failure| JsonFileError {
            file: display_path(&failure.file_path, crate_root),
            line: failure.line,
            result: "error",
            detail: failure.reason.clone(),
        })
        .collect();

    let summary = Summary::from_parts(verdicts, unscannable);
    JsonReport {
        crate_name,
        functions,
        file_errors,
        summary,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scan::AnnotatedFunction;
    use std::path::PathBuf;
    use trust_vc_core::CounterexampleBinding;

    fn sample_verdicts() -> Vec<FunctionVerdict> {
        vec![
            FunctionVerdict {
                function: AnnotatedFunction {
                    file_path: PathBuf::from("/project/src/lib.rs"),
                    name: "add_positive".into(),
                    line: 14,
                    attributes: vec!["requires".into(), "ensures".into()],
                },
                result: VerdictKind::Verified,
                duration_ms: 12,
                detail: None,
                localized_failure: None,
                bindings: Vec::new(),
            },
            FunctionVerdict {
                function: AnnotatedFunction {
                    file_path: PathBuf::from("/project/src/lib.rs"),
                    name: "broken".into(),
                    line: 28,
                    attributes: vec!["requires".into()],
                },
                result: VerdictKind::Counterexample,
                duration_ms: 45,
                detail: Some("nonneg: x = -1".into()),
                localized_failure: Some(LocalizedFailure {
                    label: "postcondition".into(),
                    phase: "assertion".into(),
                    location: Some("src/lib.rs:30:5".into()),
                    result: VerdictKind::Counterexample,
                    duration_ms: 44,
                    unknown_category: None,
                    suggestion: None,
                    used_assumptions: Vec::new(),
                }),
                bindings: Vec::new(),
            },
        ]
    }

    fn sample_bindings() -> Vec<CounterexampleBinding> {
        vec![
            CounterexampleBinding::new("old(x)", "__trust_vc_old_x", "i32", "5"),
            CounterexampleBinding::new("flag", "flag", "bool", "false"),
        ]
    }

    #[test]
    fn test_summary_counts() {
        let verdicts = sample_verdicts();
        let s = Summary::from_verdicts(&verdicts);
        assert_eq!(s.verified, 1);
        assert_eq!(s.counterexample, 1);
        assert_eq!(s.unknown, 0);
        assert!(s.has_failures());
    }

    fn verdict_named(name: &str, result: VerdictKind) -> FunctionVerdict {
        FunctionVerdict {
            function: AnnotatedFunction {
                file_path: PathBuf::from("/project/src/lib.rs"),
                name: name.to_string(),
                line: 1,
                attributes: Vec::new(),
            },
            result,
            duration_ms: 0,
            detail: None,
            localized_failure: None,
            bindings: Vec::new(),
        }
    }

    /// THE accounting pin: the buckets partition the verdict set.
    ///
    /// Every `VerdictKind` is exercised, so a variant added later without a
    /// `Summary` arm fails here (and fails to compile in `from_verdicts`),
    /// rather than quietly falling out of the totals the way an
    /// unrecognized-contract function once fell out of the report.
    #[test]
    fn every_scanned_function_lands_in_exactly_one_bucket() {
        let verdicts = vec![
            verdict_named("a", VerdictKind::Verified),
            verdict_named("b", VerdictKind::Counterexample),
            verdict_named("c", VerdictKind::Unknown),
            verdict_named("d", VerdictKind::Error),
            verdict_named("e", VerdictKind::Skipped),
            verdict_named("f", VerdictKind::NotAnalyzed),
            verdict_named("g", VerdictKind::NotAnalyzed),
        ];
        let s = Summary::from_verdicts(&verdicts);
        assert_eq!(
            s.total(),
            verdicts.len(),
            "buckets must sum to the number of functions accounted for"
        );
        assert_eq!(s.not_analyzed, 2);

        let report = json_report(&verdicts, &[], Path::new("/project"), false);
        let json: serde_json::Value =
            serde_json::from_str(&serde_json::to_string(&report).unwrap()).unwrap();
        assert_eq!(json["functions"].as_array().unwrap().len(), verdicts.len());
        assert_eq!(json["summary"]["not_analyzed"], 2);
        let summed: u64 = [
            "verified",
            "counterexample",
            "unknown",
            "error",
            "skipped",
            "not_analyzed",
        ]
        .iter()
        .map(|k| json["summary"][*k].as_u64().unwrap())
        .sum();
        assert_eq!(summed, verdicts.len() as u64);
    }

    fn unscannable_sample() -> Vec<UnscannableFile> {
        vec![UnscannableFile {
            file_path: PathBuf::from("/project/src/broken.rs"),
            line: 4,
            reason: "cannot parse source: expected `}`".to_string(),
        }]
    }

    /// The file-level half of the accounting invariant.
    ///
    /// A file that did not parse contributes exactly one accounted-for target
    /// carrying its failure — not zero targets and a clean bill of health.
    #[test]
    fn an_unscannable_file_is_counted_and_named() {
        let unscannable = unscannable_sample();
        let s = Summary::from_parts(&[], &unscannable);
        assert_eq!(s.file_error, 1);
        assert_eq!(s.total(), 1, "the failed file must be an accounted target");
        assert!(
            s.has_failures(),
            "a file we could not read must never exit 0 — that IS the fail-silent shape"
        );

        let report = json_report(&[], &unscannable, Path::new("/project"), false);
        let json: serde_json::Value =
            serde_json::from_str(&serde_json::to_string(&report).unwrap()).unwrap();
        let errors = json["file_errors"]
            .as_array()
            .expect("file_errors must be present when a file failed");
        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0]["file"], "src/broken.rs");
        assert_eq!(errors[0]["line"], 4);
        assert_eq!(errors[0]["result"], "error");
        assert_eq!(errors[0]["detail"], "cannot parse source: expected `}`");
        assert_eq!(json["summary"]["file_error"], 1);
    }

    /// No drift for the ordinary case: a run with nothing to report about files
    /// emits the schema it always did, key for key.
    #[test]
    fn a_scannable_run_emits_neither_new_key() {
        let report = json_report(&sample_verdicts(), &[], Path::new("/project"), false);
        let json: serde_json::Value =
            serde_json::from_str(&serde_json::to_string(&report).unwrap()).unwrap();
        assert!(
            json.get("file_errors").is_none(),
            "the file-error array must be absent, not empty, when nothing failed"
        );
        assert!(
            json["summary"].get("file_error").is_none(),
            "the file-error count must be absent, not zero, when nothing failed"
        );
        // Asserted on the SERIALIZED text, not on a parsed `Value`: parsing sorts
        // object keys, so a `Value` cannot witness emission order and would pass
        // this test even if the new key were emitted in the middle.
        let raw = serde_json::to_string_pretty(&report).unwrap();
        assert!(
            !raw.contains("file_error"),
            "no file-error key may appear in a scannable run's report:\n{raw}"
        );
        let summary_keys = [
            "\"verified\"",
            "\"counterexample\"",
            "\"unknown\"",
            "\"error\"",
            "\"skipped\"",
            "\"not_analyzed\"",
        ];
        let mut cursor = raw
            .find("\"summary\"")
            .expect("the report carries a summary");
        for key in summary_keys {
            let at = raw[cursor..]
                .find(key)
                .unwrap_or_else(|| panic!("summary lost `{key}`:\n{raw}"));
            cursor += at + key.len();
        }
    }

    #[test]
    fn the_summary_line_names_the_unscanned_file() {
        let s = Summary::from_parts(&[], &unscannable_sample());
        assert_eq!(format_summary_line(&s), "Summary: 1 file not scanned");
    }

    #[test]
    fn the_human_report_names_the_unscanned_file_and_its_reason() {
        let output = format_human(&[], &unscannable_sample(), Path::new("/project"), false);
        assert!(output.contains("src/broken.rs:4"), "{output}");
        assert!(output.contains("FileError"), "{output}");
        assert!(output.contains("cannot parse source"), "{output}");
    }

    /// A not-analyzed function is reported, but it is not a FAILURE — a crate of
    /// ordinary uncontracted helpers must still exit 0.
    #[test]
    fn not_analyzed_alone_is_not_a_failure() {
        let s = Summary::from_verdicts(&[
            verdict_named("a", VerdictKind::NotAnalyzed),
            verdict_named("b", VerdictKind::Verified),
        ]);
        assert!(!s.has_failures());
        assert_eq!(s.total(), 2);
    }

    #[test]
    fn the_summary_line_names_the_not_analyzed_bucket() {
        let s = Summary::from_verdicts(&[verdict_named("a", VerdictKind::NotAnalyzed)]);
        assert_eq!(format_summary_line(&s), "Summary: 1 not analyzed");
    }

    #[test]
    fn test_human_output_includes_localized_failure_when_requested() {
        let output = format_human(&sample_verdicts(), &[], Path::new("/project"), true);

        assert!(output.contains("bottleneck: postcondition [assertion]"));
        assert!(output.contains("at src/lib.rs:30:5"));
    }

    #[test]
    fn test_json_output_parses() {
        let verdicts = sample_verdicts();
        let crate_root = Path::new("/project");
        let report = json_report(&verdicts, &[], crate_root, true);
        let json = serde_json::to_string_pretty(&report).unwrap();
        let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();

        assert_eq!(parsed["crate"], "project");
        assert_eq!(parsed["functions"].as_array().unwrap().len(), 2);
        assert_eq!(parsed["functions"][0]["result"], "verified");
        assert_eq!(
            parsed["functions"][1]["localized_failure"]["label"],
            "postcondition"
        );
        assert_eq!(parsed["summary"]["verified"], 1);
        assert_eq!(parsed["summary"]["counterexample"], 1);
    }

    #[test]
    fn test_json_output_omits_localized_failure_without_flag() {
        let report = json_report(&sample_verdicts(), &[], Path::new("/project"), false);
        let json = serde_json::to_string_pretty(&report).unwrap();
        let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();

        assert!(parsed["functions"][1]["localized_failure"].is_null());
    }

    #[test]
    fn test_human_output_renders_unknown_category_and_suggestion() {
        let verdicts = vec![FunctionVerdict {
            function: AnnotatedFunction {
                file_path: PathBuf::from("/project/src/lib.rs"),
                name: "prove_timeout".into(),
                line: 41,
                attributes: vec!["ensures".into()],
            },
            result: VerdictKind::Unknown,
            duration_ms: 10024,
            detail: Some("Solver returned unknown (timeout) for 'prove_timeout'".into()),
            localized_failure: Some(LocalizedFailure {
                label: "calc step 2 of 3".into(),
                phase: "assert_by".into(),
                location: Some("src/lib.rs:41:5".into()),
                result: VerdictKind::Unknown,
                duration_ms: 10011,
                unknown_category: Some("timeout".into()),
                suggestion: Some(
                    "increase the resource limit or simplify the quantified step".into(),
                ),
                used_assumptions: vec!["gt_zero".into(), "lt_zero".into()],
            }),
            bindings: Vec::new(),
        }];

        let output = format_human(&verdicts, &[], Path::new("/project"), true);

        assert!(output.contains("used assumptions: gt_zero, lt_zero"));
        assert!(output.contains("category: timeout"));
        assert!(output.contains("suggestion: increase the resource limit"));
    }

    #[test]
    fn test_human_output_renders_counterexample_bindings() {
        let verdicts = vec![FunctionVerdict {
            function: AnnotatedFunction {
                file_path: PathBuf::from("/project/src/lib.rs"),
                name: "broken".into(),
                line: 28,
                attributes: vec!["requires".into(), "ensures".into()],
            },
            result: VerdictKind::Counterexample,
            duration_ms: 45,
            detail: Some("nonneg: x = -1".into()),
            localized_failure: None,
            bindings: sample_bindings(),
        }];

        let output = format_human(&verdicts, &[], Path::new("/project"), false);

        assert!(output.contains("The verifier found concrete values that violate nonneg:"));
        assert!(output.contains("old(x) = 5"));
        assert!(output.contains("flag = false"));
        assert!(output.contains("Suggestion: tighten the relevant requires! clause"));
        assert!(!output.contains("binding:"));
    }

    #[test]
    fn test_json_output_includes_used_assumptions_when_present() {
        let verdicts = vec![FunctionVerdict {
            function: AnnotatedFunction {
                file_path: PathBuf::from("/project/src/lib.rs"),
                name: "prove_timeout".into(),
                line: 41,
                attributes: vec!["ensures".into()],
            },
            result: VerdictKind::Unknown,
            duration_ms: 10024,
            detail: Some("Solver returned unknown (timeout) for 'prove_timeout'".into()),
            localized_failure: Some(LocalizedFailure {
                label: "calc step 2 of 3".into(),
                phase: "assert_by".into(),
                location: Some("src/lib.rs:41:5".into()),
                result: VerdictKind::Unknown,
                duration_ms: 10011,
                unknown_category: Some("timeout".into()),
                suggestion: Some(
                    "increase the resource limit or simplify the quantified step".into(),
                ),
                used_assumptions: vec!["gt_zero".into(), "lt_zero".into()],
            }),
            bindings: Vec::new(),
        }];

        let report = json_report(&verdicts, &[], Path::new("/project"), true);
        let json = serde_json::to_string_pretty(&report).unwrap();
        let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();

        assert_eq!(
            parsed["functions"][0]["localized_failure"]["used_assumptions"],
            serde_json::json!(["gt_zero", "lt_zero"])
        );
    }

    #[test]
    fn test_json_output_includes_counterexample_bindings() {
        let verdicts = vec![FunctionVerdict {
            function: AnnotatedFunction {
                file_path: PathBuf::from("/project/src/lib.rs"),
                name: "broken".into(),
                line: 28,
                attributes: vec!["requires".into(), "ensures".into()],
            },
            result: VerdictKind::Counterexample,
            duration_ms: 45,
            detail: Some("nonneg: x = -1".into()),
            localized_failure: None,
            bindings: sample_bindings(),
        }];

        let report = json_report(&verdicts, &[], Path::new("/project"), false);
        let json = serde_json::to_string_pretty(&report).unwrap();
        let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();

        assert_eq!(
            parsed["functions"][0]["bindings"],
            serde_json::json!([
                {
                    "display_name": "old(x)",
                    "raw_name": "__trust_vc_old_x",
                    "ty": "i32",
                    "value": "5"
                },
                {
                    "display_name": "flag",
                    "raw_name": "flag",
                    "ty": "bool",
                    "value": "false"
                }
            ])
        );
    }

    #[test]
    fn test_explain_counterexample_adds_negative_hint_and_suggestion() {
        let explanation = explain_counterexample(
            &[("x".into(), "-1".into()), ("y".into(), "5".into())],
            "nonneg",
        );

        assert!(explanation.starts_with("The verifier found concrete values that violate"));
        assert!(explanation.contains(
            "x = -1 (a negative value; if this should be unsigned or nonnegative, add a requires! guard)"
        ));
        assert!(explanation.contains("y = 5"));
        assert!(explanation.contains(
            "These values satisfy the current preconditions but still make nonneg false."
        ));
        assert!(explanation.ends_with(
            "Suggestion: tighten the relevant requires! clause or add an explicit guard for the failing boundary case."
        ));
    }

    #[test]
    fn test_explain_counterexample_adds_zero_and_max_int_hints() {
        let explanation = explain_counterexample(
            &[
                ("divisor".into(), "0".into()),
                ("sum".into(), "2147483647".into()),
            ],
            "division overflow check",
        );

        assert!(explanation.contains(
            "divisor = 0 (zero; division and modulo usually need an explicit nonzero precondition)"
        ));
        assert!(explanation.contains(
            "sum = 2147483647 (a maximum integer value; arithmetic here often needs an overflow check or tighter bound)"
        ));
    }

    #[test]
    fn test_human_output_replaces_redundant_single_binding_with_explanation() {
        let verdicts = vec![FunctionVerdict {
            function: AnnotatedFunction {
                file_path: PathBuf::from("/project/src/lib.rs"),
                name: "broken".into(),
                line: 28,
                attributes: vec!["requires".into()],
            },
            result: VerdictKind::Counterexample,
            duration_ms: 45,
            detail: Some("nonneg: x = -1".into()),
            localized_failure: None,
            bindings: vec![CounterexampleBinding::new("x", "x", "i32", "-1")],
        }];

        let output = format_human(&verdicts, &[], Path::new("/project"), false);

        assert!(output.contains("The verifier found concrete values that violate nonneg:"));
        assert!(output.contains(
            "x = -1 (a negative value; if this should be unsigned or nonnegative, add a requires! guard)"
        ));
        assert!(!output.contains("binding:"));
    }
}
