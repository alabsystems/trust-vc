// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Local "run everything" gate and fuzz runner.
//!
//! These subcommands replace the role of CI with on-demand local commands.
//! Everything is driven through `std::process::Command`; no new crate
//! dependencies are introduced. The gate never weakens or fakes any check:
//! each stage runs the real tool and a non-zero stage exit fails the gate.

use crate::evidence::CorpusTriageReport;
// The lane every compiling gate stage names: the gate builds this repo as a
// tool, not as a verification subject.
use crate::TARGO_UNVERIFIED_LANE;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

/// libfuzzer targets shipped under `fuzz/fuzz_targets/`.
pub(crate) const FUZZ_TARGETS: &[&str] = &[
    "ensures_false",
    "strict_inequality",
    "mode_crossing",
    "collections_contradiction",
];

/// Default per-target wall-clock budget for `cargo trust-vc fuzz`.
const DEFAULT_FUZZ_TIME_SECS: u64 = 30;

/// Per-target budget for the gate's quick fuzz smoke.
const GATE_FUZZ_SMOKE_SECS: u64 = 3;

const CANONICAL_CORPUS_MANIFEST: &str = "evals/verus/verus-tests.json";
const VERUS_REPO_URL: &str = "https://github.com/verus-lang/verus";
const REQUIRED_VERUS_TEST_ROOTS: &[&str] =
    &["source/rust_verify_test/tests", "source/cargo-verus/tests"];
/// The evidence kind whose expected cases the manifest SCHEMA fixes: it forces
/// `expected_verdict: verified` with `min_obligations: 0` and no
/// `obligation_fingerprints`, so the count those rows carry pins nothing. See
/// clause (2b) of `ACCEPTED_CASE_CORRESPONDENCE_BOUND`.
const CARGO_TRUST_VC_INTEGRATION_TEST_KIND: &str = "cargo_trust_vc_integration_test";
const ALLOWED_CORPUS_CLASSIFICATIONS: &[&str] =
    &["unchanged", "ported", "unsupported-gap", "not-applicable"];
/// The checked-in report is currently about 1.3 MiB. Keep generous growth
/// headroom while rejecting accidental logs or attacker-sized JSON before
/// deserialization.
const MAX_CORPUS_TRIAGE_JSON_BYTES: usize = 8 * 1024 * 1024;
/// Repository-relative path of the Trust-toolchain fuzz runner.
const TRUST_FUZZ_SCRIPT: &str = "fuzz/run.sh";
/// What `targo trust-vc fuzz` says when its `$CARGO` is not targo.
const FUZZ_NEEDS_TARGO: &str =
    "the fuzz lane runs fuzz/run.sh on the Trust toolchain's `targo` (run it as `targo trust-vc fuzz`)";

/// Outcome of a single gate stage.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
enum StageStatus {
    Pass,
    Fail,
    Skipped,
}

impl StageStatus {
    fn label(self) -> &'static str {
        match self {
            StageStatus::Pass => "PASS",
            StageStatus::Fail => "FAIL",
            StageStatus::Skipped => "SKIP",
        }
    }
}

#[derive(Debug, Clone, Serialize)]
struct StageResult {
    name: String,
    command: String,
    status: StageStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    exit_code: Option<i32>,
    duration_ms: u128,
    #[serde(skip_serializing_if = "Option::is_none")]
    detail: Option<String>,
}

#[derive(Debug, Serialize)]
struct GateReport {
    overall: StageStatus,
    stages: Vec<StageResult>,
}

/// Parsed `gate` arguments.
#[derive(Debug, Clone)]
pub(crate) struct GateArgs {
    current_dir: PathBuf,
    quick: bool,
    no_fuzz: bool,
    json: bool,
}

/// Detect and parse a `gate` invocation from raw process arguments.
///
/// Accepts the cargo-subcommand spellings used elsewhere in this binary:
/// `cargo-trust-vc gate ...`, `cargo trust_vc gate ...`, and
/// `cargo trust-vc gate ...`.
pub(crate) fn detect_gate_subcommand(raw_args: &[String]) -> Option<Result<GateArgs, String>> {
    let tail_start = gate_tail_start(raw_args, "gate")?;
    let current_dir = match std::env::current_dir() {
        Ok(dir) => dir,
        Err(error) => return Some(Err(format!("cannot resolve current directory: {error}"))),
    };
    Some(parse_gate_tail(current_dir, &raw_args[tail_start..]))
}

fn parse_gate_tail(current_dir: PathBuf, tail: &[String]) -> Result<GateArgs, String> {
    let mut args = GateArgs {
        current_dir,
        quick: false,
        no_fuzz: false,
        json: false,
    };
    let mut index = 0;
    while index < tail.len() {
        let arg = tail[index].as_str();
        match arg {
            "--quick" => args.quick = true,
            "--no-fuzz" => args.no_fuzz = true,
            "--json" => args.json = true,
            "--verus-path" => return Err(checkout_evidence_guidance()),
            "-h" | "--help" => {
                print!("{}", gate_help());
                std::process::exit(0);
            }
            _ if arg.starts_with("--verus-path=") => return Err(checkout_evidence_guidance()),
            _ => {
                return Err(format!(
                    "unsupported `cargo trust-vc gate` argument `{arg}`; see `cargo trust-vc gate --help`"
                ));
            }
        }
        index += 1;
    }
    Ok(args)
}

fn checkout_evidence_guidance() -> String {
    "`cargo trust-vc gate` is an offline local-integrity gate and does not accept \
     `--verus-path`; run `cargo trust-vc evidence --port-manifest-only --verus-path \
     <CHECKOUT> --json` for checkout-backed manifest evidence"
        .to_string()
}

/// Run the full local gate. Returns the process exit code (0 pass, 1 stage failed).
pub(crate) fn run_gate(args: &GateArgs) -> Result<i32, String> {
    let cargo = cargo_command();
    // Every toolchain stage runs through the Trust toolchain's `targo`. A
    // `$CARGO` that fails the targo discriminator fails those stages in-band
    // instead of letting a stock `cargo fmt` pass under the same name.
    let targo_identity = probe_targo(&cargo, &args.current_dir, GATE_NEEDS_TARGO);
    let mut stages: Vec<StageResult> = Vec::new();

    stages.push(run_targo_stage(
        "fmt",
        &cargo,
        targo_identity.as_ref(),
        &["fmt", "--all", "--check"],
        &args.current_dir,
        args.json,
    ));
    stages.push(run_targo_stage(
        "clippy",
        &cargo,
        targo_identity.as_ref(),
        &[
            "tippy",
            "--locked",
            "--workspace",
            "--all-targets",
            "--",
            "-D",
            "warnings",
        ],
        &args.current_dir,
        args.json,
    ));

    if args.quick {
        stages.push(skipped_stage(
            "test",
            &format!("{cargo} {TARGO_UNVERIFIED_LANE} test --locked --workspace"),
            "skipped by --quick",
            args.json,
        ));
    } else {
        stages.push(run_targo_stage(
            "test",
            &cargo,
            targo_identity.as_ref(),
            &[TARGO_UNVERIFIED_LANE, "test", "--locked", "--workspace"],
            &args.current_dir,
            args.json,
        ));
    }

    // Build the shipped examples. `build --examples` covers every example
    // target across the workspace without running them.
    stages.push(run_targo_stage(
        "examples",
        &cargo,
        targo_identity.as_ref(),
        &[
            TARGO_UNVERIFIED_LANE,
            "build",
            "--locked",
            "--examples",
            "--workspace",
        ],
        &args.current_dir,
        args.json,
    ));

    // This is deliberately an offline manifest-integrity check, not a
    // replacement-evidence claim. Declared unsupported gaps are honest input
    // to the triage report and do not make this local gate fail.
    stages.push(run_evidence_stage(args));

    // Fuzz smoke: fuzz/run.sh under targo; skipped when disabled or when the
    // runner is missing.
    let fuzz_runner = FuzzRunner::select(&cargo, &args.current_dir, targo_identity.is_ok());
    stages.push(run_fuzz_smoke_stage(args, &fuzz_runner));

    let overall = if stages.iter().any(|stage| stage.status == StageStatus::Fail) {
        StageStatus::Fail
    } else {
        StageStatus::Pass
    };
    let report = GateReport { overall, stages };

    if args.json {
        match serde_json::to_string_pretty(&report) {
            Ok(json) => println!("{json}"),
            Err(error) => return Err(format!("failed to serialize gate report: {error}")),
        }
    } else {
        print_summary_table(&report);
    }

    Ok(if overall == StageStatus::Fail { 1 } else { 0 })
}

/// What the gate says when its `$CARGO` is not targo.
const GATE_NEEDS_TARGO: &str =
    "the gate needs the Trust toolchain's `targo` (run it as `targo trust-vc gate`)";

/// Prove that `cargo` is the Trust toolchain's `targo` before it is handed a
/// targo lane flag. `targo --unverified --version` is the discriminator that
/// holds: targo accepts the lane flag, upstream cargo (including a cargo binary
/// shipped under the name `targo`) rejects it. Returns the refusal detail,
/// ending with `needs` (what the caller requires, naming targo), when it is not.
pub(crate) fn probe_targo(cargo: &str, current_dir: &Path, needs: &str) -> Result<(), String> {
    let output = Command::new(cargo)
        .current_dir(current_dir)
        .args([TARGO_UNVERIFIED_LANE, "--version"])
        .output();
    match output {
        Ok(output) if output.status.success() => Ok(()),
        Ok(output) => Err(format!(
            "`{cargo} {TARGO_UNVERIFIED_LANE} --version` exited {}; {needs}{}",
            output
                .status
                .code()
                .map_or_else(|| "by signal".to_string(), |code| code.to_string()),
            captured_command_failure_detail(&output.stdout, &output.stderr)
                .map(|detail| format!(": {detail}"))
                .unwrap_or_default()
        )),
        Err(error) => Err(format!("failed to launch `{cargo}`: {error}; {needs}")),
    }
}

/// Run one toolchain stage through `targo`, or fail it in-band when the
/// discriminator already showed `cargo` is not targo. There is deliberately no
/// stock-cargo fallback here.
fn run_targo_stage(
    name: &str,
    cargo: &str,
    targo_identity: Result<&(), &String>,
    args: &[&str],
    current_dir: &Path,
    json: bool,
) -> StageResult {
    if let Err(refusal) = targo_identity {
        let command = format!("{cargo} {}", args.join(" "));
        if !json {
            eprintln!("[gate] {name}: FAIL ({refusal})");
        }
        return StageResult {
            name: name.to_string(),
            command,
            status: StageStatus::Fail,
            exit_code: None,
            duration_ms: 0,
            detail: Some(refusal.clone()),
        };
    }
    run_stage(name, cargo, args, current_dir, json)
}

fn run_evidence_stage(args: &GateArgs) -> StageResult {
    // Re-invoke this same binary so the gate consumes the same deterministic
    // triage report exposed to users. Capture stdout: a zero exit is necessary
    // but insufficient; malformed or internally incoherent JSON fails closed.
    let self_exe = match std::env::current_exe() {
        Ok(path) => path,
        Err(error) => {
            return StageResult {
                name: "evidence".to_string(),
                command: "<current executable> trust-vc evidence --corpus-triage-report --json"
                    .to_string(),
                status: StageStatus::Fail,
                exit_code: None,
                duration_ms: 0,
                detail: Some(format!("cannot resolve current executable: {error}")),
            };
        }
    };
    let command_args: Vec<String> = vec![
        "trust-vc".to_string(),
        "evidence".to_string(),
        "--corpus-triage-report".to_string(),
        "--json".to_string(),
    ];
    let command = format!("{} {}", self_exe.display(), command_args.join(" "));
    if !args.json {
        eprintln!("[gate] evidence: {command}");
    }
    let start = Instant::now();
    let output = Command::new(&self_exe)
        .current_dir(&args.current_dir)
        .args(&command_args)
        .output();
    let duration_ms = start.elapsed().as_millis();

    let (status, exit_code, detail) = match output {
        Err(error) => (
            StageStatus::Fail,
            None,
            Some(format!(
                "failed to launch `{}`: {error}",
                self_exe.display()
            )),
        ),
        Ok(output) if !output.status.success() => (
            StageStatus::Fail,
            output.status.code(),
            Some(
                match captured_command_failure_detail(&output.stdout, &output.stderr) {
                    Some(detail) => format!("corpus triage command failed: {detail}"),
                    None => "corpus triage command failed".to_string(),
                },
            ),
        ),
        Ok(output) if !String::from_utf8_lossy(&output.stderr).trim().is_empty() => (
            StageStatus::Fail,
            output.status.code(),
            Some(format!(
                "corpus triage command produced unexpected stderr: {}",
                bounded_output_tail(&output.stderr)
            )),
        ),
        Ok(output) => match parse_and_validate_corpus_triage(&output.stdout) {
            Ok(detail) => (StageStatus::Pass, output.status.code(), Some(detail)),
            Err(error) => (
                StageStatus::Fail,
                output.status.code(),
                Some(format!(
                    "invalid corpus triage report: {}",
                    bounded_output_tail(error.as_bytes())
                )),
            ),
        },
    };
    if !args.json {
        match &detail {
            Some(detail) => eprintln!("[gate] evidence: {} ({detail})", status.label()),
            None => eprintln!("[gate] evidence: {}", status.label()),
        }
    }
    StageResult {
        name: "evidence".to_string(),
        command,
        status,
        exit_code,
        duration_ms,
        detail,
    }
}

fn parse_and_validate_corpus_triage(stdout: &[u8]) -> Result<String, String> {
    if stdout.len() > MAX_CORPUS_TRIAGE_JSON_BYTES {
        return Err(format!(
            "stdout is {} bytes; maximum corpus-triage JSON size is {MAX_CORPUS_TRIAGE_JSON_BYTES} bytes",
            stdout.len()
        ));
    }
    let report: CorpusTriageReport = serde_json::from_slice(stdout)
        .map_err(|error| format!("stdout is not a corpus-triage JSON report: {error}"))?;
    // CorpusTriageReport intentionally tolerates absent fields added with
    // serde defaults, but this gate consumes a schema-versioned report from
    // the same executable. Reject unknown/omitted representations so a report
    // schema change cannot silently bypass a gate invariant.
    let parsed_value: serde_json::Value = serde_json::from_slice(stdout)
        .map_err(|error| format!("stdout is not a corpus-triage JSON value: {error}"))?;
    let known_value = serde_json::to_value(&report)
        .map_err(|error| format!("cannot normalize corpus-triage JSON: {error}"))?;
    if parsed_value != known_value {
        return Err("report contains unknown, omitted, or non-canonical schema fields".to_string());
    }
    validate_corpus_triage_report(&report)
}

fn checked_count_sum(
    label: &str,
    counts: impl IntoIterator<Item = usize>,
) -> Result<usize, String> {
    counts.into_iter().try_fold(0usize, |total, count| {
        total
            .checked_add(count)
            .ok_or_else(|| format!("{label} overflows usize"))
    })
}

fn checked_count_add(total: &mut usize, count: usize, label: &str) -> Result<(), String> {
    *total = total
        .checked_add(count)
        .ok_or_else(|| format!("{label} overflows usize"))?;
    Ok(())
}

fn validate_corpus_triage_report(report: &CorpusTriageReport) -> Result<String, String> {
    if report.schema_version != 1 {
        return Err(format!(
            "unsupported report schema_version {}; expected 1",
            report.schema_version
        ));
    }
    if report.manifest_schema_version != 2 {
        return Err(format!(
            "canonical corpus manifest schema_version must be 2, got {}",
            report.manifest_schema_version
        ));
    }
    if report.manifest_path != CANONICAL_CORPUS_MANIFEST {
        return Err(format!(
            "manifest_path must be `{CANONICAL_CORPUS_MANIFEST}`, got `{}`",
            report.manifest_path
        ));
    }
    if report.upstream_repo.as_deref() != Some(VERUS_REPO_URL) {
        return Err(format!(
            "upstream_repo must be `{VERUS_REPO_URL}`, got `{}`",
            report.upstream_repo.as_deref().unwrap_or("<missing>")
        ));
    }
    let upstream_ref = report
        .upstream_ref
        .as_deref()
        .ok_or_else(|| "upstream_ref is missing".to_string())?;
    if !is_full_git_commit(upstream_ref) {
        return Err(format!(
            "upstream_ref must be a concrete 40-hex commit, got `{upstream_ref}`"
        ));
    }
    let required_roots = REQUIRED_VERUS_TEST_ROOTS
        .iter()
        .map(|root| (*root).to_string())
        .collect::<Vec<_>>();
    if report.upstream_test_roots != required_roots {
        return Err(format!(
            "upstream_test_roots must be exactly {required_roots:?}, got {:?}",
            report.upstream_test_roots
        ));
    }
    if report.entry_count == 0 {
        return Err("manifest must contain at least one entry".to_string());
    }

    for (classification, count) in &report.classification_counts {
        if !ALLOWED_CORPUS_CLASSIFICATIONS.contains(&classification.as_str()) {
            return Err(format!(
                "classification_counts contains disallowed classification `{classification}`"
            ));
        }
        if *count == 0 {
            return Err(format!(
                "classification_counts contains zero-valued classification `{classification}`"
            ));
        }
    }
    let classification_total = checked_count_sum(
        "classification count total",
        report.classification_counts.values().copied(),
    )?;
    if classification_total != report.entry_count {
        return Err(format!(
            "classification count total {classification_total} does not match entry_count {}",
            report.entry_count
        ));
    }

    let summary = &report.replacement_summary;
    if summary.total_entries != report.entry_count {
        return Err(format!(
            "replacement total_entries {} does not match entry_count {}",
            summary.total_entries, report.entry_count
        ));
    }
    let classification_count =
        |name: &str| report.classification_counts.get(name).copied().unwrap_or(0);
    let accepted_classifications = checked_count_sum(
        "accepted classification count",
        [
            classification_count("ported"),
            classification_count("unchanged"),
        ],
    )?;
    if summary.accepted_executable_entries != accepted_classifications {
        return Err(format!(
            "accepted executable count {} does not match ported/unchanged classification count {accepted_classifications}",
            summary.accepted_executable_entries
        ));
    }
    if summary.unsupported_gap_entries != classification_count("unsupported-gap") {
        return Err(format!(
            "unsupported-gap summary count {} does not match classification count {}",
            summary.unsupported_gap_entries,
            classification_count("unsupported-gap")
        ));
    }
    if summary.unclassified_entries != 0 {
        return Err(format!(
            "unclassified entries are not allowed in gate triage (observed {})",
            summary.unclassified_entries
        ));
    }
    if summary.not_applicable_entries != classification_count("not-applicable") {
        return Err(format!(
            "not-applicable summary count {} does not match classification count {}",
            summary.not_applicable_entries,
            classification_count("not-applicable")
        ));
    }
    let classified_summary_total = checked_count_sum(
        "replacement classification total",
        [
            summary.accepted_executable_entries,
            summary.unsupported_gap_entries,
            summary.unclassified_entries,
            summary.not_applicable_entries,
        ],
    )?;
    if classified_summary_total != report.entry_count {
        return Err(format!(
            "replacement classification total {classified_summary_total} does not match entry_count {}",
            report.entry_count
        ));
    }
    if summary.accepted_entries_missing_trust_vc_paths != 0 {
        return Err(format!(
            "{} accepted entries are missing trust_vc_paths",
            summary.accepted_entries_missing_trust_vc_paths
        ));
    }
    if summary.accepted_entries_missing_expected_cases != 0 {
        return Err(format!(
            "{} accepted entries are missing expected_cases",
            summary.accepted_entries_missing_expected_cases
        ));
    }

    if !report.duplicate_entries.is_empty() {
        return Err(format!(
            "manifest contains {} duplicate entries",
            report.duplicate_entries.len()
        ));
    }
    if !report.invalid_classification_entries.is_empty() {
        return Err(format!(
            "manifest contains {} invalid classification entries",
            report.invalid_classification_entries.len()
        ));
    }
    if !report.missing_trust_vc_paths.is_empty() {
        return Err(format!(
            "{} accepted entries are missing trust_vc_paths",
            report.missing_trust_vc_paths.len()
        ));
    }
    if !report.missing_trust_vc_path_files.is_empty() {
        return Err(format!(
            "{} accepted trust_vc_path files are missing or invalid",
            report.missing_trust_vc_path_files.len()
        ));
    }

    if report.accepted_executable_ports.len() != summary.accepted_executable_entries {
        return Err(format!(
            "accepted_executable_ports length {} does not match summary count {}",
            report.accepted_executable_ports.len(),
            summary.accepted_executable_entries
        ));
    }
    let mut accepted_paths = BTreeSet::new();
    let mut accepted_trust_vc_path_count = 0usize;
    let mut accepted_expected_case_count = 0usize;
    // The accepted-case total is not shippable on its own: the three buckets
    // are three unequal kinds of evidence (only `counterexample` enters the
    // source-level correspondence rule at all). Recount them here so a report
    // whose split has been zeroed, dropped or re-apportioned while the total
    // stands cannot pass the gate.
    let mut accepted_cases_counterexample = 0usize;
    let mut accepted_cases_verified = 0usize;
    let mut accepted_cases_error = 0usize;
    // And the `verified` bucket is not one kind of evidence either: for a
    // `cargo_trust_vc_integration_test` entry the schema REQUIRES `verified`
    // with `min_obligations: 0` and no fingerprints, so its count pins nothing.
    // Recount that sub-bucket here too, and re-derive the schema fact it rests
    // on, so a report cannot label a case schema-fixed while it carries a real
    // pin, or hide a schema-fixed case inside the author-pinned remainder.
    let mut accepted_cases_verified_schema_fixed = 0usize;
    let mut accepted_known_gap_entries = 0usize;
    let mut accepted_classification_counts = BTreeMap::<String, usize>::new();
    for entry in &report.accepted_executable_ports {
        if !matches!(entry.classification.as_str(), "ported" | "unchanged") {
            return Err(format!(
                "accepted executable `{}` has invalid classification `{}`",
                entry.upstream_path, entry.classification
            ));
        }
        if !accepted_paths.insert(entry.upstream_path.as_str()) {
            return Err(format!(
                "accepted_executable_ports repeats `{}`",
                entry.upstream_path
            ));
        }
        if entry.upstream_path.trim().is_empty() {
            return Err("accepted_executable_ports contains an empty upstream_path".to_string());
        }
        let accepted_classification_count = accepted_classification_counts
            .entry(entry.classification.clone())
            .or_default();
        checked_count_add(
            accepted_classification_count,
            1,
            "accepted classification count",
        )?;
        if entry.trust_vc_paths.is_empty() {
            return Err(format!(
                "accepted executable `{}` has no trust_vc_paths",
                entry.upstream_path
            ));
        }
        if entry.expected_cases.is_empty() {
            return Err(format!(
                "accepted executable `{}` has no expected_cases",
                entry.upstream_path
            ));
        }
        let mut trust_vc_paths = BTreeSet::new();
        for trust_vc_path in &entry.trust_vc_paths {
            if trust_vc_path.trim().is_empty() {
                return Err(format!(
                    "accepted executable `{}` has an empty trust_vc_path",
                    entry.upstream_path
                ));
            }
            if !trust_vc_paths.insert(trust_vc_path.as_str()) {
                return Err(format!(
                    "accepted executable `{}` repeats trust_vc_path `{trust_vc_path}`",
                    entry.upstream_path
                ));
            }
        }
        let mut expected_case_ids = BTreeSet::new();
        for expected_case in &entry.expected_cases {
            if expected_case.case_id.trim().is_empty() {
                return Err(format!(
                    "accepted executable `{}` has an empty expected case id",
                    entry.upstream_path
                ));
            }
            if !expected_case_ids.insert(expected_case.case_id.as_str()) {
                return Err(format!(
                    "accepted executable `{}` repeats expected case id `{}`",
                    entry.upstream_path, expected_case.case_id
                ));
            }
            if let Some(trust_vc_path) = expected_case.trust_vc_path.as_deref() {
                if !trust_vc_paths.contains(trust_vc_path) {
                    return Err(format!(
                        "accepted executable `{}` expected case `{}` references undeclared trust_vc_path `{trust_vc_path}`",
                        entry.upstream_path, expected_case.case_id
                    ));
                }
            }
        }
        checked_count_add(
            &mut accepted_trust_vc_path_count,
            entry.trust_vc_paths.len(),
            "accepted trust_vc_path count",
        )?;
        checked_count_add(
            &mut accepted_expected_case_count,
            entry.expected_cases.len(),
            "accepted expected-case count",
        )?;
        let schema_fixed_entry = entry.evidence_kind == CARGO_TRUST_VC_INTEGRATION_TEST_KIND;
        for expected_case in &entry.expected_cases {
            let bucket = match expected_case.expected_verdict.as_str() {
                "counterexample" => &mut accepted_cases_counterexample,
                "verified" => &mut accepted_cases_verified,
                "error" => &mut accepted_cases_error,
                other => {
                    return Err(format!(
                        "accepted executable `{}` expected case `{}` declares unaccepted verdict `{other}`",
                        entry.upstream_path, expected_case.case_id
                    ));
                }
            };
            checked_count_add(bucket, 1, "accepted expected-case split")?;
            if schema_fixed_entry {
                if expected_case.expected_verdict != "verified" {
                    return Err(format!(
                        "accepted executable `{}` expected case `{}` is `{}` inside a {CARGO_TRUST_VC_INTEGRATION_TEST_KIND} entry, where the schema requires `verified`",
                        entry.upstream_path,
                        expected_case.case_id,
                        expected_case.expected_verdict
                    ));
                }
                if expected_case.min_obligations != 0
                    || !expected_case.obligation_fingerprints.is_empty()
                {
                    return Err(format!(
                        "accepted executable `{}` expected case `{}` carries an obligation pin inside a {CARGO_TRUST_VC_INTEGRATION_TEST_KIND} entry, where the schema forbids one",
                        entry.upstream_path, expected_case.case_id
                    ));
                }
                checked_count_add(
                    &mut accepted_cases_verified_schema_fixed,
                    1,
                    "accepted schema-fixed verified-case count",
                )?;
            }
        }
        checked_count_add(
            &mut accepted_known_gap_entries,
            usize::from(!entry.known_gaps.is_empty()),
            "accepted known-gap entry count",
        )?;
    }
    let expected_accepted_classification_counts = ["ported", "unchanged"]
        .into_iter()
        .filter_map(|classification| {
            let count = classification_count(classification);
            (count > 0).then(|| (classification.to_string(), count))
        })
        .collect::<BTreeMap<_, _>>();
    if accepted_classification_counts != expected_accepted_classification_counts {
        return Err(
            "accepted executable classification counts do not match top-level classification_counts"
                .to_string(),
        );
    }
    if accepted_trust_vc_path_count != summary.accepted_trust_vc_path_count {
        return Err(format!(
            "accepted trust_vc_path count {accepted_trust_vc_path_count} does not match summary count {}",
            summary.accepted_trust_vc_path_count
        ));
    }
    if accepted_expected_case_count != summary.accepted_expected_case_count {
        return Err(format!(
            "accepted expected-case count {accepted_expected_case_count} does not match summary count {}",
            summary.accepted_expected_case_count
        ));
    }
    for (label, counted, claimed) in [
        (
            "counterexample",
            accepted_cases_counterexample,
            summary.accepted_expected_cases_counterexample,
        ),
        (
            "verified",
            accepted_cases_verified,
            summary.accepted_expected_cases_verified,
        ),
        (
            "error",
            accepted_cases_error,
            summary.accepted_expected_cases_error,
        ),
        (
            "verified (schema-fixed)",
            accepted_cases_verified_schema_fixed,
            summary.accepted_expected_cases_verified_schema_fixed,
        ),
    ] {
        if counted != claimed {
            return Err(format!(
                "accepted expected-case `{label}` count {counted} does not match summary count {claimed}"
            ));
        }
    }
    if accepted_cases_counterexample + accepted_cases_verified + accepted_cases_error
        != accepted_expected_case_count
    {
        return Err(format!(
            "accepted expected-case split {accepted_cases_counterexample}+{accepted_cases_verified}+{accepted_cases_error} does not account for all {accepted_expected_case_count} accepted cases"
        ));
    }
    if accepted_cases_verified_schema_fixed > accepted_cases_verified {
        return Err(format!(
            "schema-fixed verified-case count {accepted_cases_verified_schema_fixed} exceeds the verified bucket {accepted_cases_verified}"
        ));
    }
    if accepted_known_gap_entries != summary.accepted_known_gap_entries {
        return Err(format!(
            "accepted known-gap entry count {accepted_known_gap_entries} does not match summary count {}",
            summary.accepted_known_gap_entries
        ));
    }

    if report.unsupported_gap_evidence.len() > summary.unsupported_gap_entries {
        return Err(format!(
            "unsupported-gap evidence count {} exceeds summary count {}",
            report.unsupported_gap_evidence.len(),
            summary.unsupported_gap_entries
        ));
    }
    let mut unsupported_paths = BTreeSet::new();
    for entry in &report.unsupported_gap_evidence {
        if entry.classification != "unsupported-gap" {
            return Err(format!(
                "unsupported-gap evidence `{}` has classification `{}`",
                entry.upstream_path, entry.classification
            ));
        }
        if entry.upstream_path.trim().is_empty() {
            return Err("unsupported-gap evidence contains an empty upstream_path".to_string());
        }
        if !unsupported_paths.insert(entry.upstream_path.as_str()) {
            return Err(format!(
                "unsupported-gap evidence repeats `{}`",
                entry.upstream_path
            ));
        }
        if accepted_paths.contains(entry.upstream_path.as_str()) {
            return Err(format!(
                "upstream path `{}` appears in both accepted and unsupported-gap evidence",
                entry.upstream_path
            ));
        }
        if entry.trust_vc_paths.is_empty() && entry.expected_cases.is_empty() {
            return Err(format!(
                "unsupported-gap evidence `{}` contains no partial TrustVc evidence",
                entry.upstream_path
            ));
        }
    }

    let mut bucket_classification_counts = BTreeMap::<String, usize>::new();
    let mut bucket_entry_count = 0usize;
    let mut seen_buckets = BTreeSet::new();
    for bucket in &report.path_buckets {
        if bucket.bucket.trim().is_empty() {
            return Err("path_buckets contains an empty bucket name".to_string());
        }
        if !seen_buckets.insert(bucket.bucket.as_str()) {
            return Err(format!("path_buckets repeats `{}`", bucket.bucket));
        }
        if bucket.entry_count == 0 {
            return Err(format!(
                "path bucket `{}` has a zero entry_count",
                bucket.bucket
            ));
        }
        checked_count_add(
            &mut bucket_entry_count,
            bucket.entry_count,
            "path-bucket entry total",
        )?;
        if bucket.missing_trust_vc_paths != 0 || bucket.missing_trust_vc_path_files != 0 {
            return Err(format!(
                "path bucket `{}` reports missing accepted paths or files",
                bucket.bucket
            ));
        }
        let bucket_total = checked_count_sum(
            &format!("path bucket `{}` classification total", bucket.bucket),
            bucket.classification_counts.values().copied(),
        )?;
        if bucket
            .classification_counts
            .values()
            .any(|count| *count == 0)
        {
            return Err(format!(
                "path bucket `{}` contains a zero-valued classification",
                bucket.bucket
            ));
        }
        if bucket_total != bucket.entry_count {
            return Err(format!(
                "path bucket `{}` classification total {bucket_total} does not match entry_count {}",
                bucket.bucket, bucket.entry_count
            ));
        }
        for (classification, count) in &bucket.classification_counts {
            let aggregate = bucket_classification_counts
                .entry(classification.clone())
                .or_default();
            checked_count_add(aggregate, *count, "path-bucket classification count")?;
        }
    }
    if bucket_entry_count != report.entry_count {
        return Err(format!(
            "path-bucket entry total {bucket_entry_count} does not match entry_count {}",
            report.entry_count
        ));
    }
    if bucket_classification_counts != report.classification_counts {
        return Err(
            "path-bucket classification counts do not match top-level classification_counts"
                .to_string(),
        );
    }

    Ok(format!(
        "offline canonical manifest triage is coherent: {} entries ({} accepted, including {} with disclosed known gaps; {} declared unsupported gaps; {} not applicable); no replacement claim",
        report.entry_count,
        summary.accepted_executable_entries,
        summary.accepted_known_gap_entries,
        summary.unsupported_gap_entries,
        summary.not_applicable_entries,
    ))
}

fn is_full_git_commit(value: &str) -> bool {
    value.len() == 40
        && value.bytes().all(|byte| byte.is_ascii_hexdigit())
        && value.bytes().any(|byte| byte != b'0')
}

/// Short run of every fuzz target. Under targo that is `fuzz/run.sh`, which
/// builds the targets on `targo --unverified build` with cargo-fuzz's `-s none`
/// coverage instrumentation and runs libFuzzer without a sanitizer (the Trust
/// sysroot ships no sanitizer runtime: `ld: library 'rustc-trust_rt.asan' not
/// found`, measured 2026-09-28, and `targo fuzz` is not a command). A `$CARGO`
/// that is not targo keeps `$CARGO fuzz run`, the stock exception in
/// fuzz/README.md; this stage never falls back to a stock cargo on its own.
fn run_fuzz_smoke_stage(args: &GateArgs, runner: &FuzzRunner) -> StageResult {
    let command = runner.display("<target>", GATE_FUZZ_SMOKE_SECS);
    if args.quick {
        return skipped_stage("fuzz-smoke", &command, "skipped by --quick", args.json);
    }
    if args.no_fuzz {
        return skipped_stage("fuzz-smoke", &command, "skipped by --no-fuzz", args.json);
    }
    if !runner.available() {
        return skipped_stage("fuzz-smoke", &command, &runner.missing_reason(), args.json);
    }

    let start = Instant::now();
    for target in FUZZ_TARGETS {
        if !args.json {
            eprintln!("[gate] fuzz smoke: {target}");
        }
        let mut fuzz = runner.command(&args.current_dir, target, GATE_FUZZ_SMOKE_SECS);
        match execute_gate_command(&mut fuzz, args.json) {
            Ok((status, _)) if status.success() => {}
            Ok((status, captured_detail)) => {
                return StageResult {
                    name: "fuzz-smoke".to_string(),
                    command,
                    status: StageStatus::Fail,
                    exit_code: status.code(),
                    duration_ms: start.elapsed().as_millis(),
                    detail: Some(match captured_detail {
                        Some(detail) => format!("target `{target}` failed: {detail}"),
                        None => format!("target `{target}` failed"),
                    }),
                };
            }
            Err(error) => {
                return StageResult {
                    name: "fuzz-smoke".to_string(),
                    command,
                    status: StageStatus::Fail,
                    exit_code: None,
                    duration_ms: start.elapsed().as_millis(),
                    detail: Some(format!(
                        "failed to launch `{}`: {error}",
                        runner.display(target, GATE_FUZZ_SMOKE_SECS)
                    )),
                };
            }
        }
    }
    StageResult {
        name: "fuzz-smoke".to_string(),
        command,
        status: StageStatus::Pass,
        exit_code: Some(0),
        duration_ms: start.elapsed().as_millis(),
        detail: None,
    }
}

fn run_stage(
    name: &str,
    program: &str,
    args: &[&str],
    current_dir: &Path,
    json: bool,
) -> StageResult {
    let owned: Vec<String> = args.iter().map(|arg| (*arg).to_string()).collect();
    run_stage_owned(name, program, &owned, current_dir, json)
}

fn run_stage_owned<P: AsRef<OsStr>>(
    name: &str,
    program: P,
    args: &[String],
    current_dir: &Path,
    json: bool,
) -> StageResult {
    let program = program.as_ref();
    let program_display = program.to_string_lossy();
    let command = format!("{program_display} {}", args.join(" "));
    if !json {
        eprintln!("[gate] {name}: {command}");
    }
    let start = Instant::now();
    let mut child = Command::new(program);
    child.current_dir(current_dir).args(args);
    let status = execute_gate_command(&mut child, json);
    let duration_ms = start.elapsed().as_millis();
    match status {
        Ok((status, _)) if status.success() => StageResult {
            name: name.to_string(),
            command,
            status: StageStatus::Pass,
            exit_code: status.code(),
            duration_ms,
            detail: None,
        },
        Ok((status, captured_detail)) => StageResult {
            name: name.to_string(),
            command,
            status: StageStatus::Fail,
            exit_code: status.code(),
            duration_ms,
            detail: captured_detail,
        },
        Err(error) => StageResult {
            name: name.to_string(),
            command,
            status: StageStatus::Fail,
            exit_code: None,
            duration_ms,
            detail: Some(format!("failed to launch `{program_display}`: {error}")),
        },
    }
}

/// JSON gate mode promises that stdout contains exactly one `GateReport`.
/// Capture every child stream in that mode; retain a bounded diagnostic only
/// for failed commands so the final report remains useful and deterministic.
fn execute_gate_command(
    command: &mut Command,
    capture_output: bool,
) -> std::io::Result<(std::process::ExitStatus, Option<String>)> {
    if !capture_output {
        return command.status().map(|status| (status, None));
    }
    command.output().map(|output| {
        let detail = if output.status.success() {
            None
        } else {
            captured_command_failure_detail(&output.stdout, &output.stderr)
        };
        (output.status, detail)
    })
}

fn captured_command_failure_detail(stdout: &[u8], stderr: &[u8]) -> Option<String> {
    let mut parts = Vec::new();
    let stderr = bounded_output_tail(stderr);
    if !stderr.is_empty() {
        parts.push(format!("stderr: {stderr}"));
    }
    let stdout = bounded_output_tail(stdout);
    if !stdout.is_empty() {
        parts.push(format!("stdout: {stdout}"));
    }
    (!parts.is_empty()).then(|| parts.join("; "))
}

fn bounded_output_tail(output: &[u8]) -> String {
    const MAX_DETAIL_CHARS: usize = 1_000;
    let output = String::from_utf8_lossy(output);
    let output = output.trim();
    if output.chars().count() <= MAX_DETAIL_CHARS {
        return output.to_string();
    }
    output
        .chars()
        .rev()
        .take(MAX_DETAIL_CHARS)
        .collect::<String>()
        .chars()
        .rev()
        .collect()
}

fn skipped_stage(name: &str, command: &str, reason: &str, json: bool) -> StageResult {
    if !json {
        eprintln!("[gate] {name}: SKIP ({reason})");
    }
    StageResult {
        name: name.to_string(),
        command: command.to_string(),
        status: StageStatus::Skipped,
        exit_code: None,
        duration_ms: 0,
        detail: Some(reason.to_string()),
    }
}

fn print_summary_table(report: &GateReport) {
    let name_width = report
        .stages
        .iter()
        .map(|stage| stage.name.len())
        .max()
        .unwrap_or(4)
        .max(5);
    println!();
    println!("trust-vc gate summary");
    println!("{:-<width$}", "", width = name_width + 24);
    println!(
        "{:<name_width$}  {:<6}  {:>10}",
        "STAGE", "RESULT", "TIME(ms)"
    );
    for stage in &report.stages {
        println!(
            "{:<name_width$}  {:<6}  {:>10}",
            stage.name,
            stage.status.label(),
            stage.duration_ms,
        );
    }
    println!("{:-<width$}", "", width = name_width + 24);
    println!("overall: {}", report.overall.label());
}

/// Parsed `fuzz` arguments.
#[derive(Debug, Clone)]
pub(crate) struct FuzzArgs {
    current_dir: PathBuf,
    target: Option<String>,
    time_secs: u64,
}

/// Detect and parse a `fuzz` invocation from raw process arguments.
pub(crate) fn detect_fuzz_subcommand(raw_args: &[String]) -> Option<Result<FuzzArgs, String>> {
    let tail_start = gate_tail_start(raw_args, "fuzz")?;
    let current_dir = match std::env::current_dir() {
        Ok(dir) => dir,
        Err(error) => return Some(Err(format!("cannot resolve current directory: {error}"))),
    };
    Some(parse_fuzz_tail(current_dir, &raw_args[tail_start..]))
}

fn parse_fuzz_tail(current_dir: PathBuf, tail: &[String]) -> Result<FuzzArgs, String> {
    let mut args = FuzzArgs {
        current_dir,
        target: None,
        time_secs: DEFAULT_FUZZ_TIME_SECS,
    };
    let mut index = 0;
    while index < tail.len() {
        let arg = tail[index].as_str();
        match arg {
            "--time" => {
                let Some(value) = tail.get(index + 1) else {
                    return Err("--time requires a number of seconds".to_string());
                };
                args.time_secs = parse_time_secs(value)?;
                index += 2;
                continue;
            }
            "-h" | "--help" => {
                print!("{}", fuzz_help());
                std::process::exit(0);
            }
            _ if arg.starts_with("--time=") => {
                // quality-audit: allow-expect — the match arm's starts_with guard makes the strip infallible
                let value = arg.strip_prefix("--time=").expect("checked prefix");
                args.time_secs = parse_time_secs(value)?;
            }
            _ if arg.starts_with('-') => {
                return Err(format!(
                    "unsupported `cargo trust-vc fuzz` argument `{arg}`; see `cargo trust-vc fuzz --help`"
                ));
            }
            _ => {
                if args.target.is_some() {
                    return Err("cargo trust-vc fuzz accepts at most one target".to_string());
                }
                if !FUZZ_TARGETS.contains(&arg) {
                    return Err(format!(
                        "unknown fuzz target `{arg}`; available targets: {}",
                        FUZZ_TARGETS.join(", ")
                    ));
                }
                args.target = Some(arg.to_string());
            }
        }
        index += 1;
    }
    Ok(args)
}

fn parse_time_secs(value: &str) -> Result<u64, String> {
    let secs: u64 = value
        .parse()
        .map_err(|_| format!("invalid --time value `{value}`; expected a number of seconds"))?;
    if secs == 0 {
        return Err("--time must be greater than zero".to_string());
    }
    Ok(secs)
}

/// Run the libfuzzer targets. Under targo each target runs through
/// `fuzz/run.sh`; a `$CARGO` that is not targo needs its own `fuzz`
/// subcommand (the stock exception). When the runner is missing this prints
/// the repair and returns exit code 2 (does not fake a run).
pub(crate) fn run_fuzz(args: &FuzzArgs) -> Result<i32, String> {
    let cargo = cargo_command();
    let is_targo = probe_targo(&cargo, &args.current_dir, FUZZ_NEEDS_TARGO).is_ok();
    let runner = FuzzRunner::select(&cargo, &args.current_dir, is_targo);
    if !runner.available() {
        let target = args.target.as_deref().unwrap_or("ensures_false");
        eprintln!("Error: {}.", runner.missing_reason());
        eprintln!();
        match &runner {
            FuzzRunner::TrustScript { .. } => {
                eprintln!("Run it from the trust-vc checkout root:");
                eprintln!("  {}", runner.display(target, args.time_secs));
            }
            FuzzRunner::CargoFuzz { .. } => {
                eprintln!("The Trust lane (fuzz/run.sh on `targo --unverified build`):");
                eprintln!("  targo trust-vc fuzz {target} --time {}", args.time_secs);
                eprintln!();
                // STOCK EXCEPTION, only for an AddressSanitizer build: the
                // Trust sysroot ships no sanitizer runtime (measured
                // `ld: library 'rustc-trust_rt.asan' not found`). The commands
                // name an INSTALLED nightly and turn rustup's auto-install
                // off: `rustup run` on a missing toolchain downloads it.
                eprintln!(
                    "STOCK EXCEPTION, for an AddressSanitizer build only (see fuzz/README.md);"
                );
                eprintln!(
                    "  <nightly> is one `rustup toolchain list` shows, and RUSTUP_AUTO_INSTALL=0 makes a"
                );
                eprintln!("  missing one an error instead of a network download:");
                eprintln!("  RUSTUP_AUTO_INSTALL=0 rustup run <nightly> cargo install cargo-fuzz");
                eprintln!(
                    "  RUSTUP_AUTO_INSTALL=0 rustup run <nightly> cargo fuzz run {target} -- -max_total_time={}",
                    args.time_secs
                );
            }
        }
        eprintln!();
        eprintln!("Available targets: {}", FUZZ_TARGETS.join(", "));
        return Ok(2);
    }

    let targets: Vec<&str> = match &args.target {
        Some(target) => vec![target.as_str()],
        None => FUZZ_TARGETS.to_vec(),
    };

    for target in targets {
        println!("Running fuzz target `{target}` for {}s", args.time_secs);
        let status = runner
            .command(&args.current_dir, target, args.time_secs)
            .status()
            .map_err(|error| {
                format!(
                    "failed to launch `{}`: {error}",
                    runner.display(target, args.time_secs)
                )
            })?;
        if !status.success() {
            eprintln!(
                "fuzz target `{target}` failed with exit code {}",
                status.code().unwrap_or(-1)
            );
            return Ok(1);
        }
    }
    Ok(0)
}

/// How a fuzz target is built and run for the `$CARGO` in use.
///
/// Under targo the targets do not go through cargo-fuzz: cargo-fuzz 0.13.2
/// spawns a bare `cargo` from PATH (`src/project.rs`, `Command::new("cargo")`),
/// not `$CARGO`, so its build would leave both Targo lanes, and `targo fuzz` is
/// not a command. `fuzz/run.sh` does cargo-fuzz's build step itself on
/// `targo --unverified build` with the same coverage instrumentation, then runs
/// libFuzzer. A `$CARGO` that fails the targo discriminator keeps
/// `$CARGO fuzz run`: the labelled stock exception, never chosen on its own.
#[derive(Debug, Clone, PartialEq, Eq)]
enum FuzzRunner {
    TrustScript { script: PathBuf, targo: String },
    CargoFuzz { cargo: String },
}

impl FuzzRunner {
    /// `is_targo` is the verdict of [`probe_targo`] on `cargo`.
    fn select(cargo: &str, current_dir: &Path, is_targo: bool) -> Self {
        if is_targo {
            FuzzRunner::TrustScript {
                script: current_dir.join(TRUST_FUZZ_SCRIPT),
                targo: cargo.to_string(),
            }
        } else {
            FuzzRunner::CargoFuzz {
                cargo: cargo.to_string(),
            }
        }
    }

    /// The command a human would type for `target` with a `secs` budget.
    fn display(&self, target: &str, secs: u64) -> String {
        match self {
            FuzzRunner::TrustScript { .. } => {
                format!("{TRUST_FUZZ_SCRIPT} {target} -max_total_time={secs}")
            }
            FuzzRunner::CargoFuzz { cargo } => {
                format!("{cargo} fuzz run {target} -- -max_total_time={secs}")
            }
        }
    }

    fn available(&self) -> bool {
        match self {
            FuzzRunner::TrustScript { script, .. } => script.is_file(),
            FuzzRunner::CargoFuzz { cargo } => Command::new(cargo)
                .args(["fuzz", "--version"])
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .status()
                .map(|status| status.success())
                .unwrap_or(false),
        }
    }

    fn missing_reason(&self) -> String {
        match self {
            FuzzRunner::TrustScript { script, .. } => {
                format!("{} not found", script.display())
            }
            FuzzRunner::CargoFuzz { cargo } => format!(
                "`{cargo}` is not the Trust toolchain's targo and `{cargo} fuzz` is not \
                 available; {FUZZ_NEEDS_TARGO}"
            ),
        }
    }

    fn command(&self, current_dir: &Path, target: &str, secs: u64) -> Command {
        let budget = format!("-max_total_time={secs}");
        match self {
            FuzzRunner::TrustScript { script, targo } => {
                let mut command = Command::new("bash");
                command
                    .current_dir(current_dir)
                    .env("TARGO", targo)
                    .arg(script)
                    .arg(target)
                    .arg(budget);
                command
            }
            FuzzRunner::CargoFuzz { cargo } => {
                let mut command = Command::new(cargo);
                command
                    .current_dir(current_dir)
                    .args(["fuzz", "run", target, "--"])
                    .arg(budget);
                command
            }
        }
    }
}

fn cargo_command() -> String {
    crate::trust_cargo_command()
}

/// Compute the index of the first stage argument for a cargo subcommand named
/// `subcommand`, handling the `trust_vc`/`trust-vc` cargo prefixes and the bare
/// form. Returns `None` when the args do not select this subcommand.
fn gate_tail_start(raw_args: &[String], subcommand: &str) -> Option<usize> {
    match (
        raw_args.get(1).map(String::as_str),
        raw_args.get(2).map(String::as_str),
    ) {
        (Some("trust_vc" | "trust-vc"), Some(cmd)) if cmd == subcommand => Some(3),
        (Some(cmd), _) if cmd == subcommand => Some(2),
        _ => None,
    }
}

/// One-line description of every top-level subcommand, in display order.
const SUBCOMMAND_INDEX: &[(&str, &str)] = &[
    (
        "check",
        "Verify trust-vc-annotated functions in a Rust crate",
    ),
    (
        "gate",
        "Run the full local gate: fmt, clippy, test, examples, evidence, fuzz smoke",
    ),
    (
        "fuzz",
        "Run the libfuzzer targets (fuzz/run.sh under targo)",
    ),
    (
        "evidence",
        "Generate Verus-replacement parity evidence reports",
    ),
    (
        "suggest",
        "Suggest trust_vc annotations via the oracle backend",
    ),
    (
        "new",
        "Scaffold a new verified crate with a working annotated example",
    ),
    (
        "verus-compat",
        "cargo-verus-compatible check/build with Verus arg forwarding",
    ),
];

/// Render the discoverable top-level help index.
pub(crate) fn top_level_help() -> String {
    let mut out = String::new();
    out.push_str(
        "targo-trust-vc — Verus-parity verifier backed by the pure-Rust ay SMT solver\n\n",
    );
    out.push_str("Usage:\n");
    out.push_str("  targo trust-vc <SUBCOMMAND> [OPTIONS]\n\n");
    out.push_str("Subcommands:\n");
    let width = SUBCOMMAND_INDEX
        .iter()
        .map(|(name, _)| name.len())
        .max()
        .unwrap_or(0);
    for (name, description) in SUBCOMMAND_INDEX {
        out.push_str(&format!("  {name:<width$}  {description}\n"));
    }
    out.push('\n');
    out.push_str("Run `targo trust-vc <SUBCOMMAND> --help` for subcommand-specific options.\n");
    out
}

fn gate_help() -> String {
    let mut out = String::new();
    out.push_str("cargo trust-vc gate — run every local check, in order\n\n");
    out.push_str("Usage:\n  cargo trust-vc gate [OPTIONS]\n\n");
    out.push_str("Stages (in order):\n");
    out.push_str("  fmt       targo fmt --all --check\n");
    out.push_str("  clippy    targo tippy --locked --workspace --all-targets -- -D warnings\n");
    out.push_str("  test      targo --unverified test --locked --workspace\n");
    out.push_str("  examples  targo --unverified build --locked --examples --workspace\n");
    out.push_str("  evidence  targo trust-vc evidence --corpus-triage-report --json\n");
    out.push_str(&format!(
        "  fuzz-smoke  {TRUST_FUZZ_SCRIPT} <target> -max_total_time={GATE_FUZZ_SMOKE_SECS} per target\n"
    ));
    out.push_str("            (targo --unverified build plus libFuzzer, no sanitizer)\n\n");
    out.push_str(
        "Every toolchain stage runs `$CARGO` (targo under `targo trust-vc gate`, else\n\
         `targo` from PATH) and fails when it is not targo; there is no stock fallback.\n\n",
    );
    out.push_str("Options:\n");
    out.push_str("  --quick            Skip slow stages (test, fuzz)\n");
    out.push_str("  --no-fuzz          Skip the fuzz smoke stage\n");
    out.push_str("  --json             Emit a machine-readable JSON report\n\n");
    out.push_str(
        "Checkout-backed manifest evidence is separate:\n  cargo trust-vc evidence \
         --port-manifest-only --verus-path <CHECKOUT> --json\n\n",
    );
    out.push_str("Exit codes:\n  0  All stages passed\n  1  A stage failed\n  2  CLI error\n");
    out
}

fn fuzz_help() -> String {
    let mut out = String::new();
    out.push_str("cargo trust-vc fuzz — run the libfuzzer targets\n\n");
    out.push_str("Usage:\n  cargo trust-vc fuzz [TARGET] [--time SECS]\n\n");
    out.push_str("Targets:\n");
    for target in FUZZ_TARGETS {
        out.push_str(&format!("  {target}\n"));
    }
    out.push_str("\nOptions:\n");
    out.push_str(&format!(
        "  --time <SECS>  Per-target wall-clock budget (default {DEFAULT_FUZZ_TIME_SECS})\n"
    ));
    out.push_str("\nWhen no TARGET is given, every target runs in sequence.\n");
    out.push_str(
        "Each target runs through fuzz/run.sh (`targo --unverified build` plus libFuzzer,\n",
    );
    out.push_str("no sanitizer: the Trust sysroot ships none); run it from the checkout root.\n");
    out.push_str("An AddressSanitizer run is the stock-nightly exception in fuzz/README.md.\n");
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[cfg(unix)]
    fn unique_frontend_test_dir(label: &str) -> PathBuf {
        use std::time::{SystemTime, UNIX_EPOCH};

        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock should follow the Unix epoch")
            .as_nanos();
        std::env::temp_dir().join(format!(
            "trust-vc-gate-{label}-{}-{nonce}",
            std::process::id()
        ))
    }

    fn raw(args: &[&str]) -> Vec<String> {
        args.iter().map(|arg| (*arg).to_string()).collect()
    }

    fn valid_triage_report() -> CorpusTriageReport {
        serde_json::from_value(json!({
            "schema_version": 1,
            "manifest_schema_version": 2,
            "manifest_path": CANONICAL_CORPUS_MANIFEST,
            "upstream_repo": VERUS_REPO_URL,
            "upstream_ref": "0123456789abcdef0123456789abcdef01234567",
            "upstream_test_roots": REQUIRED_VERUS_TEST_ROOTS,
            "entry_count": 3,
            "classification_counts": {
                "ported": 1,
                "unsupported-gap": 1,
                "not-applicable": 1
            },
            "replacement_summary": {
                "total_entries": 3,
                "accepted_executable_entries": 1,
                "accepted_trust_vc_path_count": 1,
                "accepted_expected_case_count": 1,
                "accepted_expected_cases_counterexample": 0,
                "accepted_expected_cases_verified": 1,
                "accepted_expected_cases_error": 0,
                "unsupported_gap_entries": 1,
                "unclassified_entries": 0,
                "not_applicable_entries": 1,
                "accepted_known_gap_entries": 0,
                "accepted_entries_missing_trust_vc_paths": 0,
                "accepted_entries_missing_expected_cases": 0
            },
            "accepted_executable_ports": [{
                "upstream_path": "source/rust_verify_test/tests/ported.rs",
                "classification": "ported",
                "evidence_kind": "proof_obligation",
                "owner_issue": "https://example.invalid/ported",
                "reason": "Executable TrustVc coverage.",
                "trust_vc_paths": ["tests/ui/ported.rs"],
                "expected_cases": [{
                    "case_id": "ported",
                    "trust_vc_path": "tests/ui/ported.rs",
                    "expected_verdict": "verified",
                    "min_obligations": 1,
                    "obligation_fingerprints": [],
                    "expected_error_patterns": [],
                    "expected_rust_diagnostic_pattern_sets": [],
                    "forbidden_diagnostic_patterns": [],
                    "expected_warning_patterns": []
                }],
                "known_gaps": [],
                "notes": ""
            }],
            "unsupported_gap_evidence": [{
                "upstream_path": "source/rust_verify_test/tests/unsupported.rs",
                "classification": "unsupported-gap",
                "evidence_kind": "proof_obligation",
                "owner_issue": "https://example.invalid/unsupported",
                "reason": "Declared unsupported semantic surface.",
                "trust_vc_paths": ["evals/verus/ported/unsupported.rs"],
                "expected_cases": [],
                "known_gaps": ["not implemented"],
                "notes": ""
            }],
            "path_buckets": [{
                "bucket": "root",
                "entry_count": 3,
                "classification_counts": {
                    "ported": 1,
                    "unsupported-gap": 1,
                    "not-applicable": 1
                },
                "missing_trust_vc_paths": 0,
                "missing_trust_vc_path_files": 0
            }],
            "missing_trust_vc_paths": [],
            "missing_trust_vc_path_files": [],
            "duplicate_entries": [],
            "invalid_classification_entries": []
        }))
        .expect("valid triage fixture should deserialize")
    }

    fn assert_triage_rejected(report: CorpusTriageReport, expected: &str) {
        let error = validate_corpus_triage_report(&report).expect_err("report should fail closed");
        assert!(
            error.contains(expected),
            "expected `{expected}` in rejection, got `{error}`"
        );
    }

    #[test]
    fn detects_gate_bare_and_prefixed() {
        assert_eq!(
            gate_tail_start(&raw(&["cargo-trust-vc", "gate"]), "gate"),
            Some(2)
        );
        assert_eq!(
            gate_tail_start(&raw(&["cargo-trust-vc", "trust_vc", "gate"]), "gate"),
            Some(3)
        );
        assert_eq!(
            gate_tail_start(&raw(&["cargo-trust-vc", "trust-vc", "gate"]), "gate"),
            Some(3)
        );
        assert_eq!(
            gate_tail_start(&raw(&["cargo-trust-vc", "check"]), "gate"),
            None
        );
    }

    #[test]
    fn parses_gate_flags() {
        let args = parse_gate_tail(
            PathBuf::from("."),
            &raw(&["--quick", "--no-fuzz", "--json"]),
        )
        .expect("flags should parse");
        assert!(args.quick);
        assert!(args.no_fuzz);
        assert!(args.json);
    }

    #[test]
    fn gate_help_names_the_targo_fmt_and_tippy_route() {
        let help = gate_help();
        assert!(help.contains("targo fmt --all --check"), "{help}");
        assert!(
            help.contains("targo tippy --locked --workspace --all-targets -- -D warnings"),
            "{help}"
        );
        assert!(
            help.contains("targo --unverified test --locked --workspace"),
            "{help}"
        );
        assert!(
            help.contains("targo --unverified build --locked --examples --workspace"),
            "{help}"
        );
        assert!(!help.contains("rust_frontend.sh"), "{help}");
        assert!(!help.contains("cargo clippy"), "{help}");
    }

    #[cfg(unix)]
    fn write_executable(path: &Path, body: &str) {
        use std::os::unix::fs::PermissionsExt;

        std::fs::write(path, body).expect("synthetic executable should be written");
        let mut permissions = std::fs::metadata(path)
            .expect("synthetic executable metadata should exist")
            .permissions();
        permissions.set_mode(0o755);
        std::fs::set_permissions(path, permissions)
            .expect("synthetic executable should be executable");
    }

    #[cfg(unix)]
    #[test]
    fn toolchain_stages_run_targo_with_their_lane() {
        use std::fs;

        let root = unique_frontend_test_dir("targo-stages");
        fs::create_dir_all(&root).expect("synthetic gate root should exist");
        let fake_targo = root.join("targo");
        write_executable(
            &fake_targo,
            "#!/bin/sh\nprintf '%s\\n' \"$@\" >> targo-invocations.txt\n",
        );
        let cargo = fake_targo.to_string_lossy().into_owned();
        let identity = probe_targo(&cargo, &root, GATE_NEEDS_TARGO);
        assert_eq!(identity, Ok(()));

        let fmt = run_targo_stage(
            "fmt",
            &cargo,
            identity.as_ref(),
            &["fmt", "--all", "--check"],
            &root,
            true,
        );
        assert_eq!(fmt.status, StageStatus::Pass, "{fmt:?}");
        assert_eq!(fmt.command, format!("{cargo} fmt --all --check"));
        let test = run_targo_stage(
            "test",
            &cargo,
            identity.as_ref(),
            &[TARGO_UNVERIFIED_LANE, "test", "--locked", "--workspace"],
            &root,
            true,
        );
        assert_eq!(test.status, StageStatus::Pass, "{test:?}");
        assert_eq!(
            fs::read_to_string(root.join("targo-invocations.txt"))
                .expect("targo invocations should be recorded"),
            "--unverified\n--version\nfmt\n--all\n--check\n--unverified\ntest\n--locked\n--workspace\n"
        );

        fs::remove_dir_all(&root).expect("synthetic gate root should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn a_cargo_that_is_not_targo_fails_every_toolchain_stage_without_running_it() {
        use std::fs;

        let root = unique_frontend_test_dir("not-targo");
        fs::create_dir_all(&root).expect("synthetic gate root should exist");
        // Upstream cargo's answer to the discriminator.
        let stock_cargo = root.join("cargo");
        write_executable(
            &stock_cargo,
            "#!/bin/sh\nif [ \"$1\" = --unverified ]; then echo \"error: unexpected argument '--unverified' found\" >&2; exit 1; fi\ntouch ran-a-stage\n",
        );
        let cargo = stock_cargo.to_string_lossy().into_owned();
        let identity = probe_targo(&cargo, &root, GATE_NEEDS_TARGO);
        let refusal = identity
            .clone()
            .expect_err("stock cargo must fail the discriminator");
        assert!(refusal.contains("targo"), "{refusal}");
        assert!(refusal.contains("unexpected argument"), "{refusal}");

        let fmt = run_targo_stage(
            "fmt",
            &cargo,
            identity.as_ref(),
            &["fmt", "--all", "--check"],
            &root,
            true,
        );
        assert_eq!(fmt.status, StageStatus::Fail, "{fmt:?}");
        assert_eq!(fmt.detail.as_deref(), Some(refusal.as_str()));
        assert!(
            !root.join("ran-a-stage").exists(),
            "a non-targo cargo must not run the stage"
        );

        let missing = probe_targo(
            &root.join("definitely-missing").to_string_lossy(),
            &root,
            GATE_NEEDS_TARGO,
        )
        .expect_err("a missing program fails the discriminator");
        assert!(missing.contains("failed to launch"), "{missing}");

        fs::remove_dir_all(&root).expect("synthetic gate root should be removed");
    }

    #[test]
    fn rejects_verus_path_with_checkout_evidence_guidance() {
        for tail in [
            raw(&["--verus-path", "/tmp/verus"]),
            raw(&["--verus-path=/tmp/verus"]),
        ] {
            let error = parse_gate_tail(PathBuf::from("."), &tail)
                .expect_err("offline gate must not silently ignore --verus-path");
            assert!(error.contains("offline local-integrity gate"), "{error}");
            assert!(error.contains("--port-manifest-only"), "{error}");
        }
    }

    #[test]
    fn rejects_unknown_gate_flag() {
        let err = parse_gate_tail(PathBuf::from("."), &raw(&["--bogus"]))
            .expect_err("unknown flag should error");
        assert!(err.contains("--bogus"), "{err}");
    }

    #[test]
    fn accepts_coherent_offline_corpus_triage() {
        let detail = validate_corpus_triage_report(&valid_triage_report())
            .expect("coherent report should pass");
        assert!(detail.contains("no replacement claim"), "{detail}");
        assert!(detail.contains("1 declared unsupported gaps"), "{detail}");
    }

    #[test]
    fn checked_in_canonical_manifest_passes_offline_triage_validator() {
        let crate_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .canonicalize()
            .expect("workspace root should resolve");
        let canonical_manifest_path = crate_root.join(CANONICAL_CORPUS_MANIFEST);
        let evidence_args = crate::evidence::EvidenceArgs {
            crate_root: crate_root.clone(),
            output_dir: crate_root.join(".trust_vc/evidence"),
            port_output_dir: crate_root.join("evals/verus/ported"),
            verus_path: None,
            verus_rev: None,
            manifest_path: Some(canonical_manifest_path.clone()),
            canonical_manifest_path,
            strict: false,
            json: true,
            markdown: false,
            run_trust_vc: false,
            cargo_command: "cargo".to_string(),
            cargo_command_overridden: false,
            run_trust_vc_corpus: false,
            trust_vc_corpus_command: None,
            run_verus: false,
            port_manifest_only: false,
            update_verus_tests_manifest: false,
            refresh_trust_vc_corpus_evidence: false,
            repin_obligation_rendering_drift: Vec::new(),
            corpus_triage_report: true,
            scaffold_verus_port_stubs: false,
            verus_command: None,
        };
        let report = crate::evidence::run_corpus_triage_report(&evidence_args)
            .expect("checked-in canonical manifest should produce offline triage");
        validate_corpus_triage_report(&report)
            .expect("checked-in canonical manifest triage should pass gate validation");
    }

    /// The accepted-case TOTAL must never travel without its split, so a
    /// report that keeps the total and zeroes the bucket that says how the
    /// cases were checked is incoherent, not merely terse.
    ///
    /// `counterexample` is the only bucket the source-level correspondence
    /// rule reaches; re-apportioning cases into it, or out of it, changes what
    /// the accepted-case count means.
    #[test]
    fn rejects_an_accepted_case_split_that_does_not_match_the_entries() {
        let mut zeroed = valid_triage_report();
        zeroed.replacement_summary.accepted_expected_cases_verified = 0;
        let error = validate_corpus_triage_report(&zeroed)
            .expect_err("a zeroed split must not pass with the total standing");
        assert!(
            error.contains("`verified` count 1 does not match summary count 0"),
            "unexpected error: {error}"
        );

        let mut relabelled = valid_triage_report();
        relabelled
            .replacement_summary
            .accepted_expected_cases_verified = 0;
        relabelled
            .replacement_summary
            .accepted_expected_cases_counterexample = 1;
        let error = validate_corpus_triage_report(&relabelled)
            .expect_err("moving a case into the correspondence-scoped bucket must not pass");
        assert!(
            error.contains("`counterexample` count 0 does not match summary count 1"),
            "unexpected error: {error}"
        );
    }

    /// And the `verified` bucket's own sub-split is recomputed here too.
    ///
    /// Clause (2b) of the bound says 48 of the verified cases are pinned by
    /// NOTHING because the schema wrote their verdict and their zero count. A
    /// hand-written sub-count would let that sentence drift off the corpus it
    /// describes, and a mislabelled entry would let a case that really does
    /// carry a pin be reported as pin-free (or the reverse). Both directions
    /// fail here.
    #[test]
    fn rejects_a_verified_sub_split_that_does_not_match_the_entries() {
        // A schema-fixed entry whose schema-fixed sub-count was not reported.
        let mut undisclosed = valid_triage_report();
        undisclosed.accepted_executable_ports[0].evidence_kind =
            CARGO_TRUST_VC_INTEGRATION_TEST_KIND.to_string();
        undisclosed.accepted_executable_ports[0].expected_cases[0].min_obligations = 0;
        let error = validate_corpus_triage_report(&undisclosed)
            .expect_err("a schema-fixed case hidden in the author-pinned remainder must not pass");
        assert!(
            error.contains("`verified (schema-fixed)` count 1 does not match summary count 0"),
            "unexpected error: {error}"
        );

        // The same report with the sub-count disclosed passes, so the refusal
        // above is the sub-count and nothing else.
        let mut disclosed = undisclosed.clone();
        disclosed
            .replacement_summary
            .accepted_expected_cases_verified_schema_fixed = 1;
        validate_corpus_triage_report(&disclosed)
            .expect("a disclosed schema-fixed sub-count should pass");

        // A claimed schema-fixed case in an entry the schema does not fix.
        let mut overclaimed = valid_triage_report();
        overclaimed
            .replacement_summary
            .accepted_expected_cases_verified_schema_fixed = 1;
        let error = validate_corpus_triage_report(&overclaimed)
            .expect_err("an author-pinned case reported as schema-fixed must not pass");
        assert!(
            error.contains("`verified (schema-fixed)` count 0 does not match summary count 1"),
            "unexpected error: {error}"
        );

        // And a schema-fixed entry whose case carries a REAL pin is refused
        // outright: "the schema wrote it" must stay true of every case counted.
        let mut pinned = undisclosed.clone();
        pinned
            .replacement_summary
            .accepted_expected_cases_verified_schema_fixed = 1;
        pinned.accepted_executable_ports[0].expected_cases[0].min_obligations = 1;
        let error = validate_corpus_triage_report(&pinned)
            .expect_err("a pinned case inside a schema-fixed entry must not pass");
        assert!(
            error.contains("carries an obligation pin inside a cargo_trust_vc_integration_test"),
            "unexpected error: {error}"
        );

        let mut fingerprinted = undisclosed.clone();
        fingerprinted
            .replacement_summary
            .accepted_expected_cases_verified_schema_fixed = 1;
        fingerprinted.accepted_executable_ports[0].expected_cases[0]
            .obligation_fingerprints
            .push(
                "sha256:0000000000000000000000000000000000000000000000000000000000000000"
                    .to_string(),
            );
        let error = validate_corpus_triage_report(&fingerprinted)
            .expect_err("a fingerprinted case inside a schema-fixed entry must not pass");
        assert!(
            error.contains("carries an obligation pin inside a cargo_trust_vc_integration_test"),
            "unexpected error: {error}"
        );
    }

    #[test]
    fn accepts_coherent_unsupported_only_manifest() {
        let mut report = valid_triage_report();
        report.entry_count = 1;
        report.classification_counts = BTreeMap::from([("unsupported-gap".to_string(), 1)]);
        report.replacement_summary.total_entries = 1;
        report.replacement_summary.accepted_executable_entries = 0;
        report.replacement_summary.accepted_trust_vc_path_count = 0;
        report.replacement_summary.accepted_expected_case_count = 0;
        report.replacement_summary.accepted_expected_cases_verified = 0;
        report.replacement_summary.unsupported_gap_entries = 1;
        report.replacement_summary.not_applicable_entries = 0;
        report.accepted_executable_ports.clear();
        report.path_buckets[0].entry_count = 1;
        report.path_buckets[0].classification_counts =
            BTreeMap::from([("unsupported-gap".to_string(), 1)]);

        validate_corpus_triage_report(&report)
            .expect("honestly declared unsupported-only manifest should pass triage");
    }

    #[test]
    fn rejects_malformed_corpus_triage_stdout() {
        let error = parse_and_validate_corpus_triage(b"this is not JSON")
            .expect_err("malformed stdout should fail closed");
        assert!(error.contains("not a corpus-triage JSON report"), "{error}");

        let mut noisy =
            serde_json::to_vec(&valid_triage_report()).expect("fixture should serialize");
        noisy.extend_from_slice(b"\nunexpected child log");
        let error = parse_and_validate_corpus_triage(&noisy)
            .expect_err("JSON followed by child noise should fail closed");
        assert!(error.contains("not a corpus-triage JSON report"), "{error}");
    }

    #[test]
    fn rejects_unknown_or_oversized_corpus_triage_json() {
        let mut value =
            serde_json::to_value(valid_triage_report()).expect("fixture should serialize");
        value
            .as_object_mut()
            .expect("report should be an object")
            .insert("future_unchecked_field".to_string(), json!(true));
        let bytes = serde_json::to_vec(&value).expect("mutated report should serialize");
        let error = parse_and_validate_corpus_triage(&bytes)
            .expect_err("unknown schema fields should fail closed");
        assert!(
            error.contains("unknown, omitted, or non-canonical"),
            "{error}"
        );

        let oversized = vec![b' '; MAX_CORPUS_TRIAGE_JSON_BYTES + 1];
        let error = parse_and_validate_corpus_triage(&oversized)
            .expect_err("oversized stdout should fail before deserialization");
        assert!(error.contains("maximum corpus-triage JSON size"), "{error}");
    }

    #[test]
    fn rejects_wrong_corpus_identity_and_revision() {
        let mut report = valid_triage_report();
        report.schema_version = 2;
        assert_triage_rejected(report, "schema_version");

        let mut report = valid_triage_report();
        report.manifest_schema_version = 1;
        assert_triage_rejected(report, "manifest schema_version");

        let mut report = valid_triage_report();
        report.manifest_path = "other.json".to_string();
        assert_triage_rejected(report, "manifest_path");

        let mut report = valid_triage_report();
        report.upstream_repo = Some("https://example.invalid/verus".to_string());
        assert_triage_rejected(report, "upstream_repo");

        let mut report = valid_triage_report();
        report.upstream_ref = Some("main".to_string());
        assert_triage_rejected(report, "40-hex");

        let mut report = valid_triage_report();
        report.upstream_test_roots.pop();
        assert_triage_rejected(report, "upstream_test_roots");
    }

    #[test]
    fn rejects_incoherent_classification_accounting() {
        let mut report = valid_triage_report();
        report.entry_count += 1;
        assert_triage_rejected(report, "classification count total");

        let mut report = valid_triage_report();
        report.replacement_summary.total_entries += 1;
        assert_triage_rejected(report, "replacement total_entries");

        let mut report = valid_triage_report();
        report
            .classification_counts
            .insert("unclassified".to_string(), 1);
        assert_triage_rejected(report, "disallowed classification");

        let mut report = valid_triage_report();
        report.replacement_summary.unclassified_entries = 1;
        assert_triage_rejected(report, "unclassified entries");

        let mut report = valid_triage_report();
        report
            .classification_counts
            .insert("mystery".to_string(), 1);
        assert_triage_rejected(report, "disallowed classification");

        let mut report = valid_triage_report();
        report.classification_counts = BTreeMap::from([
            ("ported".to_string(), usize::MAX),
            ("unchanged".to_string(), 1),
        ]);
        assert_triage_rejected(report, "overflows usize");
    }

    #[test]
    fn rejects_manifest_structural_failures() {
        let mut report = valid_triage_report();
        report.duplicate_entries.push("duplicate.rs".to_string());
        assert_triage_rejected(report, "duplicate entries");

        let mut report = valid_triage_report();
        report.invalid_classification_entries.push(
            serde_json::from_value(json!({
                "upstream_path": "invalid.rs",
                "classification": "invalid",
                "path_bucket": "root",
                "owner_issue": "issue",
                "reason": "reason"
            }))
            .expect("triage entry should deserialize"),
        );
        assert_triage_rejected(report, "invalid classification entries");

        let mut report = valid_triage_report();
        report.missing_trust_vc_paths.push(
            serde_json::from_value(json!({
                "upstream_path": "missing.rs",
                "classification": "ported",
                "path_bucket": "root",
                "owner_issue": "issue",
                "reason": "reason"
            }))
            .expect("triage entry should deserialize"),
        );
        assert_triage_rejected(report, "missing trust_vc_paths");

        let mut report = valid_triage_report();
        report.missing_trust_vc_path_files.push(
            serde_json::from_value(json!({
                "upstream_path": "missing.rs",
                "classification": "ported",
                "trust_vc_path": "missing.rs"
            }))
            .expect("missing file entry should deserialize"),
        );
        assert_triage_rejected(report, "files are missing or invalid");
    }

    #[test]
    fn rejects_incoherent_accepted_evidence_counts() {
        let mut report = valid_triage_report();
        report.replacement_summary.accepted_executable_entries = 2;
        assert_triage_rejected(report, "accepted executable count");

        let mut report = valid_triage_report();
        report.replacement_summary.accepted_trust_vc_path_count = 2;
        assert_triage_rejected(report, "accepted trust_vc_path count");

        let mut report = valid_triage_report();
        report.replacement_summary.accepted_expected_case_count = 2;
        assert_triage_rejected(report, "accepted expected-case count");

        let mut report = valid_triage_report();
        report.accepted_executable_ports[0].expected_cases.clear();
        assert_triage_rejected(report, "has no expected_cases");

        let mut report = valid_triage_report();
        report
            .replacement_summary
            .accepted_entries_missing_trust_vc_paths = 1;
        assert_triage_rejected(report, "missing trust_vc_paths");

        let mut report = valid_triage_report();
        report.accepted_executable_ports[0].classification = "unchanged".to_string();
        assert_triage_rejected(report, "classification counts do not match");

        let mut report = valid_triage_report();
        let duplicate = report.accepted_executable_ports[0].trust_vc_paths[0].clone();
        report.accepted_executable_ports[0]
            .trust_vc_paths
            .push(duplicate);
        assert_triage_rejected(report, "repeats trust_vc_path");

        let mut report = valid_triage_report();
        let duplicate = report.accepted_executable_ports[0].expected_cases[0].clone();
        report.accepted_executable_ports[0]
            .expected_cases
            .push(duplicate);
        assert_triage_rejected(report, "repeats expected case id");
    }

    #[test]
    fn rejects_incoherent_unsupported_gap_evidence() {
        let mut report = valid_triage_report();
        report.unsupported_gap_evidence[0].classification = "ported".to_string();
        assert_triage_rejected(report, "has classification");

        let mut report = valid_triage_report();
        report.unsupported_gap_evidence[0].trust_vc_paths.clear();
        report.unsupported_gap_evidence[0].expected_cases.clear();
        assert_triage_rejected(report, "contains no partial TrustVc evidence");

        let mut report = valid_triage_report();
        report.unsupported_gap_evidence[0].upstream_path =
            report.accepted_executable_ports[0].upstream_path.clone();
        assert_triage_rejected(report, "both accepted and unsupported-gap");
    }

    #[test]
    fn rejects_incoherent_path_bucket_accounting() {
        let mut report = valid_triage_report();
        report.path_buckets[0].entry_count += 1;
        assert_triage_rejected(report, "path bucket");

        let mut report = valid_triage_report();
        report.path_buckets[0]
            .classification_counts
            .insert("ported".to_string(), 2);
        report.path_buckets[0].entry_count += 1;
        assert_triage_rejected(report, "path-bucket entry total");

        let mut report = valid_triage_report();
        report.path_buckets[0].missing_trust_vc_path_files = 1;
        assert_triage_rejected(report, "reports missing accepted paths or files");

        let mut report = valid_triage_report();
        report.path_buckets[0]
            .classification_counts
            .insert("unchanged".to_string(), 0);
        assert_triage_rejected(report, "zero-valued classification");

        let mut report = valid_triage_report();
        report.path_buckets.push(report.path_buckets[0].clone());
        assert_triage_rejected(report, "path_buckets repeats");
    }

    #[test]
    fn json_stage_mode_captures_child_output() {
        let stage = run_stage_owned(
            "noisy",
            "sh",
            &raw(&["-c", "printf child-stdout; printf child-stderr >&2; exit 7"]),
            Path::new("."),
            true,
        );
        assert_eq!(stage.status, StageStatus::Fail);
        assert_eq!(stage.exit_code, Some(7));
        let detail = stage.detail.expect("captured failure should retain detail");
        assert!(detail.contains("child-stdout"), "{detail}");
        assert!(detail.contains("child-stderr"), "{detail}");

        let large = vec![b'x'; 2_000];
        let bounded = bounded_output_tail(&large);
        assert_eq!(bounded.len(), 1_000);
        assert!(bounded.bytes().all(|byte| byte == b'x'));
    }

    #[test]
    fn fuzz_smoke_report_matches_the_real_budgeted_command() {
        let args = GateArgs {
            current_dir: PathBuf::from("."),
            quick: true,
            no_fuzz: false,
            json: true,
        };
        let targo = FuzzRunner::select("configured-targo", &args.current_dir, true);
        let stage = run_fuzz_smoke_stage(&args, &targo);
        assert_eq!(stage.status, StageStatus::Skipped);
        assert_eq!(
            stage.command,
            format!("fuzz/run.sh <target> -max_total_time={GATE_FUZZ_SMOKE_SECS}")
        );
        let stock = FuzzRunner::select("configured-cargo", &args.current_dir, false);
        let stage = run_fuzz_smoke_stage(&args, &stock);
        assert_eq!(stage.status, StageStatus::Skipped);
        assert_eq!(
            stage.command,
            format!("configured-cargo fuzz run <target> -- -max_total_time={GATE_FUZZ_SMOKE_SECS}")
        );
    }

    #[test]
    fn fuzz_runs_through_the_trust_script_under_targo_and_cargo_fuzz_otherwise() {
        let root = Path::new("/checkout");
        for targo in ["targo", "/opt/trust/bin/targo"] {
            let runner = FuzzRunner::select(targo, root, true);
            assert_eq!(
                runner,
                FuzzRunner::TrustScript {
                    script: root.join("fuzz/run.sh"),
                    targo: targo.to_string(),
                },
                "{targo}"
            );
            let command = runner.command(root, "ensures_false", 3);
            assert_eq!(command.get_program(), "bash");
            let argv: Vec<&OsStr> = command.get_args().collect();
            assert_eq!(
                argv,
                [
                    root.join("fuzz/run.sh").as_os_str(),
                    OsStr::new("ensures_false"),
                    OsStr::new("-max_total_time=3"),
                ]
            );
            assert!(
                command
                    .get_envs()
                    .any(|(key, value)| key == "TARGO" && value == Some(OsStr::new(targo))),
                "fuzz/run.sh must build with the same targo: {targo}"
            );
            let shown = runner.display("<target>", 3);
            assert_eq!(shown, "fuzz/run.sh <target> -max_total_time=3");
            assert!(!shown.contains("cargo"), "{shown}");
        }

        // A $CARGO that failed the targo discriminator keeps `$CARGO fuzz`.
        let runner = FuzzRunner::select("cargo", root, false);
        assert_eq!(
            runner,
            FuzzRunner::CargoFuzz {
                cargo: "cargo".to_string()
            }
        );
        let command = runner.command(root, "mode_crossing", 7);
        assert_eq!(command.get_program(), "cargo");
        let argv: Vec<&OsStr> = command.get_args().collect();
        assert_eq!(
            argv,
            ["fuzz", "run", "mode_crossing", "--", "-max_total_time=7"]
        );
        assert!(runner.missing_reason().contains("targo trust-vc fuzz"));
    }

    #[test]
    fn trust_fuzz_runner_is_available_only_where_the_script_exists() {
        let missing = FuzzRunner::select("targo", Path::new("/definitely/not/a/checkout"), true);
        assert!(!missing.available());
        assert!(missing.missing_reason().contains("fuzz/run.sh not found"));
        assert!(!missing.missing_reason().contains("cargo install"));

        let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        assert!(FuzzRunner::select("targo", &repo, true).available());
    }

    #[test]
    fn parses_fuzz_target_and_time() {
        let args = parse_fuzz_tail(PathBuf::from("."), &raw(&["ensures_false", "--time", "12"]))
            .expect("fuzz args should parse");
        assert_eq!(args.target.as_deref(), Some("ensures_false"));
        assert_eq!(args.time_secs, 12);
    }

    #[test]
    fn rejects_unknown_fuzz_target() {
        let err = parse_fuzz_tail(PathBuf::from("."), &raw(&["not_a_target"]))
            .expect_err("unknown target should error");
        assert!(err.contains("not_a_target"), "{err}");
    }

    #[test]
    fn rejects_zero_time() {
        let err = parse_fuzz_tail(PathBuf::from("."), &raw(&["--time", "0"]))
            .expect_err("zero time should error");
        assert!(err.contains("greater than zero"), "{err}");
    }

    #[test]
    fn top_level_help_lists_all_subcommands() {
        let help = top_level_help();
        for (name, _) in SUBCOMMAND_INDEX {
            assert!(help.contains(name), "help should list `{name}`");
        }
        assert!(help.contains("gate"));
        assert!(help.contains("fuzz"));
    }
}
