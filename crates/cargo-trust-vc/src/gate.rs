// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Local "run everything" gate and fuzz runner.
//!
//! These subcommands replace the role of CI with on-demand local commands.
//! Everything is driven through `std::process::Command`; no new crate
//! dependencies are introduced. The gate never weakens or fakes any check:
//! each stage runs the real tool and a non-zero stage exit fails the gate.

use serde::Serialize;
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
    verus_path: Option<String>,
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
        verus_path: None,
    };
    let mut index = 0;
    while index < tail.len() {
        let arg = tail[index].as_str();
        match arg {
            "--quick" => args.quick = true,
            "--no-fuzz" => args.no_fuzz = true,
            "--json" => args.json = true,
            "--verus-path" => {
                let Some(value) = tail.get(index + 1) else {
                    return Err("--verus-path requires a directory path".to_string());
                };
                args.verus_path = Some(value.clone());
                index += 2;
                continue;
            }
            "-h" | "--help" => {
                print!("{}", gate_help());
                std::process::exit(0);
            }
            _ if arg.starts_with("--verus-path=") => {
                let value = arg.strip_prefix("--verus-path=").expect("checked prefix");
                args.verus_path = Some(value.to_string());
            }
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

/// Run the full local gate. Returns the process exit code (0 pass, 1 stage failed).
pub(crate) fn run_gate(args: &GateArgs) -> Result<i32, String> {
    let cargo = cargo_command();
    let mut stages: Vec<StageResult> = Vec::new();

    stages.push(run_stage(
        "fmt",
        &cargo,
        &["fmt", "--all", "--check"],
        &args.current_dir,
        args.json,
    ));
    stages.push(run_stage(
        "clippy",
        &cargo,
        &[
            "clippy",
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
            &format!("{cargo} test --workspace"),
            "skipped by --quick",
            args.json,
        ));
    } else {
        stages.push(run_stage(
            "test",
            &cargo,
            &["test", "--workspace"],
            &args.current_dir,
            args.json,
        ));
    }

    // Build the shipped examples. `cargo build --examples` covers every
    // example target across the workspace without running them.
    stages.push(run_stage(
        "examples",
        &cargo,
        &["build", "--examples", "--workspace"],
        &args.current_dir,
        args.json,
    ));

    // Evidence: manifest-layer triage is always cheap and offline. When a Verus
    // checkout is supplied, run the fuller (still non-strict) evidence pass.
    stages.push(run_evidence_stage(args));

    // Fuzz smoke: only when cargo-fuzz is installed and not disabled.
    stages.push(run_fuzz_smoke_stage(args, &cargo));

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

fn run_evidence_stage(args: &GateArgs) -> StageResult {
    // Re-invoke this same binary so we exercise the real evidence pipeline.
    let self_exe = std::env::current_exe()
        .map(|path| path.to_string_lossy().into_owned())
        .unwrap_or_else(|_| "cargo-trust-vc".to_string());
    let mut command_args: Vec<String> = vec![
        "trust-vc".to_string(),
        "evidence".to_string(),
        "--port-manifest-only".to_string(),
    ];
    if let Some(verus_path) = &args.verus_path {
        command_args.push("--run-trust_vc".to_string());
        command_args.push("--run-trust-vc-corpus".to_string());
        command_args.push("--run-verus".to_string());
        command_args.push("--verus-path".to_string());
        command_args.push(verus_path.clone());
    }
    run_stage_owned(
        "evidence",
        &self_exe,
        &command_args,
        &args.current_dir,
        args.json,
    )
}

fn run_fuzz_smoke_stage(args: &GateArgs, cargo: &str) -> StageResult {
    let command = "cargo fuzz run <target> -- -runs=0".to_string();
    if args.quick {
        return skipped_stage("fuzz-smoke", &command, "skipped by --quick", args.json);
    }
    if args.no_fuzz {
        return skipped_stage("fuzz-smoke", &command, "skipped by --no-fuzz", args.json);
    }
    if !cargo_fuzz_available(cargo) {
        return skipped_stage(
            "fuzz-smoke",
            &command,
            "cargo-fuzz not installed (cargo install cargo-fuzz)",
            args.json,
        );
    }

    let start = Instant::now();
    for target in FUZZ_TARGETS {
        if !args.json {
            eprintln!("[gate] fuzz smoke: {target}");
        }
        let status = Command::new(cargo)
            .current_dir(&args.current_dir)
            .args(["fuzz", "run", target, "--"])
            .arg(format!("-max_total_time={GATE_FUZZ_SMOKE_SECS}"))
            .status();
        match status {
            Ok(status) if status.success() => {}
            Ok(status) => {
                return StageResult {
                    name: "fuzz-smoke".to_string(),
                    command,
                    status: StageStatus::Fail,
                    exit_code: status.code(),
                    duration_ms: start.elapsed().as_millis(),
                    detail: Some(format!("target `{target}` failed")),
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
                        "failed to launch cargo fuzz for `{target}`: {error}"
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

fn run_stage_owned(
    name: &str,
    program: &str,
    args: &[String],
    current_dir: &Path,
    json: bool,
) -> StageResult {
    let command = format!("{program} {}", args.join(" "));
    if !json {
        eprintln!("[gate] {name}: {command}");
    }
    let start = Instant::now();
    let status = Command::new(program)
        .current_dir(current_dir)
        .args(args)
        .status();
    let duration_ms = start.elapsed().as_millis();
    match status {
        Ok(status) if status.success() => StageResult {
            name: name.to_string(),
            command,
            status: StageStatus::Pass,
            exit_code: status.code(),
            duration_ms,
            detail: None,
        },
        Ok(status) => StageResult {
            name: name.to_string(),
            command,
            status: StageStatus::Fail,
            exit_code: status.code(),
            duration_ms,
            detail: None,
        },
        Err(error) => StageResult {
            name: name.to_string(),
            command,
            status: StageStatus::Fail,
            exit_code: None,
            duration_ms,
            detail: Some(format!("failed to launch `{program}`: {error}")),
        },
    }
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

/// Run the libfuzzer targets. Requires cargo-fuzz; otherwise prints the exact
/// install/run instructions and returns exit code 2 (does not fake a run).
pub(crate) fn run_fuzz(args: &FuzzArgs) -> Result<i32, String> {
    let cargo = cargo_command();
    if !cargo_fuzz_available(&cargo) {
        eprintln!("Error: cargo-fuzz is not installed.");
        eprintln!();
        eprintln!("Install it, then re-run:");
        eprintln!("  cargo install cargo-fuzz");
        let target = args.target.as_deref().unwrap_or("ensures_false");
        eprintln!(
            "  cargo fuzz run {target} -- -max_total_time={}",
            args.time_secs
        );
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
        let status = Command::new(&cargo)
            .current_dir(&args.current_dir)
            .args(["fuzz", "run", target, "--"])
            .arg(format!("-max_total_time={}", args.time_secs))
            .status()
            .map_err(|error| format!("failed to launch cargo fuzz: {error}"))?;
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

/// Return true if `cargo fuzz` is runnable (cargo-fuzz installed).
fn cargo_fuzz_available(cargo: &str) -> bool {
    Command::new(cargo)
        .args(["fuzz", "--version"])
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .map(|status| status.success())
        .unwrap_or(false)
}

fn cargo_command() -> String {
    std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string())
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
    ("fuzz", "Run the libfuzzer targets (requires cargo-fuzz)"),
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
        "cargo-trust-vc — Verus-parity verifier backed by the pure-Rust ay SMT solver\n\n",
    );
    out.push_str("Usage:\n");
    out.push_str("  cargo trust-vc <SUBCOMMAND> [OPTIONS]\n\n");
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
    out.push_str("Run `cargo trust-vc <SUBCOMMAND> --help` for subcommand-specific options.\n");
    out
}

fn gate_help() -> String {
    let mut out = String::new();
    out.push_str("cargo trust-vc gate — run every local check, in order\n\n");
    out.push_str("Usage:\n  cargo trust-vc gate [OPTIONS]\n\n");
    out.push_str("Stages (in order):\n");
    out.push_str("  fmt       cargo fmt --all --check\n");
    out.push_str("  clippy    cargo clippy --workspace --all-targets -- -D warnings\n");
    out.push_str("  test      cargo test --workspace\n");
    out.push_str("  examples  cargo build --examples --workspace\n");
    out.push_str("  evidence  cargo trust-vc evidence --port-manifest-only\n");
    out.push_str("  fuzz-smoke  short cargo-fuzz run per target (if cargo-fuzz installed)\n\n");
    out.push_str("Options:\n");
    out.push_str("  --quick            Skip slow stages (test, fuzz)\n");
    out.push_str("  --no-fuzz          Skip the fuzz smoke stage\n");
    out.push_str(
        "  --verus-path <P>   Also run the fuller evidence pass against a Verus checkout\n",
    );
    out.push_str("  --json             Emit a machine-readable JSON report\n\n");
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
    out.push_str("Requires cargo-fuzz (`cargo install cargo-fuzz`).\n");
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn raw(args: &[&str]) -> Vec<String> {
        args.iter().map(|arg| (*arg).to_string()).collect()
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
            &raw(&[
                "--quick",
                "--no-fuzz",
                "--json",
                "--verus-path",
                "/tmp/verus",
            ]),
        )
        .expect("flags should parse");
        assert!(args.quick);
        assert!(args.no_fuzz);
        assert!(args.json);
        assert_eq!(args.verus_path.as_deref(), Some("/tmp/verus"));
    }

    #[test]
    fn parses_verus_path_equals_form() {
        let args = parse_gate_tail(PathBuf::from("."), &raw(&["--verus-path=/x"]))
            .expect("equals form should parse");
        assert_eq!(args.verus_path.as_deref(), Some("/x"));
    }

    #[test]
    fn rejects_unknown_gate_flag() {
        let err = parse_gate_tail(PathBuf::from("."), &raw(&["--bogus"]))
            .expect_err("unknown flag should error");
        assert!(err.contains("--bogus"), "{err}");
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
