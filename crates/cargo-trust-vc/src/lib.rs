// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CLI library for `targo trust-vc check` (back-compat alias `cargo trust-vc check`)
//! and the one-word `trust-vc` command.
//!
//! Front-end CLI for trust-vc, the proof backend of Trust (the rustc fork) on
//! the pure-Rust `ay` solver. The `evidence` subcommand gates drop-in Verus
//! parity, which is the benchmark/proving ground — not the destination, which is
//! Trust's proof calculus + SMT backend. See `design-trust-proof-backend.md`.
//!
//! This was `src/main.rs` verbatim until the one-word bin landed; it is a
//! library now for ONE reason — two thin bins drive the SAME dispatch:
//!
//!   * `targo-trust-vc` (`src/main.rs`) → [`run_cargo_cli`], the Trust-native
//!     subcommand surface; the `cargo-trust-vc` alias bin shares the same file.
//!   * `trust-vc` (`src/bin/trust-vc.rs`) → [`run_one_word_cli`], which
//!     translates a friendlier argv (bare `trust-vc <FILE.rs>`, an `example`
//!     verb) and then calls [`run_cargo_cli`]. See [`one_word`].
//!
//! Neither bin needs cargo, rustc, a sysroot or an external solver at runtime:
//! sources are parsed with `syn` and the obligations are discharged in-process
//! on `ay`.
//!
//! Usage:
//!   `targo trust-vc check [OPTIONS] [PATH]`
//!   `trust-vc [OPTIONS] <PATH>`
//!
//! Options:
//!   `--check`                Compatibility no-op; verify mode is the default
//!   `--function <NAME>`      Verify a specific function only
//!   `--json`                 Output in JSON format
//!   `--localize`             Surface the first failing proof step
//!   `--no-cheating`          Reject trusted proof constructs before verification
//!   `--emit-certificate`     Write proof certificate to `.trust_vc/proof-certificate.json`
//!   `--emit-hints`           Generate optimization hints from proven facts (file or stdout)
//!   `--emit-hints-json`      Generate optimization hints in JSON format
//!   `--verbose`, `-v`        Increase CLI verbosity (up to 3 levels)
//!   `--timeout <SECONDS>`    Set a per-function verification timeout
//!   `--filter <PATTERN>`     Filter functions by name pattern (substring match)
//!   `--jobs`, `-j <JOBS>`    Limit parallel verification jobs
//!   `--watch`                Re-verify on file changes
//!   `--diff`                 Only verify functions in git-changed files
//!   `--ci`                   CI mode: no progress bars, non-zero exit on any failure

mod certificate;
#[allow(dead_code)]
mod coverage_report;
// R1 (two-language design, 2026-07-11): differential_oracle extracted to its
// neutral home — ay's `ay-z3-parity classify` subcommand (in-process ay replay
// vs declared/Z3 ground truth, UnsoundDisagree tripwire). See the Trust
// repo's docs/design/2026-07-09-two-language-spec-surface.md §6.1-3.
#[allow(dead_code)]
mod emit_hints;
mod evidence;
#[allow(dead_code)]
mod fact_strength;
mod format_types;
mod gate;
#[allow(dead_code)]
mod hint_transforms;
mod llvm_hints;
mod one_word;
mod optimization_pipeline;
mod oracle_cli;
#[allow(dead_code)]
mod proof_dashboard;
#[allow(dead_code)]
mod report;
mod scan;
mod suggest;
mod verify;
mod verify_pipeline;
#[allow(dead_code)]
mod watch_mode;

use clap::{ArgAction, CommandFactory, FromArgMatches, Parser};
use indicatif::{ProgressBar, ProgressStyle};
use quote::ToTokens;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::ffi::OsString;
use std::fmt::Write as _;
use std::io;
use std::path::{Path, PathBuf};
use std::process;
use std::time::{Duration, Instant, SystemTime};
use trust_vc_core::proven_facts;

const TRUST_VC_VERUS_PATH_ENV: &str = "TRUST_VC_VERUS_PATH";
const VERUS_PATH_ENV: &str = "VERUS_PATH";
const TRUST_VC_METADATA_CARGO_ENV: &str = "TRUST_VC_METADATA_CARGO";
const CARGO_DEFAULT_LIB_METADATA_ENV: &str = "__CARGO_DEFAULT_LIB_METADATA";
const RUSTC_WRAPPER_ENV: &str = "RUSTC_WRAPPER";
const VERUS_DRIVER_ARGS_ENV: &str = " __VERUS_DRIVER_ARGS__";
const VERUS_DRIVER_ARGS_FOR_ENV_PREFIX: &str = " __VERUS_DRIVER_ARGS_FOR_";
const VERUS_DRIVER_ARGS_SEP: &str = "__VERUS_DRIVER_ARGS_SEP__";
const VERUS_DRIVER_VERIFY_ENV_PREFIX: &str = "__VERUS_DRIVER_VERIFY_";
const VERUS_DRIVER_VIA_CARGO_ENV: &str = "__VERUS_DRIVER_VIA_CARGO__";
const CARGO_PKG_NAME_ENV: &str = "CARGO_PKG_NAME";
const CARGO_PKG_VERSION_ENV: &str = "CARGO_PKG_VERSION";
const CARGO_MANIFEST_DIR_ENV: &str = "CARGO_MANIFEST_DIR";
const CARGO_CRATE_NAME_ENV: &str = "CARGO_CRATE_NAME";
const TRUST_VC_RUSTC_WRAPPER_ARTIFACT_MAGIC: &str = "trust-vc-rustc-wrapper-artifact-v1\n";
const TRUST_VC_RUSTC_WRAPPER_ARTIFACT_SCHEMA_VERSION: u32 = 1;
const TRUST_VC_RUSTC_WRAPPER_ARTIFACT_KIND: &str =
    "cargo-trust-vc-rustc-wrapper-dependency-metadata";
const TRUST_VC_RUSTC_WRAPPER_SEMANTIC_PAYLOAD_KIND: &str = "none";
const TRUST_VC_RUSTC_WRAPPER_SEMANTIC_FACTS_PAYLOAD_KIND: &str = "trust-vc-semantic-facts-v1";
const TRUST_VC_DEPENDENCY_FACTS_ENV: &str = "__TRUST_VC_DEPENDENCY_FACTS__";
/// Opt-in frontend selection propagated into the per-crate RUSTC_WRAPPER
/// subprocess. Absent, or any value other than `driver`, means the trusted syn
/// path alone runs (the unchanged default). `driver` additionally runs the
/// nightly rustc-driver bin as a *parallel, non-authoritative* VC producer and
/// emits a driver-vs-syn parity witness.
const TRUST_VC_FRONTEND_ENV: &str = "__TRUST_VC_FRONTEND__";
/// Path to the prebuilt nightly `trust-vc-driver` bin and its runtime dylib
/// search path (both printed by `scripts/build-trust-vc-driver.sh bin`). The
/// `--frontend=driver` parity path activates only when `TRUST_VC_DRIVER_BIN` is
/// present; otherwise it is silently skipped so default behavior is unchanged.
const TRUST_VC_DRIVER_BIN_ENV: &str = "TRUST_VC_DRIVER_BIN";
const TRUST_VC_DRIVER_DYLD_ENV: &str = "TRUST_VC_DRIVER_DYLD";
/// Distinct, clearly-tagged stderr log tags for the driver-vs-syn parity
/// witness. This is a NON-authoritative evidence record — never a manifest flip
/// and never a promotion; the syn verdict stays authoritative for pass/fail.
const DRIVER_SYN_PARITY_TAG: &str = "TRUST_VC_DRIVER_SYN_PARITY";
const DRIVER_SYN_PARITY_SUMMARY_TAG: &str = "TRUST_VC_DRIVER_SYN_PARITY_SUMMARY";

#[derive(Debug, Deserialize, Serialize)]
struct TrustVcRustcWrapperArtifact {
    schema_version: u32,
    artifact_kind: String,
    crate_name: String,
    package_name: String,
    package_version: String,
    package_env_id: String,
    manifest_path: String,
    metadata_path: String,
    metadata_len: u64,
    metadata_sha256: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    source_path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    source_len: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    source_sha256: Option<String>,
    semantic_payload: TrustVcRustcWrapperSemanticPayload,
}

#[derive(Debug, Deserialize, Serialize)]
struct TrustVcRustcWrapperSemanticPayload {
    kind: String,
    proof_facts_exported: bool,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    concrete_functions: Vec<TrustVcRustcWrapperConcreteFunctionFact>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
struct TrustVcRustcWrapperConcreteFunctionFact {
    name: String,
    return_type: String,
    params: Vec<TrustVcRustcWrapperParamFact>,
    return_binding: String,
    requires: Vec<String>,
    ensures: Vec<String>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
struct TrustVcRustcWrapperParamFact {
    name: String,
    ty: String,
}

#[derive(Debug)]
struct TrustVcRustcWrapperSourceBinding {
    path: String,
    len: u64,
    sha256: String,
}

#[derive(Debug)]
struct TrustVcRustcWrapperSemanticExport {
    payload: TrustVcRustcWrapperSemanticPayload,
    source_binding: Option<TrustVcRustcWrapperSourceBinding>,
}

#[derive(Debug, Parser)]
#[command(
    bin_name = "targo trust-vc check",
    about = "Verify trust-vc-annotated functions in a Rust crate.",
    after_help = "Exit codes:\n  0  All verified (or no functions found)\n  1  At least one failure, counterexample, or unknown\n  2  CLI error"
)]
struct CliArgs {
    /// Compatibility no-op; verification is the default mode.
    #[arg(long)]
    check: bool,

    /// Verify a specific function only.
    #[arg(long = "function", value_name = "NAME")]
    function_filter: Option<String>,

    /// Output in JSON format.
    #[arg(long = "json")]
    json_output: bool,

    /// Surface the first failing proof step.
    #[arg(long)]
    localize: bool,

    /// Reject trusted proof constructs such as assume/admit/external_body before verification.
    #[arg(long = "no-cheating")]
    no_cheating: bool,

    /// Write proof certificate to `.trust_vc/proof-certificate.json`.
    #[arg(long = "emit-certificate")]
    emit_certificate: bool,

    /// Emit optimization hints derived from proven verification facts.
    ///
    /// Without a value or with `--emit-hints`, writes `<crate>.hints.rs` to the
    /// crate root. With `--emit-hints=stdout`, prints to stdout instead.
    #[arg(long = "emit-hints", value_name = "TARGET", default_missing_value = "file", num_args = 0..=1, require_equals = true)]
    emit_hints: Option<String>,

    /// Emit optimization hints as JSON (includes summary, facts, and hints).
    #[arg(long = "emit-hints-json")]
    emit_hints_json: bool,

    /// Increase CLI verbosity.
    #[arg(short = 'v', long = "verbose", action = ArgAction::Count)]
    verbose: u8,

    /// Timeout in seconds.
    #[arg(long, value_name = "SECONDS")]
    timeout: Option<u64>,

    /// Filter by pattern.
    #[arg(long, value_name = "PATTERN")]
    filter: Option<String>,

    /// Number of worker jobs.
    #[arg(short = 'j', long = "jobs", value_name = "JOBS")]
    jobs: Option<usize>,

    /// Re-verify on file changes.
    #[arg(long)]
    watch: bool,

    /// Only verify functions in files changed since the last git commit.
    #[arg(long)]
    diff: bool,

    /// CI mode: deterministic output (no progress bars, no color), non-zero exit on any failure.
    #[arg(long)]
    ci: bool,

    /// Crate root (default: current directory).
    #[arg(value_name = "PATH", default_value = ".")]
    crate_root: PathBuf,
}

#[derive(Debug, Parser)]
#[command(
    bin_name = "targo trust-vc evidence",
    about = "Generate reproducible evidence for TrustVc/Verus replacement parity.",
    after_help = "Exit codes:\n  0  Evidence generated and strict gates passed\n  1  Evidence generated but one or more required gates failed\n  2  CLI or execution error"
)]
struct EvidenceCliArgs {
    /// TrustVc crate root.
    #[arg(value_name = "PATH", default_value = ".")]
    crate_root: PathBuf,

    /// Directory where evidence JSON/Markdown reports are written.
    #[arg(long = "output-dir", value_name = "DIR")]
    output_dir: Option<PathBuf>,

    /// Existing Verus checkout root or source/ subdir. For --run-verus, --strict, or manifest updates,
    /// TRUST_VC_VERUS_PATH and then VERUS_PATH are used when this flag is absent.
    #[arg(long = "verus-path", value_name = "DIR")]
    verus_path: Option<PathBuf>,

    /// Upstream Verus git commit that --verus-path must match. Optional when the manifest upstream.ref is pinned.
    #[arg(long = "verus-rev", value_name = "REV")]
    verus_rev: Option<String>,

    /// Verus corpus classification manifest.
    #[arg(long = "manifest", value_name = "FILE")]
    manifest_path: Option<PathBuf>,

    /// Run TrustVc build/test gates.
    #[arg(long = "run-trust_vc")]
    run_trust_vc: bool,

    /// Cargo executable used for TrustVc build/test gates.
    #[arg(long = "cargo-command", value_name = "PROGRAM")]
    cargo_command: Option<String>,

    /// Verify mapped TrustVc corpus paths from accepted manifest entries.
    #[arg(long = "run-trust-vc-corpus")]
    run_trust_vc_corpus: bool,

    /// Shell command template used for each mapped TrustVc corpus path.
    ///
    /// Placeholders are shell-quoted before substitution: {crate_root},
    /// {trust_vc_path}, and {upstream_path}. Without this flag, the evidence CLI
    /// runs its built-in per-file verifier for mapped paths.
    #[arg(long = "trust-vc-corpus-command", value_name = "COMMAND")]
    trust_vc_corpus_command: Option<String>,

    /// Run upstream Verus tests from --verus-path, TRUST_VC_VERUS_PATH, or VERUS_PATH.
    #[arg(long = "run-verus")]
    run_verus: bool,

    /// Shell command to run inside --verus-path for upstream Verus tests.
    #[arg(long = "verus-command", value_name = "COMMAND")]
    verus_command: Option<String>,

    /// Generate or validate only the Verus port manifest layer.
    #[arg(long = "port-manifest-only")]
    port_manifest_only: bool,

    /// Generate or update evals/verus/verus-tests.json from --verus-path.
    #[arg(long = "update-verus-tests-manifest")]
    update_verus_tests_manifest: bool,

    /// Refresh trust_vc_source_hashes and observed obligation_fingerprints in the corpus manifest.
    #[arg(long = "refresh-trust-vc-corpus-evidence")]
    refresh_trust_vc_corpus_evidence: bool,

    /// Print a deterministic manifest triage summary and skip replacement gates.
    #[arg(long = "corpus-triage-report")]
    corpus_triage_report: bool,

    /// Create fail-closed placeholder files for unsupported/unclassified Verus corpus ports.
    #[arg(long = "scaffold-verus-port-stubs")]
    scaffold_verus_port_stubs: bool,

    /// Directory where --scaffold-verus-port-stubs writes repo-local port placeholders.
    #[arg(long = "port-output-dir", value_name = "DIR")]
    port_output_dir: Option<PathBuf>,

    /// Require every gate and manifest classification needed for a replacement claim.
    #[arg(long = "strict")]
    strict: bool,

    /// Print the JSON report to stdout instead of only writing it.
    #[arg(long = "json")]
    json: bool,

    /// Print Markdown to stdout when --json is absent. Report files still honor both flags.
    #[arg(long = "markdown")]
    markdown: bool,
}

/// Parse check-mode args from an EXPLICIT argv.
///
/// Taking the argv as an argument (rather than reading `std::env::args()` here)
/// is what lets the one-word `trust-vc` bin hand this exact parser its own
/// translated argv, so both commands accept the same flags from one definition.
/// Clap's own `--help`/error exits are preserved.
///
/// `bin_name` renames the command in clap's usage/error output — the one-word
/// bin passes `trust-vc` so a typo'd flag is answered with `Usage: trust-vc …`.
/// `None` is the cargo subcommand's own spelling and parses exactly as before.
fn parse_check_args(
    raw_args: &[String],
    bin_name: Option<&'static str>,
) -> Result<CliArgs, String> {
    let normalized = normalize_raw_args(raw_args);
    let Some(name) = bin_name else {
        let args = CliArgs::try_parse_from(normalized).unwrap_or_else(|err| err.exit());
        return finalize_args(args);
    };
    let matches = CliArgs::command()
        .name(name)
        .bin_name(name)
        .try_get_matches_from(normalized)
        .unwrap_or_else(|err| err.exit());
    let args = CliArgs::from_arg_matches(&matches).map_err(|err| err.to_string())?;
    finalize_args(args)
}

fn parse_evidence_args_from(raw_args: &[String]) -> Result<Option<EvidenceCliArgs>, clap::Error> {
    let Some(normalized) = normalize_evidence_raw_args(raw_args) else {
        return Ok(None);
    };
    EvidenceCliArgs::try_parse_from(normalized).map(Some)
}

fn normalize_evidence_raw_args(raw_args: &[String]) -> Option<Vec<String>> {
    if raw_args.is_empty() {
        return None;
    }

    let program = raw_args[0].clone();
    match (
        raw_args.get(1).map(String::as_str),
        raw_args.get(2).map(String::as_str),
    ) {
        (Some("trust_vc" | "trust-vc"), Some("evidence")) => Some(
            std::iter::once(program)
                .chain(raw_args[3..].iter().cloned())
                .collect(),
        ),
        (Some("evidence"), _) => Some(
            std::iter::once(program)
                .chain(raw_args[2..].iter().cloned())
                .collect(),
        ),
        _ => None,
    }
}

fn finalize_evidence_args(args: EvidenceCliArgs) -> Result<evidence::EvidenceArgs, String> {
    let crate_root = args
        .crate_root
        .canonicalize()
        .map_err(|err| format!("cannot resolve evidence crate root: {err}"))?;
    let output_dir = match args.output_dir {
        Some(path) if path.is_absolute() => path,
        Some(path) => crate_root.join(path),
        None => crate_root.join(".trust_vc").join("evidence"),
    };
    let use_verus_env_fallback =
        (args.run_verus || args.strict || args.update_verus_tests_manifest)
            && !args.corpus_triage_report
            && !args.scaffold_verus_port_stubs;
    let verus_path = select_verus_path_candidate(args.verus_path, use_verus_env_fallback, |name| {
        std::env::var_os(name)
    })
    .map(resolve_verus_path_candidate)
    .transpose()?;
    let canonical_manifest_path = crate_root
        .join("evals")
        .join("verus")
        .join("verus-tests.json");
    let manifest_path = match args.manifest_path {
        Some(path) => Some(if path.is_absolute() {
            path
        } else {
            crate_root.join(path)
        }),
        None => {
            let seed_manifest = crate_root
                .join("evals")
                .join("verus")
                .join("upstream-verus-corpus.seed.yaml");
            if canonical_manifest_path.exists() {
                Some(canonical_manifest_path.clone())
            } else {
                seed_manifest.exists().then_some(seed_manifest)
            }
        }
    };
    let cargo_command_overridden = args.cargo_command.is_some();
    if args.scaffold_verus_port_stubs {
        let mut incompatible = Vec::new();
        if args.strict {
            incompatible.push("--strict");
        }
        if args.run_trust_vc {
            incompatible.push("--run-trust_vc");
        }
        if args.run_trust_vc_corpus {
            incompatible.push("--run-trust-vc-corpus");
        }
        if args.run_verus {
            incompatible.push("--run-verus");
        }
        if args.port_manifest_only {
            incompatible.push("--port-manifest-only");
        }
        if args.update_verus_tests_manifest {
            incompatible.push("--update-verus-tests-manifest");
        }
        if args.refresh_trust_vc_corpus_evidence {
            incompatible.push("--refresh-trust-vc-corpus-evidence");
        }
        if args.corpus_triage_report {
            incompatible.push("--corpus-triage-report");
        }
        if args.cargo_command.is_some() {
            incompatible.push("--cargo-command");
        }
        if args.trust_vc_corpus_command.is_some() {
            incompatible.push("--trust-vc-corpus-command");
        }
        if args.verus_command.is_some() {
            incompatible.push("--verus-command");
        }
        if !incompatible.is_empty() {
            return Err(format!(
                "--scaffold-verus-port-stubs is a triage write mode and cannot be combined with {}",
                incompatible.join(", ")
            ));
        }
    }
    if args.refresh_trust_vc_corpus_evidence {
        let mut incompatible = Vec::new();
        if !args.run_trust_vc_corpus {
            incompatible.push("missing --run-trust-vc-corpus");
        }
        if args.update_verus_tests_manifest {
            incompatible.push("--update-verus-tests-manifest");
        }
        if args.corpus_triage_report {
            incompatible.push("--corpus-triage-report");
        }
        if args.trust_vc_corpus_command.is_some() {
            incompatible.push("--trust-vc-corpus-command");
        }
        if !incompatible.is_empty() {
            return Err(format!(
                "--refresh-trust-vc-corpus-evidence rewrites manifest evidence pins from a passing corpus run and cannot proceed with {}",
                incompatible.join(", ")
            ));
        }
    }
    let cargo_command = args.cargo_command.unwrap_or_else(default_cargo_command);
    let port_output_dir = match args.port_output_dir {
        Some(path) if path.is_absolute() => path,
        Some(path) => crate_root.join(path),
        None => crate_root.join("evals").join("verus").join("ported"),
    };

    Ok(evidence::EvidenceArgs {
        crate_root,
        output_dir,
        port_output_dir,
        verus_path,
        verus_rev: args.verus_rev,
        manifest_path,
        canonical_manifest_path,
        strict: args.strict,
        json: args.json,
        markdown: args.markdown,
        run_trust_vc: args.run_trust_vc,
        cargo_command,
        cargo_command_overridden,
        run_trust_vc_corpus: args.run_trust_vc_corpus,
        trust_vc_corpus_command: args.trust_vc_corpus_command,
        run_verus: args.run_verus,
        port_manifest_only: args.port_manifest_only,
        update_verus_tests_manifest: args.update_verus_tests_manifest,
        refresh_trust_vc_corpus_evidence: args.refresh_trust_vc_corpus_evidence,
        corpus_triage_report: args.corpus_triage_report,
        scaffold_verus_port_stubs: args.scaffold_verus_port_stubs,
        verus_command: args.verus_command,
    })
}

fn default_cargo_command() -> String {
    select_default_cargo_command(default_cargo_candidates())
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct VerusPathCandidate {
    source: &'static str,
    path: PathBuf,
}

fn select_verus_path_candidate<F>(
    cli_path: Option<PathBuf>,
    use_env_fallback: bool,
    mut env_var: F,
) -> Option<VerusPathCandidate>
where
    F: FnMut(&str) -> Option<OsString>,
{
    if let Some(path) = cli_path {
        return Some(VerusPathCandidate {
            source: "--verus-path",
            path,
        });
    }
    if !use_env_fallback {
        return None;
    }
    [TRUST_VC_VERUS_PATH_ENV, VERUS_PATH_ENV]
        .into_iter()
        .find_map(|name| {
            let value = env_var(name)?;
            if value.as_os_str().is_empty() {
                return None;
            }
            Some(VerusPathCandidate {
                source: name,
                path: PathBuf::from(value),
            })
        })
}

fn resolve_verus_path_candidate(candidate: VerusPathCandidate) -> Result<PathBuf, String> {
    let canonical = candidate
        .path
        .canonicalize()
        .map_err(|err| format!("cannot resolve {}: {err}", candidate.source))?;
    Ok(normalize_verus_checkout_root(canonical))
}

fn normalize_verus_checkout_root(canonical: PathBuf) -> PathBuf {
    if canonical.file_name().and_then(|name| name.to_str()) != Some("source") {
        return canonical;
    }
    let Some(parent) = canonical.parent() else {
        return canonical;
    };
    let looks_like_verus_source = canonical.join("rust_verify_test").is_dir()
        || canonical.join("tools").join("get-z3.sh").is_file();
    let looks_like_verus_root =
        parent.join("tools").join("activate").is_file() || parent.join("source").is_dir();
    if looks_like_verus_source && looks_like_verus_root {
        parent.to_path_buf()
    } else {
        canonical
    }
}

fn default_cargo_candidates() -> Vec<PathBuf> {
    let mut candidates = vec![
        PathBuf::from("/opt/homebrew/bin/cargo"),
        PathBuf::from("/usr/local/bin/cargo"),
        PathBuf::from("/usr/bin/cargo"),
    ];
    if let Some(home) = std::env::var_os("HOME") {
        candidates.push(PathBuf::from(home).join(".cargo").join("bin").join("cargo"));
    }
    candidates
}

fn select_default_cargo_command(candidates: Vec<PathBuf>) -> String {
    candidates
        .iter()
        .find(|path| path.exists())
        .map(|path| path.to_string_lossy().into_owned())
        .unwrap_or_else(|| "cargo".to_string())
}

#[cfg(test)]
fn parse_args_from(raw_args: &[String]) -> Result<CliArgs, String> {
    let args =
        CliArgs::try_parse_from(normalize_raw_args(raw_args)).map_err(|err| err.to_string())?;
    finalize_args(args)
}

fn normalize_raw_args(raw_args: &[String]) -> Vec<String> {
    if raw_args.is_empty() {
        return Vec::new();
    }

    let program = raw_args[0].clone();
    let normalized: Vec<String> = match (
        raw_args.get(1).map(String::as_str),
        raw_args.get(2).map(String::as_str),
    ) {
        (Some("trust_vc" | "trust-vc"), Some("check")) => std::iter::once(program)
            .chain(raw_args[3..].iter().cloned())
            .collect(),
        (Some("trust_vc" | "trust-vc"), _) => std::iter::once(program)
            .chain(raw_args[2..].iter().cloned())
            .collect(),
        (Some("check"), _) => std::iter::once(program)
            .chain(raw_args[2..].iter().cloned())
            .collect(),
        _ => raw_args.to_vec(),
    };

    strip_split_unstable_options_arg(normalized)
}

fn strip_split_unstable_options_arg(args: Vec<String>) -> Vec<String> {
    let mut normalized = Vec::with_capacity(args.len());
    let mut args = args.into_iter();
    if let Some(program) = args.next() {
        normalized.push(program);
    }

    while let Some(arg) = args.next() {
        if arg == "-Z" {
            match args.next() {
                Some(value) if value == "unstable-options" => continue,
                Some(value) => {
                    normalized.push(arg);
                    normalized.push(value);
                }
                None => normalized.push(arg),
            }
        } else {
            normalized.push(arg);
        }
    }

    normalized
}

fn finalize_args(mut args: CliArgs) -> Result<CliArgs, String> {
    args.crate_root = args
        .crate_root
        .canonicalize()
        .map_err(|err| format!("cannot resolve path: {err}"))?;
    Ok(args)
}

fn print_usage() {
    let mut command = CliArgs::command();
    let mut stderr = io::stderr();
    let _ = command.write_long_help(&mut stderr);
    eprintln!();
}

/// True when the discoverable top-level subcommand index should be shown.
///
/// This fires for a bare invocation, for `help`, and for a top-level
/// `--help`/`-h` — but never when a concrete subcommand is selected (so
/// `cargo trust-vc check --help` still shows the check-specific help).
fn wants_top_level_help(raw_args: &[String]) -> bool {
    // Strip the leading `trust_vc`/`trust-vc` cargo prefix, if present, so both
    // `cargo trust-vc ...` and bare `cargo-trust-vc ...` are handled.
    let rest: &[String] = match raw_args.get(1).map(String::as_str) {
        Some("trust_vc" | "trust-vc") => &raw_args[2..],
        _ => &raw_args[1..],
    };
    matches!(
        rest.first().map(String::as_str),
        None | Some("help" | "--help" | "-h")
    )
}

/// Returns true if progress bars should be shown (not in CI, JSON, or quiet mode).
fn show_progress(args: &CliArgs) -> bool {
    !args.ci && !args.json_output && args.verbose < 3
}

/// Creates a progress bar for verification, or a hidden one in CI/JSON mode.
fn make_progress_bar(total: usize, args: &CliArgs) -> ProgressBar {
    if !show_progress(args) {
        return ProgressBar::hidden();
    }
    let pb = ProgressBar::new(total as u64);
    if let Ok(style) = ProgressStyle::with_template(
        "{spinner:.green} [{elapsed_precise}] [{bar:40.cyan/blue}] {pos}/{len} ({eta}) {msg}",
    ) {
        pb.set_style(style.progress_chars("=>-"));
    }
    pb.enable_steady_tick(Duration::from_millis(200));
    pb
}

/// Effective job limit: `--jobs` value, or all available CPUs.
fn effective_jobs(args: &CliArgs) -> usize {
    args.jobs
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(1, |n| n.get()))
}

/// Simple counting semaphore backed by a mutex and condvar.
///
/// Used to limit concurrent verification threads when `--jobs` is specified.
struct JobLimiter {
    state: std::sync::Mutex<usize>,
    available: std::sync::Condvar,
}

impl JobLimiter {
    fn new(permits: usize) -> Self {
        Self {
            state: std::sync::Mutex::new(permits),
            available: std::sync::Condvar::new(),
        }
    }

    /// Blocks until a permit is available, then decrements the counter.
    fn acquire(&self) -> JobPermit<'_> {
        let mut count = self
            .state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        while *count == 0 {
            count = self
                .available
                .wait(count)
                .unwrap_or_else(|poisoned| poisoned.into_inner());
        }
        *count -= 1;
        JobPermit { limiter: self }
    }

    /// Returns a permit, incrementing the counter and waking one waiter.
    fn release(&self) {
        let mut count = self
            .state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        *count += 1;
        self.available.notify_one();
    }
}

struct JobPermit<'a> {
    limiter: &'a JobLimiter,
}

impl Drop for JobPermit<'_> {
    fn drop(&mut self) {
        self.limiter.release();
    }
}

fn verification_thread_panic_verdict(func: &scan::AnnotatedFunction) -> verify::FunctionVerdict {
    verify::FunctionVerdict {
        function: func.clone(),
        result: verify::VerdictKind::Unknown,
        duration_ms: 0,
        detail: Some("verification thread panicked".into()),
        localized_failure: None,
        bindings: Vec::new(),
    }
}

fn verification_thread_panic_detailed(
    func: &scan::AnnotatedFunction,
) -> verify::FunctionVerification {
    verify::FunctionVerification {
        verdict: verification_thread_panic_verdict(func),
        source_hash: None,
        obligations: Vec::new(),
        report: None,
        #[cfg(feature = "proof-certificates")]
        proof_alethe: None,
        #[cfg(feature = "proof-certificates")]
        proof_strict_verified: None,
        warnings: Vec::new(),
    }
}

/// Verify all functions in parallel using one OS thread per function.
///
/// Each function gets an independent `VerificationContext` and `AYEncoder` with
/// no shared state, so parallelism is safe. The ay solver thread limiter
/// (`LIVE_SOLVER_THREADS`) throttles concurrent SMT solving to `num_cores / 2`.
/// Result ordering matches the input function order.
///
/// When `--jobs` is set, the number of concurrent verification threads is
/// capped accordingly. A progress bar with ETA is shown unless `--ci` or
/// `--json` is active.
fn verify_all(
    functions: &[scan::AnnotatedFunction],
    args: &CliArgs,
) -> Vec<verify::FunctionVerdict> {
    if functions.is_empty() {
        return Vec::new();
    }
    let pb = make_progress_bar(functions.len(), args);
    let timeout = args.timeout.map(Duration::from_secs);

    if functions.len() == 1 {
        pb.set_message(functions[0].name.clone());
        let verdict = verify_with_timeout(&functions[0], timeout);
        pb.inc(1);
        pb.finish_and_clear();
        return vec![verdict];
    }

    let limiter = JobLimiter::new(effective_jobs(args));

    let results: Vec<verify::FunctionVerdict> = std::thread::scope(|s| {
        let handles: Vec<_> = functions
            .iter()
            .map(|func| {
                let limiter = &limiter;
                let pb = &pb;
                let handle = s.spawn(move || {
                    let _permit = limiter.acquire();
                    pb.set_message(func.name.clone());
                    let verdict = verify_with_timeout(func, timeout);
                    pb.inc(1);
                    verdict
                });
                (func, handle)
            })
            .collect();
        handles
            .into_iter()
            .map(|(func, h)| {
                h.join()
                    .unwrap_or_else(|_| verification_thread_panic_verdict(func))
            })
            .collect()
    });
    pb.finish_and_clear();
    results
}

/// Verify all functions in parallel, returning full obligation metadata.
fn verify_all_detailed(
    functions: &[scan::AnnotatedFunction],
    args: &CliArgs,
) -> Vec<verify::FunctionVerification> {
    if functions.is_empty() {
        return Vec::new();
    }
    let pb = make_progress_bar(functions.len(), args);
    let timeout = args.timeout.map(Duration::from_secs);

    if functions.len() == 1 {
        pb.set_message(functions[0].name.clone());
        let verification = verify_detailed_with_timeout(&functions[0], timeout);
        pb.inc(1);
        pb.finish_and_clear();
        return vec![verification];
    }

    let limiter = JobLimiter::new(effective_jobs(args));

    let results: Vec<verify::FunctionVerification> = std::thread::scope(|s| {
        let handles: Vec<_> = functions
            .iter()
            .map(|func| {
                let limiter = &limiter;
                let pb = &pb;
                let handle = s.spawn(move || {
                    let _permit = limiter.acquire();
                    pb.set_message(func.name.clone());
                    let verification = verify_detailed_with_timeout(func, timeout);
                    pb.inc(1);
                    verification
                });
                (func, handle)
            })
            .collect();
        handles
            .into_iter()
            .map(|(func, h)| {
                h.join()
                    .unwrap_or_else(|_| verification_thread_panic_detailed(func))
            })
            .collect()
    });
    pb.finish_and_clear();
    results
}

/// Wraps `verify_one` with an optional timeout. If the timeout expires, returns
/// a verdict with `VerdictKind::Unknown` and a timeout detail message.
fn verify_with_timeout(
    func: &scan::AnnotatedFunction,
    timeout: Option<Duration>,
) -> verify::FunctionVerdict {
    let start = Instant::now();
    match timeout {
        Some(limit) => {
            // Run verification on a dedicated thread so we can enforce the wall-clock limit.
            let func_clone = func.clone();
            let handle = std::thread::spawn(move || verify::verify_one(&func_clone));
            loop {
                if handle.is_finished() {
                    return handle
                        .join()
                        .unwrap_or_else(|_| verification_thread_panic_verdict(func));
                }
                if start.elapsed() > limit {
                    // The thread keeps running (we cannot kill it), but we report a timeout.
                    return verify::FunctionVerdict {
                        function: func.clone(),
                        result: verify::VerdictKind::Unknown,
                        duration_ms: u64::try_from(start.elapsed().as_millis()).unwrap_or(u64::MAX),
                        detail: Some(format!("timed out after {}s", start.elapsed().as_secs())),
                        localized_failure: None,
                        bindings: Vec::new(),
                    };
                }
                std::thread::sleep(Duration::from_millis(50));
            }
        }
        None => verify::verify_one(func),
    }
}

/// Wraps `verify_one_detailed` with an optional timeout.
fn verify_detailed_with_timeout(
    func: &scan::AnnotatedFunction,
    timeout: Option<Duration>,
) -> verify::FunctionVerification {
    let start = Instant::now();
    match timeout {
        Some(limit) => {
            let func_clone = func.clone();
            let handle = std::thread::spawn(move || verify::verify_one_detailed(&func_clone));
            loop {
                if handle.is_finished() {
                    return handle
                        .join()
                        .unwrap_or_else(|_| verification_thread_panic_detailed(func));
                }
                if start.elapsed() > limit {
                    return verify::FunctionVerification {
                        verdict: verify::FunctionVerdict {
                            function: func.clone(),
                            result: verify::VerdictKind::Unknown,
                            duration_ms: u64::try_from(start.elapsed().as_millis())
                                .unwrap_or(u64::MAX),
                            detail: Some(format!("timed out after {}s", start.elapsed().as_secs())),
                            localized_failure: None,
                            bindings: Vec::new(),
                        },
                        source_hash: None,
                        obligations: Vec::new(),
                        report: None,
                        #[cfg(feature = "proof-certificates")]
                        proof_alethe: None,
                        #[cfg(feature = "proof-certificates")]
                        proof_strict_verified: None,
                        warnings: Vec::new(),
                    };
                }
                std::thread::sleep(Duration::from_millis(50));
            }
        }
        None => verify::verify_one_detailed(func),
    }
}

/// Collects the set of `.rs` files changed since the last git commit.
///
/// Returns `None` if git is not available or the command fails, so callers
/// can distinguish "no changes" from "git failed."
fn git_changed_rs_files(root: &Path) -> Option<Vec<PathBuf>> {
    let output = std::process::Command::new("git")
        .args([
            "diff",
            "--name-only",
            "HEAD",
            "--diff-filter=ACMR",
            "--",
            "*.rs",
        ])
        .current_dir(root)
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let text = String::from_utf8_lossy(&output.stdout);
    Some(
        text.lines()
            .filter(|line| !line.is_empty())
            .map(|line| root.join(line))
            .collect(),
    )
}

fn print_no_cheating_findings(args: &CliArgs, findings: &[scan::TrustedConstructFinding]) {
    if args.json_output {
        let json_findings: Vec<_> = findings
            .iter()
            .map(|finding| {
                serde_json::json!({
                    "file": display_finding_path(artifact_root(&args.crate_root), &finding.file_path),
                    "line": finding.line,
                    "construct": finding.construct,
                    "detail": finding.detail,
                })
            })
            .collect();
        let payload = serde_json::json!({
            "result": "no_cheating_failed",
            "trusted_constructs": findings.len(),
            "findings": json_findings,
        });
        match serde_json::to_string_pretty(&payload) {
            Ok(json) => println!("{json}"),
            Err(err) => eprintln!("Error: failed to serialize no-cheating findings: {err}"),
        }
        return;
    }

    eprintln!(
        "trust_vc check --no-cheating: rejected {} trusted construct{}",
        findings.len(),
        if findings.len() == 1 { "" } else { "s" },
    );
    for finding in findings {
        eprintln!(
            "  {}:{}: {} ({})",
            display_finding_path(artifact_root(&args.crate_root), &finding.file_path),
            finding.line,
            finding.construct,
            finding.detail,
        );
    }
}

fn display_finding_path(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .display()
        .to_string()
}

/// Discover annotated functions in a verification TARGET.
///
/// A target is either a crate root (its `src/` tree is walked — the long-
/// standing behavior, unchanged) or a single `.rs` file. Both cases delegate to
/// `scan`, which is the only thing that reads Rust source here.
fn scan_target(target: &Path) -> Vec<scan::AnnotatedFunction> {
    if target.is_file() {
        scan::scan_file(target)
    } else {
        scan::scan_crate(target)
    }
}

/// `--no-cheating` counterpart of [`scan_target`].
fn scan_target_trusted_constructs(target: &Path) -> Vec<scan::TrustedConstructFinding> {
    if target.is_file() {
        scan::scan_file_trusted_constructs(target)
    } else {
        scan::scan_crate_trusted_constructs(target)
    }
}

/// Directory that generated artifacts and report-relative paths hang off.
///
/// Identical to the target for a crate root; the containing directory for a
/// single-file target, so `--emit-certificate` / `--emit-hints` / `--watch` /
/// `--diff` write and read a DIRECTORY in both modes and reports print
/// `demo.rs` rather than an empty path.
fn artifact_root(target: &Path) -> &Path {
    if target.is_file() {
        target.parent().unwrap_or(target)
    } else {
        target
    }
}

fn run_verification(args: &CliArgs) -> Result<report::Summary, i32> {
    let start = Instant::now();
    let root = artifact_root(&args.crate_root);
    if args.no_cheating {
        let findings = scan_target_trusted_constructs(&args.crate_root);
        if !findings.is_empty() {
            print_no_cheating_findings(args, &findings);
            return Err(1);
        }
    }

    let mut functions = scan_target(&args.crate_root);
    if functions.is_empty() {
        if args.emit_certificate {
            let cert = certificate::generate_certificate(&[], root);
            if let Err(err) = certificate::write_certificate(&cert, root) {
                eprintln!("Error: failed to write proof certificate: {err}");
                return Err(2);
            }
        }

        if args.json_output {
            report::print_json(&[], root, args.localize);
        } else {
            println!("trust_vc check: 0 functions found");
        }

        return Ok(report::Summary::from_verdicts(&[]));
    }

    // --function: exact function name match
    if let Some(ref name) = args.function_filter {
        functions.retain(|function| function.name == *name);
        if functions.is_empty() {
            eprintln!("Error: no function named '{name}' found with trust_vc attributes");
            return Err(2);
        }
    }

    // --filter: substring match on function name
    if let Some(ref pattern) = args.filter {
        functions.retain(|function| function.name.contains(pattern.as_str()));
        if functions.is_empty() {
            eprintln!("Error: no functions matching filter '{pattern}'");
            return Err(2);
        }
    }

    // --diff: only verify functions in git-changed files
    if args.diff {
        let changed_files = match git_changed_rs_files(root) {
            Some(files) => files,
            None => {
                eprintln!("trust_vc check: --diff requires git, but `git diff` failed");
                return Err(2);
            }
        };
        if changed_files.is_empty() {
            if !args.json_output {
                println!("trust_vc check: no changed .rs files since last commit");
            }
            return Ok(report::Summary::from_verdicts(&[]));
        }
        functions.retain(|function| {
            changed_files.iter().any(|changed| {
                // Canonicalize for robust comparison; fall back to direct comparison.
                match (function.file_path.canonicalize(), changed.canonicalize()) {
                    (Ok(a), Ok(b)) => a == b,
                    _ => function.file_path == *changed,
                }
            })
        });
        if functions.is_empty() {
            if !args.json_output {
                println!("trust_vc check: no annotated functions in changed files");
            }
            return Ok(report::Summary::from_verdicts(&[]));
        }
    }

    if args.verbose >= 1 && !args.json_output {
        eprintln!(
            "trust_vc: verifying {} function{} (jobs: {}, timeout: {})",
            functions.len(),
            if functions.len() == 1 { "" } else { "s" },
            effective_jobs(args),
            args.timeout
                .map_or_else(|| "none".to_string(), |t| format!("{t}s")),
        );
    }
    if args.verbose >= 2 && !args.json_output {
        for func in &functions {
            eprintln!(
                "  {} ({}:{})",
                func.name,
                func.file_path.display(),
                func.line
            );
        }
    }

    let wants_hints = args.emit_hints.is_some() || args.emit_hints_json;
    let use_detailed_verification = args.emit_certificate || args.localize || wants_hints;
    let verifications = if use_detailed_verification {
        verify_all_detailed(&functions, args)
    } else {
        Vec::new()
    };
    let verdicts: Vec<verify::FunctionVerdict> = if use_detailed_verification {
        verifications
            .iter()
            .map(|verification| verification.verdict.clone())
            .collect()
    } else {
        verify_all(&functions, args)
    };

    if args.json_output {
        report::print_json(&verdicts, root, args.localize);
    } else {
        report::print_human(&verdicts, root, args.localize);
    }

    if args.verbose >= 1 && !args.json_output {
        eprintln!(
            "trust_vc: finished in {:.1}s",
            start.elapsed().as_secs_f64()
        );
    }

    if args.emit_certificate {
        let cert = certificate::generate_certificate(&verifications, root);
        match certificate::write_certificate(&cert, root) {
            Ok(path) if !args.json_output => {
                println!("Certificate: {}", path.display());
            }
            Ok(_) => {}
            Err(err) => {
                eprintln!("Error: failed to write proof certificate: {err}");
                return Err(2);
            }
        }
    }

    if wants_hints {
        emit_hints(args, &verifications)?;
    }

    Ok(report::Summary::from_verdicts(&verdicts))
}

/// Extracts proven facts from verification reports and emits optimization hints.
///
/// When `--emit-hints` is passed (with optional `=stdout`), this function:
/// 1. Collects all `VerificationReport`s from detailed verification results
/// 2. Calls `extract_proven_facts` on each report
/// 3. Generates optimization hints via `generate_hints`
/// 4. Emits annotated Rust comments via `emit_hint_annotations`
/// 5. Produces a summary report via `format_report` (or `to_json` for `--emit-hints-json`)
fn emit_hints(args: &CliArgs, verifications: &[verify::FunctionVerification]) -> Result<(), i32> {
    // Collect proven facts from all verification reports.
    let mut all_facts = Vec::new();
    for verification in verifications {
        if let Some(ref report) = verification.report {
            let facts = proven_facts::extract_proven_facts(report);
            all_facts.extend(facts);
        }
    }

    let hints = proven_facts::generate_hints(&all_facts);

    // JSON output mode: emit structured JSON and return.
    if args.emit_hints_json {
        let json = proven_facts::to_json(&all_facts);
        let target = args.emit_hints.as_deref().unwrap_or("file");
        if target == "stdout" {
            println!("{json}");
        } else {
            let output_path = artifact_root(&args.crate_root).join("optimization-hints.json");
            if let Err(err) = std::fs::write(&output_path, &json) {
                eprintln!("Error: failed to write hints JSON: {err}");
                return Err(2);
            }
            if !args.json_output {
                println!("Hints (JSON): {}", output_path.display());
            }
        }
        return Ok(());
    }

    // Human-readable mode: emit annotated source comments + summary report.
    let annotations = proven_facts::emit_hint_annotations(&hints);
    let summary = proven_facts::format_report(&all_facts);

    let target = args.emit_hints.as_deref().unwrap_or("file");
    if target == "stdout" {
        println!("{summary}");
        if !annotations.is_empty() {
            println!("Annotated hints:\n{annotations}");
        }
    } else {
        // Write annotations to <crate_name>.hints.rs
        let root = artifact_root(&args.crate_root);
        let crate_name = root.file_name().and_then(|n| n.to_str()).unwrap_or("crate");
        let output_path = root.join(format!("{crate_name}.hints.rs"));
        let mut content = String::new();
        content.push_str("// Auto-generated optimization hints from trust_vc verification\n");
        content.push_str("// These hints are advisory — review before applying.\n\n");
        let _ = write!(content, "// {}\n\n", summary.replace('\n', "\n// "));
        content.push_str(&annotations);

        if let Err(err) = std::fs::write(&output_path, &content) {
            eprintln!("Error: failed to write hints file: {err}");
            return Err(2);
        }
        if !args.json_output {
            println!("Hints: {}", output_path.display());
        }
    }

    Ok(())
}

fn has_modified_rust_files_since(root: &Path, since: SystemTime) -> io::Result<bool> {
    let entries = std::fs::read_dir(root)?;
    for entry in entries {
        let entry = match entry {
            Ok(entry) => entry,
            Err(_) => continue,
        };
        let path = entry.path();
        let file_type = match entry.file_type() {
            Ok(file_type) => file_type,
            Err(_) => continue,
        };

        if file_type.is_dir() {
            if has_modified_rust_files_since(&path, since)? {
                return Ok(true);
            }
            continue;
        }

        if file_type.is_file() && path.extension().is_some_and(|ext| ext == "rs") {
            let modified = match std::fs::metadata(&path).and_then(|metadata| metadata.modified()) {
                Ok(modified) => modified,
                Err(_) => continue,
            };
            if modified > since {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CargoVerusCompatSubcommand {
    Verify,
    Focus,
    Build,
    Check,
}

impl CargoVerusCompatSubcommand {
    fn parse(value: &str) -> Option<Self> {
        match value {
            "verify" => Some(Self::Verify),
            "focus" => Some(Self::Focus),
            "build" => Some(Self::Build),
            "check" => Some(Self::Check),
            _ => None,
        }
    }

    fn cargo_subcommand(self) -> &'static str {
        match self {
            Self::Verify | Self::Focus | Self::Check => "check",
            Self::Build => "build",
        }
    }

    fn default_forwarding_selector(self) -> VerusArgForwardingSelector {
        match self {
            Self::Verify | Self::Build | Self::Check => VerusArgForwardingSelector::All,
            Self::Focus => VerusArgForwardingSelector::Roots,
        }
    }
}

/// Which verification front end the cargo-verus forwarding path drives.
///
/// `Syn` (default) is the trusted, authoritative source-scanning path. `Driver`
/// additionally runs the nightly rustc-driver bin as a *parallel,
/// non-authoritative* VC producer and emits a driver-vs-syn parity witness. It
/// never changes the pass/fail verdict (syn stays authoritative) and hard-errors
/// if the driver ever reports Verified where syn does not (the unsound
/// direction — a new VC producer must never prove more than the trusted path).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TrustVcFrontend {
    Syn,
    Driver,
}

impl TrustVcFrontend {
    fn parse(value: &str) -> Option<Self> {
        match value {
            "syn" => Some(Self::Syn),
            "driver" => Some(Self::Driver),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VerusArgForwardingSelector {
    All,
    Roots,
    Deps,
}

impl VerusArgForwardingSelector {
    fn parse(value: &str) -> Option<Self> {
        match value {
            "all" => Some(Self::All),
            "roots" => Some(Self::Roots),
            "deps" => Some(Self::Deps),
            _ => None,
        }
    }

    fn accepts_package(
        self,
        package_id: &str,
        packages_to_process: &BTreeSet<String>,
        root_packages: &BTreeSet<String>,
    ) -> bool {
        match self {
            Self::All => packages_to_process.contains(package_id),
            Self::Roots => root_packages.contains(package_id),
            Self::Deps => {
                packages_to_process.contains(package_id) && !root_packages.contains(package_id)
            }
        }
    }
}

#[derive(Debug, Clone)]
struct CargoVerusArgForwardingArgs {
    current_dir: PathBuf,
    subcommand: CargoVerusCompatSubcommand,
    forwarding_selector: VerusArgForwardingSelector,
    frontend: TrustVcFrontend,
    cargo_args: Vec<String>,
    manifest_path: Option<PathBuf>,
    workspace_selected: bool,
    package_selectors: Vec<String>,
    excluded_package_selectors: Vec<String>,
    verus_args: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CargoTrustVcNewKind {
    Bin,
    Lib,
}

#[derive(Debug, Clone)]
struct CargoTrustVcNewArgs {
    current_dir: PathBuf,
    name: String,
    kind: CargoTrustVcNewKind,
}

#[derive(Debug, Clone)]
struct CargoMetadataPackage {
    id: String,
    name: String,
    version: String,
    manifest_path: String,
    verus_verify: bool,
    has_lib_target: bool,
}

#[derive(Debug, Clone)]
struct CargoMetadataGraph {
    packages: BTreeMap<String, CargoMetadataPackage>,
    deps: BTreeMap<String, Vec<String>>,
    workspace_members: BTreeSet<String>,
    workspace_default_members: BTreeSet<String>,
    workspace_root: PathBuf,
}

fn maybe_run_cargo_verus_arg_forwarding(raw_args: &[String]) -> Option<Result<i32, String>> {
    let parsed = match parse_cargo_verus_arg_forwarding_args(raw_args) {
        Some(Ok(args)) => args,
        Some(Err(error)) => return Some(Err(error)),
        None => return None,
    };
    Some(run_cargo_verus_arg_forwarding(parsed))
}

fn maybe_run_cargo_trust_vc_new(raw_args: &[String]) -> Option<Result<i32, String>> {
    let parsed = match parse_cargo_trust_vc_new_args(raw_args) {
        Some(Ok(args)) => args,
        Some(Err(error)) => return Some(Err(error)),
        None => return None,
    };
    Some(run_cargo_trust_vc_new(parsed))
}

fn maybe_run_cargo_rustc_wrapper(raw_args: &[String]) -> Option<Result<i32, String>> {
    if !env_flag(VERUS_DRIVER_VIA_CARGO_ENV) {
        return None;
    }
    let Some(rustc_arg) = raw_args.get(1) else {
        return Some(Err(format!(
            "{VERUS_DRIVER_VIA_CARGO_ENV}=1 requires cargo-trust-vc to be invoked with a rustc path as its first argument"
        )));
    };
    Some(run_cargo_rustc_wrapper(rustc_arg, &raw_args[2..]))
}

fn run_cargo_rustc_wrapper(rustc: &str, rustc_args: &[String]) -> Result<i32, String> {
    if is_cargo_rustc_probe(rustc_args) || is_cargo_build_script_rustc_invocation(rustc_args) {
        return run_rustc_directly(rustc, rustc_args);
    }

    let Some(package_id) = cargo_package_env_id() else {
        return run_rustc_directly(rustc, rustc_args);
    };
    if !env_flag(&format!("{VERUS_DRIVER_VERIFY_ENV_PREFIX}{package_id}")) {
        return run_rustc_directly(rustc, rustc_args);
    }

    let driver_args = cargo_rustc_wrapper_driver_args(&package_id);
    if driver_args.iter().any(|arg| arg == "--no-verify") {
        return run_rustc_directly(rustc, rustc_args);
    }

    let verification_exit = run_trust_vc_rustc_wrapper_verification(&driver_args, rustc_args)?;
    if verification_exit != 0 {
        return Ok(verification_exit);
    }
    let rustc_exit = run_rustc_directly(rustc, rustc_args)?;
    if rustc_exit == 0 {
        export_trust_vc_rustc_wrapper_artifact(rustc_args)?;
    }
    Ok(rustc_exit)
}

fn run_rustc_directly(rustc: &str, rustc_args: &[String]) -> Result<i32, String> {
    let status = process::Command::new(rustc)
        .args(rustc_args)
        .status()
        .map_err(|error| format!("failed to run rustc from cargo-trust-vc wrapper: {error}"))?;
    Ok(status.code().unwrap_or(1))
}

fn run_trust_vc_rustc_wrapper_verification(
    driver_args: &[String],
    rustc_args: &[String],
) -> Result<i32, String> {
    let unsupported = unsupported_trust_vc_rustc_wrapper_driver_args(driver_args);
    if !unsupported.is_empty() {
        return Err(format!(
            "unsupported Verus cargo driver arguments for cargo-trust-vc rustc-wrapper mode: {}; TrustVc does not yet expose a rustc-driver/Verus-argument API for these",
            unsupported.join(", ")
        ));
    }
    let dependency_artifacts = verify_trust_vc_rustc_wrapper_imports(driver_args, rustc_args)?;
    let dependency_facts = serde_json::to_string(&dependency_artifacts).map_err(|error| {
        format!("failed to encode cargo-trust-vc dependency facts for verifier import: {error}")
    })?;
    let crate_root = cargo_manifest_dir_from_env()?;
    // Publish the dependency facts to the in-process verifier via the workspace
    // env choke point's restore-on-drop guard. This is a single-threaded CLI
    // (rustc-wrapper) invocation with no concurrent env writer, so the guard
    // needs no additional lock hold; it stays in place through the parity
    // witness below and restores the previous value when this function returns
    // (also on the `?` early-returns / panic).
    let _dependency_facts_env =
        trust_vc_core::env::ScopedEnvVar::set(TRUST_VC_DEPENDENCY_FACTS_ENV, &dependency_facts);

    let args = CliArgs {
        check: true,
        function_filter: None,
        json_output: false,
        localize: false,
        no_cheating: false,
        emit_certificate: false,
        emit_hints: None,
        emit_hints_json: false,
        verbose: 3,
        timeout: None,
        filter: None,
        jobs: None,
        watch: false,
        diff: false,
        ci: true,
        crate_root,
    };
    let result = run_verification(&args).map_err(|exit_code| {
        format!("cargo-trust-vc rustc-wrapper verification failed before summary generation with exit code {exit_code}")
    });

    // Opt-in, NON-authoritative driver-vs-syn parity witness. The trusted syn
    // path above is authoritative for pass/fail; this additionally runs the
    // nightly rustc-driver bin as a parallel VC producer and compares per
    // function. It is env-gated (frontend=driver AND `TRUST_VC_DRIVER_BIN`
    // present) so the default path is byte-unchanged. Run it while the
    // dependency-facts env is still in place, so the parity re-scan sees the
    // exact same import context as the authoritative run. It hard-errors if the
    // driver reports Verified where syn does not (the unsound direction).
    let parity_result = if result.is_ok() && trust_vc_frontend() == TrustVcFrontend::Driver {
        match std::env::var_os(TRUST_VC_DRIVER_BIN_ENV) {
            Some(driver_bin) if !driver_bin.is_empty() => {
                run_driver_syn_parity_witness(&driver_bin, rustc_args, &args)
            }
            _ => Ok(()),
        }
    } else {
        Ok(())
    };

    // `_dependency_facts_env` (declared above) restores the previous value when
    // this function returns.
    let summary = result?;
    // A parity failure is a driver soundness bug (driver proved more than syn):
    // surface it as a hard error so the run fails.
    parity_result?;
    Ok(if summary.has_failures() { 1 } else { 0 })
}

/// Reads the opt-in frontend selection from the environment. Absent / any value
/// other than `driver` ⇒ the trusted syn path (default).
fn trust_vc_frontend() -> TrustVcFrontend {
    match std::env::var(TRUST_VC_FRONTEND_ENV) {
        Ok(value) if value == "driver" => TrustVcFrontend::Driver,
        _ => TrustVcFrontend::Syn,
    }
}

/// Runs the nightly `trust-vc-driver` bin on the *same* real rustc arg vector,
/// then compares its per-function verdicts against the trusted syn path and
/// emits a distinct parity witness. Returns `Err` iff the driver reported
/// `Verified` for a function where syn did not (the unsound direction).
fn run_driver_syn_parity_witness(
    driver_bin: &std::ffi::OsStr,
    rustc_args: &[String],
    args: &CliArgs,
) -> Result<(), String> {
    let driver_verdicts = run_trust_vc_driver_bin(driver_bin, rustc_args)?;
    let syn_verdicts = collect_syn_function_verdicts(args);
    emit_driver_syn_parity(&driver_verdicts, &syn_verdicts)
}

/// Spawns the prebuilt driver bin with the same rustc argv (argv[0] is ignored
/// by `rustc_driver`, exactly like `rustc`), supplying the bootstrap escape
/// hatch + runtime dylib search path the nightly bin needs, and parses its
/// machine `TRUST_VC_DRIVER_RESULT` records off stdout. Driver rustc diagnostics
/// (stderr) and its fail-closed exit status are intentionally not propagated —
/// only the parsed verdicts and the soundness comparison matter here.
fn run_trust_vc_driver_bin(
    driver_bin: &std::ffi::OsStr,
    rustc_args: &[String],
) -> Result<BTreeMap<String, String>, String> {
    let mut command = process::Command::new(driver_bin);
    command.args(rustc_args);
    command.env("RUSTC_BOOTSTRAP", "1");
    if let Some(dyld) = std::env::var_os(TRUST_VC_DRIVER_DYLD_ENV) {
        if !dyld.is_empty() {
            command.env("DYLD_FALLBACK_LIBRARY_PATH", dyld);
        }
    }
    let output = command.output().map_err(|error| {
        format!(
            "failed to spawn trust-vc-driver bin ({}) for the driver-vs-syn parity witness: {error}",
            driver_bin.to_string_lossy()
        )
    })?;
    Ok(parse_driver_result_lines(&String::from_utf8_lossy(
        &output.stdout,
    )))
}

/// Parses `TRUST_VC_DRIVER_RESULT\t<function>\t<verdict>\t<detail>` records off
/// the driver bin's stdout into a `function -> verdict` map. The trailing
/// `TRUST_VC_DRIVER_SUMMARY` line and any non-record output are ignored.
fn parse_driver_result_lines(stdout: &str) -> BTreeMap<String, String> {
    let mut verdicts = BTreeMap::new();
    for line in stdout.lines() {
        let mut cols = line.split('\t');
        if cols.next() == Some("TRUST_VC_DRIVER_RESULT") {
            if let (Some(function), Some(verdict)) = (cols.next(), cols.next()) {
                verdicts.insert(function.to_string(), verdict.to_string());
            }
        }
    }
    verdicts
}

/// The trusted syn per-function verdicts for the crate, keyed by bare function
/// name (matching the driver's `tcx.item_name`), collapsed to the coarse driver
/// verdict vocabulary so the comparison is apples-to-apples.
fn collect_syn_function_verdicts(args: &CliArgs) -> BTreeMap<String, String> {
    let functions = scan::scan_crate(&args.crate_root);
    verify_all(&functions, args)
        .into_iter()
        .map(|verdict| {
            (
                verdict.function.name.clone(),
                syn_verdict_word(&verdict.result).to_string(),
            )
        })
        .collect()
}

/// Maps a syn `VerdictKind` into the coarse driver verdict vocabulary. Only
/// `Verified` needs exact identity for the soundness check; everything else
/// collapses to a distinct "not verified" word.
fn syn_verdict_word(kind: &verify::VerdictKind) -> &'static str {
    match kind {
        verify::VerdictKind::Verified => "Verified",
        verify::VerdictKind::Counterexample => "Refuted",
        verify::VerdictKind::Unknown => "Unknown",
        verify::VerdictKind::Error => "Error",
        verify::VerdictKind::Skipped => "Skipped",
    }
}

/// One driver-vs-syn parity comparison for a single function.
#[derive(Debug, Clone, PartialEq, Eq)]
struct DriverSynParity {
    function: String,
    driver: String,
    syn: String,
    agree: bool,
    /// True iff the driver claims `Verified` where syn does not — the UNSOUND
    /// direction (the driver, a new VC producer, proving more than the trusted
    /// path). Any such entry fails the run.
    driver_proves_more: bool,
}

/// Compares the driver's verdicts against syn's, one record per driver-reported
/// in-fragment function. `UnsupportedType`/`UnsupportedContract` are fail-closed
/// skips — not credited, not compared. A function the driver verified but syn
/// never even scanned (`Absent`) counts as the driver proving more.
fn compare_driver_syn(
    driver_verdicts: &BTreeMap<String, String>,
    syn_verdicts: &BTreeMap<String, String>,
) -> Vec<DriverSynParity> {
    let mut records = Vec::new();
    for (function, driver) in driver_verdicts {
        if driver == "UnsupportedType" || driver == "UnsupportedContract" {
            continue;
        }
        let syn = syn_verdicts
            .get(function)
            .cloned()
            .unwrap_or_else(|| "Absent".to_string());
        let agree = *driver == syn;
        let driver_proves_more = driver == "Verified" && syn != "Verified";
        records.push(DriverSynParity {
            function: function.clone(),
            driver: driver.clone(),
            syn,
            agree,
            driver_proves_more,
        });
    }
    records
}

/// The soundness gate over a set of parity records: fail iff any record has the
/// driver proving more than syn.
fn driver_syn_parity_soundness_check(records: &[DriverSynParity]) -> Result<(), String> {
    let disagreements: Vec<&DriverSynParity> = records
        .iter()
        .filter(|record| record.driver_proves_more)
        .collect();
    if disagreements.is_empty() {
        return Ok(());
    }
    let detail = disagreements
        .iter()
        .map(|record| format!("{} (driver=Verified, syn={})", record.function, record.syn))
        .collect::<Vec<_>>()
        .join(", ");
    Err(format!(
        "trust-vc-driver reported Verified where the trusted syn path did not for: {detail}. \
         The driver is a new VC producer and must never prove more than syn (soundness) — \
         failing the run. Investigate as a driver soundness bug; this is NOT a manifest flip."
    ))
}

/// Emits the distinct, clearly-tagged driver-vs-syn parity witness to stderr
/// (a NON-authoritative evidence log — never a manifest flip, never a
/// promotion) and applies the soundness gate.
fn emit_driver_syn_parity(
    driver_verdicts: &BTreeMap<String, String>,
    syn_verdicts: &BTreeMap<String, String>,
) -> Result<(), String> {
    let records = compare_driver_syn(driver_verdicts, syn_verdicts);
    for record in &records {
        eprintln!(
            "{DRIVER_SYN_PARITY_TAG}\t{}\tdriver={}\tsyn={}\t{}",
            record.function,
            record.driver,
            record.syn,
            if record.agree { "agree" } else { "differ" },
        );
    }
    let compared = records.len();
    let agree = records.iter().filter(|record| record.agree).count();
    let skipped_unsupported = driver_verdicts.len().saturating_sub(compared);
    eprintln!(
        "{DRIVER_SYN_PARITY_SUMMARY_TAG}\tcompared={compared}\tagree={agree}\tskipped_unsupported={skipped_unsupported}"
    );
    driver_syn_parity_soundness_check(&records)
}

fn unsupported_trust_vc_rustc_wrapper_driver_args(driver_args: &[String]) -> Vec<String> {
    driver_args
        .iter()
        .filter(|arg| !is_supported_trust_vc_rustc_wrapper_driver_arg(arg))
        .cloned()
        .collect()
}

fn is_supported_trust_vc_rustc_wrapper_driver_arg(arg: &str) -> bool {
    matches!(
        arg,
        "--VIA-CARGO"
            | "compile-when-not-primary-package"
            | "compile-when-primary-package"
            | "--expand-errors"
            | "--no-verify"
    ) || cargo_rustc_wrapper_import_dep_arg(arg).is_some()
        || cargo_rustc_wrapper_rlimit_arg(arg).is_some()
}

fn cargo_rustc_wrapper_import_dep_arg(arg: &str) -> Option<&str> {
    let dep = arg.strip_prefix("import-dep-if-present=")?;
    is_valid_cargo_rustc_wrapper_import_dep_name(dep).then_some(dep)
}

fn cargo_rustc_wrapper_rlimit_arg(arg: &str) -> Option<&str> {
    let value = arg.strip_prefix("--rlimit=")?;
    (!value.is_empty() && value.bytes().all(|byte| byte.is_ascii_digit())).then_some(value)
}

fn is_valid_cargo_rustc_wrapper_import_dep_name(dep: &str) -> bool {
    !dep.is_empty()
        && dep
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'-')
}

fn verify_trust_vc_rustc_wrapper_imports(
    driver_args: &[String],
    rustc_args: &[String],
) -> Result<Vec<TrustVcRustcWrapperArtifact>, String> {
    let import_deps: BTreeSet<String> = driver_args
        .iter()
        .filter_map(|arg| cargo_rustc_wrapper_import_dep_arg(arg).map(rust_extern_name_for_dep))
        .collect();
    if import_deps.is_empty() {
        return Ok(Vec::new());
    }

    let mut artifacts = Vec::new();
    for (name, paths) in cargo_rustc_wrapper_externs(rustc_args) {
        if !import_deps.contains(&name) {
            continue;
        }
        let mut found = false;
        for path in paths {
            let artifact_path = trust_vc_rustc_wrapper_artifact_path(&path);
            if artifact_path.exists() {
                artifacts.push(validate_trust_vc_rustc_wrapper_artifact(
                    &artifact_path,
                    &name,
                    &path,
                )?);
                found = true;
                break;
            }
        }
        if !found {
            return Err(format!(
                "could not find cargo-trust-vc dependency artifact for `{name}`; expected a verified sidecar next to a matching --extern path"
            ));
        }
    }
    Ok(artifacts)
}

fn rust_extern_name_for_dep(dep: &str) -> String {
    dep.replace('-', "_")
}

fn cargo_rustc_wrapper_externs(rustc_args: &[String]) -> BTreeMap<String, Vec<PathBuf>> {
    let mut externs: BTreeMap<String, Vec<PathBuf>> = BTreeMap::new();
    let mut index = 0;
    while index < rustc_args.len() {
        let arg = &rustc_args[index];
        let extern_spec = if arg == "--extern" {
            index += 1;
            rustc_args.get(index).map(String::as_str)
        } else {
            arg.strip_prefix("--extern=")
        };

        if let Some((name, path)) = extern_spec.and_then(parse_cargo_rustc_wrapper_extern_spec) {
            externs.entry(name).or_default().push(path);
        }
        index += 1;
    }
    externs
}

fn parse_cargo_rustc_wrapper_extern_spec(spec: &str) -> Option<(String, PathBuf)> {
    let (raw_name, raw_path) = spec.split_once('=')?;
    let name = raw_name.rsplit(':').next().unwrap_or(raw_name);
    if !is_valid_cargo_rustc_wrapper_import_dep_name(name) || raw_path.is_empty() {
        return None;
    }
    Some((name.to_string(), PathBuf::from(raw_path)))
}

fn export_trust_vc_rustc_wrapper_artifact(rustc_args: &[String]) -> Result<(), String> {
    let Some(metadata_path) = cargo_rustc_wrapper_metadata_output_path(rustc_args) else {
        return Ok(());
    };
    let package_name = std::env::var(CARGO_PKG_NAME_ENV)
        .map_err(|_| format!("{CARGO_PKG_NAME_ENV} is required to export dependency metadata"))?;
    let manifest_dir = std::env::var(CARGO_MANIFEST_DIR_ENV).map_err(|_| {
        format!("{CARGO_MANIFEST_DIR_ENV} is required to export dependency metadata")
    })?;
    let manifest_path = PathBuf::from(manifest_dir).join("Cargo.toml");
    if !trust_vc_rustc_wrapper_is_library_target(&manifest_path, &package_name, rustc_args)? {
        return Ok(());
    }
    if !metadata_path.is_file() {
        return Err(format!(
            "rustc metadata output {} was not produced; refusing to write cargo-trust-vc dependency artifact",
            metadata_path.display()
        ));
    }
    let artifact_path = trust_vc_rustc_wrapper_artifact_path(&metadata_path);
    if let Some(parent) = artifact_path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        std::fs::create_dir_all(parent).map_err(|error| {
            format!(
                "failed to create cargo-trust-vc dependency artifact directory {}: {error}",
                parent.display()
            )
        })?;
    }

    let artifact = build_trust_vc_rustc_wrapper_artifact(rustc_args, &metadata_path)?;
    let content = format!(
        "{TRUST_VC_RUSTC_WRAPPER_ARTIFACT_MAGIC}{}\n",
        serde_json::to_string_pretty(&artifact).map_err(|error| {
            format!(
                "failed to encode cargo-trust-vc dependency artifact {}: {error}",
                artifact_path.display()
            )
        })?
    );
    std::fs::write(&artifact_path, content).map_err(|error| {
        format!(
            "failed to write cargo-trust-vc dependency artifact {}: {error}",
            artifact_path.display()
        )
    })
}

fn validate_trust_vc_rustc_wrapper_artifact(
    artifact_path: &Path,
    _expected_extern_name: &str,
    expected_metadata_path: &Path,
) -> Result<TrustVcRustcWrapperArtifact, String> {
    let content = std::fs::read_to_string(artifact_path).map_err(|error| {
        format!(
            "failed to read cargo-trust-vc dependency artifact {}: {error}",
            artifact_path.display()
        )
    })?;
    if !content.starts_with(TRUST_VC_RUSTC_WRAPPER_ARTIFACT_MAGIC) {
        return Err(format!(
            "dependency artifact {} is not a cargo-trust-vc rustc-wrapper artifact",
            artifact_path.display()
        ));
    }
    if !expected_metadata_path.is_file() {
        return Err(format!(
            "dependency artifact {} points at missing rustc metadata output {}",
            artifact_path.display(),
            expected_metadata_path.display()
        ));
    }
    let artifact = parse_trust_vc_rustc_wrapper_artifact(artifact_path, &content)?;
    validate_trust_vc_rustc_wrapper_artifact_schema(artifact_path, &artifact)?;
    let expected_metadata_path = expected_metadata_path.display().to_string();
    if artifact.metadata_path != expected_metadata_path {
        return Err(format!(
            "dependency artifact {} does not match imported metadata path {}",
            artifact_path.display(),
            expected_metadata_path
        ));
    }
    let (metadata_len, metadata_sha256) =
        trust_vc_rustc_wrapper_metadata_digest(Path::new(&expected_metadata_path))?;
    if artifact.metadata_len != metadata_len {
        return Err(format!(
            "dependency artifact {} metadata length mismatch for {}",
            artifact_path.display(),
            expected_metadata_path
        ));
    }
    if artifact.metadata_sha256 != metadata_sha256 {
        return Err(format!(
            "dependency artifact {} metadata hash mismatch for {}",
            artifact_path.display(),
            expected_metadata_path
        ));
    }
    Ok(artifact)
}

fn build_trust_vc_rustc_wrapper_artifact(
    rustc_args: &[String],
    metadata_path: &Path,
) -> Result<TrustVcRustcWrapperArtifact, String> {
    let crate_name = cargo_rustc_wrapper_crate_name(rustc_args).unwrap_or_default();
    let package_name = std::env::var(CARGO_PKG_NAME_ENV)
        .map_err(|_| format!("{CARGO_PKG_NAME_ENV} is required to export dependency metadata"))?;
    let package_version = std::env::var(CARGO_PKG_VERSION_ENV).map_err(|_| {
        format!("{CARGO_PKG_VERSION_ENV} is required to export dependency metadata")
    })?;
    let manifest_dir = std::env::var(CARGO_MANIFEST_DIR_ENV).map_err(|_| {
        format!("{CARGO_MANIFEST_DIR_ENV} is required to export dependency metadata")
    })?;
    let manifest_path = PathBuf::from(manifest_dir).join("Cargo.toml");
    let package_env_id =
        package_env_id_from_manifest_path(&package_name, &package_version, &manifest_path);
    let semantic_export = build_trust_vc_rustc_wrapper_semantic_export(&manifest_path)?;
    let manifest_path = canonical_manifest_path_for_hash(&manifest_path);
    let (metadata_len, metadata_sha256) = trust_vc_rustc_wrapper_metadata_digest(metadata_path)?;
    let (source_path, source_len, source_sha256) =
        if let Some(source_binding) = semantic_export.source_binding {
            (
                Some(source_binding.path),
                Some(source_binding.len),
                Some(source_binding.sha256),
            )
        } else {
            (None, None, None)
        };

    Ok(TrustVcRustcWrapperArtifact {
        schema_version: TRUST_VC_RUSTC_WRAPPER_ARTIFACT_SCHEMA_VERSION,
        artifact_kind: TRUST_VC_RUSTC_WRAPPER_ARTIFACT_KIND.to_string(),
        crate_name,
        package_name,
        package_version,
        package_env_id,
        manifest_path,
        metadata_path: metadata_path.display().to_string(),
        metadata_len,
        metadata_sha256,
        source_path,
        source_len,
        source_sha256,
        semantic_payload: semantic_export.payload,
    })
}

fn build_trust_vc_rustc_wrapper_semantic_export(
    manifest_path: &Path,
) -> Result<TrustVcRustcWrapperSemanticExport, String> {
    let lib_path = trust_vc_rustc_wrapper_lib_path(manifest_path)?;
    if !lib_path.is_file() {
        return Ok(TrustVcRustcWrapperSemanticExport {
            payload: TrustVcRustcWrapperSemanticPayload {
                kind: TRUST_VC_RUSTC_WRAPPER_SEMANTIC_PAYLOAD_KIND.to_string(),
                proof_facts_exported: false,
                concrete_functions: Vec::new(),
            },
            source_binding: None,
        });
    }

    let source = std::fs::read_to_string(&lib_path).map_err(|error| {
        format!(
            "failed to read dependency source {} for semantic artifact export: {error}",
            lib_path.display()
        )
    })?;
    let file = trust_vc_core::parse_file_allow_tracked(&source).map_err(|error| {
        format!(
            "failed to parse dependency source {} for semantic artifact export: {error}",
            lib_path.display()
        )
    })?;
    let source_binding = TrustVcRustcWrapperSourceBinding {
        path: canonical_manifest_path_for_hash(&lib_path),
        len: source.len() as u64,
        sha256: format!("sha256:{}", sha256_hex(source.as_bytes())),
    };
    let facts = collect_trust_vc_rustc_wrapper_concrete_facts(&file.items)?;
    if facts.is_empty() {
        Ok(TrustVcRustcWrapperSemanticExport {
            payload: TrustVcRustcWrapperSemanticPayload {
                kind: TRUST_VC_RUSTC_WRAPPER_SEMANTIC_PAYLOAD_KIND.to_string(),
                proof_facts_exported: false,
                concrete_functions: Vec::new(),
            },
            source_binding: Some(source_binding),
        })
    } else {
        Ok(TrustVcRustcWrapperSemanticExport {
            payload: TrustVcRustcWrapperSemanticPayload {
                kind: TRUST_VC_RUSTC_WRAPPER_SEMANTIC_FACTS_PAYLOAD_KIND.to_string(),
                proof_facts_exported: true,
                concrete_functions: facts,
            },
            source_binding: Some(source_binding),
        })
    }
}

fn trust_vc_rustc_wrapper_lib_path(manifest_path: &Path) -> Result<PathBuf, String> {
    let root = manifest_path.parent().ok_or_else(|| {
        format!(
            "dependency manifest has no parent for semantic artifact export: {}",
            manifest_path.display()
        )
    })?;
    let source = std::fs::read_to_string(manifest_path).map_err(|error| {
        format!(
            "failed to read dependency manifest {} for semantic artifact export: {error}",
            manifest_path.display()
        )
    })?;
    let mut in_lib_table = false;
    for raw_line in source.lines() {
        let line = strip_simple_toml_comment(raw_line).trim().to_string();
        if line.is_empty() {
            continue;
        }
        if let Some(header) = line
            .strip_prefix('[')
            .and_then(|line| line.strip_suffix(']'))
        {
            in_lib_table = header.trim() == "lib";
            continue;
        }
        if in_lib_table {
            if let Some((key, value)) = line.split_once('=') {
                if key.trim() == "path" {
                    if let Some(path) = simple_toml_string_value(value) {
                        return Ok(root.join(path));
                    }
                }
            }
        }
    }
    Ok(root.join("src/lib.rs"))
}

fn trust_vc_rustc_wrapper_is_library_target(
    manifest_path: &Path,
    package_name: &str,
    rustc_args: &[String],
) -> Result<bool, String> {
    let lib_path = trust_vc_rustc_wrapper_lib_path(manifest_path)?;
    if !lib_path.is_file() {
        return Ok(false);
    }
    let Some(crate_name) = cargo_rustc_wrapper_crate_name(rustc_args) else {
        return Ok(false);
    };
    Ok(crate_name == trust_vc_rustc_wrapper_lib_target_name(manifest_path, package_name)?)
}

fn trust_vc_rustc_wrapper_lib_target_name(
    manifest_path: &Path,
    package_name: &str,
) -> Result<String, String> {
    let source = std::fs::read_to_string(manifest_path).map_err(|error| {
        format!(
            "failed to read dependency manifest {} for semantic artifact export: {error}",
            manifest_path.display()
        )
    })?;
    let mut in_lib_table = false;
    for raw_line in source.lines() {
        let line = strip_simple_toml_comment(raw_line).trim().to_string();
        if line.is_empty() {
            continue;
        }
        if let Some(header) = line
            .strip_prefix('[')
            .and_then(|line| line.strip_suffix(']'))
        {
            in_lib_table = header.trim() == "lib";
            continue;
        }
        if in_lib_table {
            if let Some((key, value)) = line.split_once('=') {
                if key.trim() == "name" {
                    if let Some(name) = simple_toml_string_value(value) {
                        return Ok(rust_extern_name_for_dep(&name.to_string_lossy()));
                    }
                }
            }
        }
    }
    Ok(rust_extern_name_for_dep(package_name))
}

fn collect_trust_vc_rustc_wrapper_concrete_facts(
    items: &[syn::Item],
) -> Result<Vec<TrustVcRustcWrapperConcreteFunctionFact>, String> {
    let functions = collect_trust_vc_rustc_wrapper_public_function_map(items);
    let reexports = collect_trust_vc_rustc_wrapper_public_reexports(items);
    let mut facts = Vec::new();
    let mut seen = BTreeSet::new();

    for (exported_name, item_fn) in functions
        .iter()
        .map(|(name, item_fn)| (name.as_str(), *item_fn))
        .chain(reexports.iter().filter_map(|(exported, source)| {
            functions
                .get(source)
                .map(|item_fn| (exported.as_str(), *item_fn))
        }))
    {
        if !seen.insert(exported_name.to_string())
            || has_trust_vc_rustc_wrapper_attr(&item_fn.attrs, "spec")
        {
            continue;
        }
        let Some(contract) =
            trust_vc_rustc_wrapper_contract_fact_from_attrs(exported_name, &item_fn.attrs)?
        else {
            continue;
        };
        if contract.ensures.is_empty() {
            continue;
        }

        let mut params = Vec::new();
        let mut unsupported_signature = false;
        for input in &item_fn.sig.inputs {
            let syn::FnArg::Typed(pat_type) = input else {
                unsupported_signature = true;
                break;
            };
            let syn::Pat::Ident(pat_ident) = &*pat_type.pat else {
                unsupported_signature = true;
                break;
            };
            if matches!(&*pat_type.ty, syn::Type::Reference(_)) {
                unsupported_signature = true;
                break;
            }
            params.push(TrustVcRustcWrapperParamFact {
                name: pat_ident.ident.to_string(),
                ty: pat_type.ty.to_token_stream().to_string(),
            });
        }
        if unsupported_signature {
            continue;
        }
        let return_type = match &item_fn.sig.output {
            syn::ReturnType::Type(_, ty) if !matches!(&**ty, syn::Type::Reference(_)) => {
                ty.to_token_stream().to_string()
            }
            syn::ReturnType::Default => "()".to_string(),
            syn::ReturnType::Type(_, _) => continue,
        };

        facts.push(TrustVcRustcWrapperConcreteFunctionFact {
            name: exported_name.to_string(),
            return_type,
            params,
            return_binding: contract.return_binding,
            requires: contract.requires,
            ensures: contract.ensures,
        });
    }

    facts.sort_by(|left, right| left.name.cmp(&right.name));
    Ok(facts)
}

#[derive(Debug)]
struct TrustVcRustcWrapperContractFact {
    return_binding: String,
    requires: Vec<String>,
    ensures: Vec<String>,
}

struct TrustVcRustcWrapperContractClause {
    name: syn::Ident,
    args: Vec<syn::Expr>,
}

impl syn::parse::Parse for TrustVcRustcWrapperContractClause {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::Result<Self> {
        let name: syn::Ident = input.parse()?;
        let content;
        syn::parenthesized!(content in input);
        let args =
            syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated(&content)?;
        Ok(Self {
            name,
            args: args.into_iter().collect(),
        })
    }
}

fn trust_vc_rustc_wrapper_contract_fact_from_attrs(
    function_name: &str,
    attrs: &[syn::Attribute],
) -> Result<Option<TrustVcRustcWrapperContractFact>, String> {
    let mut contract = TrustVcRustcWrapperContractFact {
        return_binding: "result".to_string(),
        requires: Vec::new(),
        ensures: Vec::new(),
    };
    let mut saw_contract = false;

    for attr in attrs {
        let Some(last) = attr
            .path()
            .segments
            .last()
            .map(|segment| segment.ident.to_string())
        else {
            continue;
        };
        match last.as_str() {
            "requires" => {
                saw_contract = true;
                let expr = attr.parse_args::<syn::Expr>().map_err(|error| {
                    format!("failed to parse `{function_name}` requires for semantic artifact export: {error}")
                })?;
                contract.requires.push(expr.to_token_stream().to_string());
            }
            "ensures" => {
                saw_contract = true;
                let expr = attr.parse_args::<syn::Expr>().map_err(|error| {
                    format!("failed to parse `{function_name}` ensures for semantic artifact export: {error}")
                })?;
                contract.ensures.push(expr.to_token_stream().to_string());
            }
            "returns" => {
                saw_contract = true;
                let expr = attr.parse_args::<syn::Expr>().map_err(|error| {
                    format!("failed to parse `{function_name}` returns for semantic artifact export: {error}")
                })?;
                apply_trust_vc_rustc_wrapper_returns_fact(function_name, expr, &mut contract)?;
            }
            "contract" => {
                saw_contract = true;
                let clauses = attr
                    .parse_args_with(
                        syn::punctuated::Punctuated::<
                            TrustVcRustcWrapperContractClause,
                            syn::Token![,],
                        >::parse_terminated,
                    )
                    .map_err(|error| {
                        format!("failed to parse `{function_name}` contract for semantic artifact export: {error}")
                    })?;
                for clause in clauses {
                    apply_trust_vc_rustc_wrapper_contract_fact_clause(
                        function_name,
                        clause,
                        &mut contract,
                    )?;
                }
            }
            _ => {}
        }
    }

    Ok(saw_contract.then_some(contract))
}

fn apply_trust_vc_rustc_wrapper_contract_fact_clause(
    function_name: &str,
    clause: TrustVcRustcWrapperContractClause,
    contract: &mut TrustVcRustcWrapperContractFact,
) -> Result<(), String> {
    match clause.name.to_string().as_str() {
        "requires" => {
            for expr in clause.args {
                contract.requires.push(expr.to_token_stream().to_string());
            }
        }
        "ensures" => {
            for expr in clause.args {
                contract.ensures.push(expr.to_token_stream().to_string());
            }
        }
        "returns" => {
            if clause.args.len() != 1 {
                return Err(format!(
                    "`{function_name}` returns() clause has unsupported arity for semantic artifact export"
                ));
            }
            let expr = clause.args.into_iter().next().ok_or_else(|| {
                format!("`{function_name}` returns() clause is missing its return expression")
            })?;
            apply_trust_vc_rustc_wrapper_returns_fact(function_name, expr, contract)?;
        }
        _ => {}
    }
    Ok(())
}

fn apply_trust_vc_rustc_wrapper_returns_fact(
    function_name: &str,
    expr: syn::Expr,
    contract: &mut TrustVcRustcWrapperContractFact,
) -> Result<(), String> {
    if let syn::Expr::Path(path) = &expr {
        if path.qself.is_none() {
            if let Some(ident) = path.path.get_ident() {
                contract.return_binding = ident.to_string();
                return Ok(());
            }
        }
    }

    let direct_return = syn::parse_str::<syn::Expr>(&format!(
        "result == ({})",
        expr.to_token_stream()
    ))
    .map_err(|error| {
        format!("failed to build `{function_name}` direct returns fact for semantic artifact export: {error}")
    })?;
    contract
        .ensures
        .push(direct_return.to_token_stream().to_string());
    Ok(())
}

fn collect_trust_vc_rustc_wrapper_public_function_map(
    items: &[syn::Item],
) -> BTreeMap<String, &syn::ItemFn> {
    let mut functions = BTreeMap::new();
    collect_trust_vc_rustc_wrapper_public_function_map_inner(items, "", &mut functions);
    functions
}

fn collect_trust_vc_rustc_wrapper_public_function_map_inner<'a>(
    items: &'a [syn::Item],
    module_path: &str,
    functions: &mut BTreeMap<String, &'a syn::ItemFn>,
) {
    for item in items {
        match item {
            syn::Item::Fn(item_fn) if is_public_syn_vis(&item_fn.vis) => {
                let local_name = qualified_trust_vc_rustc_wrapper_name(
                    module_path,
                    &item_fn.sig.ident.to_string(),
                );
                functions.insert(local_name, item_fn);
            }
            syn::Item::Mod(module) if is_public_syn_vis(&module.vis) => {
                if let Some((_, items)) = &module.content {
                    let path = qualified_trust_vc_rustc_wrapper_name(
                        module_path,
                        &module.ident.to_string(),
                    );
                    collect_trust_vc_rustc_wrapper_public_function_map_inner(
                        items, &path, functions,
                    );
                }
            }
            _ => {}
        }
    }
}

fn collect_trust_vc_rustc_wrapper_public_reexports(
    items: &[syn::Item],
) -> BTreeMap<String, String> {
    let mut reexports = BTreeMap::new();
    collect_trust_vc_rustc_wrapper_public_reexports_inner(items, "", &mut reexports);
    reexports
}

fn collect_trust_vc_rustc_wrapper_public_reexports_inner(
    items: &[syn::Item],
    module_path: &str,
    reexports: &mut BTreeMap<String, String>,
) {
    for item in items {
        match item {
            syn::Item::Use(item_use) if is_public_syn_vis(&item_use.vis) => {
                collect_trust_vc_rustc_wrapper_public_reexport_tree(
                    module_path,
                    &mut Vec::new(),
                    &item_use.tree,
                    reexports,
                );
            }
            syn::Item::Mod(module) if is_public_syn_vis(&module.vis) => {
                if let Some((_, items)) = &module.content {
                    let path = qualified_trust_vc_rustc_wrapper_name(
                        module_path,
                        &module.ident.to_string(),
                    );
                    collect_trust_vc_rustc_wrapper_public_reexports_inner(items, &path, reexports);
                }
            }
            _ => {}
        }
    }
}

fn collect_trust_vc_rustc_wrapper_public_reexport_tree(
    module_path: &str,
    prefix: &mut Vec<String>,
    tree: &syn::UseTree,
    reexports: &mut BTreeMap<String, String>,
) {
    match tree {
        syn::UseTree::Path(path) => {
            prefix.push(path.ident.to_string());
            collect_trust_vc_rustc_wrapper_public_reexport_tree(
                module_path,
                prefix,
                &path.tree,
                reexports,
            );
            prefix.pop();
        }
        syn::UseTree::Name(name) => {
            let exported =
                qualified_trust_vc_rustc_wrapper_name(module_path, &name.ident.to_string());
            if let Some(source) =
                trust_vc_rustc_wrapper_reexport_source(module_path, prefix, &name.ident.to_string())
            {
                reexports.insert(exported, source);
            }
        }
        syn::UseTree::Rename(rename) => {
            let exported =
                qualified_trust_vc_rustc_wrapper_name(module_path, &rename.rename.to_string());
            if let Some(source) = trust_vc_rustc_wrapper_reexport_source(
                module_path,
                prefix,
                &rename.ident.to_string(),
            ) {
                reexports.insert(exported, source);
            }
        }
        syn::UseTree::Group(group) => {
            for tree in &group.items {
                collect_trust_vc_rustc_wrapper_public_reexport_tree(
                    module_path,
                    prefix,
                    tree,
                    reexports,
                );
            }
        }
        syn::UseTree::Glob(_) => {}
    }
}

fn trust_vc_rustc_wrapper_reexport_source(
    module_path: &str,
    prefix: &[String],
    leaf: &str,
) -> Option<String> {
    let mut path = prefix.to_vec();
    path.push(leaf.to_string());
    let crate_absolute = path.first().is_some_and(|segment| segment == "crate");
    if crate_absolute || path.first().is_some_and(|segment| segment == "self") {
        path.remove(0);
    }
    if path.is_empty() || path.iter().any(|segment| segment == "super") {
        return None;
    }
    let local = path.join("::");
    if crate_absolute || module_path.is_empty() {
        Some(local)
    } else {
        Some(qualified_trust_vc_rustc_wrapper_name(module_path, &local))
    }
}

fn has_trust_vc_rustc_wrapper_attr(attrs: &[syn::Attribute], name: &str) -> bool {
    attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == name)
    })
}

fn is_public_syn_vis(vis: &syn::Visibility) -> bool {
    matches!(vis, syn::Visibility::Public(_))
}

fn qualified_trust_vc_rustc_wrapper_name(module_path: &str, local_name: &str) -> String {
    if module_path.is_empty() {
        local_name.to_string()
    } else {
        format!("{module_path}::{local_name}")
    }
}

fn strip_simple_toml_comment(line: &str) -> String {
    let mut out = String::new();
    let mut in_string = false;
    let mut escaped = false;
    for ch in line.chars() {
        if escaped {
            out.push(ch);
            escaped = false;
            continue;
        }
        if in_string && ch == '\\' {
            out.push(ch);
            escaped = true;
            continue;
        }
        if ch == '"' {
            in_string = !in_string;
            out.push(ch);
            continue;
        }
        if ch == '#' && !in_string {
            break;
        }
        out.push(ch);
    }
    out
}

fn simple_toml_string_value(value: &str) -> Option<PathBuf> {
    let after_quote = value.trim_start().strip_prefix('"')?;
    let end = after_quote.find('"')?;
    Some(PathBuf::from(&after_quote[..end]))
}

fn parse_trust_vc_rustc_wrapper_artifact(
    artifact_path: &Path,
    content: &str,
) -> Result<TrustVcRustcWrapperArtifact, String> {
    let body = content
        .strip_prefix(TRUST_VC_RUSTC_WRAPPER_ARTIFACT_MAGIC)
        .expect("artifact magic should already be validated")
        .trim();
    if body.is_empty() {
        return Err(format!(
            "dependency artifact {} is missing structured dependency metadata",
            artifact_path.display()
        ));
    }
    serde_json::from_str(body).map_err(|error| {
        format!(
            "dependency artifact {} does not contain valid structured dependency metadata: {error}",
            artifact_path.display()
        )
    })
}

fn validate_trust_vc_rustc_wrapper_artifact_schema(
    artifact_path: &Path,
    artifact: &TrustVcRustcWrapperArtifact,
) -> Result<(), String> {
    if artifact.schema_version != TRUST_VC_RUSTC_WRAPPER_ARTIFACT_SCHEMA_VERSION {
        return Err(format!(
            "dependency artifact {} uses unsupported schema version {}",
            artifact_path.display(),
            artifact.schema_version
        ));
    }
    if artifact.artifact_kind != TRUST_VC_RUSTC_WRAPPER_ARTIFACT_KIND {
        return Err(format!(
            "dependency artifact {} has unexpected artifact kind `{}`",
            artifact_path.display(),
            artifact.artifact_kind
        ));
    }
    let semantic_payload_is_empty = artifact.semantic_payload.kind
        == TRUST_VC_RUSTC_WRAPPER_SEMANTIC_PAYLOAD_KIND
        && !artifact.semantic_payload.proof_facts_exported
        && artifact.semantic_payload.concrete_functions.is_empty();
    let semantic_payload_has_facts = artifact.semantic_payload.kind
        == TRUST_VC_RUSTC_WRAPPER_SEMANTIC_FACTS_PAYLOAD_KIND
        && artifact.semantic_payload.proof_facts_exported;
    if !semantic_payload_is_empty && !semantic_payload_has_facts {
        return Err(format!(
            "dependency artifact {} claims unsupported semantic dependency payload `{}`",
            artifact_path.display(),
            artifact.semantic_payload.kind
        ));
    }
    if artifact.crate_name.is_empty()
        || artifact.package_name.is_empty()
        || artifact.package_version.is_empty()
        || artifact.package_env_id.is_empty()
        || artifact.manifest_path.is_empty()
        || artifact.metadata_path.is_empty()
        || artifact.metadata_sha256.is_empty()
    {
        return Err(format!(
            "dependency artifact {} has incomplete structured dependency metadata",
            artifact_path.display()
        ));
    }
    let expected_package_env_id = package_env_id_from_manifest_path(
        &artifact.package_name,
        &artifact.package_version,
        Path::new(&artifact.manifest_path),
    );
    if artifact.package_env_id != expected_package_env_id {
        return Err(format!(
            "dependency artifact {} has mismatched package identity metadata",
            artifact_path.display()
        ));
    }
    let expected_crate_name = trust_vc_rustc_wrapper_lib_target_name(
        Path::new(&artifact.manifest_path),
        &artifact.package_name,
    )?;
    if artifact.crate_name != expected_crate_name {
        return Err(format!(
            "dependency artifact {} has mismatched library crate identity metadata",
            artifact_path.display()
        ));
    }
    if semantic_payload_has_facts {
        validate_trust_vc_rustc_wrapper_semantic_facts(artifact_path, artifact)?;
        validate_trust_vc_rustc_wrapper_source_binding(artifact_path, artifact)?;
    }
    Ok(())
}

fn validate_trust_vc_rustc_wrapper_semantic_facts(
    artifact_path: &Path,
    artifact: &TrustVcRustcWrapperArtifact,
) -> Result<(), String> {
    for fact in &artifact.semantic_payload.concrete_functions {
        if fact.name.is_empty()
            || fact.return_type.is_empty()
            || fact.return_binding.is_empty()
            || fact.ensures.is_empty()
            || fact
                .params
                .iter()
                .any(|param| param.name.is_empty() || param.ty.is_empty())
        {
            return Err(format!(
                "dependency artifact {} has incomplete semantic fact metadata",
                artifact_path.display()
            ));
        }
    }
    Ok(())
}

fn validate_trust_vc_rustc_wrapper_source_binding(
    artifact_path: &Path,
    artifact: &TrustVcRustcWrapperArtifact,
) -> Result<(), String> {
    let (Some(source_path), Some(source_len), Some(source_sha256)) = (
        artifact.source_path.as_deref(),
        artifact.source_len,
        artifact.source_sha256.as_deref(),
    ) else {
        return Err(format!(
            "dependency artifact {} semantic facts are missing dependency source binding metadata",
            artifact_path.display()
        ));
    };
    if source_path.is_empty() || source_sha256.is_empty() {
        return Err(format!(
            "dependency artifact {} has incomplete dependency source binding metadata",
            artifact_path.display()
        ));
    }

    let expected_source_path = trust_vc_rustc_wrapper_lib_path(Path::new(&artifact.manifest_path))?;
    let expected_source_path = canonical_manifest_path_for_hash(&expected_source_path);
    if source_path != expected_source_path {
        return Err(format!(
            "dependency artifact {} source path mismatch for {}",
            artifact_path.display(),
            expected_source_path
        ));
    }

    let (actual_source_len, actual_source_sha256) =
        trust_vc_rustc_wrapper_source_digest(Path::new(&expected_source_path))?;
    if source_len != actual_source_len {
        return Err(format!(
            "dependency artifact {} source length mismatch for {}",
            artifact_path.display(),
            expected_source_path
        ));
    }
    if source_sha256 != actual_source_sha256 {
        return Err(format!(
            "dependency artifact {} source hash mismatch for {}",
            artifact_path.display(),
            expected_source_path
        ));
    }
    Ok(())
}

fn trust_vc_rustc_wrapper_metadata_digest(path: &Path) -> Result<(u64, String), String> {
    let bytes = std::fs::read(path).map_err(|error| {
        format!(
            "failed to read rustc metadata output {} for cargo-trust-vc dependency artifact: {error}",
            path.display()
        )
    })?;
    Ok((bytes.len() as u64, format!("sha256:{}", sha256_hex(&bytes))))
}

fn trust_vc_rustc_wrapper_source_digest(path: &Path) -> Result<(u64, String), String> {
    let bytes = std::fs::read(path).map_err(|error| {
        format!(
            "failed to read dependency source {} for cargo-trust-vc dependency artifact: {error}",
            path.display()
        )
    })?;
    Ok((bytes.len() as u64, format!("sha256:{}", sha256_hex(&bytes))))
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut hex = String::with_capacity(digest.len() * 2);
    for byte in digest {
        write!(&mut hex, "{byte:02x}").expect("write to string should succeed");
    }
    hex
}

fn trust_vc_rustc_wrapper_artifact_path(metadata_path: &Path) -> PathBuf {
    metadata_path.with_extension("vir")
}

fn cargo_rustc_wrapper_metadata_output_path(rustc_args: &[String]) -> Option<PathBuf> {
    let mut metadata_emit = false;
    let mut explicit_metadata_path = None;
    let mut out_dir = None;
    let mut output_path = None;
    let mut extra_filename = String::new();
    let mut index = 0;

    while index < rustc_args.len() {
        let arg = &rustc_args[index];
        match arg.as_str() {
            "--emit" => {
                if let Some(value) = rustc_args.get(index + 1) {
                    let (emits_metadata, path) = parse_rustc_emit_metadata(value);
                    metadata_emit |= emits_metadata;
                    explicit_metadata_path = explicit_metadata_path.or(path);
                    index += 1;
                }
            }
            "--out-dir" => {
                if let Some(value) = rustc_args.get(index + 1) {
                    out_dir = Some(PathBuf::from(value));
                    index += 1;
                }
            }
            "-o" => {
                if let Some(value) = rustc_args.get(index + 1) {
                    output_path = Some(PathBuf::from(value));
                    index += 1;
                }
            }
            "-C" => {
                if let Some(value) = rustc_args.get(index + 1) {
                    if let Some(value) = value.strip_prefix("extra-filename=") {
                        extra_filename = value.to_string();
                    }
                    index += 1;
                }
            }
            _ => {
                if let Some(value) = arg.strip_prefix("--emit=") {
                    let (emits_metadata, path) = parse_rustc_emit_metadata(value);
                    metadata_emit |= emits_metadata;
                    explicit_metadata_path = explicit_metadata_path.or(path);
                } else if let Some(value) = arg.strip_prefix("--out-dir=") {
                    out_dir = Some(PathBuf::from(value));
                } else if let Some(value) = arg.strip_prefix("-Cextra-filename=") {
                    extra_filename = value.to_string();
                }
            }
        }
        index += 1;
    }

    if let Some(path) = explicit_metadata_path {
        return Some(path);
    }
    if !metadata_emit {
        return None;
    }
    if let Some(path) = output_path {
        return Some(path);
    }
    let crate_name = cargo_rustc_wrapper_crate_name(rustc_args)?;
    let out_dir = out_dir?;
    Some(out_dir.join(format!("lib{crate_name}{extra_filename}.rmeta")))
}

fn parse_rustc_emit_metadata(value: &str) -> (bool, Option<PathBuf>) {
    let mut metadata_emit = false;
    let mut metadata_path = None;
    for emit in value.split(',') {
        let emit = emit.trim();
        if emit == "metadata" {
            metadata_emit = true;
        } else if let Some(path) = emit.strip_prefix("metadata=") {
            metadata_emit = true;
            if !path.is_empty() {
                metadata_path = Some(PathBuf::from(path));
            }
        }
    }
    (metadata_emit, metadata_path)
}

fn cargo_rustc_wrapper_crate_name(rustc_args: &[String]) -> Option<String> {
    let mut index = 0;
    while index < rustc_args.len() {
        let arg = &rustc_args[index];
        if arg == "--crate-name" {
            return rustc_args.get(index + 1).cloned();
        }
        if let Some(value) = arg.strip_prefix("--crate-name=") {
            return Some(value.to_string());
        }
        index += 1;
    }
    None
}

fn cargo_manifest_dir_from_env() -> Result<PathBuf, String> {
    let manifest_dir = std::env::var(CARGO_MANIFEST_DIR_ENV).map_err(|_| {
        format!(
            "{CARGO_MANIFEST_DIR_ENV} is required for cargo-trust-vc rustc-wrapper verification"
        )
    })?;
    PathBuf::from(manifest_dir)
        .canonicalize()
        .map_err(|error| format!("cannot resolve {CARGO_MANIFEST_DIR_ENV}: {error}"))
}

fn cargo_rustc_wrapper_driver_args(package_id: &str) -> Vec<String> {
    let mut args = Vec::new();
    if let Ok(value) = std::env::var(VERUS_DRIVER_ARGS_ENV) {
        args.extend(unpack_verus_driver_args(&value));
    }
    if let Ok(value) = std::env::var(format!("{VERUS_DRIVER_ARGS_FOR_ENV_PREFIX}{package_id}")) {
        args.extend(unpack_verus_driver_args(&value));
    }
    args
}

fn unpack_verus_driver_args(value: &str) -> Vec<String> {
    value
        .split(VERUS_DRIVER_ARGS_SEP)
        .skip(1)
        .filter(|arg| !arg.is_empty())
        .map(str::to_string)
        .collect()
}

fn env_flag(key: &str) -> bool {
    std::env::var(key).is_ok_and(|value| value == "1")
}

fn is_cargo_rustc_probe(rustc_args: &[String]) -> bool {
    rustc_args
        .windows(2)
        .any(|window| window[0] == "--crate-name" && window[1] == "___")
}

fn is_cargo_build_script_rustc_invocation(rustc_args: &[String]) -> bool {
    let crate_name_is_build_script =
        std::env::var(CARGO_CRATE_NAME_ENV).is_ok_and(|name| name.starts_with("build_script_"));
    crate_name_is_build_script
        && rustc_args.iter().any(|arg| {
            Path::new(arg)
                .file_name()
                .is_some_and(|name| name == "build.rs")
        })
}

fn cargo_package_env_id() -> Option<String> {
    let name = std::env::var(CARGO_PKG_NAME_ENV).ok()?;
    let version = std::env::var(CARGO_PKG_VERSION_ENV).ok()?;
    let manifest_dir = std::env::var(CARGO_MANIFEST_DIR_ENV).ok()?;
    let manifest_path = PathBuf::from(manifest_dir).join("Cargo.toml");
    Some(package_env_id_from_manifest_path(
        &name,
        &version,
        &manifest_path,
    ))
}

fn parse_cargo_trust_vc_new_args(
    raw_args: &[String],
) -> Option<Result<CargoTrustVcNewArgs, String>> {
    let normalized = normalize_cargo_trust_vc_new_raw_args(raw_args)?;
    if normalized.get(1).map(String::as_str) != Some("new") {
        return None;
    }
    let current_dir = match std::env::current_dir() {
        Ok(current_dir) => current_dir,
        Err(error) => return Some(Err(format!("cannot resolve current directory: {error}"))),
    };
    Some(parse_cargo_trust_vc_new_tail(current_dir, &normalized[2..]))
}

fn normalize_cargo_trust_vc_new_raw_args(raw_args: &[String]) -> Option<Vec<String>> {
    if raw_args.is_empty() {
        return None;
    }
    let program = raw_args[0].clone();
    match (
        raw_args.get(1).map(String::as_str),
        raw_args.get(2).map(String::as_str),
    ) {
        (Some("trust_vc" | "trust-vc"), Some("new")) => Some(
            std::iter::once(program)
                .chain(raw_args[2..].iter().cloned())
                .collect(),
        ),
        (Some("new"), _) => Some(raw_args.to_vec()),
        _ => None,
    }
}

fn parse_cargo_trust_vc_new_tail(
    current_dir: PathBuf,
    tail: &[String],
) -> Result<CargoTrustVcNewArgs, String> {
    let mut selected = None;
    let mut index = 0;
    while index < tail.len() {
        let arg = &tail[index];
        match arg.as_str() {
            "--bin" | "-b" => {
                let Some(name) = tail.get(index + 1) else {
                    return Err(format!("{arg} requires a project name"));
                };
                set_cargo_trust_vc_new_selection(&mut selected, CargoTrustVcNewKind::Bin, name)?;
                index += 2;
            }
            "--lib" | "-l" => {
                let Some(name) = tail.get(index + 1) else {
                    return Err(format!("{arg} requires a project name"));
                };
                set_cargo_trust_vc_new_selection(&mut selected, CargoTrustVcNewKind::Lib, name)?;
                index += 2;
            }
            _ if arg.starts_with("--bin=") => {
                let name = arg.strip_prefix("--bin=").expect("checked --bin prefix");
                set_cargo_trust_vc_new_selection(&mut selected, CargoTrustVcNewKind::Bin, name)?;
                index += 1;
            }
            _ if arg.starts_with("--lib=") => {
                let name = arg.strip_prefix("--lib=").expect("checked --lib prefix");
                set_cargo_trust_vc_new_selection(&mut selected, CargoTrustVcNewKind::Lib, name)?;
                index += 1;
            }
            _ => {
                return Err(format!(
                    "unsupported cargo trust_vc new argument `{arg}`; expected --bin <NAME> or --lib <NAME>"
                ));
            }
        }
    }

    let Some((kind, name)) = selected else {
        return Err(
            "cargo trust_vc new requires exactly one of --bin <NAME> or --lib <NAME>".to_string(),
        );
    };

    validate_cargo_trust_vc_new_name(&name)?;
    Ok(CargoTrustVcNewArgs {
        current_dir,
        name,
        kind,
    })
}

fn set_cargo_trust_vc_new_selection(
    selected: &mut Option<(CargoTrustVcNewKind, String)>,
    kind: CargoTrustVcNewKind,
    name: &str,
) -> Result<(), String> {
    if selected.is_some() {
        return Err(
            "cargo trust_vc new accepts exactly one of --bin <NAME> or --lib <NAME>".to_string(),
        );
    }
    *selected = Some((kind, name.to_string()));
    Ok(())
}

fn validate_cargo_trust_vc_new_name(name: &str) -> Result<(), String> {
    if name.is_empty() {
        return Err("cargo trust_vc new project name must not be empty".to_string());
    }
    if name.contains(std::path::MAIN_SEPARATOR)
        || name.contains('/')
        || name.contains('\\')
        || name.contains('"')
        || name.chars().any(char::is_control)
    {
        return Err(format!(
            "unsupported cargo trust_vc new project name `{name}`"
        ));
    }
    Ok(())
}

fn parse_cargo_verus_arg_forwarding_args(
    raw_args: &[String],
) -> Option<Result<CargoVerusArgForwardingArgs, String>> {
    let normalized = normalize_cargo_verus_compat_raw_args(raw_args)?;
    let has_forwarding_selector = normalized
        .iter()
        .any(|arg| arg == "--fwd-verus-args-to" || arg.starts_with("--fwd-verus-args-to="));
    let has_late_verus_args = normalized.iter().any(|arg| arg == "--");
    if normalized.len() < 2 {
        return None;
    }

    let subcommand = CargoVerusCompatSubcommand::parse(&normalized[1])?;
    if !has_forwarding_selector
        && !has_late_verus_args
        && matches!(subcommand, CargoVerusCompatSubcommand::Check)
        && !check_tail_looks_like_cargo_verus_compat(&normalized[2..])
    {
        return None;
    }
    let current_dir = match std::env::current_dir() {
        Ok(current_dir) => current_dir,
        Err(error) => return Some(Err(format!("cannot resolve current directory: {error}"))),
    };
    Some(parse_cargo_verus_arg_forwarding_tail(
        current_dir,
        subcommand,
        &normalized[2..],
    ))
}

fn normalize_cargo_verus_compat_raw_args(raw_args: &[String]) -> Option<Vec<String>> {
    if raw_args.is_empty() {
        return None;
    }
    let program = raw_args[0].clone();
    match (
        raw_args.get(1).map(String::as_str),
        raw_args.get(2).map(String::as_str),
    ) {
        (Some("trust_vc" | "trust-vc"), Some(subcommand))
            if CargoVerusCompatSubcommand::parse(subcommand).is_some() =>
        {
            Some(
                std::iter::once(program)
                    .chain(raw_args[2..].iter().cloned())
                    .collect(),
            )
        }
        (Some(subcommand), _) if CargoVerusCompatSubcommand::parse(subcommand).is_some() => {
            Some(raw_args.to_vec())
        }
        _ => None,
    }
}

fn check_tail_looks_like_cargo_verus_compat(tail: &[String]) -> bool {
    if !tail.first().is_some_and(|arg| arg.starts_with('-')) {
        return false;
    }
    tail.iter().any(|arg| {
        arg == "--release" || arg.starts_with("-Z") || cargo_verus_relevant_arg(arg).is_some()
    })
}

fn parse_cargo_verus_arg_forwarding_tail(
    current_dir: PathBuf,
    subcommand: CargoVerusCompatSubcommand,
    tail: &[String],
) -> Result<CargoVerusArgForwardingArgs, String> {
    let split_at = tail
        .iter()
        .position(|arg| arg == "--")
        .unwrap_or(tail.len());
    let (cargo_tail, verus_tail_with_separator) = tail.split_at(split_at);
    validate_cargo_verus_arg_order(cargo_tail)?;
    let verus_args = if split_at < tail.len() {
        verus_tail_with_separator[1..].to_vec()
    } else {
        Vec::new()
    };

    let mut cargo_args = Vec::new();
    let mut manifest_path = None;
    let mut workspace_selected = false;
    let mut package_selectors = Vec::new();
    let mut excluded_package_selectors = Vec::new();
    let mut forwarding_selector = None;
    let mut frontend = None;
    let mut index = 0;
    while index < cargo_tail.len() {
        let arg = &cargo_tail[index];
        if arg == "--fwd-verus-args-to" {
            let Some(selector) = cargo_tail.get(index + 1) else {
                return Err("--fwd-verus-args-to requires a selector".to_string());
            };
            forwarding_selector = Some(parse_verus_arg_forwarding_selector(selector)?);
            index += 2;
            continue;
        }
        if let Some(selector) = arg.strip_prefix("--fwd-verus-args-to=") {
            forwarding_selector = Some(parse_verus_arg_forwarding_selector(selector)?);
            index += 1;
            continue;
        }
        // `--frontend {syn|driver}` selects the (opt-in) verification front end.
        // It is a cargo-trust-vc concept, never forwarded to cargo.
        if arg == "--frontend" {
            let Some(value) = cargo_tail.get(index + 1) else {
                return Err("--frontend requires a value (syn or driver)".to_string());
            };
            frontend = Some(parse_trust_vc_frontend(value)?);
            index += 2;
            continue;
        }
        if let Some(value) = arg.strip_prefix("--frontend=") {
            frontend = Some(parse_trust_vc_frontend(value)?);
            index += 1;
            continue;
        }

        if arg == "--manifest-path" {
            let Some(path) = cargo_tail.get(index + 1) else {
                return Err(format!("{arg} requires a manifest path"));
            };
            manifest_path = Some(PathBuf::from(path));
            cargo_args.push(arg.clone());
            cargo_args.push(path.clone());
            index += 2;
            continue;
        }
        if let Some(path) = arg.strip_prefix("--manifest-path=") {
            manifest_path = Some(PathBuf::from(path));
            cargo_args.push(arg.clone());
            index += 1;
            continue;
        }
        if arg == "--workspace" || arg == "--all" {
            workspace_selected = true;
            cargo_args.push(arg.clone());
            index += 1;
            continue;
        }
        if arg == "--exclude" {
            let Some(package) = cargo_tail.get(index + 1) else {
                return Err(format!("{arg} requires a package name"));
            };
            excluded_package_selectors.push(package.clone());
            cargo_args.push(arg.clone());
            cargo_args.push(package.clone());
            index += 2;
            continue;
        }
        if let Some(package) = arg.strip_prefix("--exclude=") {
            excluded_package_selectors.push(package.to_string());
            cargo_args.push(arg.clone());
            index += 1;
            continue;
        }
        if arg == "--package" || arg == "-p" {
            let Some(package) = cargo_tail.get(index + 1) else {
                return Err(format!("{arg} requires a package name"));
            };
            package_selectors.push(package.clone());
            cargo_args.push(arg.clone());
            cargo_args.push(package.clone());
            index += 2;
            continue;
        }
        if let Some(package) = arg.strip_prefix("--package=") {
            package_selectors.push(package.to_string());
            cargo_args.push("--package".to_string());
            cargo_args.push(package.to_string());
            index += 1;
            continue;
        }
        if let Some(package) = arg.strip_prefix("-p=") {
            package_selectors.push(package.to_string());
            cargo_args.push(arg.clone());
            index += 1;
            continue;
        }
        if arg.starts_with("-p") && arg.len() > 2 {
            package_selectors.push(arg[2..].to_string());
            cargo_args.push(arg.clone());
            index += 1;
            continue;
        }
        if let Some(features) = arg.strip_prefix("--features=") {
            cargo_args.push("--features".to_string());
            cargo_args.push(features.to_string());
            index += 1;
            continue;
        }

        cargo_args.push(arg.clone());
        index += 1;
    }

    let forwarding_selector =
        forwarding_selector.unwrap_or_else(|| subcommand.default_forwarding_selector());
    let frontend = frontend.unwrap_or(TrustVcFrontend::Syn);

    Ok(CargoVerusArgForwardingArgs {
        current_dir,
        subcommand,
        forwarding_selector,
        frontend,
        cargo_args,
        manifest_path,
        workspace_selected,
        package_selectors,
        excluded_package_selectors,
        verus_args,
    })
}

fn parse_verus_arg_forwarding_selector(
    selector: &str,
) -> Result<VerusArgForwardingSelector, String> {
    VerusArgForwardingSelector::parse(selector).ok_or_else(|| {
        format!(
            "unsupported --fwd-verus-args-to selector `{selector}`; expected all, roots, or deps"
        )
    })
}

fn parse_trust_vc_frontend(value: &str) -> Result<TrustVcFrontend, String> {
    TrustVcFrontend::parse(value)
        .ok_or_else(|| format!("unsupported --frontend selector `{value}`; expected syn or driver"))
}

fn validate_cargo_verus_arg_order(cargo_tail: &[String]) -> Result<(), String> {
    let mut saw_passthrough_arg = false;
    let mut index = 0;
    while index < cargo_tail.len() {
        let arg = &cargo_tail[index];
        if arg.starts_with("-Z") && arg != "-Z" {
            return Err("cargo-verus compatibility requires `-Z <flag>` with a space".to_string());
        }

        let cargo_verus_arg = cargo_verus_relevant_arg(arg.as_str());
        if cargo_verus_arg.is_some() {
            if saw_passthrough_arg {
                return Err(format!(
                    "cargo-verus compatibility option `{arg}` must appear before cargo-only passthrough arguments"
                ));
            }
            index += if cargo_verus_arg == Some(true) && cargo_tail.get(index + 1).is_some() {
                2
            } else {
                1
            };
            continue;
        }

        saw_passthrough_arg = true;
        index += 1;
    }

    Ok(())
}

fn cargo_verus_relevant_arg(arg: &str) -> Option<bool> {
    match arg {
        "--fwd-verus-args-to"
        | "--frontend"
        | "--manifest-path"
        | "--package"
        | "-p"
        | "--exclude"
        | "--features"
        | "-F"
        | "--target"
        | "--target-dir"
        | "--config"
        | "-Z" => Some(true),
        "--workspace"
        | "--all"
        | "--all-features"
        | "--no-default-features"
        | "--frozen"
        | "--locked"
        | "--offline" => Some(false),
        _ if arg.starts_with("--fwd-verus-args-to=")
            || arg.starts_with("--frontend=")
            || arg.starts_with("--manifest-path=")
            || arg.starts_with("--package=")
            || arg.starts_with("-p=")
            || arg.starts_with("--exclude=")
            || arg.starts_with("--features=")
            || arg.starts_with("--target=")
            || arg.starts_with("--target-dir=")
            || arg.starts_with("--config=") =>
        {
            Some(false)
        }
        _ if arg.starts_with("-p") && arg.len() > 2 => Some(false),
        _ if arg.starts_with("-F") && arg.len() > 2 => Some(false),
        _ => None,
    }
}

fn run_cargo_verus_arg_forwarding(args: CargoVerusArgForwardingArgs) -> Result<i32, String> {
    let metadata = load_cargo_metadata(&args.current_dir, &args.cargo_args)?;
    let root_packages = select_root_packages(&metadata, &args)?;
    let packages_to_process = transitive_package_closure(&metadata, &root_packages);
    let env_overrides =
        make_cargo_verus_forwarding_env(&metadata, &packages_to_process, &root_packages, &args)?;

    let mut command = process::Command::new(final_cargo_command());
    command.current_dir(&args.current_dir);
    command.arg(args.subcommand.cargo_subcommand());
    command.args(final_cargo_args(&metadata, &args));
    command.envs(env_overrides.iter());

    let status = command
        .status()
        .map_err(|error| format!("failed to run cargo: {error}"))?;
    Ok(status.code().unwrap_or(1))
}

fn run_cargo_trust_vc_new(args: CargoTrustVcNewArgs) -> Result<i32, String> {
    create_cargo_trust_vc_project(&args)?;
    println!("Created new TrustVc project at {}", args.name);
    Ok(0)
}

fn create_cargo_trust_vc_project(args: &CargoTrustVcNewArgs) -> Result<(), String> {
    let project_dir = args.current_dir.join(&args.name);
    if project_dir.exists() {
        return Err(format!("Directory `{}` already exists", args.name));
    }

    let src_file = match args.kind {
        CargoTrustVcNewKind::Bin => "main.rs",
        CargoTrustVcNewKind::Lib => "lib.rs",
    };
    let src_data = match args.kind {
        CargoTrustVcNewKind::Bin => cargo_trust_vc_new_bin_template(),
        CargoTrustVcNewKind::Lib => cargo_trust_vc_new_lib_template(),
    };

    std::fs::create_dir(&project_dir)
        .map_err(|error| format!("failed to create project directory: {error}"))?;
    let result = (|| {
        std::fs::create_dir(project_dir.join("src"))
            .map_err(|error| format!("failed to create src directory: {error}"))?;
        std::fs::write(project_dir.join(".gitignore"), "/target\n")
            .map_err(|error| format!("failed to write .gitignore: {error}"))?;
        std::fs::write(
            project_dir.join("Cargo.toml"),
            cargo_trust_vc_new_manifest_template(&args.name),
        )
        .map_err(|error| format!("failed to write Cargo.toml: {error}"))?;
        std::fs::write(project_dir.join("src").join(src_file), src_data)
            .map_err(|error| format!("failed to write src/{src_file}: {error}"))?;
        init_cargo_trust_vc_project_git(&project_dir)?;
        Ok(())
    })();

    if result.is_err() {
        std::fs::remove_dir_all(&project_dir).ok();
    }
    result
}

fn cargo_trust_vc_new_manifest_template(name: &str) -> String {
    format!(
        r#"[package]
name = "{name}"
version = "0.1.0"
edition = "2021"

[package.metadata.verus]
verify = true

[dependencies]
trust_vc = {{ package = "trust-vc", version = "1.0" }}
"#
    )
}

fn cargo_trust_vc_new_bin_template() -> &'static str {
    r#"//! Scaffolded TrustVc binary.
//!
//! `increment` carries a `#[trust_vc::contract]` so that
//! `cargo trust-vc check` has a function to verify out of the box.

/// Returns `x + 1`, proven greater than `x` when `x < u32::MAX`.
#[trust_vc::contract(
    requires(x < u32::MAX),
    ensures(ret > x),
    returns(ret),
)]
fn increment(x: u32) -> u32 {
    x + 1
}

fn main() {
    println!("increment(41) = {}", increment(41));
}
"#
}

fn cargo_trust_vc_new_lib_template() -> &'static str {
    r#"//! Scaffolded TrustVc library.
//!
//! `checked_add_one` carries a `#[trust_vc::contract]` so that
//! `cargo trust-vc check` has a function to verify out of the box.

/// Returns `value + 1`, proven greater than `value` when `value < u64::MAX`.
#[trust_vc::contract(
    requires(value < u64::MAX),
    ensures(ret > value),
    returns(ret),
)]
pub fn checked_add_one(value: u64) -> u64 {
    value + 1
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checked_add_one_increments() {
        assert_eq!(checked_add_one(1), 2);
    }
}
"#
}

fn init_cargo_trust_vc_project_git(project_dir: &Path) -> Result<(), String> {
    let status = process::Command::new("git")
        .current_dir(project_dir)
        .arg("init")
        .stdout(process::Stdio::null())
        .status()
        .map_err(|error| format!("failed to run git init: {error}"))?;
    if status.success() {
        Ok(())
    } else {
        Err(format!("git init failed with status {status}"))
    }
}

fn final_cargo_args(
    metadata: &CargoMetadataGraph,
    args: &CargoVerusArgForwardingArgs,
) -> Vec<String> {
    let mut cargo_args = args.cargo_args.clone();
    if matches!(args.subcommand, CargoVerusCompatSubcommand::Focus) {
        let target_dir_args = [
            "--target-dir".to_string(),
            metadata
                .workspace_root
                .join("target")
                .join("verus-partial")
                .to_string_lossy()
                .into_owned(),
        ];
        let insertion_index = cargo_args
            .iter()
            .position(|arg| {
                arg == "--package"
                    || arg == "-p"
                    || arg.starts_with("--package=")
                    || arg.starts_with("-p") && arg.len() > 2
            })
            .unwrap_or(cargo_args.len());
        cargo_args.splice(insertion_index..insertion_index, target_dir_args);
    }
    cargo_args
}

fn load_cargo_metadata(
    current_dir: &Path,
    cargo_args: &[String],
) -> Result<CargoMetadataGraph, String> {
    let output = process::Command::new(metadata_cargo_command())
        .current_dir(current_dir)
        .arg("metadata")
        .arg("--format-version")
        .arg("1")
        .args(metadata_passthrough_args(cargo_args))
        .output()
        .map_err(|error| format!("failed to run cargo metadata: {error}"))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!("cargo metadata failed: {}", stderr.trim()));
    }
    let value: serde_json::Value = serde_json::from_slice(&output.stdout)
        .map_err(|error| format!("invalid cargo metadata JSON: {error}"))?;
    cargo_metadata_graph_from_json(&value)
}

fn metadata_cargo_command() -> String {
    std::env::var(TRUST_VC_METADATA_CARGO_ENV).unwrap_or_else(|_| default_cargo_command())
}

fn final_cargo_command() -> String {
    std::env::var("CARGO").unwrap_or_else(|_| default_cargo_command())
}

fn metadata_passthrough_args(cargo_args: &[String]) -> Vec<String> {
    let mut passthrough = Vec::new();
    let mut index = 0;
    while index < cargo_args.len() {
        let arg = &cargo_args[index];
        match arg.as_str() {
            "--frozen" | "--locked" | "--offline" | "--all-features" | "--no-default-features" => {
                passthrough.push(arg.clone());
                index += 1;
            }
            "--manifest-path" | "--features" | "-F" | "--config" | "-Z" => {
                if let Some(value) = cargo_args.get(index + 1) {
                    passthrough.push(arg.clone());
                    passthrough.push(value.clone());
                    index += 2;
                } else {
                    index += 1;
                }
            }
            "--target" => {
                if let Some(value) = cargo_args.get(index + 1) {
                    passthrough.push("--filter-platform".to_string());
                    passthrough.push(value.clone());
                    index += 2;
                } else {
                    index += 1;
                }
            }
            _ if arg.starts_with("--manifest-path=")
                || arg.starts_with("--features=")
                || arg.starts_with("-F") && arg.len() > 2
                || arg.starts_with("--config=")
                || arg.starts_with("-Z") && arg.len() > 2 =>
            {
                passthrough.push(arg.clone());
                index += 1;
            }
            _ if arg.starts_with("--target=") => {
                let value = arg
                    .strip_prefix("--target=")
                    .expect("checked --target prefix");
                passthrough.push(format!("--filter-platform={value}"));
                index += 1;
            }
            "--package" | "-p" | "--exclude" | "--target-dir" => {
                index += if cargo_args.get(index + 1).is_some() {
                    2
                } else {
                    1
                };
            }
            _ if arg.starts_with("--package=")
                || arg.starts_with("-p")
                || arg.starts_with("--exclude=")
                || arg.starts_with("--target-dir=") =>
            {
                index += 1;
            }
            _ => {
                index += 1;
            }
        }
    }
    passthrough
}

fn cargo_metadata_graph_from_json(value: &serde_json::Value) -> Result<CargoMetadataGraph, String> {
    let packages_array = value
        .get("packages")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "cargo metadata missing packages array".to_string())?;
    let mut packages = BTreeMap::new();
    for package in packages_array {
        let id = json_string(package, "id")?;
        let metadata = package.get("metadata").unwrap_or(&serde_json::Value::Null);
        let verus_verify = metadata
            .get("verus")
            .and_then(|verus| verus.get("verify"))
            .and_then(serde_json::Value::as_bool)
            .unwrap_or(false);
        packages.insert(
            id.clone(),
            CargoMetadataPackage {
                id,
                name: json_string(package, "name")?,
                version: json_string(package, "version")?,
                manifest_path: json_string(package, "manifest_path")?,
                verus_verify,
                has_lib_target: package_has_lib_target(package),
            },
        );
    }

    let mut deps = BTreeMap::new();
    if let Some(nodes) = value
        .get("resolve")
        .and_then(|resolve| resolve.get("nodes"))
        .and_then(serde_json::Value::as_array)
    {
        for node in nodes {
            let id = json_string(node, "id")?;
            let dependencies = node
                .get("dependencies")
                .and_then(serde_json::Value::as_array)
                .map(|deps| {
                    deps.iter()
                        .filter_map(|dep| dep.as_str().map(str::to_string))
                        .collect()
                })
                .unwrap_or_else(Vec::new);
            deps.insert(id, dependencies);
        }
    }

    Ok(CargoMetadataGraph {
        packages,
        deps,
        workspace_members: json_string_set(value, "workspace_members"),
        workspace_default_members: json_string_set(value, "workspace_default_members"),
        workspace_root: PathBuf::from(json_string(value, "workspace_root")?),
    })
}

fn package_has_lib_target(package: &serde_json::Value) -> bool {
    package
        .get("targets")
        .and_then(serde_json::Value::as_array)
        .into_iter()
        .flatten()
        .any(|target| {
            target
                .get("kind")
                .and_then(serde_json::Value::as_array)
                .into_iter()
                .flatten()
                .any(|kind| kind.as_str() == Some("lib"))
        })
}

fn json_string(value: &serde_json::Value, key: &str) -> Result<String, String> {
    value
        .get(key)
        .and_then(serde_json::Value::as_str)
        .map(str::to_string)
        .ok_or_else(|| format!("cargo metadata entry missing string field `{key}`"))
}

fn json_string_set(value: &serde_json::Value, key: &str) -> BTreeSet<String> {
    value
        .get(key)
        .and_then(serde_json::Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(|entry| entry.as_str().map(str::to_string))
        .collect()
}

fn select_root_packages(
    metadata: &CargoMetadataGraph,
    args: &CargoVerusArgForwardingArgs,
) -> Result<BTreeSet<String>, String> {
    let mut root_packages = if !args.package_selectors.is_empty() {
        resolve_package_selectors(metadata, &args.package_selectors)?
    } else if args.workspace_selected {
        if metadata.workspace_members.is_empty() {
            return Err("cargo metadata did not report workspace members".to_string());
        }
        metadata.workspace_members.clone()
    } else if let Some(package_id) = manifest_selected_package(metadata, args)? {
        std::iter::once(package_id).collect()
    } else if !metadata.workspace_default_members.is_empty() {
        metadata.workspace_default_members.clone()
    } else if !metadata.workspace_members.is_empty() {
        metadata.workspace_members.clone()
    } else {
        return Err("cargo metadata did not report workspace members".to_string());
    };

    for package_id in resolve_package_selectors(metadata, &args.excluded_package_selectors)? {
        root_packages.remove(&package_id);
    }
    if root_packages.is_empty() {
        return Err("cargo package selection did not include any packages".to_string());
    }
    Ok(root_packages)
}

fn manifest_selected_package(
    metadata: &CargoMetadataGraph,
    args: &CargoVerusArgForwardingArgs,
) -> Result<Option<String>, String> {
    let Some(manifest_path) = &args.manifest_path else {
        return Ok(None);
    };
    let absolute_manifest_path = if manifest_path.is_absolute() {
        manifest_path.clone()
    } else {
        args.current_dir.join(manifest_path)
    };
    let canonical_manifest_path = absolute_manifest_path
        .canonicalize()
        .map_err(|error| format!("cannot resolve --manifest-path: {error}"))?;

    let mut matches = metadata.packages.values().filter_map(|package| {
        Path::new(&package.manifest_path)
            .canonicalize()
            .ok()
            .filter(|package_manifest| package_manifest == &canonical_manifest_path)
            .map(|_| package.id.clone())
    });
    let selected = matches.next();
    if matches.next().is_some() {
        return Err(format!(
            "--manifest-path `{}` matched multiple cargo metadata packages",
            manifest_path.display()
        ));
    }
    Ok(selected)
}

fn resolve_package_selectors(
    metadata: &CargoMetadataGraph,
    package_selectors: &[String],
) -> Result<BTreeSet<String>, String> {
    let mut packages = BTreeSet::new();
    for selector in package_selectors {
        let matches: Vec<&CargoMetadataPackage> = metadata
            .packages
            .values()
            .filter(|package| package.name == *selector)
            .collect();
        match matches.as_slice() {
            [] => {
                return Err(format!(
                    "package `{selector}` was not found in cargo metadata"
                ))
            }
            [package] => {
                packages.insert(package.id.clone());
            }
            _ => {
                return Err(format!(
                    "package selector `{selector}` is ambiguous; use a unique package name"
                ));
            }
        }
    }
    Ok(packages)
}

fn transitive_package_closure(
    metadata: &CargoMetadataGraph,
    root_packages: &BTreeSet<String>,
) -> BTreeSet<String> {
    let mut seen = BTreeSet::new();
    let mut queue: VecDeque<String> = root_packages.iter().cloned().collect();
    while let Some(package_id) = queue.pop_front() {
        if !seen.insert(package_id.clone()) {
            continue;
        }
        if let Some(deps) = metadata.deps.get(&package_id) {
            for dep in deps {
                if metadata.packages.contains_key(dep) && !seen.contains(dep) {
                    queue.push_back(dep.clone());
                }
            }
        }
    }
    seen
}

fn make_cargo_verus_forwarding_env(
    metadata: &CargoMetadataGraph,
    packages_to_process: &BTreeSet<String>,
    root_packages: &BTreeSet<String>,
    args: &CargoVerusArgForwardingArgs,
) -> Result<BTreeMap<String, String>, String> {
    let mut env_overrides = BTreeMap::new();
    env_overrides.insert(
        RUSTC_WRAPPER_ENV.to_string(),
        std::env::current_exe()
            .map_err(|error| format!("cannot resolve current executable: {error}"))?
            .to_string_lossy()
            .into_owned(),
    );
    env_overrides.insert(VERUS_DRIVER_VIA_CARGO_ENV.to_string(), "1".to_string());
    env_overrides.insert(
        CARGO_DEFAULT_LIB_METADATA_ENV.to_string(),
        "verus".to_string(),
    );
    env_overrides.insert(
        VERUS_DRIVER_ARGS_ENV.to_string(),
        pack_verus_driver_args(["--VIA-CARGO", "compile-when-not-primary-package"].into_iter()),
    );

    // Opt-in `--frontend=driver`: propagate the selection plus the prebuilt
    // nightly driver bin + its runtime dylib path into the per-crate
    // RUSTC_WRAPPER subprocess. The parity path activates only when
    // `TRUST_VC_DRIVER_BIN` is present, so this is a no-op (default behavior)
    // when the driver bin has not been built/exported.
    if matches!(args.frontend, TrustVcFrontend::Driver) {
        env_overrides.insert(TRUST_VC_FRONTEND_ENV.to_string(), "driver".to_string());
        for key in [TRUST_VC_DRIVER_BIN_ENV, TRUST_VC_DRIVER_DYLD_ENV] {
            if let Ok(value) = std::env::var(key) {
                env_overrides.insert(key.to_string(), value);
            }
        }
    }

    for package_id in packages_to_process {
        let Some(package) = metadata.packages.get(package_id) else {
            continue;
        };
        if !package.verus_verify {
            continue;
        }
        let env_package_id = package_env_id(package);
        env_overrides.insert(
            format!("{VERUS_DRIVER_VERIFY_ENV_PREFIX}{env_package_id}"),
            "1".to_string(),
        );
        if args
            .forwarding_selector
            .accepts_package(package_id, packages_to_process, root_packages)
            && !args.verus_args.is_empty()
        {
            env_overrides.insert(
                format!("{VERUS_DRIVER_ARGS_FOR_ENV_PREFIX}{env_package_id}"),
                pack_verus_driver_args(args.verus_args.iter().map(String::as_str)),
            );
        }
        if matches!(args.subcommand, CargoVerusCompatSubcommand::Build) {
            let key = format!("{VERUS_DRIVER_ARGS_FOR_ENV_PREFIX}{env_package_id}");
            let import_deps = cargo_rustc_wrapper_import_deps_for_package(metadata, package_id);
            if !import_deps.is_empty() {
                let mut import_args = vec!["--VIA-CARGO".to_string()];
                import_args.extend(
                    import_deps
                        .into_iter()
                        .map(|dep| format!("import-dep-if-present={dep}")),
                );
                let packed = pack_verus_driver_args(import_args.iter().map(String::as_str));
                env_overrides
                    .entry(key)
                    .and_modify(|value| value.push_str(&packed))
                    .or_insert(packed);
            }
        }
        if matches!(args.subcommand, CargoVerusCompatSubcommand::Focus)
            && packages_to_process.contains(package_id)
            && !root_packages.contains(package_id)
        {
            let key = format!("{VERUS_DRIVER_ARGS_FOR_ENV_PREFIX}{env_package_id}");
            env_overrides
                .entry(key)
                .and_modify(|value| {
                    value.push_str(&pack_verus_driver_args(["--no-verify"].into_iter()))
                })
                .or_insert_with(|| pack_verus_driver_args(["--no-verify"].into_iter()));
        }
    }

    Ok(env_overrides)
}

fn cargo_rustc_wrapper_import_deps_for_package(
    metadata: &CargoMetadataGraph,
    package_id: &str,
) -> BTreeSet<String> {
    let mut deps = BTreeSet::new();
    let Some(package) = metadata.packages.get(package_id) else {
        return deps;
    };

    if package.has_lib_target {
        deps.insert(package.name.clone());
    }

    if let Some(package_deps) = metadata.deps.get(package_id) {
        for dep_id in package_deps {
            let Some(dep) = metadata.packages.get(dep_id) else {
                continue;
            };
            if dep.verus_verify && dep.has_lib_target {
                deps.insert(dep.name.clone());
            }
        }
    }

    deps
}

fn package_env_id(package: &CargoMetadataPackage) -> String {
    package_env_id_from_manifest_path(
        &package.name,
        &package.version,
        Path::new(&package.manifest_path),
    )
}

fn package_env_id_from_manifest_path(name: &str, version: &str, manifest_path: &Path) -> String {
    let manifest_path = canonical_manifest_path_for_hash(manifest_path);
    let digest = Sha256::digest(manifest_path.as_bytes());
    let mut manifest_path_hash = String::with_capacity(12);
    for byte in &digest[..6] {
        write!(&mut manifest_path_hash, "{byte:02x}").expect("write to string should succeed");
    }
    format!("{name}-{version}-{manifest_path_hash}")
}

fn canonical_manifest_path_for_hash(manifest_path: &Path) -> String {
    manifest_path
        .canonicalize()
        .unwrap_or_else(|_| manifest_path.to_path_buf())
        .to_string_lossy()
        .into_owned()
}

fn pack_verus_driver_args<'a>(args: impl Iterator<Item = &'a str>) -> String {
    args.flat_map(|arg| [VERUS_DRIVER_ARGS_SEP, arg]).collect()
}

/// Entry point for the one-word `trust-vc` bin (`src/bin/trust-vc.rs`).
///
/// Returns the process exit code. See [`one_word`] for the translation it does;
/// every verification still runs through [`run_cargo_cli`] below.
pub fn run_one_word_cli(argv: &[String]) -> i32 {
    one_word::run(argv)
}

/// The full `cargo-trust-vc` dispatch, driven by an EXPLICIT argv.
///
/// `cargo-trust-vc`'s `main` passes the process argv; the one-word `trust-vc`
/// bin passes its translated argv (through [`run_cli`]). Exits the process on
/// the paths that always did (subcommands, clap errors, verification failures).
pub fn run_cargo_cli(argv: &[String]) {
    run_cli(argv, None);
}

/// [`run_cargo_cli`] with the check parser's displayed program name overridden.
/// See [`parse_check_args`]; `None` is the unchanged cargo-subcommand spelling.
pub(crate) fn run_cli(argv: &[String], check_bin_name: Option<&'static str>) {
    // Check for evidence and suggest subcommands before standard check arg parsing.
    let raw_args: Vec<String> = argv.to_vec();
    if let Some(result) = maybe_run_cargo_rustc_wrapper(&raw_args) {
        match result {
            Ok(exit_code) => process::exit(exit_code),
            Err(error) => {
                eprintln!("Error: {error}");
                process::exit(2);
            }
        }
    }

    if wants_top_level_help(&raw_args) {
        print!("{}", gate::top_level_help());
        return;
    }

    if let Some(result) = gate::detect_gate_subcommand(&raw_args) {
        match result {
            Ok(args) => match gate::run_gate(&args) {
                Ok(exit_code) => process::exit(exit_code),
                Err(error) => {
                    eprintln!("Error: {error}");
                    process::exit(2);
                }
            },
            Err(error) => {
                eprintln!("Error: {error}");
                process::exit(2);
            }
        }
    }

    if let Some(result) = gate::detect_fuzz_subcommand(&raw_args) {
        match result {
            Ok(args) => match gate::run_fuzz(&args) {
                Ok(exit_code) => process::exit(exit_code),
                Err(error) => {
                    eprintln!("Error: {error}");
                    process::exit(2);
                }
            },
            Err(error) => {
                eprintln!("Error: {error}");
                process::exit(2);
            }
        }
    }

    match parse_evidence_args_from(&raw_args) {
        Ok(Some(args)) => {
            let args = match finalize_evidence_args(args) {
                Ok(args) => args,
                Err(error) => {
                    eprintln!("Error: {error}");
                    process::exit(2);
                }
            };
            if args.corpus_triage_report {
                match evidence::run_corpus_triage_report(&args) {
                    Ok(report) => {
                        if args.markdown && !args.json {
                            println!("{}", report.render_markdown());
                        } else {
                            match serde_json::to_string_pretty(&report) {
                                Ok(json) => println!("{json}"),
                                Err(error) => {
                                    eprintln!(
                                        "Error: failed to serialize corpus triage report: {error}"
                                    );
                                    process::exit(2);
                                }
                            }
                        }
                        return;
                    }
                    Err(error) => {
                        eprintln!("Error: {error}");
                        process::exit(2);
                    }
                }
            }
            if args.scaffold_verus_port_stubs {
                match evidence::run_verus_port_scaffold(&args) {
                    Ok(report) => {
                        if args.markdown && !args.json {
                            println!("{}", report.render_markdown());
                        } else {
                            match serde_json::to_string_pretty(&report) {
                                Ok(json) => println!("{json}"),
                                Err(error) => {
                                    eprintln!(
                                        "Error: failed to serialize Verus port scaffold report: {error}"
                                    );
                                    process::exit(2);
                                }
                            }
                        }
                        return;
                    }
                    Err(error) => {
                        eprintln!("Error: {error}");
                        process::exit(2);
                    }
                }
            }
            match evidence::run_evidence(&args) {
                Ok(report) => {
                    if args.json {
                        match serde_json::to_string_pretty(&report) {
                            Ok(json) => println!("{json}"),
                            Err(error) => {
                                eprintln!("Error: failed to serialize evidence report: {error}");
                                process::exit(2);
                            }
                        }
                    } else if args.markdown {
                        println!("{}", report.render_markdown());
                    }
                    if report.has_blocking_failures() {
                        process::exit(1);
                    }
                    return;
                }
                Err(error) => {
                    eprintln!("Error: {error}");
                    process::exit(2);
                }
            }
        }
        Ok(None) => {}
        Err(error) => error.exit(),
    }

    match suggest::detect_suggest_subcommand(&raw_args) {
        Ok(Some(suggest_args)) => match suggest::run_suggest(&suggest_args) {
            Ok(output) => {
                print!("{output}");
                return;
            }
            Err(error) => {
                eprintln!("Error: {error}");
                process::exit(2);
            }
        },
        Ok(None) => {}
        Err(error) => error.exit(),
    }

    if let Some(result) = maybe_run_cargo_trust_vc_new(&raw_args) {
        match result {
            Ok(exit_code) => process::exit(exit_code),
            Err(error) => {
                eprintln!("Error: {error}");
                process::exit(2);
            }
        }
    }

    if let Some(result) = maybe_run_cargo_verus_arg_forwarding(&raw_args) {
        match result {
            Ok(exit_code) => process::exit(exit_code),
            Err(error) => {
                eprintln!("Error: {error}");
                process::exit(2);
            }
        }
    }

    let args = match parse_check_args(&raw_args, check_bin_name) {
        Ok(args) => args,
        Err(msg) => {
            eprintln!("Error: {msg}");
            print_usage();
            process::exit(2);
        }
    };

    let summary = match run_verification(&args) {
        Ok(summary) => summary,
        Err(exit_code) => process::exit(exit_code),
    };

    if args.watch {
        let mut last_verification_completed_at = SystemTime::now();
        loop {
            std::thread::sleep(Duration::from_secs(2));
            match has_modified_rust_files_since(
                artifact_root(&args.crate_root),
                last_verification_completed_at,
            ) {
                Ok(true) => {
                    println!("[watch] Re-verifying...");
                    if let Err(exit_code) = run_verification(&args) {
                        process::exit(exit_code);
                    }
                    last_verification_completed_at = SystemTime::now();
                }
                Ok(false) => {}
                Err(err) => {
                    eprintln!("Error: failed to watch crate for changes: {err}");
                    process::exit(2);
                }
            }
        }
    }

    if summary.has_failures() {
        process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::{Path, PathBuf};
    use std::sync::{Arc, Barrier};
    use std::time::{SystemTime, UNIX_EPOCH};

    const STRESS_FUNCTION_COUNT: usize = 8;
    const STRESS_CALLER_THREADS: usize = 4;
    const STRESS_ROUNDS_PER_CALLER: usize = 3;

    fn make_temp_crate_root(label: &str) -> PathBuf {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock should be after UNIX_EPOCH")
            .as_nanos();
        std::env::temp_dir().join(format!(
            "cargo_trust_vc_{label}_{}_{}",
            std::process::id(),
            unique
        ))
    }

    #[test]
    fn test_select_default_cargo_command_uses_first_existing_candidate() {
        let root = make_temp_crate_root("default_cargo_first_candidate");
        std::fs::create_dir_all(&root).expect("temp root should exist");
        let missing = root.join("missing").join("cargo");
        let first = root.join("system").join("cargo");
        let second = root.join("home").join(".cargo").join("bin").join("cargo");
        std::fs::create_dir_all(first.parent().expect("first candidate parent"))
            .expect("first candidate parent should exist");
        std::fs::create_dir_all(second.parent().expect("second candidate parent"))
            .expect("second candidate parent should exist");
        std::fs::write(&first, "").expect("first candidate should be writable");
        std::fs::write(&second, "").expect("second candidate should be writable");

        let selected = select_default_cargo_command(vec![missing, first.clone(), second]);

        assert_eq!(selected, first.to_string_lossy());
        std::fs::remove_dir_all(root).ok();
    }

    #[test]
    fn test_select_verus_path_candidate_uses_env_only_when_requested() {
        let selected = select_verus_path_candidate(None, true, |name| {
            (name == TRUST_VC_VERUS_PATH_ENV).then(|| OsString::from("/tmp/verus"))
        })
        .expect("env Verus path should be selected");
        assert_eq!(selected.source, TRUST_VC_VERUS_PATH_ENV);
        assert_eq!(selected.path, PathBuf::from("/tmp/verus"));

        let skipped = select_verus_path_candidate(None, false, |name| {
            (name == TRUST_VC_VERUS_PATH_ENV).then(|| OsString::from("/tmp/verus"))
        });
        assert!(skipped.is_none());

        let cli =
            select_verus_path_candidate(Some(PathBuf::from("/tmp/cli-verus")), true, |name| {
                (name == TRUST_VC_VERUS_PATH_ENV).then(|| OsString::from("/tmp/env-verus"))
            })
            .expect("CLI Verus path should win over env fallback");
        assert_eq!(cli.source, "--verus-path");
        assert_eq!(cli.path, PathBuf::from("/tmp/cli-verus"));
    }

    #[test]
    fn test_normalize_verus_path_accepts_source_subdir() {
        let root = make_temp_crate_root("verus_source_subdir");
        let source = root.join("source");
        std::fs::create_dir_all(source.join("rust_verify_test"))
            .expect("Verus source marker should exist");
        std::fs::create_dir_all(root.join("tools")).expect("Verus tools dir should exist");
        std::fs::write(root.join("tools").join("activate"), "")
            .expect("Verus activate marker should exist");

        let normalized = normalize_verus_checkout_root(
            source
                .canonicalize()
                .expect("source path should canonicalize"),
        );
        assert_eq!(
            normalized,
            root.canonicalize().expect("root path should canonicalize")
        );

        std::fs::remove_dir_all(root).ok();
    }

    #[test]
    fn test_select_default_cargo_command_falls_back_to_cargo() {
        let root = make_temp_crate_root("default_cargo_fallback");
        let selected = select_default_cargo_command(vec![root.join("missing-cargo")]);

        assert_eq!(selected, "cargo");
    }

    fn write_synthetic_crate(root: &Path, function_count: usize) {
        let src_dir = root.join("src");
        std::fs::create_dir_all(&src_dir).expect("synthetic src dir should exist");
        std::fs::write(
            root.join("Cargo.toml"),
            "[package]\nname = \"cargo-trust-vc-stress\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
        )
        .expect("synthetic Cargo.toml should be writable");

        let mut source = String::from("// synthetic crate for cargo-trust-vc stress tests\n\n");
        for index in 0..function_count {
            source.push_str(&format!(
                "#[trust_vc::contract(requires(x > 0), ensures(result == x), returns(result))]\nfn verified_{index}(x: u32) -> u32 {{\n    x\n}}\n\n"
            ));
        }
        std::fs::write(src_dir.join("lib.rs"), source)
            .expect("synthetic lib.rs should be writable");
    }

    fn assert_verified_verdicts(
        functions: &[scan::AnnotatedFunction],
        verdicts: &[verify::FunctionVerdict],
        caller: usize,
        round: usize,
    ) {
        assert_eq!(
            verdicts.len(),
            functions.len(),
            "caller {caller} round {round}: verdict count should match input function count"
        );
        for (expected, verdict) in functions.iter().zip(verdicts.iter()) {
            assert_eq!(
                verdict.function.name, expected.name,
                "caller {caller} round {round}: result ordering changed"
            );
            assert!(
                matches!(verdict.result, verify::VerdictKind::Verified),
                "caller {caller} round {round}: {} should verify, got {:?} ({:?})",
                verdict.function.name,
                verdict.result,
                verdict.detail
            );
        }
    }

    fn assert_verified_detailed(
        functions: &[scan::AnnotatedFunction],
        verifications: &[verify::FunctionVerification],
        caller: usize,
        round: usize,
    ) {
        assert_eq!(
            verifications.len(),
            functions.len(),
            "caller {caller} round {round}: detailed result count should match input function count"
        );
        for (expected, verification) in functions.iter().zip(verifications.iter()) {
            assert_eq!(
                verification.verdict.function.name, expected.name,
                "caller {caller} round {round}: detailed result ordering changed"
            );
            assert!(
                matches!(verification.verdict.result, verify::VerdictKind::Verified),
                "caller {caller} round {round}: {} detailed verification failed with {:?} ({:?})",
                verification.verdict.function.name,
                verification.verdict.result,
                verification.verdict.detail
            );
            assert!(
                !verification.obligations.is_empty(),
                "caller {caller} round {round}: {} should report obligations in certificate mode",
                verification.verdict.function.name
            );
        }
    }

    #[test]
    fn test_parse_args_enables_emit_certificate() {
        let crate_root = std::env::temp_dir().join("cargo_trust_vc_parse_args");
        std::fs::create_dir_all(&crate_root).expect("temp dir should exist");
        let args = vec![
            "cargo".to_string(),
            "trust_vc".to_string(),
            "check".to_string(),
            "--emit-certificate".to_string(),
            "--json".to_string(),
            crate_root.display().to_string(),
        ];

        let parsed = parse_args_from(&args).expect("arguments should parse");

        assert!(parsed.emit_certificate);
        assert!(parsed.json_output);
        assert!(!parsed.check);
        assert!(!parsed.localize);
        assert!(!parsed.no_cheating);
        assert_eq!(parsed.verbose, 0);
        assert_eq!(parsed.timeout, None);
        assert!(parsed.filter.is_none());
        assert_eq!(parsed.jobs, None);
        assert_eq!(
            parsed.crate_root,
            crate_root
                .canonicalize()
                .expect("temp dir path should canonicalize")
        );

        std::fs::remove_dir_all(&parsed.crate_root).ok();
    }

    #[test]
    fn test_parse_args_accepts_localize_flag() {
        let crate_root = std::env::temp_dir().join("cargo_trust_vc_parse_args_localize");
        std::fs::create_dir_all(&crate_root).expect("temp dir should exist");
        let args = vec![
            "cargo-trust-vc".to_string(),
            "check".to_string(),
            "--localize".to_string(),
            crate_root.display().to_string(),
        ];

        let parsed = parse_args_from(&args).expect("arguments should parse");

        assert!(parsed.localize);
        assert!(!parsed.emit_certificate);
        assert!(!parsed.json_output);
        assert!(!parsed.no_cheating);

        std::fs::remove_dir_all(&parsed.crate_root).ok();
    }

    #[test]
    fn test_parse_args_accepts_no_cheating_flag() {
        let crate_root = make_temp_crate_root("parse_args_no_cheating");
        std::fs::create_dir_all(&crate_root).expect("temp dir should exist");
        let args = vec![
            "cargo".to_string(),
            "trust_vc".to_string(),
            "check".to_string(),
            "--no-cheating".to_string(),
            crate_root.display().to_string(),
        ];

        let parsed = parse_args_from(&args).expect("arguments should parse");

        assert!(parsed.no_cheating);
        assert!(!parsed.localize);
        assert!(!parsed.json_output);

        std::fs::remove_dir_all(&parsed.crate_root).ok();
    }

    #[test]
    fn test_parse_evidence_args_accepts_update_verus_tests_manifest() {
        let args = vec![
            "cargo".to_string(),
            "trust_vc".to_string(),
            "evidence".to_string(),
            "--verus-path".to_string(),
            "/tmp/verus".to_string(),
            "--verus-rev".to_string(),
            "abc123".to_string(),
            "--update-verus-tests-manifest".to_string(),
            "--port-manifest-only".to_string(),
        ];

        let parsed = parse_evidence_args_from(&args)
            .expect("evidence args should parse")
            .expect("evidence subcommand should be recognized");

        assert!(parsed.update_verus_tests_manifest);
        assert!(parsed.port_manifest_only);
        assert_eq!(parsed.verus_rev.as_deref(), Some("abc123"));
    }

    #[test]
    fn test_parse_evidence_args_accepts_corpus_triage_report() {
        let args = vec![
            "cargo".to_string(),
            "trust_vc".to_string(),
            "evidence".to_string(),
            "--corpus-triage-report".to_string(),
            "--markdown".to_string(),
        ];

        let parsed = parse_evidence_args_from(&args)
            .expect("evidence args should parse")
            .expect("evidence subcommand should be recognized");

        assert!(parsed.corpus_triage_report);
        assert!(parsed.markdown);
    }

    #[test]
    fn test_parse_evidence_args_accepts_port_scaffold() {
        let args = vec![
            "cargo".to_string(),
            "trust_vc".to_string(),
            "evidence".to_string(),
            "--scaffold-verus-port-stubs".to_string(),
            "--port-output-dir".to_string(),
            "evals/verus/ported".to_string(),
            "--json".to_string(),
        ];

        let parsed = parse_evidence_args_from(&args)
            .expect("evidence args should parse")
            .expect("evidence subcommand should be recognized");

        assert!(parsed.scaffold_verus_port_stubs);
        assert_eq!(
            parsed.port_output_dir.as_deref(),
            Some(Path::new("evals/verus/ported"))
        );
        assert!(parsed.json);
    }

    #[test]
    fn test_finalize_evidence_args_resolves_relative_manifest_under_crate_root() {
        let crate_root =
            std::env::temp_dir().join("cargo_trust_vc_evidence_relative_manifest_root");
        std::fs::create_dir_all(crate_root.join("evals/verus")).expect("temp dir should exist");
        let manifest = PathBuf::from("evals/verus/verus-tests.json");
        let args = EvidenceCliArgs {
            crate_root: crate_root.clone(),
            output_dir: Some(PathBuf::from("reports/evidence")),
            verus_path: None,
            verus_rev: None,
            manifest_path: Some(manifest),
            run_trust_vc: false,
            cargo_command: None,
            run_trust_vc_corpus: false,
            trust_vc_corpus_command: None,
            run_verus: false,
            verus_command: None,
            port_manifest_only: false,
            update_verus_tests_manifest: false,
            refresh_trust_vc_corpus_evidence: false,
            corpus_triage_report: false,
            scaffold_verus_port_stubs: false,
            port_output_dir: None,
            strict: false,
            json: false,
            markdown: false,
        };

        let parsed = finalize_evidence_args(args).expect("evidence args should finalize");

        assert_eq!(
            parsed.manifest_path.as_deref(),
            Some(
                parsed
                    .crate_root
                    .join("evals/verus/verus-tests.json")
                    .as_path()
            )
        );
        assert_eq!(
            parsed.port_output_dir,
            parsed.crate_root.join("evals/verus/ported")
        );
        assert_eq!(
            parsed.output_dir,
            parsed.crate_root.join("reports/evidence")
        );

        std::fs::remove_dir_all(crate_root).ok();
    }

    #[test]
    fn test_parse_evidence_args_accepts_refresh_trust_vc_corpus_evidence() {
        let args = vec![
            "cargo".to_string(),
            "trust_vc".to_string(),
            "evidence".to_string(),
            "--refresh-trust-vc-corpus-evidence".to_string(),
            "--run-trust-vc-corpus".to_string(),
            "--manifest".to_string(),
            "tmp/verus-tests.json".to_string(),
        ];

        let parsed = parse_evidence_args_from(&args)
            .expect("evidence args should parse")
            .expect("evidence subcommand should be recognized");

        assert!(parsed.refresh_trust_vc_corpus_evidence);
        assert!(parsed.run_trust_vc_corpus);
        assert_eq!(
            parsed.manifest_path.as_deref(),
            Some(Path::new("tmp/verus-tests.json"))
        );
    }

    #[test]
    fn test_finalize_evidence_args_rejects_refresh_without_run_trust_vc_corpus() {
        let crate_root =
            std::env::temp_dir().join("cargo_trust_vc_evidence_refresh_requires_corpus");
        std::fs::create_dir_all(crate_root.join("evals/verus")).expect("temp dir should exist");
        let args = vec![
            "cargo".to_string(),
            "trust_vc".to_string(),
            "evidence".to_string(),
            "--refresh-trust-vc-corpus-evidence".to_string(),
            "--manifest".to_string(),
            "evals/verus/verus-tests.json".to_string(),
            crate_root.to_string_lossy().into_owned(),
        ];

        let parsed = parse_evidence_args_from(&args)
            .expect("evidence args should parse")
            .expect("evidence subcommand should be recognized");
        let err = finalize_evidence_args(parsed)
            .expect_err("refresh mode must require a TrustVc corpus run");

        assert!(err.contains("--refresh-trust-vc-corpus-evidence"));
        assert!(err.contains("--run-trust-vc-corpus"));

        std::fs::remove_dir_all(crate_root).ok();
    }

    #[test]
    fn test_finalize_evidence_args_rejects_scaffold_with_replacement_gates() {
        let crate_root = std::env::temp_dir().join("cargo_trust_vc_evidence_scaffold_mode");
        std::fs::create_dir_all(crate_root.join("evals/verus")).expect("temp dir should exist");
        let args = vec![
            "cargo".to_string(),
            "trust_vc".to_string(),
            "evidence".to_string(),
            "--scaffold-verus-port-stubs".to_string(),
            "--strict".to_string(),
            "--run-trust_vc".to_string(),
            crate_root.to_string_lossy().into_owned(),
        ];

        let parsed = parse_evidence_args_from(&args)
            .expect("evidence args should parse")
            .expect("evidence subcommand should be recognized");
        let err = finalize_evidence_args(parsed).expect_err("scaffold mode should reject gates");

        assert!(err.contains("--scaffold-verus-port-stubs"));
        assert!(err.contains("--strict"));
        assert!(err.contains("--run-trust_vc"));

        std::fs::remove_dir_all(crate_root).ok();
    }

    #[test]
    fn test_parse_args_accepts_new_frontend_flags() {
        let crate_root = std::env::temp_dir().join("cargo_trust_vc_parse_args_new_flags");
        std::fs::create_dir_all(&crate_root).expect("temp dir should exist");
        let args = vec![
            "cargo".to_string(),
            "trust_vc".to_string(),
            "check".to_string(),
            "--check".to_string(),
            "--function".to_string(),
            "target_fn".to_string(),
            "--json".to_string(),
            "--emit-certificate".to_string(),
            "-vv".to_string(),
            "--timeout".to_string(),
            "30".to_string(),
            "--filter".to_string(),
            "proof_*".to_string(),
            "-j".to_string(),
            "4".to_string(),
            crate_root.display().to_string(),
        ];

        let parsed = parse_args_from(&args).expect("arguments should parse");

        assert!(parsed.check);
        assert_eq!(parsed.function_filter.as_deref(), Some("target_fn"));
        assert!(parsed.json_output);
        assert!(parsed.emit_certificate);
        assert!(!parsed.no_cheating);
        assert_eq!(parsed.verbose, 2);
        assert_eq!(parsed.timeout, Some(30));
        assert_eq!(parsed.filter.as_deref(), Some("proof_*"));
        assert_eq!(parsed.jobs, Some(4));
        assert_eq!(
            parsed.crate_root,
            crate_root
                .canonicalize()
                .expect("temp dir path should canonicalize")
        );

        std::fs::remove_dir_all(&parsed.crate_root).ok();
    }

    #[test]
    fn test_parse_args_accepts_watch_flag() {
        let crate_root = std::env::temp_dir().join("cargo_trust_vc_parse_args_watch");
        std::fs::create_dir_all(&crate_root).expect("temp dir should exist");
        let args = vec![
            "cargo".to_string(),
            "trust_vc".to_string(),
            "check".to_string(),
            "--watch".to_string(),
            crate_root.display().to_string(),
        ];

        let parsed = parse_args_from(&args).expect("arguments should parse");

        assert!(parsed.watch);
        assert_eq!(
            parsed.crate_root,
            crate_root
                .canonicalize()
                .expect("temp dir path should canonicalize")
        );

        std::fs::remove_dir_all(&parsed.crate_root).ok();
    }

    #[test]
    fn test_has_modified_rust_files_since_detects_recursive_rust_files() {
        let crate_root = make_temp_crate_root("watch_detects_rust_files");
        let nested_dir = crate_root.join("src/nested");
        std::fs::create_dir_all(&nested_dir).expect("nested dir should exist");
        std::fs::write(nested_dir.join("mod.rs"), "fn watched() {}\n")
            .expect("rust file should be writable");

        assert!(
            has_modified_rust_files_since(&crate_root, UNIX_EPOCH)
                .expect("watch scan should succeed"),
            "recursive .rs files should be detected"
        );

        std::fs::remove_dir_all(&crate_root).ok();
    }

    #[test]
    fn test_has_modified_rust_files_since_ignores_non_rust_files() {
        let crate_root = make_temp_crate_root("watch_ignores_non_rust");
        std::fs::create_dir_all(&crate_root).expect("crate root should exist");
        std::fs::write(crate_root.join("README.md"), "# not rust\n")
            .expect("markdown file should be writable");

        assert!(
            !has_modified_rust_files_since(&crate_root, UNIX_EPOCH)
                .expect("watch scan should succeed"),
            "non-.rs files should not trigger re-verification"
        );

        std::fs::remove_dir_all(&crate_root).ok();
    }

    /// Creates a minimal `CliArgs` for test use with CI mode (no progress bars).
    fn test_cli_args(crate_root: PathBuf) -> CliArgs {
        CliArgs {
            check: false,
            function_filter: None,
            json_output: false,
            localize: false,
            no_cheating: false,
            emit_certificate: false,
            emit_hints: None,
            emit_hints_json: false,
            verbose: 0,
            timeout: None,
            filter: None,
            jobs: None,
            watch: false,
            diff: false,
            ci: true,
            crate_root,
        }
    }

    #[test]
    fn test_parallel_verify_paths_stay_correct_under_concurrent_callers() {
        let crate_root = make_temp_crate_root("parallel_verify_stress");
        write_synthetic_crate(&crate_root, STRESS_FUNCTION_COUNT);

        let functions = scan::scan_crate(&crate_root);
        assert_eq!(
            functions.len(),
            STRESS_FUNCTION_COUNT,
            "synthetic crate should expose all annotated functions"
        );

        let barrier = Arc::new(Barrier::new(STRESS_CALLER_THREADS));
        let mut handles = Vec::with_capacity(STRESS_CALLER_THREADS);
        for caller in 0..STRESS_CALLER_THREADS {
            let barrier = Arc::clone(&barrier);
            let functions = functions.clone();
            let args = test_cli_args(crate_root.clone());
            handles.push(std::thread::spawn(move || {
                barrier.wait();
                for round in 0..STRESS_ROUNDS_PER_CALLER {
                    let verdicts = verify_all(&functions, &args);
                    assert_verified_verdicts(&functions, &verdicts, caller, round);

                    let detailed = verify_all_detailed(&functions, &args);
                    assert_verified_detailed(&functions, &detailed, caller, round);
                }
            }));
        }

        for handle in handles {
            handle
                .join()
                .expect("parallel cargo-trust-vc stress caller should not panic");
        }

        std::fs::remove_dir_all(&crate_root).ok();
    }

    // -- diff and ci flag parsing tests --

    #[test]
    fn test_parse_args_accepts_diff_flag() {
        let crate_root = std::env::temp_dir().join("cargo_trust_vc_parse_args_diff");
        std::fs::create_dir_all(&crate_root).expect("temp dir should exist");
        let args = vec![
            "cargo".to_string(),
            "trust_vc".to_string(),
            "check".to_string(),
            "--diff".to_string(),
            crate_root.display().to_string(),
        ];

        let parsed = parse_args_from(&args).expect("arguments should parse");

        assert!(parsed.diff);
        assert!(!parsed.ci);

        std::fs::remove_dir_all(&parsed.crate_root).ok();
    }

    #[test]
    fn test_parse_args_accepts_ci_flag() {
        let crate_root = std::env::temp_dir().join("cargo_trust_vc_parse_args_ci");
        std::fs::create_dir_all(&crate_root).expect("temp dir should exist");
        let args = vec![
            "cargo".to_string(),
            "trust_vc".to_string(),
            "check".to_string(),
            "--ci".to_string(),
            crate_root.display().to_string(),
        ];

        let parsed = parse_args_from(&args).expect("arguments should parse");

        assert!(parsed.ci);
        assert!(!parsed.diff);

        std::fs::remove_dir_all(&parsed.crate_root).ok();
    }

    #[test]
    fn test_parse_args_accepts_combined_diff_ci_filter_flags() {
        let crate_root = std::env::temp_dir().join("cargo_trust_vc_parse_combo_flags");
        std::fs::create_dir_all(&crate_root).expect("temp dir should exist");
        let args = vec![
            "cargo".to_string(),
            "trust_vc".to_string(),
            "check".to_string(),
            "--diff".to_string(),
            "--ci".to_string(),
            "--filter".to_string(),
            "prove_".to_string(),
            "-j".to_string(),
            "2".to_string(),
            "--timeout".to_string(),
            "60".to_string(),
            crate_root.display().to_string(),
        ];

        let parsed = parse_args_from(&args).expect("arguments should parse");

        assert!(parsed.diff);
        assert!(parsed.ci);
        assert_eq!(parsed.filter.as_deref(), Some("prove_"));
        assert_eq!(parsed.jobs, Some(2));
        assert_eq!(parsed.timeout, Some(60));

        std::fs::remove_dir_all(&parsed.crate_root).ok();
    }

    // -- emit-hints flag parsing tests --

    #[test]
    fn test_parse_args_accepts_emit_hints_flag_without_value() {
        let crate_root = std::env::temp_dir().join("cargo_trust_vc_parse_emit_hints_no_val");
        std::fs::create_dir_all(&crate_root).expect("temp dir should exist");
        let args = vec![
            "cargo".to_string(),
            "trust_vc".to_string(),
            "check".to_string(),
            "--emit-hints".to_string(),
            crate_root.display().to_string(),
        ];

        let parsed = parse_args_from(&args).expect("arguments should parse");

        assert_eq!(
            parsed.emit_hints.as_deref(),
            Some("file"),
            "--emit-hints without value should default to 'file'"
        );
        assert!(!parsed.emit_hints_json);

        std::fs::remove_dir_all(&parsed.crate_root).ok();
    }

    #[test]
    fn test_parse_args_accepts_emit_hints_stdout() {
        let crate_root = std::env::temp_dir().join("cargo_trust_vc_parse_emit_hints_stdout");
        std::fs::create_dir_all(&crate_root).expect("temp dir should exist");
        let args = vec![
            "cargo".to_string(),
            "trust_vc".to_string(),
            "check".to_string(),
            "--emit-hints=stdout".to_string(),
            crate_root.display().to_string(),
        ];

        let parsed = parse_args_from(&args).expect("arguments should parse");

        assert_eq!(
            parsed.emit_hints.as_deref(),
            Some("stdout"),
            "--emit-hints=stdout should be captured"
        );

        std::fs::remove_dir_all(&parsed.crate_root).ok();
    }

    #[test]
    fn test_parse_args_accepts_emit_hints_json_flag() {
        let crate_root = std::env::temp_dir().join("cargo_trust_vc_parse_emit_hints_json");
        std::fs::create_dir_all(&crate_root).expect("temp dir should exist");
        let args = vec![
            "cargo".to_string(),
            "trust_vc".to_string(),
            "check".to_string(),
            "--emit-hints-json".to_string(),
            crate_root.display().to_string(),
        ];

        let parsed = parse_args_from(&args).expect("arguments should parse");

        assert!(parsed.emit_hints_json, "--emit-hints-json should be true");
        // emit_hints is not set when only --emit-hints-json is passed
        assert!(
            parsed.emit_hints.is_none(),
            "--emit-hints should be None when only --emit-hints-json is used"
        );

        std::fs::remove_dir_all(&parsed.crate_root).ok();
    }

    #[test]
    fn test_parse_args_accepts_both_emit_hints_and_json() {
        let crate_root = std::env::temp_dir().join("cargo_trust_vc_parse_both_hints");
        std::fs::create_dir_all(&crate_root).expect("temp dir should exist");
        let args = vec![
            "cargo".to_string(),
            "trust_vc".to_string(),
            "check".to_string(),
            "--emit-hints".to_string(),
            "--emit-hints-json".to_string(),
            crate_root.display().to_string(),
        ];

        let parsed = parse_args_from(&args).expect("arguments should parse");

        assert_eq!(parsed.emit_hints.as_deref(), Some("file"));
        assert!(parsed.emit_hints_json);

        std::fs::remove_dir_all(&parsed.crate_root).ok();
    }

    #[test]
    fn test_parse_args_emit_hints_default_does_not_interfere_with_other_flags() {
        let crate_root = std::env::temp_dir().join("cargo_trust_vc_hints_no_interfere");
        std::fs::create_dir_all(&crate_root).expect("temp dir should exist");
        let args = vec![
            "cargo".to_string(),
            "trust_vc".to_string(),
            "check".to_string(),
            "--emit-hints".to_string(),
            "--emit-certificate".to_string(),
            "--localize".to_string(),
            crate_root.display().to_string(),
        ];

        let parsed = parse_args_from(&args).expect("arguments should parse");

        assert_eq!(parsed.emit_hints.as_deref(), Some("file"));
        assert!(parsed.emit_certificate);
        assert!(parsed.localize);

        std::fs::remove_dir_all(&parsed.crate_root).ok();
    }

    #[test]
    fn test_emit_hints_function_produces_output_for_empty_verifications() {
        let crate_root = make_temp_crate_root("emit_hints_empty");
        std::fs::create_dir_all(&crate_root).expect("temp dir should exist");

        let args = CliArgs {
            check: false,
            function_filter: None,
            json_output: false,
            localize: false,
            no_cheating: false,
            emit_certificate: false,
            emit_hints: Some("file".to_string()),
            emit_hints_json: false,
            verbose: 0,
            timeout: None,
            filter: None,
            jobs: None,
            watch: false,
            diff: false,
            ci: false,
            crate_root: crate_root.clone(),
        };

        let result = emit_hints(&args, &[]);
        assert!(
            result.is_ok(),
            "emit_hints should succeed with no verifications"
        );

        // Should create a .hints.rs file with empty content (no facts)
        let crate_name = crate_root
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or("crate");
        let hints_file = crate_root.join(format!("{crate_name}.hints.rs"));
        assert!(hints_file.exists(), "hints file should be created");

        let content = std::fs::read_to_string(&hints_file).expect("hints file should be readable");
        assert!(
            content.contains("Auto-generated optimization hints"),
            "hints file should contain header"
        );
        assert!(
            content.contains("Total proven facts: 0"),
            "empty verifications should show 0 facts"
        );

        std::fs::remove_dir_all(&crate_root).ok();
    }

    #[test]
    fn test_emit_hints_json_function_produces_valid_json() {
        let crate_root = make_temp_crate_root("emit_hints_json_out");
        std::fs::create_dir_all(&crate_root).expect("temp dir should exist");

        let args = CliArgs {
            check: false,
            function_filter: None,
            json_output: false,
            localize: false,
            no_cheating: false,
            emit_certificate: false,
            emit_hints: Some("file".to_string()),
            emit_hints_json: true,
            verbose: 0,
            timeout: None,
            filter: None,
            jobs: None,
            watch: false,
            diff: false,
            ci: false,
            crate_root: crate_root.clone(),
        };

        let result = emit_hints(&args, &[]);
        assert!(
            result.is_ok(),
            "emit_hints (JSON) should succeed with no verifications"
        );

        let json_file = crate_root.join("optimization-hints.json");
        assert!(json_file.exists(), "JSON hints file should be created");

        let content = std::fs::read_to_string(&json_file).expect("JSON file should be readable");
        let parsed: serde_json::Value =
            serde_json::from_str(&content).expect("output should be valid JSON");
        assert!(parsed["summary"].is_object());
        assert_eq!(parsed["summary"]["total_facts"], 0);
        assert!(parsed["facts"].is_array());
        assert!(parsed["hints"].is_array());

        std::fs::remove_dir_all(&crate_root).ok();
    }

    // -----------------------------------------------------------------------
    // CLI integration tests: cross-cutting verification of subcommand logic
    // -----------------------------------------------------------------------

    /// Helper: create a temp directory with a synthetic Rust source file.
    fn write_temp_source(label: &str, source: &str) -> (PathBuf, PathBuf) {
        let dir = make_temp_crate_root(label);
        let src_dir = dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("temp src dir should exist");
        let file_path = src_dir.join("lib.rs");
        std::fs::write(&file_path, source).expect("temp source should be writable");
        (dir, file_path)
    }

    #[test]
    fn test_check_verified_function_returns_verified_verdict() {
        let (crate_root, _file_path) = write_temp_source(
            "check_verified",
            r#"
                #[trust_vc::contract(
                    requires(x > 0),
                    ensures(result == x),
                    returns(result),
                )]
                fn identity(x: u32) -> u32 {
                    x
                }
            "#,
        );

        let functions = scan::scan_crate(&crate_root);
        assert_eq!(
            functions.len(),
            1,
            "should find exactly one annotated function"
        );
        assert_eq!(functions[0].name, "identity");
        assert!(functions[0].attributes.contains(&"contract".to_string()));

        let verdict = verify::verify_one(&functions[0]);
        assert_eq!(
            verdict.result,
            verify::VerdictKind::Verified,
            "identity function should verify: {:?}",
            verdict.detail
        );

        std::fs::remove_dir_all(&crate_root).ok();
    }

    #[test]
    fn test_no_cheating_rejects_visible_assumption_before_verification() {
        let (crate_root, _file_path) = write_temp_source(
            "no_cheating_rejects_assume",
            r#"
                fn helper(x: i32) -> i32 {
                    trust_vc::assume!(false);
                    x
                }
            "#,
        );
        let mut args = test_cli_args(crate_root.clone());
        args.no_cheating = true;

        let result = run_verification(&args);

        assert!(
            matches!(result, Err(1)),
            "--no-cheating should reject trusted constructs even without annotated functions"
        );
        std::fs::remove_dir_all(&crate_root).ok();
    }

    #[test]
    fn test_scan_finds_trust_vc_macros_in_source() {
        let (crate_root, file_path) = write_temp_source(
            "scan_macros",
            r#"
                #[requires(n > 0)]
                fn positive(n: u32) -> u32 { n }

                #[ensures(result == a + b)]
                fn add(a: u32, b: u32) -> u32 { a + b }

                #[proof]
                fn lemma_trivial() {}

                fn unannotated() -> bool { true }
            "#,
        );

        // Test scan_crate (walks src/ directory).
        let crate_functions = scan::scan_crate(&crate_root);
        assert_eq!(
            crate_functions.len(),
            3,
            "scan_crate should find 3 annotated functions, ignoring unannotated"
        );

        let names: Vec<&str> = crate_functions.iter().map(|f| f.name.as_str()).collect();
        assert!(names.contains(&"positive"), "should find 'positive'");
        assert!(names.contains(&"add"), "should find 'add'");
        assert!(
            names.contains(&"lemma_trivial"),
            "should find 'lemma_trivial'"
        );
        assert!(
            !names.contains(&"unannotated"),
            "should NOT find 'unannotated'"
        );

        // Test scan_file (single file scan).
        let file_functions = scan::scan_file(&file_path);
        assert_eq!(
            file_functions.len(),
            3,
            "scan_file should find 3 annotated functions"
        );

        // Verify attributes are correctly captured.
        let positive_fn = file_functions
            .iter()
            .find(|f| f.name == "positive")
            .unwrap();
        assert!(positive_fn.attributes.contains(&"requires".to_string()));

        let add_fn = file_functions.iter().find(|f| f.name == "add").unwrap();
        assert!(add_fn.attributes.contains(&"ensures".to_string()));

        std::fs::remove_dir_all(&crate_root).ok();
    }

    #[test]
    fn test_suggest_output_format_contains_expected_sections() {
        let (_crate_root, file_path) =
            write_temp_source("suggest_format", "fn double(x: u32) -> u32 { x * 2 }\n");

        let args = suggest::SuggestArgs {
            file: file_path.clone(),
            function: None,
            backend: suggest::BackendKind::Mock,
            model: None,
            max_iterations: 3,
        };

        let output = suggest::run_suggest(&args).expect("mock suggest should succeed");

        // Output should contain function header with signature.
        assert!(
            output.contains("--- fn double(x: u32) -> u32 ---"),
            "suggest output should contain function header, got: {output}"
        );
        // Output should report verification status.
        assert!(
            output.contains("Status:"),
            "suggest output should contain 'Status:' line"
        );
        // Output should report iteration count.
        assert!(
            output.contains("Iterations:"),
            "suggest output should contain 'Iterations:' line"
        );

        std::fs::remove_dir_all(file_path.parent().unwrap().parent().unwrap()).ok();
    }

    #[test]
    fn test_check_error_missing_file() {
        let func = scan::AnnotatedFunction {
            file_path: PathBuf::from("/nonexistent/path/missing.rs"),
            name: "ghost_function".into(),
            line: 1,
            attributes: vec!["requires".into(), "ensures".into()],
        };

        let verdict = verify::verify_one(&func);
        assert_eq!(
            verdict.result,
            verify::VerdictKind::Error,
            "verify on a missing file should return Error"
        );
        assert!(
            verdict.detail.is_some(),
            "error verdict should include a detail message"
        );
        assert!(
            verdict.detail.as_ref().unwrap().contains("No such file")
                || verdict.detail.as_ref().unwrap().contains("not found")
                || verdict.detail.as_ref().unwrap().contains("cannot")
                || !verdict.detail.as_ref().unwrap().is_empty(),
            "detail should describe the missing file, got: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_parse_args_rejects_invalid_argument() {
        let crate_root = std::env::temp_dir().join("cargo_trust_vc_invalid_args");
        std::fs::create_dir_all(&crate_root).expect("temp dir should exist");
        let args = vec![
            "cargo".to_string(),
            "trust_vc".to_string(),
            "check".to_string(),
            "--nonexistent-flag".to_string(),
            crate_root.display().to_string(),
        ];

        let result = parse_args_from(&args);
        assert!(
            result.is_err(),
            "unknown flags should produce a parse error"
        );
        let err_msg = result.unwrap_err();
        assert!(
            err_msg.contains("unexpected argument")
                || err_msg.contains("unrecognized")
                || err_msg.contains("not expected"),
            "error should mention the invalid flag, got: {err_msg}"
        );

        std::fs::remove_dir_all(&crate_root).ok();
    }

    #[test]
    fn test_parse_args_rejects_joined_z_unstable_options() {
        let crate_root = make_temp_crate_root("joined_z_unstable_options");
        std::fs::create_dir_all(&crate_root).expect("temp dir should exist");
        let args = vec![
            "cargo".to_string(),
            "trust_vc".to_string(),
            "check".to_string(),
            crate_root.display().to_string(),
            "-Zunstable-options".to_string(),
        ];

        let result = parse_args_from(&args);

        assert!(
            result.is_err(),
            "joined -Zunstable-options should remain a parser error"
        );

        std::fs::remove_dir_all(crate_root).ok();
    }

    #[test]
    fn test_parse_args_accepts_split_z_unstable_options() {
        let crate_root = make_temp_crate_root("split_z_unstable_options");
        std::fs::create_dir_all(&crate_root).expect("temp dir should exist");
        let args = vec![
            "cargo".to_string(),
            "trust_vc".to_string(),
            "check".to_string(),
            crate_root.display().to_string(),
            "-Z".to_string(),
            "unstable-options".to_string(),
        ];

        let parsed = parse_args_from(&args).expect("split -Z unstable-options should parse");

        assert_eq!(
            parsed.crate_root,
            crate_root
                .canonicalize()
                .expect("temp dir path should canonicalize")
        );

        std::fs::remove_dir_all(&parsed.crate_root).ok();
    }

    #[test]
    fn test_parse_args_nonexistent_crate_root() {
        let args = vec![
            "cargo".to_string(),
            "trust_vc".to_string(),
            "check".to_string(),
            "/nonexistent/path/to/crate".to_string(),
        ];

        let result = parse_args_from(&args);
        assert!(
            result.is_err(),
            "nonexistent crate root should produce a path resolution error"
        );
        let err_msg = result.unwrap_err();
        assert!(
            err_msg.contains("cannot resolve path"),
            "error should mention path resolution, got: {err_msg}"
        );
    }

    #[test]
    fn test_json_output_format_structure() {
        let (crate_root, _file_path) = write_temp_source(
            "json_format",
            r#"
                #[trust_vc::contract(
                    requires(x > 0),
                    ensures(result == x),
                    returns(result),
                )]
                fn pass_through(x: u32) -> u32 {
                    x
                }
            "#,
        );

        let functions = scan::scan_crate(&crate_root);
        assert_eq!(functions.len(), 1);

        let verdict = verify::verify_one(&functions[0]);
        let verdicts = vec![verdict];

        // Construct summary and verify its structure.
        let summary = report::Summary::from_verdicts(&verdicts);
        assert_eq!(summary.verified, 1);
        assert_eq!(summary.counterexample, 0);
        assert_eq!(summary.unknown, 0);
        assert_eq!(summary.error, 0);
        assert!(
            !summary.has_failures(),
            "fully verified should not have failures"
        );

        // Serialize summary to JSON to verify the output schema.
        let json = serde_json::to_string_pretty(&summary).expect("summary should serialize");
        let parsed: serde_json::Value =
            serde_json::from_str(&json).expect("summary JSON should be valid");
        assert_eq!(parsed["verified"], 1);
        assert_eq!(parsed["counterexample"], 0);
        assert_eq!(parsed["unknown"], 0);
        assert_eq!(parsed["error"], 0);
        assert_eq!(parsed["skipped"], 0);

        std::fs::remove_dir_all(&crate_root).ok();
    }

    #[test]
    fn test_normalize_raw_args_strips_cargo_trust_vc_check_prefix() {
        // "cargo trust_vc check --json ." -> strip "trust_vc check" -> "cargo --json ."
        let raw = vec![
            "cargo".into(),
            "trust_vc".into(),
            "check".into(),
            "--json".into(),
            ".".into(),
        ];
        let normalized = normalize_raw_args(&raw);
        assert_eq!(normalized, vec!["cargo", "--json", "."]);

        // "cargo trust_vc --json ." -> strip "trust_vc" -> "cargo --json ."
        let raw2 = vec![
            "cargo".into(),
            "trust_vc".into(),
            "--json".into(),
            ".".into(),
        ];
        let normalized2 = normalize_raw_args(&raw2);
        assert_eq!(normalized2, vec!["cargo", "--json", "."]);

        // "cargo-trust-vc check --json ." -> strip "check" -> "cargo-trust-vc --json ."
        let raw3 = vec![
            "cargo-trust-vc".into(),
            "check".into(),
            "--json".into(),
            ".".into(),
        ];
        let normalized3 = normalize_raw_args(&raw3);
        assert_eq!(normalized3, vec!["cargo-trust-vc", "--json", "."]);

        // Direct invocation: "cargo-trust-vc --json ." -> pass through unchanged.
        let raw4 = vec!["cargo-trust-vc".into(), "--json".into(), ".".into()];
        let normalized4 = normalize_raw_args(&raw4);
        assert_eq!(normalized4, vec!["cargo-trust-vc", "--json", "."]);

        // Empty args.
        let raw5: Vec<String> = Vec::new();
        let normalized5 = normalize_raw_args(&raw5);
        assert!(normalized5.is_empty());
    }

    // ---- `--frontend=driver` wiring: parse + parity-compare soundness ----

    #[test]
    fn test_parse_trust_vc_frontend_accepts_syn_and_driver() {
        assert_eq!(TrustVcFrontend::parse("syn"), Some(TrustVcFrontend::Syn));
        assert_eq!(
            TrustVcFrontend::parse("driver"),
            Some(TrustVcFrontend::Driver)
        );
        assert_eq!(TrustVcFrontend::parse("z3"), None);
        assert!(parse_trust_vc_frontend("bogus").is_err());
    }

    #[test]
    fn test_frontend_flag_parsed_and_not_forwarded_to_cargo() {
        let current_dir = std::env::temp_dir();
        // Space form.
        let parsed = parse_cargo_verus_arg_forwarding_tail(
            current_dir.clone(),
            CargoVerusCompatSubcommand::Check,
            &[
                "--frontend".to_string(),
                "driver".to_string(),
                "-p".to_string(),
                "demo".to_string(),
            ],
        )
        .expect("frontend + package should parse");
        assert_eq!(parsed.frontend, TrustVcFrontend::Driver);
        assert!(
            !parsed.cargo_args.iter().any(|arg| arg.contains("frontend")),
            "--frontend must not be forwarded to cargo; got {:?}",
            parsed.cargo_args
        );
        assert!(parsed.cargo_args.contains(&"demo".to_string()));

        // Equals form, default when absent is Syn.
        let eq = parse_cargo_verus_arg_forwarding_tail(
            current_dir.clone(),
            CargoVerusCompatSubcommand::Check,
            &["--frontend=driver".to_string()],
        )
        .expect("equals-form frontend should parse");
        assert_eq!(eq.frontend, TrustVcFrontend::Driver);

        let default = parse_cargo_verus_arg_forwarding_tail(
            current_dir,
            CargoVerusCompatSubcommand::Check,
            &["-p".to_string(), "demo".to_string()],
        )
        .expect("no frontend flag should parse");
        assert_eq!(default.frontend, TrustVcFrontend::Syn);
    }

    #[test]
    fn test_frontend_flag_rejects_unknown_value() {
        let err = parse_cargo_verus_arg_forwarding_tail(
            std::env::temp_dir(),
            CargoVerusCompatSubcommand::Check,
            &["--frontend=z3".to_string()],
        )
        .expect_err("unknown frontend must be rejected");
        assert!(err.contains("--frontend"), "err={err}");
    }

    #[test]
    fn test_frontend_flag_is_cargo_verus_relevant() {
        // Recognized so it triggers interception + passes the arg-order check.
        assert_eq!(cargo_verus_relevant_arg("--frontend"), Some(true));
        assert_eq!(cargo_verus_relevant_arg("--frontend=driver"), Some(false));
        assert!(check_tail_looks_like_cargo_verus_compat(&[
            "--frontend=driver".to_string()
        ]));
    }

    #[test]
    fn test_parse_driver_result_lines() {
        let stdout = "\
noise before\n\
TRUST_VC_DRIVER_RESULT\tverify_case\tVerified\t\n\
TRUST_VC_DRIVER_RESULT\trefute_case\tRefuted\t\n\
TRUST_VC_DRIVER_RESULT\tloop_case\tUnsupportedContract\twhile loop\n\
TRUST_VC_DRIVER_SUMMARY\t3\t1\t1\t0\t0\t1\n";
        let verdicts = parse_driver_result_lines(stdout);
        assert_eq!(
            verdicts.get("verify_case").map(String::as_str),
            Some("Verified")
        );
        assert_eq!(
            verdicts.get("refute_case").map(String::as_str),
            Some("Refuted")
        );
        assert_eq!(
            verdicts.get("loop_case").map(String::as_str),
            Some("UnsupportedContract")
        );
        // The SUMMARY line is not a RESULT record.
        assert_eq!(verdicts.len(), 3);
    }

    fn parity_map(pairs: &[(&str, &str)]) -> BTreeMap<String, String> {
        pairs
            .iter()
            .map(|(k, v)| (k.to_string(), v.to_string()))
            .collect()
    }

    #[test]
    fn test_compare_driver_syn_agreement_and_skips() {
        let driver = parity_map(&[
            ("verify_case", "Verified"),
            ("refute_case", "Refuted"),
            ("loop_case", "UnsupportedContract"),
            ("typ_case", "UnsupportedType"),
        ]);
        let syn = parity_map(&[
            ("verify_case", "Verified"),
            ("refute_case", "Refuted"),
            ("loop_case", "Unknown"),
            ("typ_case", "Skipped"),
        ]);
        let records = compare_driver_syn(&driver, &syn);
        // Unsupported* are skipped — only the two in-fragment functions compared.
        assert_eq!(records.len(), 2);
        assert!(records.iter().all(|record| record.agree));
        assert!(records.iter().all(|record| !record.driver_proves_more));
        // Agreement ⇒ soundness check passes.
        assert!(driver_syn_parity_soundness_check(&records).is_ok());
    }

    #[test]
    fn test_driver_proves_more_is_a_hard_error() {
        // Driver Verified where syn is Unknown ⇒ unsound direction ⇒ hard error.
        let records = compare_driver_syn(
            &parity_map(&[("f", "Verified")]),
            &parity_map(&[("f", "Unknown")]),
        );
        assert_eq!(records.len(), 1);
        assert!(records[0].driver_proves_more);
        let err = driver_syn_parity_soundness_check(&records)
            .expect_err("driver proving more must fail the run");
        assert!(err.contains("must never prove more than syn"), "err={err}");

        // Driver Verified where syn never scanned the function (Absent) is also
        // the driver proving more.
        let absent = compare_driver_syn(&parity_map(&[("g", "Verified")]), &parity_map(&[]));
        assert!(absent[0].driver_proves_more);
        assert!(driver_syn_parity_soundness_check(&absent).is_err());
    }

    #[test]
    fn test_driver_weaker_than_syn_is_not_an_error() {
        // Driver Unknown/Refuted where syn Verified is the SOUND direction (the
        // driver is a weaker prover) — informational, never a failure.
        let records = compare_driver_syn(
            &parity_map(&[("a", "Unknown"), ("b", "Refuted")]),
            &parity_map(&[("a", "Verified"), ("b", "Verified")]),
        );
        assert!(records.iter().all(|record| !record.driver_proves_more));
        assert!(records.iter().all(|record| !record.agree));
        assert!(driver_syn_parity_soundness_check(&records).is_ok());
    }
}
