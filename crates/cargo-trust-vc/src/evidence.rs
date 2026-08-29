// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Reproducible evidence generation for TrustVc/Verus replacement claims.

use crate::{certificate, scan, verify};
use proc_macro2::{Delimiter, TokenStream, TokenTree};
use quote::ToTokens;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Write as _};
use std::fs;
use std::io::{ErrorKind, Read};
use std::path::{Component, Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::OnceLock;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

const TVC_BUILD_GIT_HEAD: &str = env!("TVC_BUILD_GIT_HEAD");
const TRUST_VC_DEPENDENCY_FACTS_ENV: &str = "__TRUST_VC_DEPENDENCY_FACTS__";
const TRUST_VC_RUSTC_WRAPPER_ARTIFACT_MAGIC: &str = "trust-vc-rustc-wrapper-artifact-v1\n";
const TRUST_VC_RUSTC_WRAPPER_ARTIFACT_KIND: &str =
    "cargo-trust-vc-rustc-wrapper-dependency-metadata";
const TRUST_VC_RUSTC_WRAPPER_SEMANTIC_FACTS_PAYLOAD_KIND: &str = "trust-vc-semantic-facts-v1";
const CARGO_DEFAULT_LIB_METADATA_ENV: &str = "__CARGO_DEFAULT_LIB_METADATA";
const VERUS_DRIVER_ARGS_ENV: &str = " __VERUS_DRIVER_ARGS__";
const VERUS_DRIVER_ARGS_FOR_ENV_PREFIX: &str = " __VERUS_DRIVER_ARGS_FOR_";
const VERUS_DRIVER_ARGS_SEP: &str = "__VERUS_DRIVER_ARGS_SEP__";
const VERUS_DRIVER_VERIFY_ENV_PREFIX: &str = "__VERUS_DRIVER_VERIFY_";
const VERUS_DRIVER_VIA_CARGO_ENV: &str = "__VERUS_DRIVER_VIA_CARGO__";
const EVIDENCE_COMMAND_TIMEOUT_ENV: &str = "TRUST_VC_EVIDENCE_COMMAND_TIMEOUT_SECONDS";
const DEFAULT_EVIDENCE_COMMAND_TIMEOUT_SECONDS: u64 = 30 * 60;

#[derive(Debug, Clone)]
pub(crate) struct EvidenceArgs {
    pub(crate) crate_root: PathBuf,
    pub(crate) output_dir: PathBuf,
    pub(crate) port_output_dir: PathBuf,
    pub(crate) verus_path: Option<PathBuf>,
    pub(crate) verus_rev: Option<String>,
    pub(crate) manifest_path: Option<PathBuf>,
    pub(crate) canonical_manifest_path: PathBuf,
    pub(crate) strict: bool,
    pub(crate) json: bool,
    pub(crate) markdown: bool,
    pub(crate) run_trust_vc: bool,
    pub(crate) cargo_command: String,
    pub(crate) cargo_command_overridden: bool,
    pub(crate) run_trust_vc_corpus: bool,
    pub(crate) trust_vc_corpus_command: Option<String>,
    pub(crate) run_verus: bool,
    pub(crate) port_manifest_only: bool,
    pub(crate) update_verus_tests_manifest: bool,
    pub(crate) refresh_trust_vc_corpus_evidence: bool,
    pub(crate) corpus_triage_report: bool,
    pub(crate) scaffold_verus_port_stubs: bool,
    pub(crate) verus_command: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct EvidenceReport {
    pub schema_version: u32,
    pub generated_unix_seconds: u64,
    pub strict: bool,
    pub replacement_verdict: ReplacementVerdict,
    pub repository: RepositoryEvidence,
    pub ay: AYEvidence,
    pub cargo: CargoEvidence,
    pub verus: VerusEvidence,
    pub gates: Vec<GateResult>,
    pub corpus: Option<VerusCorpusReport>,
    pub trust_vc_corpus: Option<TrustVcCorpusRunReport>,
    pub blocking_reasons: Vec<String>,
}

impl EvidenceReport {
    pub(crate) fn has_blocking_failures(&self) -> bool {
        matches!(self.replacement_verdict, ReplacementVerdict::NotProven)
    }

    pub(crate) fn render_markdown(&self) -> String {
        let mut out = String::new();
        out.push_str("# TrustVc Verus-Replacement Evidence\n\n");
        out.push_str(&format!("Verdict: **{}**\n\n", self.replacement_verdict));
        out.push_str("## Repository\n\n");
        out.push_str(&format!(
            "- TrustVc HEAD: `{}`\n",
            display_opt(&self.repository.trust_vc_head)
        ));
        out.push_str(&format!("- Dirty worktree: `{}`\n", self.repository.dirty));
        out.push_str(&format!(
            "- ay pin: `{}`\n",
            display_opt(&self.ay.pinned_rev)
        ));
        out.push_str(&format!(
            "- latest private ay main: `{}`\n",
            display_opt(&self.ay.latest_private_main)
        ));
        if self.ay.ay_identity_rev.is_some() {
            out.push_str(&format!(
                "- ay identity rev: `{}`\n",
                display_opt(&self.ay.ay_identity_rev)
            ));
            out.push_str(&format!(
                "- ay repo root: `{}`\n",
                display_path_opt(&self.ay.ay_repo_root)
            ));
            out.push_str(&format!(
                "- ay origin URL: `{}`\n",
                display_opt(&self.ay.ay_origin_url)
            ));
            out.push_str(&format!(
                "- ay worktree clean: `{}`\n",
                self.ay
                    .ay_worktree_clean
                    .map(|clean| clean.to_string())
                    .unwrap_or_else(|| "<unknown>".to_string())
            ));
            out.push_str(&format!(
                "- ay published: `{}`\n",
                display_opt(&self.ay.ay_published)
            ));
        }
        out.push_str(&format!(
            "- Cargo command: `{}`\n",
            escape_md(&self.cargo.command)
        ));
        out.push_str(&format!(
            "- Cargo command canonical: `{}`\n",
            display_path_opt(&self.cargo.canonical_command)
        ));
        out.push_str(&format!(
            "- Cargo provenance failures: `{}`\n",
            self.cargo.failures.len()
        ));
        out.push_str(&format!(
            "- Verus HEAD: `{}`\n",
            display_opt(&self.verus.head)
        ));
        out.push_str(&format!(
            "- Requested Verus rev: `{}`\n\n",
            display_opt(&self.verus.requested_rev)
        ));

        out.push_str("## Gates\n\n");
        out.push_str("| Gate | Required | Status | Detail |\n");
        out.push_str("|---|---:|---|---|\n");
        for gate in &self.gates {
            out.push_str(&format!(
                "| {} | {} | {} | {} |\n",
                escape_md(&gate.name),
                gate.required,
                gate.status,
                escape_md(gate.detail.as_deref().unwrap_or(""))
            ));
        }

        if let Some(corpus) = &self.corpus {
            out.push_str("\n## Verus Corpus\n\n");
            out.push_str(&format!(
                "- Manifest: `{}`\n",
                corpus.manifest_path.display()
            ));
            out.push_str(&format!(
                "- Upstream tests found: `{}`\n",
                corpus.upstream_test_count
            ));
            out.push_str(&format!("- Manifest entries: `{}`\n", corpus.entry_count));
            out.push_str(&format!(
                "- Missing entries: `{}`\n",
                corpus.missing_entries.len()
            ));
            out.push_str(&format!(
                "- Extra entries: `{}`\n",
                corpus.extra_entries.len()
            ));
            out.push_str(&format!(
                "- Unsupported gaps: `{}`\n",
                corpus.unsupported_entries.len()
            ));
            out.push_str(&format!(
                "- Invalid entries: `{}`\n",
                corpus.invalid_entries.len()
            ));
            out.push_str(&format!(
                "- Duplicate entries: `{}`\n",
                corpus.duplicate_entries.len()
            ));
            out.push_str(&format!(
                "- Failing classifications: `{}`\n",
                corpus.failing_entries.len()
            ));
            out.push_str(&format!(
                "- Port path failures: `{}`\n",
                corpus.port_path_failures.len()
            ));
            out.push_str(&format!(
                "- Upstream case failures: `{}`\n",
                corpus.upstream_case_failures.len()
            ));
            out.push_str(&format!(
                "- Ignored upstream cases: `{}`\n",
                corpus.ignored_upstream_cases.len()
            ));
            out.push_str(&format!(
                "- Upstream case extraction gaps: `{}`\n",
                corpus.upstream_case_extraction_gaps.len()
            ));
            out.push_str("\n### Replacement Summary\n\n");
            out.push_str(&format!(
                "- Total manifest entries: `{}`\n",
                corpus.replacement_summary.total_entries
            ));
            out.push_str(&format!(
                "- Accepted executable entries: `{}`\n",
                corpus.replacement_summary.accepted_executable_entries
            ));
            out.push_str(&format!(
                "- Accepted TrustVc path bindings: `{}`\n",
                corpus.replacement_summary.accepted_trust_vc_path_count
            ));
            out.push_str(&format!(
                "- Accepted expected cases: `{}`\n",
                corpus.replacement_summary.accepted_expected_case_count
            ));
            out.push_str(&format!(
                "- Unsupported gaps: `{}`\n",
                corpus.replacement_summary.unsupported_gap_entries
            ));
            out.push_str(&format!(
                "- Unclassified gaps: `{}`\n",
                corpus.replacement_summary.unclassified_entries
            ));
            out.push_str(&format!(
                "- Not-applicable entries: `{}`\n",
                corpus.replacement_summary.not_applicable_entries
            ));
            out.push_str(&format!(
                "- Accepted entries with known gaps: `{}`\n",
                corpus.replacement_summary.accepted_known_gap_entries
            ));
            if let Some(action) = &corpus.porting_next_action {
                out.push_str("\n### Verus Porting Next Action\n\n");
                out.push_str(&format!(
                    "- Blocking entries: `{}`\n",
                    action.blocking_entries
                ));
                out.push_str(&format!(
                    "- Classifications: `{}`\n",
                    escape_md(&joined_or_none(&action.classifications))
                ));
                out.push_str(&format!(
                    "- Run from: `{}`\n",
                    escape_md(&action.working_directory)
                ));
                out.push_str(&format!("- Command: `{}`\n", escape_md(&action.command)));
                out.push_str("- This scaffolds fail-closed port placeholders and is not replacement evidence.\n");
            }
            out.push_str("\n### Accepted Executable Ports\n\n");
            if corpus.accepted_executable_ports.is_empty() {
                out.push_str("None.\n");
            } else {
                out.push_str("| Upstream path | Classification | Issue | TrustVc paths | Expected cases | Proof gaps |\n");
                out.push_str("|---|---|---|---|---|---|\n");
                for entry in &corpus.accepted_executable_ports {
                    out.push_str(&format!(
                        "| {} | {} | {} | {} | {} | {} |\n",
                        escape_md(&entry.upstream_path),
                        escape_md(&entry.classification),
                        issue_markdown_link(entry),
                        escape_md(&joined_or_none(&entry.trust_vc_paths)),
                        escape_md(&expected_case_summaries(&entry.expected_cases)),
                        escape_md(&joined_or_none(&entry.known_gaps))
                    ));
                }
            }
            out.push_str("\n### Unsupported Gap Partial Evidence\n\n");
            if corpus.unsupported_gap_evidence.is_empty() {
                out.push_str("None.\n");
            } else {
                out.push_str("| Upstream path | Issue | Partial TrustVc paths | Partial expected cases | Proof gaps | Reason |\n");
                out.push_str("|---|---|---|---|---|---|\n");
                for entry in &corpus.unsupported_gap_evidence {
                    out.push_str(&format!(
                        "| {} | {} | {} | {} | {} | {} |\n",
                        escape_md(&entry.upstream_path),
                        issue_markdown_link(entry),
                        escape_md(&joined_or_none(&entry.trust_vc_paths)),
                        escape_md(&expected_case_summaries(&entry.expected_cases)),
                        escape_md(&joined_or_none(&entry.known_gaps)),
                        escape_md(&entry.reason)
                    ));
                }
            }
            out.push_str("\n### Ignored Upstream Cases\n\n");
            if corpus.ignored_upstream_cases.is_empty() {
                out.push_str("None.\n");
            } else {
                out.push_str("| Upstream path | Case | Upstream verdict | Expected case ids |\n");
                out.push_str("|---|---|---|---|\n");
                for case in &corpus.ignored_upstream_cases {
                    out.push_str(&format!(
                        "| {} | {} | {} | {} |\n",
                        escape_md(&case.upstream_path),
                        escape_md(&case.case_id),
                        escape_md(&case.expected_verdict),
                        escape_md(&joined_or_none(&case.expected_case_ids))
                    ));
                }
            }
            out.push_str("\n### Upstream Case Extraction Gaps\n\n");
            if corpus.upstream_case_extraction_gaps.is_empty() {
                out.push_str("None.\n");
            } else {
                for gap in &corpus.upstream_case_extraction_gaps {
                    out.push_str(&format!("- {}\n", escape_md(gap)));
                }
            }
            out.push_str("\n### Accepted TrustVc Source Hashes\n\n");
            if corpus.accepted_trust_vc_source_hashes.is_empty() {
                out.push_str("None.\n");
            } else {
                out.push_str(
                    "| Upstream path | Classification | TrustVc path | Kind | SHA-256 |\n",
                );
                out.push_str("|---|---|---|---|---|\n");
                for entry in &corpus.accepted_trust_vc_source_hashes {
                    for source_hash in &entry.trust_vc_paths {
                        out.push_str(&format!(
                            "| {} | {} | {} | {} | `{}` |\n",
                            escape_md(&entry.upstream_path),
                            escape_md(&entry.classification),
                            escape_md(&source_hash.path),
                            source_hash.kind,
                            source_hash.sha256
                        ));
                    }
                }
            }
        }

        if let Some(corpus_run) = &self.trust_vc_corpus {
            out.push_str("\n## TrustVc Corpus Execution\n\n");
            out.push_str(&format!(
                "- Attempted paths: `{}`\n",
                corpus_run.attempted_paths
            ));
            out.push_str(&format!("- Passed paths: `{}`\n", corpus_run.passed_paths));
            out.push_str(&format!("- Failed paths: `{}`\n", corpus_run.failed_paths));
            out.push_str(&format!(
                "- Skipped entries: `{}`\n",
                corpus_run.skipped_entries
            ));
        }

        if !self.blocking_reasons.is_empty() {
            out.push_str("\n## Blocking Reasons\n\n");
            for reason in &self.blocking_reasons {
                out.push_str(&format!("- {}\n", escape_md(reason)));
            }
        }
        out
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub(crate) enum ReplacementVerdict {
    Proven,
    NotProven,
}

impl fmt::Display for ReplacementVerdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Proven => f.write_str("proven"),
            Self::NotProven => f.write_str("not_proven"),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct RepositoryEvidence {
    pub trust_vc_head: Option<String>,
    pub dirty: bool,
    pub crate_root: PathBuf,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct AYEvidence {
    pub pinned_rev: Option<String>,
    pub pinned_revs: BTreeMap<String, Option<String>>,
    pub pinned_sources: BTreeMap<String, Option<String>>,
    pub lock_sources: BTreeMap<String, Option<String>>,
    pub lock_source_entries: Vec<AYLockSourceEntry>,
    pub latest_private_main: Option<String>,
    pub is_latest_private_main: Option<bool>,
    pub local_patch_detected: bool,
    /// Auditable ay identity facts whenever dependency resolution uses the
    /// verified sibling Path authority. These describe exactly which ay
    /// produced the proofs: the clean,
    /// origin-verified `../ay` HEAD (`ay_identity_rev`), its worktree root and
    /// origin URL, whether the worktree was clean, and whether that HEAD is
    /// already published to `origin/main` (`ay_published`). All are `None`
    /// outside a Path-backed model.
    #[serde(default)]
    pub ay_identity_rev: Option<String>,
    #[serde(default)]
    pub ay_repo_root: Option<PathBuf>,
    #[serde(default)]
    pub ay_origin_url: Option<String>,
    #[serde(default)]
    pub ay_worktree_clean: Option<bool>,
    #[serde(default)]
    pub ay_published: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct AYLockSourceEntry {
    pub package_name: String,
    pub source: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AYManifestProvenance {
    pinned_rev: Option<String>,
    pinned_revs: BTreeMap<String, Option<String>>,
    pinned_sources: BTreeMap<String, Option<String>>,
    source_model: AYSourceModel,
    /// Independently verified sibling-path identity facts. These are present
    /// for the pure Path model and for the normal Git-rev + committed-patch
    /// composition, where both authorities must agree before evidence passes.
    sibling_identity: Option<AYSiblingIdentity>,
}

/// Auditable identity facts for the verified `../ay` sibling that produced the
/// proofs under a Path-backed dependency resolution.
#[derive(Debug, Clone, PartialEq, Eq)]
struct AYSiblingIdentity {
    head: String,
    repo_root: PathBuf,
    origin_url: String,
    worktree_clean: bool,
    published: AYPublished,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AYSourceModel {
    GitRev,
    GitRevWithVerifiedSiblingPath,
    VerifiedSiblingPath,
    Unverified,
}

impl AYSourceModel {
    fn label(self) -> &'static str {
        match self {
            Self::GitRev => "git-rev",
            Self::GitRevWithVerifiedSiblingPath => "git-rev+verified-sibling-path",
            Self::VerifiedSiblingPath => "verified-sibling-path",
            Self::Unverified => "unverified",
        }
    }

    fn has_verified_sibling_path(self) -> bool {
        matches!(
            self,
            Self::GitRevWithVerifiedSiblingPath | Self::VerifiedSiblingPath
        )
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct VerusEvidence {
    pub path: Option<PathBuf>,
    pub requested_rev: Option<String>,
    pub head: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct CargoEvidence {
    pub command: String,
    pub command_overridden: bool,
    pub canonical_command: Option<PathBuf>,
    pub default_rustup_cargo: bool,
    pub rustup_command: Option<PathBuf>,
    pub rustup_active_toolchain: Option<String>,
    pub rustup_which_cargo: Option<PathBuf>,
    pub cargo_proxy_sha256: Option<String>,
    pub rustup_sha256: Option<String>,
    pub toolchain_cargo_sha256: Option<String>,
    pub failures: Vec<String>,
    pub rustup_show_active_toolchain: Option<CommandResult>,
    pub rustup_which_cargo_command: Option<CommandResult>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct GateResult {
    pub name: String,
    pub required: bool,
    pub status: GateStatus,
    pub detail: Option<String>,
    pub command: Option<CommandResult>,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub(crate) enum GateStatus {
    Passed,
    Failed,
    Skipped,
}

impl fmt::Display for GateStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Passed => f.write_str("passed"),
            Self::Failed => f.write_str("failed"),
            Self::Skipped => f.write_str("skipped"),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct CommandResult {
    pub program: String,
    pub args: Vec<String>,
    pub cwd: PathBuf,
    pub exit_code: Option<i32>,
    pub duration_ms: u128,
    pub stdout_tail: String,
    pub stderr_tail: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct VerusCorpusReport {
    pub manifest_path: PathBuf,
    pub manifest_schema_version: u32,
    pub upstream_repo: Option<String>,
    pub upstream_ref: Option<String>,
    pub upstream_test_roots: Vec<String>,
    pub upstream_test_count: usize,
    pub entry_count: usize,
    pub classification_counts: BTreeMap<String, usize>,
    #[serde(default)]
    pub replacement_summary: VerusReplacementSummary,
    pub duplicate_entries: Vec<String>,
    pub invalid_entries: Vec<String>,
    pub missing_entries: Vec<String>,
    pub extra_entries: Vec<String>,
    pub unsupported_entries: Vec<String>,
    pub failing_entries: Vec<String>,
    pub port_path_failures: Vec<String>,
    pub upstream_case_failures: Vec<String>,
    #[serde(default)]
    pub ignored_upstream_cases: Vec<IgnoredUpstreamCaseEvidence>,
    #[serde(default)]
    pub upstream_case_extraction_gaps: Vec<String>,
    #[serde(default)]
    #[serde(skip_serializing_if = "Option::is_none")]
    pub porting_next_action: Option<VerusCorpusPortingAction>,
    #[serde(default)]
    pub accepted_executable_ports: Vec<VerusManifestEntryEvidence>,
    #[serde(default)]
    pub unsupported_gap_evidence: Vec<VerusManifestEntryEvidence>,
    #[serde(default)]
    pub accepted_trust_vc_source_hashes: Vec<AcceptedTrustVcSourceHashes>,
    #[serde(skip)]
    pub(crate) run_candidates: Vec<TrustVcCorpusRunCandidate>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default, PartialEq, Eq)]
pub(crate) struct VerusReplacementSummary {
    pub total_entries: usize,
    pub accepted_executable_entries: usize,
    pub accepted_trust_vc_path_count: usize,
    pub accepted_expected_case_count: usize,
    pub unsupported_gap_entries: usize,
    pub unclassified_entries: usize,
    pub not_applicable_entries: usize,
    pub accepted_known_gap_entries: usize,
    pub accepted_entries_missing_trust_vc_paths: usize,
    pub accepted_entries_missing_expected_cases: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct IgnoredUpstreamCaseEvidence {
    pub upstream_path: String,
    pub case_id: String,
    pub expected_verdict: String,
    pub expected_case_ids: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct VerusCorpusPortingAction {
    pub command: String,
    pub working_directory: String,
    pub manifest_path: String,
    pub blocking_entries: usize,
    pub classifications: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct VerusManifestEntryEvidence {
    pub upstream_path: String,
    pub classification: String,
    pub evidence_kind: String,
    pub owner_issue: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub owner_issue_url: Option<String>,
    pub reason: String,
    pub trust_vc_paths: Vec<String>,
    pub expected_cases: Vec<VerusExpectedCaseEvidence>,
    pub known_gaps: Vec<String>,
    pub notes: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct VerusExpectedCaseEvidence {
    pub case_id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub upstream_case_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trust_vc_path: Option<String>,
    pub expected_verdict: String,
    pub min_obligations: usize,
    pub obligation_fingerprints: Vec<String>,
    pub expected_error_patterns: Vec<String>,
    pub expected_rust_diagnostic_pattern_sets: Vec<Vec<String>>,
    pub forbidden_diagnostic_patterns: Vec<String>,
    pub expected_warning_patterns: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct AcceptedTrustVcSourceHashes {
    pub upstream_path: String,
    pub classification: String,
    pub trust_vc_paths: Vec<TrustVcSourcePathHash>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct TrustVcSourcePathHash {
    pub path: String,
    pub kind: TrustVcSourceHashKind,
    pub sha256: String,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub(crate) enum TrustVcSourceHashKind {
    File,
    Directory,
}

impl fmt::Display for TrustVcSourceHashKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::File => f.write_str("file"),
            Self::Directory => f.write_str("directory"),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct CorpusTriageReport {
    pub schema_version: u32,
    /// Schema version of the parsed corpus manifest itself. This is distinct
    /// from `schema_version`, which versions this triage-report envelope.
    #[serde(default)]
    pub manifest_schema_version: u32,
    pub manifest_path: String,
    pub upstream_repo: Option<String>,
    pub upstream_ref: Option<String>,
    pub upstream_test_roots: Vec<String>,
    pub entry_count: usize,
    pub classification_counts: BTreeMap<String, usize>,
    #[serde(default)]
    pub replacement_summary: VerusReplacementSummary,
    #[serde(default)]
    pub accepted_executable_ports: Vec<VerusManifestEntryEvidence>,
    #[serde(default)]
    pub unsupported_gap_evidence: Vec<VerusManifestEntryEvidence>,
    pub path_buckets: Vec<CorpusPathBucketSummary>,
    pub missing_trust_vc_paths: Vec<CorpusTriageEntry>,
    pub missing_trust_vc_path_files: Vec<CorpusMissingTrustVcPathFile>,
    pub duplicate_entries: Vec<String>,
    pub invalid_classification_entries: Vec<CorpusTriageEntry>,
}

impl CorpusTriageReport {
    pub(crate) fn render_markdown(&self) -> String {
        let mut out = String::new();
        out.push_str("# Verus Corpus Triage Report\n\n");
        out.push_str(&format!("- Manifest: `{}`\n", self.manifest_path));
        out.push_str(&format!(
            "- Manifest schema version: `{}`\n",
            self.manifest_schema_version
        ));
        out.push_str(&format!("- Entries: `{}`\n", self.entry_count));
        out.push_str(&format!(
            "- Duplicate entries: `{}`\n",
            self.duplicate_entries.len()
        ));
        out.push_str(&format!(
            "- Invalid classifications: `{}`\n",
            self.invalid_classification_entries.len()
        ));
        out.push_str(&format!(
            "- Missing trust_vc_paths: `{}`\n",
            self.missing_trust_vc_paths.len()
        ));
        out.push_str(&format!(
            "- Missing trust_vc_path files: `{}`\n",
            self.missing_trust_vc_path_files.len()
        ));

        out.push_str("\n## Classification Counts\n\n");
        out.push_str("| Classification | Entries |\n");
        out.push_str("|---|---:|\n");
        for (classification, count) in &self.classification_counts {
            out.push_str(&format!("| {} | {} |\n", escape_md(classification), count));
        }

        out.push_str("\n## Replacement Summary\n\n");
        out.push_str(&format!(
            "- Accepted executable entries: `{}`\n",
            self.replacement_summary.accepted_executable_entries
        ));
        out.push_str(&format!(
            "- Accepted TrustVc path bindings: `{}`\n",
            self.replacement_summary.accepted_trust_vc_path_count
        ));
        out.push_str(&format!(
            "- Accepted expected cases: `{}`\n",
            self.replacement_summary.accepted_expected_case_count
        ));
        out.push_str(&format!(
            "- Unsupported gaps: `{}`\n",
            self.replacement_summary.unsupported_gap_entries
        ));
        out.push_str(&format!(
            "- Unclassified gaps: `{}`\n",
            self.replacement_summary.unclassified_entries
        ));
        out.push_str(&format!(
            "- Not-applicable entries: `{}`\n",
            self.replacement_summary.not_applicable_entries
        ));

        out.push_str("\n### Accepted Executable Ports\n\n");
        if self.accepted_executable_ports.is_empty() {
            out.push_str("None.\n");
        } else {
            out.push_str(
                "| Upstream path | Classification | Issue | TrustVc paths | Expected cases |\n",
            );
            out.push_str("|---|---|---|---|---|\n");
            for entry in &self.accepted_executable_ports {
                out.push_str(&format!(
                    "| {} | {} | {} | {} | {} |\n",
                    escape_md(&entry.upstream_path),
                    escape_md(&entry.classification),
                    issue_markdown_link(entry),
                    escape_md(&joined_or_none(&entry.trust_vc_paths)),
                    escape_md(&expected_case_summaries(&entry.expected_cases))
                ));
            }
        }

        out.push_str("\n### Unsupported Gap Partial Evidence\n\n");
        if self.unsupported_gap_evidence.is_empty() {
            out.push_str("None.\n");
        } else {
            out.push_str("| Upstream path | Issue | Partial TrustVc paths | Partial expected cases | Reason |\n");
            out.push_str("|---|---|---|---|---|\n");
            for entry in &self.unsupported_gap_evidence {
                out.push_str(&format!(
                    "| {} | {} | {} | {} | {} |\n",
                    escape_md(&entry.upstream_path),
                    issue_markdown_link(entry),
                    escape_md(&joined_or_none(&entry.trust_vc_paths)),
                    escape_md(&expected_case_summaries(&entry.expected_cases)),
                    escape_md(&entry.reason)
                ));
            }
        }

        out.push_str("\n## Path Buckets\n\n");
        out.push_str(
            "| Bucket | Entries | Missing trust_vc_paths | Missing files | Classifications |\n",
        );
        out.push_str("|---|---:|---:|---:|---|\n");
        for bucket in &self.path_buckets {
            out.push_str(&format!(
                "| {} | {} | {} | {} | {} |\n",
                escape_md(&bucket.bucket),
                bucket.entry_count,
                bucket.missing_trust_vc_paths,
                bucket.missing_trust_vc_path_files,
                escape_md(&format_count_map(&bucket.classification_counts))
            ));
        }

        out.push_str("\n## Missing trust_vc_paths\n\n");
        if self.missing_trust_vc_paths.is_empty() {
            out.push_str("None.\n");
        } else {
            out.push_str("| Upstream path | Classification | Bucket | Owner issue |\n");
            out.push_str("|---|---|---|---|\n");
            for entry in &self.missing_trust_vc_paths {
                out.push_str(&format!(
                    "| {} | {} | {} | {} |\n",
                    escape_md(&entry.upstream_path),
                    escape_md(&entry.classification),
                    escape_md(&entry.path_bucket),
                    escape_md(&entry.owner_issue)
                ));
            }
        }

        out.push_str("\n## Missing trust_vc_path Files\n\n");
        if self.missing_trust_vc_path_files.is_empty() {
            out.push_str("None.\n");
        } else {
            out.push_str("| Upstream path | Classification | trust_vc_path |\n");
            out.push_str("|---|---|---|\n");
            for entry in &self.missing_trust_vc_path_files {
                out.push_str(&format!(
                    "| {} | {} | {} |\n",
                    escape_md(&entry.upstream_path),
                    escape_md(&entry.classification),
                    escape_md(&entry.trust_vc_path)
                ));
            }
        }

        out
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct CorpusPathBucketSummary {
    pub bucket: String,
    pub entry_count: usize,
    pub classification_counts: BTreeMap<String, usize>,
    pub missing_trust_vc_paths: usize,
    pub missing_trust_vc_path_files: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct CorpusTriageEntry {
    pub upstream_path: String,
    pub classification: String,
    pub path_bucket: String,
    pub owner_issue: String,
    pub reason: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct CorpusMissingTrustVcPathFile {
    pub upstream_path: String,
    pub classification: String,
    pub trust_vc_path: String,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct VerusPortScaffoldReport {
    pub schema_version: u32,
    pub manifest_path: String,
    pub output_dir: String,
    pub created_count: usize,
    pub existing_count: usize,
    pub skipped_count: usize,
    pub created: Vec<VerusPortScaffoldEntry>,
    pub existing: Vec<VerusPortScaffoldEntry>,
}

impl VerusPortScaffoldReport {
    pub(crate) fn render_markdown(&self) -> String {
        let mut out = String::new();
        out.push_str("# Verus Port Scaffold Report\n\n");
        out.push_str(&format!("- Manifest: `{}`\n", self.manifest_path));
        out.push_str(&format!("- Output directory: `{}`\n", self.output_dir));
        out.push_str(&format!("- Created stubs: `{}`\n", self.created_count));
        out.push_str(&format!("- Existing stubs: `{}`\n", self.existing_count));
        out.push_str(&format!(
            "- Skipped accepted entries: `{}`\n\n",
            self.skipped_count
        ));

        if !self.created.is_empty() {
            out.push_str("## Created\n\n");
            out.push_str("| Upstream Path | TrustVc Path | Owner |\n");
            out.push_str("|---|---|---|\n");
            for entry in &self.created {
                out.push_str(&format!(
                    "| `{}` | `{}` | `{}` |\n",
                    entry.upstream_path, entry.trust_vc_path, entry.owner_issue
                ));
            }
            out.push('\n');
        }
        if !self.existing.is_empty() {
            out.push_str("## Existing\n\n");
            out.push_str("| Upstream Path | TrustVc Path | Owner |\n");
            out.push_str("|---|---|---|\n");
            for entry in &self.existing {
                out.push_str(&format!(
                    "| `{}` | `{}` | `{}` |\n",
                    entry.upstream_path, entry.trust_vc_path, entry.owner_issue
                ));
            }
            out.push('\n');
        }
        out
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct VerusPortScaffoldEntry {
    pub upstream_path: String,
    pub trust_vc_path: String,
    pub classification: String,
    pub owner_issue: String,
    pub reason: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct TrustVcCorpusRunReport {
    pub attempted_paths: usize,
    pub passed_paths: usize,
    pub failed_paths: usize,
    pub skipped_entries: usize,
    pub results: Vec<TrustVcCorpusRunResult>,
}

impl TrustVcCorpusRunReport {
    fn passed(&self) -> bool {
        self.attempted_paths > 0
            && self.passed_paths == self.attempted_paths
            && self.failed_paths == 0
            && self.skipped_entries == 0
    }

    fn command_mode_paths(&self) -> Vec<&str> {
        self.results
            .iter()
            .filter(|result| result.execution_mode == TrustVcCorpusExecutionMode::Command)
            .map(|result| result.trust_vc_path.as_str())
            .collect()
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct TrustVcCorpusRunResult {
    pub upstream_path: String,
    pub trust_vc_path: String,
    pub trust_vc_paths: Vec<String>,
    #[serde(default = "default_trust_vc_corpus_execution_mode")]
    pub execution_mode: TrustVcCorpusExecutionMode,
    pub status: GateStatus,
    pub detail: Option<String>,
    pub function_count: usize,
    pub expected_case_count: usize,
    pub observed_case_count: usize,
    pub expected_obligation_count: usize,
    pub observed_obligation_count: usize,
    pub expected_case_ids: Vec<String>,
    pub observed_case_ids: Vec<String>,
    pub observed_cases: Vec<TrustVcCorpusObservedCase>,
    pub failures: Vec<String>,
    pub command: Option<CommandResult>,
    #[serde(default)]
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub commands: Vec<CommandResult>,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub(crate) enum TrustVcCorpusExecutionMode {
    DirectSource,
    CargoFixture,
    CargoTrustVcIntegrationTest,
    Command,
}

fn default_trust_vc_corpus_execution_mode() -> TrustVcCorpusExecutionMode {
    TrustVcCorpusExecutionMode::DirectSource
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct TrustVcCorpusObservedCase {
    pub case_id: String,
    pub trust_vc_path: String,
    pub verdict: String,
    pub obligation_count: usize,
    #[serde(default)]
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub obligation_fingerprints: Vec<String>,
    #[serde(default)]
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub diagnostic_context: Vec<String>,
    #[serde(default)]
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub warnings: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct TrustVcCorpusRunCandidate {
    pub upstream_path: String,
    pub classification: String,
    pub evidence_kind: VerusEvidenceKind,
    pub trust_vc_paths: Vec<String>,
    #[serde(default)]
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub trust_vc_check_args: Vec<String>,
    expected_cases: Vec<VerusExpectedCase>,
}

#[derive(Debug)]
pub(crate) struct EvidenceError {
    message: String,
}

impl EvidenceError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for EvidenceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for EvidenceError {}

#[derive(Debug, Clone, Copy, Default)]
struct CorpusLoadOptions {
    refresh_evidence_pins: bool,
}

#[derive(Debug, Clone, Copy)]
struct TrustVcCorpusEvidenceRefreshSummary {
    accepted_entries: usize,
    source_hash_paths: usize,
    obligation_cases: usize,
    obligation_fingerprints: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ScoutExpectedCaseInventory {
    case_id: String,
    expected_verdict: VerusExpectedVerdict,
    min_obligations: usize,
}

#[derive(Debug, Clone)]
struct VerusManifest {
    schema_version: u32,
    upstream_repo: Option<String>,
    upstream_ref: Option<String>,
    test_roots: Vec<String>,
    failing_classifications: BTreeSet<String>,
    entries: Vec<VerusManifestEntry>,
}

#[derive(Debug, Clone, Serialize)]
struct GeneratedVerusManifest {
    schema_version: u32,
    manifest_id: String,
    description: String,
    upstream: GeneratedUpstream,
    gate: GeneratedGate,
    entries: Vec<VerusManifestEntry>,
}

#[derive(Debug, Clone, Serialize)]
struct GeneratedUpstream {
    repo: String,
    #[serde(rename = "ref")]
    upstream_ref: String,
    test_roots: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
struct GeneratedGate {
    missing_entry: String,
    failing_classifications: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct JsonVerusManifest {
    schema_version: u32,
    manifest_id: String,
    description: String,
    upstream: JsonUpstream,
    gate: JsonGate,
    entries: Vec<VerusManifestEntry>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct JsonUpstream {
    repo: String,
    #[serde(rename = "ref")]
    upstream_ref: String,
    test_roots: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct JsonGate {
    missing_entry: String,
    failing_classifications: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct VerusManifestEntry {
    upstream_path: String,
    classification: String,
    #[serde(default)]
    #[serde(skip_serializing_if = "is_default_verus_evidence_kind")]
    evidence_kind: VerusEvidenceKind,
    owner_issue: String,
    reason: String,
    #[serde(default)]
    #[serde(skip_serializing_if = "Vec::is_empty")]
    trust_vc_paths: Vec<String>,
    #[serde(default)]
    #[serde(skip_serializing_if = "Vec::is_empty")]
    trust_vc_source_hashes: Vec<TrustVcSourcePathHash>,
    #[serde(default)]
    #[serde(skip_serializing_if = "Vec::is_empty")]
    trust_vc_check_args: Vec<String>,
    #[serde(default)]
    #[serde(skip_serializing_if = "Vec::is_empty")]
    expected_cases: Vec<VerusExpectedCase>,
    #[serde(default)]
    #[serde(skip_serializing_if = "Vec::is_empty")]
    known_gaps: Vec<String>,
    #[serde(default)]
    #[serde(skip_serializing_if = "String::is_empty")]
    notes: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct VerusExpectedCase {
    case_id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    upstream_case_id: Option<String>,
    #[serde(default)]
    #[serde(skip_serializing_if = "Option::is_none")]
    trust_vc_path: Option<String>,
    expected_verdict: VerusExpectedVerdict,
    min_obligations: usize,
    #[serde(default)]
    #[serde(skip_serializing_if = "Vec::is_empty")]
    obligation_fingerprints: Vec<String>,
    #[serde(default)]
    #[serde(skip_serializing_if = "Vec::is_empty")]
    expected_error_patterns: Vec<String>,
    #[serde(default)]
    #[serde(skip_serializing_if = "Vec::is_empty")]
    expected_rust_diagnostic_pattern_sets: Vec<Vec<String>>,
    #[serde(default)]
    #[serde(skip_serializing_if = "Vec::is_empty")]
    forbidden_diagnostic_patterns: Vec<String>,
    /// Verifier WARNINGS this case must emit, in upstream's order.
    ///
    /// Upstream's `test_verify_one_file!(.. => Ok(()))` arm asserts
    /// `err.warnings.len() == 0`, so an EMPTY list is NOT "unchecked" — it means
    /// the case must emit NO warning at all. A case that declares patterns must
    /// emit exactly that many warnings, the i-th containing the i-th pattern.
    #[serde(default)]
    #[serde(skip_serializing_if = "Vec::is_empty")]
    expected_warning_patterns: Vec<String>,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
enum VerusExpectedVerdict {
    Verified,
    Counterexample,
    Error,
    // Scout-only: trust-vc currently verifies the case, but it is a known parity/soundness
    // blocker. Never valid as accepted-evidence; only appears in unsupported-gap scout cases.
    #[serde(rename = "verified-blocker")]
    VerifiedBlocker,
}

#[derive(Debug, Clone, Copy, Default, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub(crate) enum VerusEvidenceKind {
    #[default]
    ProofObligation,
    CargoTrustVcIntegrationTest,
}

fn is_default_verus_evidence_kind(value: &VerusEvidenceKind) -> bool {
    *value == VerusEvidenceKind::ProofObligation
}

fn evidence_kind_label(value: VerusEvidenceKind) -> &'static str {
    match value {
        VerusEvidenceKind::ProofObligation => "proof_obligation",
        VerusEvidenceKind::CargoTrustVcIntegrationTest => "cargo_trust_vc_integration_test",
    }
}

const VERUS_TEST_ROOT: &str = "source/rust_verify_test/tests";
const VERUS_CARGO_VERUS_TEST_ROOT: &str = "source/cargo-verus/tests";
const REQUIRED_VERUS_TEST_ROOTS: &[&str] = &[VERUS_TEST_ROOT, VERUS_CARGO_VERUS_TEST_ROOT];
const VERUS_CARGO_WRAPPER_TEST_PATH: &str = "source/rust_verify_test/tests/cargo.rs";
const VERUS_REPO_URL: &str = "https://github.com/verus-lang/verus";
const TRUST_VC_REPO_URL: &str = "https://github.com/alabsystems/trust-vc";
const REQUIRED_AY_CRATES: &[&str] = &["ay-core", "ay-dpll", "ay-frontend", "ay-sys"];
const SUPPORTED_TRUST_VC_CHECK_ARGS: &[&str] = &["--no-cheating"];
const DEFAULT_VERUS_TEST_COMMAND: &str =
    "/bin/bash --noprofile --norc -c 'export PATH=\"$(dirname \"$CARGO\"):$PATH\"; git sparse-checkout disable; cd source && ./tools/get-z3.sh && source ../tools/activate && vargo test -p rust_verify_test && cargo test -p cargo-verus --features integration-tests'";
const AY_REPO_URL: &str = "https://github.com/alabsystems/ay";
const DEFAULT_GIT_COMMAND: &str = "/usr/bin/git";
const DEFAULT_SH_COMMAND: &str = "/bin/sh";
const SANITIZED_PATH: &str = "/usr/bin:/bin:/usr/sbin:/sbin:/opt/homebrew/bin:/usr/local/bin";
const CORPUS_BLOCKER_SUMMARY_LIMIT: usize = 5;

/// Active rustup toolchain facts, detected once at runner startup, that the
/// otherwise-hermetic evidence command environment must carry so corpus/gate
/// `cargo`/`rustc` invocations resolve to the SAME toolchain the interactive
/// dev/CI environment uses — the one that accepts Trust's nightly
/// `-Ztrust-verify=off` flag.
///
/// The base `SANITIZED_PATH` deliberately excludes the rustup shim directory
/// (`~/.cargo/bin`) and does not propagate `RUSTUP_TOOLCHAIN`, so without this
/// injection a bare `cargo`/`rustc` resolves to whatever non-rustup compiler
/// sits on the sanitized system PATH (e.g. a Homebrew stable `rustc`), which
/// rejects `-Ztrust-verify=off` and produces spurious corpus failures. The
/// injection also exports `RUSTC` (the active toolchain's rustup `rustc` shim)
/// for tooling that resolves the compiler from the sibling of `$CARGO` rather
/// than from PATH — the cargo-trust-vc integration-test witnesses compile a
/// helper with `rustc -Ztrust-verify=off` and take the sibling of the isolated
/// stable `$CARGO`, which the PATH prepend alone cannot redirect. Both
/// fields are detected DYNAMICALLY from the ambient environment (never
/// hardcoded); when a field cannot be resolved it is left `None` and the
/// pre-existing sanitized behaviour is preserved.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct SanitizedToolchainEnv {
    /// The rustup shim directory (the parent of the `rustup` proxy, i.e.
    /// `CARGO_HOME/bin`). Prepended to PATH so the shim `cargo`/`rustc` win
    /// over any non-rustup compiler on the sanitized system PATH.
    rustup_bin_dir: Option<String>,
    /// The active toolchain name (e.g. `trust`). Exported as `RUSTUP_TOOLCHAIN`
    /// so the shims resolve to it even in cwds without a `rust-toolchain.toml`
    /// (corpus fixtures run in isolated directories that lack the override).
    active_toolchain: Option<String>,
}

static SANITIZED_TOOLCHAIN_ENV: OnceLock<SanitizedToolchainEnv> = OnceLock::new();

/// Detect the active rustup toolchain facts once, at runner startup, from the
/// still-unsanitized ambient process environment. Idempotent: a second call is
/// a no-op (the first-detected value wins for the whole process).
fn init_sanitized_toolchain_env(crate_root: &Path) {
    let _ = SANITIZED_TOOLCHAIN_ENV.set(detect_sanitized_toolchain_env(crate_root));
}

/// The toolchain facts detected at startup, or `None` if `init_...` has not run
/// yet. `sanitized_command_env` uses `get()` (not `get_or_init`) DELIBERATELY:
/// detection itself runs `rustup` through `sanitized_command_env`, so a
/// self-initialising read would re-enter the same `OnceLock` and deadlock.
fn sanitized_toolchain_env() -> Option<&'static SanitizedToolchainEnv> {
    SANITIZED_TOOLCHAIN_ENV.get()
}

fn detect_sanitized_toolchain_env(crate_root: &Path) -> SanitizedToolchainEnv {
    let rustup_bin_dir = detect_rustup_bin_dir();
    let active_toolchain = detect_active_toolchain(crate_root, rustup_bin_dir.as_deref());
    SanitizedToolchainEnv {
        rustup_bin_dir: rustup_bin_dir.map(|dir| dir.to_string_lossy().into_owned()),
        active_toolchain,
    }
}

/// Locate the rustup shim directory (where the `rustup` proxy and its
/// `cargo`/`rustc` shims live). Resolved dynamically, in order: the first
/// entry on the ambient PATH that holds a `rustup` executable, then
/// `$CARGO_HOME/bin`, then `$HOME/.cargo/bin`. Never hardcodes an absolute
/// user path.
fn detect_rustup_bin_dir() -> Option<PathBuf> {
    if let Some(path) = std::env::var_os("PATH") {
        for dir in std::env::split_paths(&path) {
            if dir.as_os_str().is_empty() {
                continue;
            }
            if dir.join("rustup").is_file() {
                return Some(dir);
            }
        }
    }
    if let Some(cargo_home) = std::env::var_os("CARGO_HOME") {
        let dir = PathBuf::from(cargo_home).join("bin");
        if dir.join("rustup").is_file() {
            return Some(dir);
        }
    }
    if let Some(home) = std::env::var_os("HOME") {
        let dir = PathBuf::from(home).join(".cargo").join("bin");
        if dir.join("rustup").is_file() {
            return Some(dir);
        }
    }
    None
}

/// Determine the active toolchain name dynamically: an explicit ambient
/// `RUSTUP_TOOLCHAIN` (captured before the env is sanitized) wins; otherwise
/// ask `rustup show active-toolchain` in the crate root so a repo-local
/// `rust-toolchain.toml` override is honoured.
fn detect_active_toolchain(crate_root: &Path, rustup_bin_dir: Option<&Path>) -> Option<String> {
    if let Some(toolchain) = std::env::var("RUSTUP_TOOLCHAIN")
        .ok()
        .map(|value| value.trim().to_string())
        .filter(|value| !value.is_empty())
    {
        return Some(toolchain);
    }
    let rustup = rustup_bin_dir?.join("rustup");
    let rustup = rustup.to_str()?;
    // Runs via `sanitized_command_env`, which returns the un-injected base env
    // here (the OnceLock is not set yet) — rustup is invoked by absolute path
    // and needs only the passed-through RUSTUP_HOME/HOME.
    let result = run_command(crate_root, rustup, &["show", "active-toolchain"]);
    if result.exit_code != Some(0) {
        return None;
    }
    active_toolchain_name(&result.stdout_tail)
}

/// Parse the toolchain name from `rustup show active-toolchain` output, whose
/// first non-empty line looks like `trust (overridden by '…')` or a bare
/// `trust`. Returns the leading whitespace-delimited token.
fn active_toolchain_name(output: &str) -> Option<String> {
    output
        .lines()
        .map(str::trim)
        .find(|line| !line.is_empty())
        .and_then(|line| line.split_whitespace().next())
        .filter(|name| !name.is_empty())
        .map(str::to_string)
}

fn required_verus_test_roots() -> Vec<String> {
    REQUIRED_VERUS_TEST_ROOTS
        .iter()
        .map(|root| (*root).to_string())
        .collect()
}

pub(crate) fn run_corpus_triage_report(
    args: &EvidenceArgs,
) -> Result<CorpusTriageReport, EvidenceError> {
    let manifest_path = args
        .manifest_path
        .as_deref()
        .ok_or_else(|| EvidenceError::new("no manifest supplied or found"))?;
    let manifest_path = resolve_repo_path(&args.crate_root, manifest_path);
    load_corpus_triage_report(&manifest_path, &args.crate_root)
}

pub(crate) fn run_verus_port_scaffold(
    args: &EvidenceArgs,
) -> Result<VerusPortScaffoldReport, EvidenceError> {
    let manifest_path = args
        .manifest_path
        .as_deref()
        .ok_or_else(|| EvidenceError::new("no manifest supplied or found"))?;
    let manifest_path = resolve_repo_path(&args.crate_root, manifest_path);
    let manifest = load_manifest(&manifest_path)?;
    let output_dir = ensure_repo_local_output_dir(&args.crate_root, &args.port_output_dir)?;
    let manifest_rel = repo_relative_display(&args.crate_root, &manifest_path)?;
    let output_rel = repo_relative_display(&args.crate_root, &output_dir)?;

    let mut created = Vec::new();
    let mut existing = Vec::new();
    let mut skipped_count = 0;
    for entry in &manifest.entries {
        if !matches!(
            entry.classification.as_str(),
            "unsupported-gap" | "unclassified"
        ) {
            skipped_count += 1;
            continue;
        }
        let upstream_rel = scaffold_relative_port_path(&entry.upstream_path, &manifest.test_roots)?;
        let trust_vc_path = join_slash_path(&output_rel, &upstream_rel);
        let stub_path = output_dir.join(&upstream_rel);
        let scaffold_entry = VerusPortScaffoldEntry {
            upstream_path: entry.upstream_path.clone(),
            trust_vc_path,
            classification: entry.classification.clone(),
            owner_issue: entry.owner_issue.clone(),
            reason: entry.reason.clone(),
        };
        if stub_path.exists() {
            existing.push(scaffold_entry);
            continue;
        }
        if let Some(parent) = stub_path.parent() {
            fs::create_dir_all(parent).map_err(|err| {
                EvidenceError::new(format!(
                    "failed to create port scaffold dir `{}`: {err}",
                    parent.display()
                ))
            })?;
        }
        fs::write(&stub_path, render_verus_port_stub(entry)).map_err(|err| {
            EvidenceError::new(format!(
                "failed to write Verus port scaffold `{}`: {err}",
                stub_path.display()
            ))
        })?;
        created.push(scaffold_entry);
    }

    Ok(VerusPortScaffoldReport {
        schema_version: 1,
        manifest_path: manifest_rel,
        output_dir: output_rel,
        created_count: created.len(),
        existing_count: existing.len(),
        skipped_count,
        created,
        existing,
    })
}

pub(crate) fn run_evidence(args: &EvidenceArgs) -> Result<EvidenceReport, EvidenceError> {
    fs::create_dir_all(&args.output_dir).map_err(|err| {
        EvidenceError::new(format!(
            "failed to create evidence output dir `{}`: {err}",
            args.output_dir.display()
        ))
    })?;

    // Detect the active rustup toolchain once, up front, from the still-ambient
    // process environment, so every subsequent sanitized command resolves
    // `cargo`/`rustc` to the toolchain the interactive dev/CI shell uses (the
    // one that accepts Trust's `-Ztrust-verify=off`). Must precede any command
    // that runs `cargo`/`rustc`.
    init_sanitized_toolchain_env(&args.crate_root);

    let initial_dirty = git_dirty(&args.crate_root);
    let trust_vc_head = git_rev_parse(&args.crate_root, "HEAD");
    let ay_manifest_provenance = collect_ay_manifest_provenance(&args.crate_root);
    let pinned_ay_revs = ay_manifest_provenance.pinned_revs.clone();
    let pinned_ay_sources = ay_manifest_provenance.pinned_sources.clone();
    let pinned_ay = ay_manifest_provenance.pinned_rev.clone();
    // Auditable ay identity facts under every Path-backed model;
    // `ay_identity_rev` is the independently read sibling HEAD, not a copy of
    // the manifest pin. Keeping them separate makes disagreement observable.
    let ay_sibling_identity = ay_manifest_provenance.sibling_identity.clone();
    let ay_identity_rev = ay_sibling_identity
        .as_ref()
        .map(|identity| identity.head.clone());
    let ay_lock_source_entries = parse_ay_lock_sources(&args.crate_root.join("Cargo.lock"));
    let ay_lock_sources = ay_lock_sources_by_package(&ay_lock_source_entries);
    let latest_ay = ls_remote_head(AY_REPO_URL);
    let cargo_env = cargo_gate_env(args);
    let verified_ay_root = ay_manifest_provenance
        .sibling_identity
        .as_ref()
        .map(|identity| identity.repo_root.as_path());
    let local_ay_patch_detected = active_local_ay_patch_detected(
        &args.crate_root,
        Some(&cargo_gate_home(args)),
        verified_ay_root,
    );
    let is_latest_private_main = ay_latest_private_main_gate_passes(
        &ay_manifest_provenance,
        latest_ay.as_deref(),
        local_ay_patch_detected,
    );
    let verus_head = args
        .verus_path
        .as_ref()
        .and_then(|path| git_rev_parse(path, "HEAD"));
    let verus_dirty = args.verus_path.as_ref().and_then(|path| git_dirty(path));
    if args.update_verus_tests_manifest {
        update_verus_tests_manifest(args, verus_head.as_deref())?;
    }
    let corpus_path = if args.update_verus_tests_manifest {
        Some(args.canonical_manifest_path.clone())
    } else {
        args.manifest_path
            .as_ref()
            .map(|path| resolve_repo_path(&args.crate_root, path))
    };
    let dirty = initial_dirty.unwrap_or(true);
    let using_canonical_manifest = corpus_path
        .as_deref()
        .map(|path| same_path(path, &args.canonical_manifest_path, &args.crate_root))
        .unwrap_or(false);
    let corpus_load_options = CorpusLoadOptions {
        refresh_evidence_pins: args.refresh_trust_vc_corpus_evidence,
    };
    let corpus = match corpus_path.as_deref() {
        Some(path) => Some(load_corpus_report_with_options(
            path,
            &args.crate_root,
            args.verus_path.as_deref(),
            corpus_load_options,
        )?),
        None => None,
    };
    let cargo_evidence = collect_cargo_evidence(args);
    let mut trust_vc_corpus = None;
    let mut cargo_fixture_preflight_failures: BTreeMap<PathBuf, Vec<String>> = BTreeMap::new();
    let cargo_fixture_lockfile_check = corpus.as_ref().map(|corpus| {
        cargo_fixture_lockfile_check(&args.crate_root, corpus, &ay_manifest_provenance)
    });
    if let Some(check) = &cargo_fixture_lockfile_check {
        extend_fixture_preflight_failures(
            &mut cargo_fixture_preflight_failures,
            &check.fixture_failures,
        );
    }

    let mut gates = Vec::new();
    gates.push(GateResult {
        name: "latest private ay pin".to_string(),
        required: true,
        status: match is_latest_private_main {
            Some(true) => GateStatus::Passed,
            Some(false) | None => GateStatus::Failed,
        },
        detail: Some(format!(
            "pinned={}, latest={}, repo={}, source_model={}, local_patch_detected={}, ay_published={}",
            display_opt(&pinned_ay),
            display_opt(&latest_ay),
            AY_REPO_URL,
            ay_manifest_provenance.source_model.label(),
            local_ay_patch_detected,
            ay_sibling_identity
                .as_ref()
                .map(|identity| identity.published.label())
                .unwrap_or("n/a"),
        )),
        command: None,
    });
    gates.push(cargo_lock_tracked_gate(&args.crate_root));
    gates.push(ay_lock_provenance_gate(
        &ay_manifest_provenance,
        &ay_lock_source_entries,
    ));
    if let Some(check) = &cargo_fixture_lockfile_check {
        gates.push(cargo_fixture_lockfile_gate_from_check(check));
    } else {
        gates.push(skipped_gate(
            "cargo fixture Cargo.lock provenance",
            true,
            "requires a Verus corpus manifest",
        ));
    }
    gates.push(evidence_output_isolated_gate(
        &args.crate_root,
        &args.output_dir,
    ));
    gates.push(evidence_cargo_home_isolated_gate(args));
    gates.push(cargo_command_provenance_gate(
        args.run_trust_vc,
        &cargo_evidence,
    ));
    gates.push(trust_vc_worktree_gate(
        "TrustVc worktree clean before evidence commands",
        &args.crate_root,
        initial_dirty,
    ));
    gates.push(verus_revision_gate(
        args,
        verus_head.as_deref(),
        corpus.as_ref(),
    ));
    gates.push(verus_worktree_gate(args.verus_path.as_deref(), verus_dirty));

    if root_workspace_fetch_required(args, corpus.as_ref()) {
        gates.push(run_gate_with_owned_env(
            "cargo fetch --locked",
            true,
            &args.crate_root,
            &args.cargo_command,
            &["fetch", "--locked"],
            &cargo_env,
        ));
    }
    if args.run_trust_vc_corpus {
        if let Some(corpus) = corpus.as_ref() {
            let fixture_fetch_gates =
                trust_vc_corpus_fixture_fetch_gates(&args.crate_root, corpus, &cargo_env);
            for gate in &fixture_fetch_gates {
                if gate.status == GateStatus::Failed {
                    if let Some(command) = &gate.command {
                        cargo_fixture_preflight_failures
                            .entry(command.cwd.clone())
                            .or_default()
                            .push(gate.detail.clone().unwrap_or_else(|| gate.name.clone()));
                    }
                }
            }
            gates.extend(fixture_fetch_gates);
        }
    }

    if args.run_trust_vc {
        gates.push(run_gate_with_owned_env(
            "cargo check --workspace --locked --offline",
            true,
            &args.crate_root,
            &args.cargo_command,
            &["check", "--workspace", "--locked", "--offline"],
            &cargo_env,
        ));
        gates.push(run_gate_with_owned_env(
            "cargo test --workspace --locked --offline",
            true,
            &args.crate_root,
            &args.cargo_command,
            &["test", "--workspace", "--locked", "--offline"],
            &cargo_env,
        ));
    } else if args.port_manifest_only {
        gates.push(skipped_gate(
            "trust_vc workspace gates",
            false,
            "port_manifest_only requested",
        ));
    } else {
        gates.push(skipped_gate(
            "trust_vc workspace gates",
            true,
            "pass --run-trust_vc to run cargo check/test evidence",
        ));
    }

    if args.run_verus {
        if let Some(verus_path) = &args.verus_path {
            let verus_command = args
                .verus_command
                .as_deref()
                .unwrap_or(DEFAULT_VERUS_TEST_COMMAND);
            gates.push(run_shell_gate(
                "upstream Verus tests",
                true,
                verus_path,
                verus_command,
                &cargo_env,
            ));
        } else {
            gates.push(GateResult {
                name: "upstream Verus tests".to_string(),
                required: true,
                status: GateStatus::Failed,
                detail: Some("--run-verus requires --verus-path".to_string()),
                command: None,
            });
        }
    } else if args.port_manifest_only {
        gates.push(skipped_gate(
            "upstream Verus tests",
            false,
            "port_manifest_only requested",
        ));
    } else {
        gates.push(skipped_gate(
            "upstream Verus tests",
            true,
            "pass --run-verus --verus-path <checkout> to run upstream tests",
        ));
    }

    if let Some(corpus) = &corpus {
        let passed = corpus.upstream_test_count > 0
            && corpus.duplicate_entries.is_empty()
            && corpus.invalid_entries.is_empty()
            && corpus.missing_entries.is_empty()
            && corpus.extra_entries.is_empty()
            && corpus.unsupported_entries.is_empty()
            && corpus.failing_entries.is_empty()
            && corpus.port_path_failures.is_empty()
            && corpus.upstream_case_failures.is_empty()
            && corpus.upstream_case_extraction_gaps.is_empty();
        gates.push(GateResult {
            name: "Verus corpus manifest".to_string(),
            required: true,
            status: if passed {
                GateStatus::Passed
            } else {
                GateStatus::Failed
            },
            detail: Some(verus_corpus_manifest_gate_detail(corpus)),
            command: None,
        });
        gates.push(verus_corpus_root_coverage_gate(corpus));
    } else {
        gates.push(GateResult {
            name: "Verus corpus manifest".to_string(),
            required: true,
            status: GateStatus::Failed,
            detail: Some("no manifest supplied or found".to_string()),
            command: None,
        });
        gates.push(GateResult {
            name: "Verus corpus root coverage".to_string(),
            required: true,
            status: GateStatus::Failed,
            detail: Some("no manifest supplied or found".to_string()),
            command: None,
        });
    }

    if args.strict && args.run_trust_vc && args.run_trust_vc_corpus {
        match &corpus {
            Some(corpus) => gates.push(direct_source_rust_typecheck_gate(
                &args.crate_root,
                &args.output_dir,
                corpus,
                &cargo_env,
            )),
            None => gates.push(GateResult {
                name: "direct-source Rust typecheck".to_string(),
                required: true,
                status: GateStatus::Failed,
                detail: Some(
                    "--run-trust-vc-corpus direct-source typecheck requires a Verus corpus manifest"
                        .to_string(),
                ),
                command: None,
            }),
        }
    } else if args.port_manifest_only {
        gates.push(skipped_gate(
            "direct-source Rust typecheck",
            false,
            "port_manifest_only requested",
        ));
    } else {
        gates.push(skipped_gate(
            "direct-source Rust typecheck",
            args.strict,
            "requires --strict --run-trust_vc --run-trust-vc-corpus",
        ));
    }

    if args.run_trust_vc_corpus {
        gates.push(cargo_trust_vc_executable_provenance_gate(&args.crate_root));
        match &corpus {
            Some(corpus) => {
                let run_report = run_trust_vc_corpus_with_env(
                    &args.crate_root,
                    corpus,
                    args.trust_vc_corpus_command.as_deref(),
                    &cargo_env,
                    &cargo_fixture_preflight_failures,
                );
                gates.push(trust_vc_corpus_gate(&run_report));
                trust_vc_corpus = Some(run_report);
            }
            None => gates.push(GateResult {
                name: "TrustVc corpus execution".to_string(),
                required: true,
                status: GateStatus::Failed,
                detail: Some("--run-trust-vc-corpus requires a Verus corpus manifest".to_string()),
                command: None,
            }),
        }
    } else if args.port_manifest_only {
        gates.push(skipped_gate(
            "TrustVc corpus execution",
            false,
            "port_manifest_only requested",
        ));
    } else {
        gates.push(skipped_gate(
            "TrustVc corpus execution",
            true,
            "pass --run-trust-vc-corpus to verify mapped TrustVc ports",
        ));
    }

    if args.refresh_trust_vc_corpus_evidence {
        let gate = match (corpus_path.as_deref(), corpus.as_ref()) {
            (Some(manifest_path), Some(corpus)) => refresh_trust_vc_corpus_evidence_gate(
                manifest_path,
                corpus,
                trust_vc_corpus.as_ref(),
            ),
            _ => GateResult {
                name: "TrustVc corpus evidence refresh".to_string(),
                required: true,
                status: GateStatus::Failed,
                detail: Some(
                    "--refresh-trust-vc-corpus-evidence requires a Verus corpus manifest"
                        .to_string(),
                ),
                command: None,
            },
        };
        gates.push(gate);
    }

    let final_dirty = git_dirty(&args.crate_root).unwrap_or(true);
    gates.push(trust_vc_worktree_gate(
        "TrustVc worktree clean after evidence commands",
        &args.crate_root,
        Some(final_dirty),
    ));
    let final_verus_dirty = args.verus_path.as_ref().and_then(|path| git_dirty(path));
    gates.push(verus_worktree_gate_named(
        "Verus worktree clean after evidence commands",
        args.verus_path.as_deref(),
        final_verus_dirty,
    ));

    let mut blocking_reasons = Vec::new();
    for gate in &gates {
        if gate.required && gate.status != GateStatus::Passed {
            blocking_reasons.push(format!(
                "{}: {}",
                gate.name,
                gate.detail
                    .as_deref()
                    .unwrap_or("required gate did not pass")
            ));
        }
    }
    if args.port_manifest_only {
        blocking_reasons.push(
            "port-manifest-only validates the corpus layer but cannot prove replacement"
                .to_string(),
        );
    }
    if args.update_verus_tests_manifest {
        blocking_reasons.push("--update-verus-tests-manifest cannot prove replacement".to_string());
    }
    if args.refresh_trust_vc_corpus_evidence {
        blocking_reasons
            .push("--refresh-trust-vc-corpus-evidence cannot prove replacement".to_string());
    }
    if !args.strict {
        blocking_reasons.push("replacement verdict requires --strict".to_string());
    }
    if dirty || final_dirty {
        blocking_reasons.push("replacement evidence requires a clean TrustVc worktree".to_string());
    }
    if args.cargo_command_overridden {
        blocking_reasons.push("--cargo-command override cannot prove replacement".to_string());
    }
    if args.verus_command.is_some() {
        blocking_reasons.push("--verus-command override cannot prove replacement".to_string());
    }
    if args.trust_vc_corpus_command.is_some() {
        blocking_reasons
            .push("--trust-vc-corpus-command override cannot prove replacement".to_string());
    }
    blocking_reasons.extend(evidence_environment_blocking_reasons(args, &cargo_evidence));
    if !using_canonical_manifest {
        blocking_reasons.push(
            "replacement evidence requires canonical evals/verus/verus-tests.json manifest"
                .to_string(),
        );
    }
    if let Some(reason) =
        canonical_manifest_schema_blocking_reason(corpus.as_ref(), using_canonical_manifest)
    {
        blocking_reasons.push(reason);
    }
    if args.strict && !args.run_trust_vc {
        blocking_reasons.push("strict mode requires --run-trust_vc".to_string());
    }
    if args.strict && !args.run_trust_vc_corpus {
        blocking_reasons.push("strict mode requires --run-trust-vc-corpus".to_string());
    }
    if args.strict && !args.run_verus {
        blocking_reasons.push("strict mode requires --run-verus".to_string());
    }

    let replacement_verdict = if blocking_reasons.is_empty() {
        ReplacementVerdict::Proven
    } else {
        ReplacementVerdict::NotProven
    };
    let report = EvidenceReport {
        schema_version: 1,
        generated_unix_seconds: now_unix_seconds(),
        strict: args.strict,
        replacement_verdict,
        repository: RepositoryEvidence {
            trust_vc_head,
            dirty,
            crate_root: args.crate_root.clone(),
        },
        ay: AYEvidence {
            pinned_rev: pinned_ay,
            pinned_revs: pinned_ay_revs,
            pinned_sources: pinned_ay_sources,
            lock_sources: ay_lock_sources,
            lock_source_entries: ay_lock_source_entries,
            latest_private_main: latest_ay,
            is_latest_private_main,
            local_patch_detected: local_ay_patch_detected,
            ay_identity_rev,
            ay_repo_root: ay_sibling_identity
                .as_ref()
                .map(|identity| identity.repo_root.clone()),
            ay_origin_url: ay_sibling_identity
                .as_ref()
                .map(|identity| identity.origin_url.clone()),
            ay_worktree_clean: ay_sibling_identity
                .as_ref()
                .map(|identity| identity.worktree_clean),
            ay_published: ay_sibling_identity
                .as_ref()
                .map(|identity| identity.published.label().to_string()),
        },
        cargo: cargo_evidence,
        verus: VerusEvidence {
            path: args.verus_path.clone(),
            requested_rev: args.verus_rev.clone(),
            head: verus_head,
        },
        gates,
        corpus,
        trust_vc_corpus,
        blocking_reasons,
    };
    write_report_files(args, &report)?;
    Ok(report)
}

fn write_report_files(args: &EvidenceArgs, report: &EvidenceReport) -> Result<(), EvidenceError> {
    let write_json = args.json || !args.markdown;
    let write_markdown = args.markdown || !args.json;

    if write_json {
        let json = serde_json::to_string_pretty(report).map_err(|err| {
            EvidenceError::new(format!("failed to serialize evidence JSON: {err}"))
        })?;
        fs::write(
            args.output_dir.join("replacement-evidence.json"),
            format!("{json}\n"),
        )
        .map_err(|err| EvidenceError::new(format!("failed to write evidence JSON: {err}")))?;
    }
    if write_markdown {
        fs::write(
            args.output_dir.join("replacement-evidence.md"),
            report.render_markdown(),
        )
        .map_err(|err| EvidenceError::new(format!("failed to write evidence markdown: {err}")))?;
    }
    Ok(())
}

fn verus_corpus_manifest_gate_detail(corpus: &VerusCorpusReport) -> String {
    let mut detail = format!(
        "schema v{}, {} upstream tests, {} entries, replacement summary: {} accepted executable entries, {} accepted TrustVc path bindings, {} accepted expected cases, {} unsupported gaps, {} unclassified gaps, {} not-applicable entries, {} accepted entries with known gaps; {} duplicates, {} invalid, {} missing, {} extra, {} unsupported, {} failing classifications, {} port path failures, {} upstream case failures, {} upstream extraction gaps",
        corpus.manifest_schema_version,
        corpus.upstream_test_count,
        corpus.entry_count,
        corpus.replacement_summary.accepted_executable_entries,
        corpus.replacement_summary.accepted_trust_vc_path_count,
        corpus.replacement_summary.accepted_expected_case_count,
        corpus.replacement_summary.unsupported_gap_entries,
        corpus.replacement_summary.unclassified_entries,
        corpus.replacement_summary.not_applicable_entries,
        corpus.replacement_summary.accepted_known_gap_entries,
        corpus.duplicate_entries.len(),
        corpus.invalid_entries.len(),
        corpus.missing_entries.len(),
        corpus.extra_entries.len(),
        corpus.unsupported_entries.len(),
        corpus.failing_entries.len(),
        corpus.port_path_failures.len(),
        corpus.upstream_case_failures.len(),
        corpus.upstream_case_extraction_gaps.len()
    );
    if let Some(summary) = verus_corpus_blocker_summary(corpus) {
        detail.push_str("; blockers: ");
        detail.push_str(&summary);
    }
    detail
}

fn canonical_manifest_schema_blocking_reason(
    corpus: Option<&VerusCorpusReport>,
    using_canonical_manifest: bool,
) -> Option<String> {
    if !using_canonical_manifest {
        return None;
    }
    let Some(corpus) = corpus else {
        return Some(
            "replacement evidence requires canonical evals/verus/verus-tests.json schema_version 2"
                .to_string(),
        );
    };
    if corpus.manifest_schema_version == 2 {
        None
    } else {
        Some(format!(
            "replacement evidence requires canonical evals/verus/verus-tests.json schema_version 2, got {}",
            corpus.manifest_schema_version
        ))
    }
}

fn verus_corpus_root_coverage_gate(corpus: &VerusCorpusReport) -> GateResult {
    let required_roots = required_verus_test_roots();
    let passed = corpus.upstream_test_roots == required_roots;
    GateResult {
        name: "Verus corpus root coverage".to_string(),
        required: true,
        status: if passed {
            GateStatus::Passed
        } else {
            GateStatus::Failed
        },
        detail: Some(format!(
            "manifest roots={:?}, required roots={:?}",
            corpus.upstream_test_roots, required_roots
        )),
        command: None,
    }
}

fn verus_corpus_blocker_summary(corpus: &VerusCorpusReport) -> Option<String> {
    let mut summaries = Vec::new();
    append_limited_blocker_summary(&mut summaries, "duplicates", &corpus.duplicate_entries);
    append_limited_blocker_summary(&mut summaries, "invalid", &corpus.invalid_entries);
    append_limited_blocker_summary(&mut summaries, "missing", &corpus.missing_entries);
    append_limited_blocker_summary(&mut summaries, "extra", &corpus.extra_entries);
    append_limited_blocker_summary(&mut summaries, "unsupported", &corpus.unsupported_entries);
    append_limited_blocker_summary(
        &mut summaries,
        "failing classifications",
        &corpus.failing_entries,
    );
    append_limited_blocker_summary(
        &mut summaries,
        "port path failures",
        &corpus.port_path_failures,
    );
    append_limited_blocker_summary(
        &mut summaries,
        "upstream case failures",
        &corpus.upstream_case_failures,
    );
    append_limited_blocker_summary(
        &mut summaries,
        "upstream extraction gaps",
        &corpus.upstream_case_extraction_gaps,
    );
    if summaries.is_empty() {
        None
    } else {
        Some(summaries.join("; "))
    }
}

fn append_limited_blocker_summary(summaries: &mut Vec<String>, label: &str, entries: &[String]) {
    if entries.is_empty() {
        return;
    }
    let mut sample = entries
        .iter()
        .take(CORPUS_BLOCKER_SUMMARY_LIMIT)
        .cloned()
        .collect::<Vec<_>>();
    let remaining = entries.len().saturating_sub(sample.len());
    if remaining > 0 {
        sample.push(format!("{remaining} more"));
    }
    summaries.push(format!("{label}: {}", sample.join(" | ")));
}

fn run_gate_with_owned_env(
    name: &str,
    required: bool,
    cwd: &Path,
    program: &str,
    args: &[&str],
    env: &[(String, String)],
) -> GateResult {
    let env = env
        .iter()
        .map(|(key, value)| (key.as_str(), value.as_str()))
        .collect::<Vec<_>>();
    let command = run_command_with_env(cwd, program, args, &env);
    gate_from_command_result(name, required, command)
}

fn root_workspace_fetch_required(args: &EvidenceArgs, corpus: Option<&VerusCorpusReport>) -> bool {
    if args.run_trust_vc {
        return true;
    }
    if !args.run_trust_vc_corpus || args.trust_vc_corpus_command.is_some() {
        return false;
    }
    let Some(corpus) = corpus else {
        return false;
    };
    corpus.run_candidates.iter().any(|candidate| {
        candidate_has_cargo_trust_vc_integration_test_path(&args.crate_root, candidate)
    })
}

fn borrowed_env(env: &[(String, String)]) -> Vec<(&str, &str)> {
    env.iter()
        .map(|(key, value)| (key.as_str(), value.as_str()))
        .collect()
}

fn gate_from_command_result(name: &str, required: bool, command: CommandResult) -> GateResult {
    GateResult {
        name: name.to_string(),
        required,
        status: gate_status_from_exit(command.exit_code),
        detail: command_result_detail(&command),
        command: Some(command),
    }
}

fn cargo_gate_env(args: &EvidenceArgs) -> Vec<(String, String)> {
    vec![
        ("CARGO".to_string(), args.cargo_command.clone()),
        (
            "PATH".to_string(),
            cargo_gate_path(&args.cargo_command).to_string(),
        ),
        (
            "CARGO_HOME".to_string(),
            cargo_gate_home(args).to_string_lossy().into_owned(),
        ),
    ]
}

fn cargo_gate_home(args: &EvidenceArgs) -> PathBuf {
    args.output_dir.join("cargo-home")
}

fn cargo_gate_path(cargo_command: &str) -> String {
    cargo_gate_path_with(
        cargo_command,
        sanitized_toolchain_env().and_then(|t| t.rustup_bin_dir.as_deref()),
    )
}

/// Build the cargo-gate PATH: the cargo command's own directory prepended to
/// the sanitized system PATH (so a rustup `cargo` can execute its sibling
/// `rustc`), with the detected rustup shim directory prepended AHEAD of that
/// (so the trust shim `rustc` wins even when the resolved default `cargo` lives
/// in a non-rustup directory such as Homebrew's). Pure over `rustup_bin_dir`
/// for unit-testability.
fn cargo_gate_path_with(cargo_command: &str, rustup_bin_dir: Option<&str>) -> String {
    let base = Path::new(cargo_command)
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .map(|parent| format!("{}:{SANITIZED_PATH}", parent.display()))
        .unwrap_or_else(|| SANITIZED_PATH.to_string());
    match rustup_bin_dir {
        Some(dir) => prepend_path_dir(dir, &base),
        None => base,
    }
}

fn run_shell_gate(
    name: &str,
    required: bool,
    cwd: &Path,
    shell_command: &str,
    env: &[(String, String)],
) -> GateResult {
    run_gate_with_owned_env(
        name,
        required,
        cwd,
        DEFAULT_SH_COMMAND,
        &["-c", shell_command],
        env,
    )
}

fn verus_revision_gate(
    args: &EvidenceArgs,
    verus_head: Option<&str>,
    corpus: Option<&VerusCorpusReport>,
) -> GateResult {
    if let (Some(cli_rev), Some(manifest_rev)) = (
        args.verus_rev.as_deref(),
        corpus.and_then(|corpus| corpus.upstream_ref.as_deref()),
    ) {
        if cli_rev != manifest_rev {
            return GateResult {
                name: "Verus revision pin".to_string(),
                required: true,
                status: GateStatus::Failed,
                detail: Some(format!(
                    "--verus-rev {cli_rev} does not match manifest upstream.ref {manifest_rev}"
                )),
                command: None,
            };
        }
    }
    let required_rev = args
        .verus_rev
        .as_deref()
        .or_else(|| corpus.and_then(|corpus| corpus.upstream_ref.as_deref()));
    let Some(required_rev) = required_rev else {
        return GateResult {
            name: "Verus revision pin".to_string(),
            required: true,
            status: GateStatus::Failed,
            detail: Some("no --verus-rev or manifest upstream.ref supplied".to_string()),
            command: None,
        };
    };
    if required_rev.trim().is_empty()
        || required_rev.contains("PIN_UPSTREAM_VERUS_COMMIT")
        || required_rev == "main"
    {
        return GateResult {
            name: "Verus revision pin".to_string(),
            required: true,
            status: GateStatus::Failed,
            detail: Some(format!(
                "Verus revision must be a concrete commit, got `{required_rev}`"
            )),
            command: None,
        };
    }
    let Some(verus_head) = verus_head else {
        return GateResult {
            name: "Verus revision pin".to_string(),
            required: true,
            status: GateStatus::Failed,
            detail: Some("--verus-path is required to verify the Verus revision".to_string()),
            command: None,
        };
    };
    let passed = verus_head == required_rev;
    GateResult {
        name: "Verus revision pin".to_string(),
        required: true,
        status: if passed {
            GateStatus::Passed
        } else {
            GateStatus::Failed
        },
        detail: Some(format!("required={required_rev}, verus_head={verus_head}")),
        command: None,
    }
}

fn verus_worktree_gate(verus_path: Option<&Path>, dirty: Option<bool>) -> GateResult {
    verus_worktree_gate_named("Verus worktree clean", verus_path, dirty)
}

fn verus_worktree_gate_named(
    name: &str,
    verus_path: Option<&Path>,
    dirty: Option<bool>,
) -> GateResult {
    let Some(path) = verus_path else {
        return GateResult {
            name: name.to_string(),
            required: true,
            status: GateStatus::Failed,
            detail: Some("--verus-path is required to verify a clean Verus worktree".to_string()),
            command: None,
        };
    };
    let Some(dirty) = dirty else {
        return GateResult {
            name: name.to_string(),
            required: true,
            status: GateStatus::Failed,
            detail: Some(format!(
                "could not verify clean Verus git worktree at `{}`",
                path.display()
            )),
            command: None,
        };
    };
    GateResult {
        name: name.to_string(),
        required: true,
        status: if dirty {
            GateStatus::Failed
        } else {
            GateStatus::Passed
        },
        detail: Some(format!("dirty={dirty}, path={}", path.display())),
        command: None,
    }
}

fn trust_vc_worktree_gate(name: &str, path: &Path, dirty: Option<bool>) -> GateResult {
    let Some(dirty) = dirty else {
        return GateResult {
            name: name.to_string(),
            required: true,
            status: GateStatus::Failed,
            detail: Some(format!(
                "could not verify clean TrustVc git worktree at `{}`",
                path.display()
            )),
            command: None,
        };
    };
    GateResult {
        name: name.to_string(),
        required: true,
        status: if dirty {
            GateStatus::Failed
        } else {
            GateStatus::Passed
        },
        detail: Some(format!("dirty={dirty}, path={}", path.display())),
        command: None,
    }
}

fn ay_lock_provenance_gate(
    provenance: &AYManifestProvenance,
    lock_sources: &[AYLockSourceEntry],
) -> GateResult {
    let mut failures = Vec::new();
    let Some(pinned_rev) = provenance.pinned_rev.as_deref() else {
        failures.push("no common ay pin available from Cargo.toml".to_string());
        return GateResult {
            name: "Cargo.lock ay provenance".to_string(),
            required: true,
            status: GateStatus::Failed,
            detail: Some(failures.join("; ")),
            command: None,
        };
    };
    if lock_sources.is_empty() {
        failures.push("Cargo.lock has no ay package source entries".to_string());
    }
    for crate_name in REQUIRED_AY_CRATES {
        if !lock_sources
            .iter()
            .any(|entry| entry.package_name == *crate_name)
        {
            failures.push(format!("missing Cargo.lock entry for {crate_name}"));
        }
    }
    for entry in lock_sources {
        match entry.source.as_deref() {
            Some(source) if ay_lock_source_matches_pin(source, pinned_rev) => {}
            None if provenance.source_model.has_verified_sibling_path() => {}
            Some(source) => failures.push(format!(
                "{} source does not match pin: {source}",
                entry.package_name
            )),
            None => failures.push(format!("{} has no Cargo.lock source", entry.package_name)),
        }
    }
    GateResult {
        name: "Cargo.lock ay provenance".to_string(),
        required: true,
        status: if failures.is_empty() {
            GateStatus::Passed
        } else {
            GateStatus::Failed
        },
        detail: Some(if failures.is_empty() {
            if provenance.source_model.has_verified_sibling_path() {
                format!(
                    "{} ay package entries match verified sibling-path ay repo at {pinned_rev}",
                    lock_sources.len()
                )
            } else {
                format!(
                    "{} ay package sources match {pinned_rev}",
                    lock_sources.len()
                )
            }
        } else {
            failures.join("; ")
        }),
        command: None,
    }
}

#[cfg(test)]
fn cargo_fixture_lockfile_gate(
    crate_root: &Path,
    corpus: &VerusCorpusReport,
    provenance: &AYManifestProvenance,
) -> GateResult {
    let check = cargo_fixture_lockfile_check(crate_root, corpus, provenance);
    cargo_fixture_lockfile_gate_from_check(&check)
}

#[derive(Debug, Clone)]
struct CargoFixtureLockfileCheck {
    checked: usize,
    ay_checked: usize,
    failures: Vec<String>,
    fixture_failures: BTreeMap<PathBuf, Vec<String>>,
}

fn cargo_fixture_lockfile_check(
    crate_root: &Path,
    corpus: &VerusCorpusReport,
    provenance: &AYManifestProvenance,
) -> CargoFixtureLockfileCheck {
    let mut fixture_roots = BTreeMap::new();
    let mut failures = Vec::new();
    let mut fixture_failures: BTreeMap<PathBuf, Vec<String>> = BTreeMap::new();
    for candidate in &corpus.run_candidates {
        for trust_vc_path in &candidate.trust_vc_paths {
            match validate_repo_trust_vc_path(crate_root, trust_vc_path) {
                Ok(path) if is_cargo_fixture_root(&path) => {
                    fixture_roots.insert(path, trust_vc_path.clone());
                }
                Ok(_) => {}
                Err(error) => failures.push(error),
            }
        }
    }

    let mut checked = 0usize;
    let mut ay_checked = 0usize;
    for (fixture_root, trust_vc_path) in fixture_roots {
        checked += 1;
        let manifest_path = fixture_root.join("Cargo.toml");
        let manifest_rel = git_relative_path(crate_root, &manifest_path);
        match git_path_tracked(crate_root, &manifest_path) {
            Some(true) => {}
            Some(false) => {
                let failure = format!(
                    "{} must be tracked by git so fixture evidence cannot depend on ignored or untracked package manifests",
                    manifest_rel.display()
                );
                push_fixture_preflight_failure(
                    &mut failures,
                    &mut fixture_failures,
                    &fixture_root,
                    failure,
                );
            }
            None => {
                let failure = format!(
                    "could not verify git tracking status for {}",
                    manifest_rel.display()
                );
                push_fixture_preflight_failure(
                    &mut failures,
                    &mut fixture_failures,
                    &fixture_root,
                    failure,
                );
            }
        }

        let lock_path = fixture_root.join("Cargo.lock");
        let lock_rel = git_relative_path(crate_root, &lock_path);
        if !lock_path.is_file() {
            let failure = format!(
                "{trust_vc_path}: cargo fixture must include Cargo.lock for locked offline evidence"
            );
            push_fixture_preflight_failure(
                &mut failures,
                &mut fixture_failures,
                &fixture_root,
                failure,
            );
            continue;
        }
        match git_path_tracked(crate_root, &lock_path) {
            Some(true) => {}
            Some(false) => {
                let failure = format!(
                    "{} must be tracked by git so fixture evidence cannot depend on ignored or untracked resolution state",
                    lock_rel.display()
                );
                push_fixture_preflight_failure(
                    &mut failures,
                    &mut fixture_failures,
                    &fixture_root,
                    failure,
                );
            }
            None => {
                let failure = format!(
                    "could not verify git tracking status for {}",
                    lock_rel.display()
                );
                push_fixture_preflight_failure(
                    &mut failures,
                    &mut fixture_failures,
                    &fixture_root,
                    failure,
                );
            }
        }

        let lock_sources = parse_ay_lock_sources(&lock_path);
        if !lock_sources.is_empty() {
            ay_checked += 1;
            if let Some(pinned_rev) = provenance.pinned_rev.as_deref() {
                let mismatch = fixture_ay_lock_mismatch_detail(
                    &lock_rel,
                    &lock_sources,
                    pinned_rev,
                    provenance.source_model.has_verified_sibling_path(),
                );
                if let Some(mismatch) = mismatch {
                    push_fixture_preflight_failure(
                        &mut failures,
                        &mut fixture_failures,
                        &fixture_root,
                        mismatch,
                    );
                }
            } else {
                let failure = format!(
                    "{} contains ay package sources but root Cargo.toml has no common ay pin",
                    lock_rel.display()
                );
                push_fixture_preflight_failure(
                    &mut failures,
                    &mut fixture_failures,
                    &fixture_root,
                    failure,
                );
            }
        }
    }

    CargoFixtureLockfileCheck {
        checked,
        ay_checked,
        failures,
        fixture_failures,
    }
}

fn cargo_fixture_lockfile_gate_from_check(check: &CargoFixtureLockfileCheck) -> GateResult {
    GateResult {
        name: "cargo fixture Cargo.lock provenance".to_string(),
        required: true,
        status: if check.failures.is_empty() {
            GateStatus::Passed
        } else {
            GateStatus::Failed
        },
        detail: Some(if check.failures.is_empty() {
            format!(
                "{checked} cargo fixture Cargo.lock file(s) are tracked; {ay_checked} contain ay sources matching the root pin",
                checked = check.checked,
                ay_checked = check.ay_checked,
            )
        } else {
            check.failures.join("; ")
        }),
        command: None,
    }
}

fn push_fixture_preflight_failure(
    failures: &mut Vec<String>,
    fixture_failures: &mut BTreeMap<PathBuf, Vec<String>>,
    fixture_root: &Path,
    failure: String,
) {
    failures.push(failure.clone());
    fixture_failures
        .entry(fixture_root.to_path_buf())
        .or_default()
        .push(failure);
}

fn extend_fixture_preflight_failures(
    target: &mut BTreeMap<PathBuf, Vec<String>>,
    source: &BTreeMap<PathBuf, Vec<String>>,
) {
    for (fixture_root, failures) in source {
        target
            .entry(fixture_root.clone())
            .or_default()
            .extend(failures.iter().cloned());
    }
}

fn fixture_ay_lock_mismatch_detail(
    lock_rel: &Path,
    lock_sources: &[AYLockSourceEntry],
    pinned_rev: &str,
    path_model: bool,
) -> Option<String> {
    // Under the Path model, the root `[patch."…ay.git"]` redirects every ay
    // crate to the verified `../ay` sibling regardless of what each fixture's
    // Cargo.lock records, so a fixture's ay source (null/path AND git+rev) is
    // irrelevant to which ay actually ran. The binding lives in the single root
    // Path identity, not independently in each fixture lockfile. Accept any
    // recorded source; canonical Git-source fixture locks are still required
    // by the neutral/config-isolated reproducibility lane.
    if path_model {
        return None;
    }
    let mut missing_sources = Vec::new();
    let mut stale_revs = BTreeSet::new();
    let mut malformed_sources = 0usize;
    for entry in lock_sources {
        match entry.source.as_deref() {
            Some(source) if ay_lock_source_matches_pin(source, pinned_rev) => {}
            Some(source) => {
                if let Some(rev) = ay_lock_source_observed_rev(source) {
                    stale_revs.insert(rev.to_string());
                } else {
                    malformed_sources += 1;
                }
            }
            None => missing_sources.push(entry.package_name.as_str()),
        }
    }
    if stale_revs.is_empty() && malformed_sources == 0 && missing_sources.is_empty() {
        return None;
    }

    let mut parts = Vec::new();
    if !stale_revs.is_empty() {
        parts.push(format!(
            "observed ay rev(s) {}",
            stale_revs.into_iter().collect::<Vec<_>>().join(", ")
        ));
    }
    if malformed_sources > 0 {
        parts.push(format!(
            "{malformed_sources} ay source entr{} did not include an observed rev",
            if malformed_sources == 1 { "y" } else { "ies" }
        ));
    }
    if !missing_sources.is_empty() {
        parts.push(format!("missing source for {}", missing_sources.join(", ")));
    }
    Some(format!(
        "{}: ay lock provenance does not match root ay pin {pinned_rev}: {}",
        lock_rel.display(),
        parts.join("; ")
    ))
}

fn cargo_command_provenance_gate(run_trust_vc: bool, evidence: &CargoEvidence) -> GateResult {
    if !run_trust_vc {
        return skipped_gate(
            "Cargo command provenance",
            false,
            "pass --run-trust_vc to require cargo command provenance",
        );
    }
    GateResult {
        name: "Cargo command provenance".to_string(),
        required: true,
        status: if evidence.failures.is_empty() {
            GateStatus::Passed
        } else {
            GateStatus::Failed
        },
        detail: Some(if evidence.failures.is_empty() {
            if evidence.default_rustup_cargo {
                format!(
                    "default rustup cargo verified: command={}, toolchain={}, cargo_hash={}, toolchain_cargo_hash={}",
                    evidence.command,
                    display_opt(&evidence.rustup_active_toolchain),
                    display_opt(&evidence.cargo_proxy_sha256),
                    display_opt(&evidence.toolchain_cargo_sha256)
                )
            } else {
                format!(
                    "absolute cargo command accepted outside HOME with executable hash: command={}, canonical={}, cargo_hash={}",
                    evidence.command,
                    display_path_opt(&evidence.canonical_command),
                    display_opt(&evidence.cargo_proxy_sha256)
                )
            }
        } else {
            evidence.failures.join("; ")
        }),
        command: None,
    }
}

fn cargo_trust_vc_executable_provenance_gate(crate_root: &Path) -> GateResult {
    cargo_trust_vc_executable_provenance_gate_with_build_head(crate_root, TVC_BUILD_GIT_HEAD)
}

fn cargo_trust_vc_executable_provenance_gate_with_build_head(
    crate_root: &Path,
    build_git_head: &str,
) -> GateResult {
    let mut failures = Vec::new();
    let exe = match current_trust_vc_binary() {
        Ok(path) => path,
        Err(error) => {
            failures.push(error);
            PathBuf::new()
        }
    };
    let canonical_root = crate_root.canonicalize().ok();
    let canonical_exe = if exe.as_os_str().is_empty() {
        None
    } else {
        match exe.canonicalize() {
            Ok(path) => Some(path),
            Err(error) => {
                failures.push(format!(
                    "failed to canonicalize current cargo-trust-vc executable `{}`: {error}",
                    exe.display()
                ));
                None
            }
        }
    };
    let exe_hash = if let Some(path) = canonical_exe.as_deref() {
        match source_file_sha256(path) {
            Ok(hash) => Some(hash),
            Err(error) => {
                failures.push(format!(
                    "failed to hash current cargo-trust-vc executable `{}`: {error}",
                    path.display()
                ));
                None
            }
        }
    } else {
        None
    };
    if let (Some(root), Some(exe)) = (canonical_root.as_deref(), canonical_exe.as_deref()) {
        let target_dir = root.join("target");
        if !exe.starts_with(&target_dir) {
            failures.push(format!(
                "replacement corpus execution must use the repo-built cargo-trust-vc binary under `{}`, got `{}`",
                target_dir.display(),
                exe.display()
            ));
        }
        match git_rev_parse(root, "HEAD") {
            Some(head) if build_git_head == "unknown" => {
                failures.push(format!(
                    "cargo-trust-vc executable lacks embedded build git HEAD; repository HEAD is {head}"
                ));
            }
            Some(head) if head != build_git_head => {
                failures.push(format!(
                    "cargo-trust-vc executable was built from {build_git_head}, but claimed repository HEAD is {head}; rebuild cargo-trust-vc before generating replacement evidence"
                ));
            }
            Some(_) => {}
            None => failures.push(format!(
                "failed to resolve TrustVc repository HEAD under `{}`",
                root.display()
            )),
        }
    } else if canonical_root.is_none() {
        failures.push(format!(
            "failed to canonicalize TrustVc repo root `{}`",
            crate_root.display()
        ));
    }
    let exe_display = canonical_exe
        .as_deref()
        .map(|path| {
            canonical_root
                .as_deref()
                .and_then(|root| path.strip_prefix(root).ok())
                .unwrap_or(path)
                .display()
                .to_string()
        })
        .unwrap_or_else(|| "unavailable".to_string());
    GateResult {
        name: "cargo-trust-vc executable provenance".to_string(),
        required: true,
        status: if failures.is_empty() {
            GateStatus::Passed
        } else {
            GateStatus::Failed
        },
        detail: Some(if failures.is_empty() {
            format!(
                "current_exe={}, executable_hash={}, build_git_head={}",
                exe_display,
                display_opt(&exe_hash),
                build_git_head
            )
        } else {
            failures.join("; ")
        }),
        command: None,
    }
}

fn collect_cargo_evidence(args: &EvidenceArgs) -> CargoEvidence {
    let command_path = Path::new(&args.cargo_command);
    let canonical_command = command_path.canonicalize().ok();
    let mut evidence = CargoEvidence {
        command: args.cargo_command.clone(),
        command_overridden: args.cargo_command_overridden,
        canonical_command,
        default_rustup_cargo: false,
        rustup_command: None,
        rustup_active_toolchain: None,
        rustup_which_cargo: None,
        cargo_proxy_sha256: None,
        rustup_sha256: None,
        toolchain_cargo_sha256: None,
        failures: Vec::new(),
        rustup_show_active_toolchain: None,
        rustup_which_cargo_command: None,
    };

    if !args.run_trust_vc {
        return evidence;
    }
    if args.cargo_command_overridden {
        evidence
            .failures
            .push("--cargo-command override cannot prove replacement".to_string());
    }
    if !command_path.is_absolute() {
        evidence.failures.push(format!(
            "replacement evidence requires an absolute default cargo command, got `{}`",
            args.cargo_command
        ));
        return evidence;
    }
    if !cargo_command_is_home_relative(&args.cargo_command) {
        match source_file_sha256(command_path) {
            Ok(hash) => evidence.cargo_proxy_sha256 = Some(hash),
            Err(err) => evidence.failures.push(format!(
                "failed to hash absolute cargo command `{}`: {err}",
                command_path.display()
            )),
        }
        return evidence;
    }

    let Some(home) = std::env::var_os("HOME").map(PathBuf::from) else {
        evidence
            .failures
            .push("HOME is required to prove rustup cargo provenance".to_string());
        return evidence;
    };
    let home_cargo = standard_home_cargo_path(&home);
    if !same_filesystem_path(command_path, &home_cargo) {
        evidence.failures.push(format!(
            "cargo under HOME must be the default rustup cargo path `{}`",
            home_cargo.display()
        ));
        return evidence;
    }
    evidence.default_rustup_cargo = true;
    if !is_symlink_to_rustup(command_path, &home) {
        evidence.failures.push(format!(
            "default HOME cargo must be the rustup shim symlink `{}` -> `rustup`",
            home_cargo.display()
        ));
    }
    match source_file_sha256(command_path) {
        Ok(hash) => evidence.cargo_proxy_sha256 = Some(hash),
        Err(err) => evidence.failures.push(format!(
            "failed to hash default rustup cargo `{}`: {err}",
            command_path.display()
        )),
    }

    let rustup_command = home.join(".cargo").join("bin").join("rustup");
    evidence.rustup_command = Some(rustup_command.clone());
    match source_file_sha256(&rustup_command) {
        Ok(hash) => evidence.rustup_sha256 = Some(hash),
        Err(err) => evidence.failures.push(format!(
            "failed to hash rustup command `{}`: {err}",
            rustup_command.display()
        )),
    }
    let Some(rustup_program) = rustup_command.to_str() else {
        evidence
            .failures
            .push("rustup command path is not valid UTF-8".to_string());
        return evidence;
    };

    let active_toolchain_command = run_command(
        &args.crate_root,
        rustup_program,
        &["show", "active-toolchain"],
    );
    if active_toolchain_command.exit_code == Some(0) {
        let active_toolchain = active_toolchain_command
            .stdout_tail
            .split_whitespace()
            .next()
            .map(str::to_string);
        if let Some(active_toolchain) = active_toolchain {
            evidence.rustup_active_toolchain = Some(active_toolchain);
        } else {
            evidence
                .failures
                .push("rustup active toolchain output was empty".to_string());
        }
    } else {
        evidence.failures.push(format!(
            "rustup show active-toolchain failed with exit {:?}",
            active_toolchain_command.exit_code
        ));
    }
    evidence.rustup_show_active_toolchain = Some(active_toolchain_command);

    let rustup_which_command = run_command(&args.crate_root, rustup_program, &["which", "cargo"]);
    if rustup_which_command.exit_code == Some(0) {
        let which_cargo = PathBuf::from(rustup_which_command.stdout_tail.trim());
        evidence.rustup_which_cargo = Some(which_cargo.clone());
        if let Some(active_toolchain) = evidence.rustup_active_toolchain.as_deref() {
            let rustup_home = std::env::var_os("RUSTUP_HOME")
                .map(PathBuf::from)
                .unwrap_or_else(|| home.join(".rustup"));
            let default_rustup_home = home.join(".rustup");
            if !same_filesystem_path(&rustup_home, &default_rustup_home) {
                evidence.failures.push(format!(
                    "RUSTUP_HOME must be unset or the default `{}` for replacement evidence",
                    default_rustup_home.display()
                ));
            }
            if !rustup_toolchain_cargo_matches(&which_cargo, &rustup_home, active_toolchain) {
                evidence.failures.push(format!(
                    "rustup which cargo `{}` is not under `{}` for active toolchain `{}`",
                    which_cargo.display(),
                    rustup_home.join("toolchains").display(),
                    active_toolchain
                ));
            }
            match source_file_sha256(&which_cargo) {
                Ok(hash) => evidence.toolchain_cargo_sha256 = Some(hash),
                Err(err) => evidence.failures.push(format!(
                    "failed to hash rustup toolchain cargo `{}`: {err}",
                    which_cargo.display()
                )),
            }
        }
    } else {
        evidence.failures.push(format!(
            "rustup which cargo failed with exit {:?}",
            rustup_which_command.exit_code
        ));
    }
    evidence.rustup_which_cargo_command = Some(rustup_which_command);

    evidence
}

fn cargo_lock_tracked_gate(crate_root: &Path) -> GateResult {
    match git_path_tracked(crate_root, Path::new("Cargo.lock")) {
        Some(true) => GateResult {
            name: "Cargo.lock tracked by git".to_string(),
            required: true,
            status: GateStatus::Passed,
            detail: Some("Cargo.lock is part of the claimed TrustVc commit".to_string()),
            command: None,
        },
        Some(false) => GateResult {
            name: "Cargo.lock tracked by git".to_string(),
            required: true,
            status: GateStatus::Failed,
            detail: Some(
                "Cargo.lock must be tracked so --locked evidence cannot depend on a local ignored file"
                    .to_string(),
            ),
            command: None,
        },
        None => GateResult {
            name: "Cargo.lock tracked by git".to_string(),
            required: true,
            status: GateStatus::Failed,
            detail: Some("could not verify Cargo.lock git tracking status".to_string()),
            command: None,
        },
    }
}

fn evidence_output_isolated_gate(crate_root: &Path, output_dir: &Path) -> GateResult {
    let resolved_output = resolve_repo_path(crate_root, output_dir);
    let output_inside_repo = path_starts_with(&resolved_output, crate_root);
    let all_outputs_ignored = if output_inside_repo {
        let output_dir_ignored = git_path_ignored(crate_root, &resolved_output);
        let json_ignored = output_dir_ignored
            || git_path_ignored(
                crate_root,
                &resolved_output.join("replacement-evidence.json"),
            );
        let markdown_ignored = output_dir_ignored
            || git_path_ignored(crate_root, &resolved_output.join("replacement-evidence.md"));
        json_ignored && markdown_ignored
    } else {
        true
    };
    GateResult {
        name: "Evidence output path isolated".to_string(),
        required: true,
        status: if all_outputs_ignored {
            GateStatus::Passed
        } else {
            GateStatus::Failed
        },
        detail: Some(if output_inside_repo {
            if all_outputs_ignored {
                format!(
                    "output_dir={} is inside the repo but all generated report files are ignored by git",
                    output_dir.display()
                )
            } else {
                format!(
                    "output_dir={} is inside the repo and not all generated report files are git-ignored; use an ignored or external output path",
                    output_dir.display()
                )
            }
        } else {
            format!("output_dir={} is outside the repo", output_dir.display())
        }),
        command: None,
    }
}

fn evidence_cargo_home_isolated_gate(args: &EvidenceArgs) -> GateResult {
    if !(args.run_trust_vc || args.run_trust_vc_corpus || args.run_verus) {
        return skipped_gate(
            "Evidence Cargo home isolated",
            false,
            "no subprocess gates requested",
        );
    }
    let cargo_home = cargo_gate_home(args);
    let config_paths = cargo_home_config_paths(&cargo_home);
    let active_configs = config_paths
        .iter()
        .filter(|path| cargo_config_has_effective_lines(path))
        .map(|path| path.display().to_string())
        .collect::<Vec<_>>();
    GateResult {
        name: "Evidence Cargo home isolated".to_string(),
        required: true,
        status: if active_configs.is_empty() {
            GateStatus::Passed
        } else {
            GateStatus::Failed
        },
        detail: Some(if active_configs.is_empty() {
            format!(
                "CARGO_HOME={} has no active config file; subprocesses use this isolated home",
                cargo_home.display()
            )
        } else {
            format!(
                "isolated CARGO_HOME={} must not contain Cargo config files: {}",
                cargo_home.display(),
                active_configs.join(", ")
            )
        }),
        command: None,
    }
}

fn skipped_gate(name: &str, required: bool, detail: &str) -> GateResult {
    GateResult {
        name: name.to_string(),
        required,
        status: GateStatus::Skipped,
        detail: Some(detail.to_string()),
        command: None,
    }
}

fn trust_vc_corpus_gate(report: &TrustVcCorpusRunReport) -> GateResult {
    let command_mode_paths = report.command_mode_paths();
    let command_mode_detail = if command_mode_paths.is_empty() {
        String::new()
    } else {
        format!(
            "; command-mode path(s) [{}] are ad hoc checks and cannot satisfy pinned expected-case/fingerprint corpus evidence",
            command_mode_paths.join(", ")
        )
    };
    GateResult {
        name: "TrustVc corpus execution".to_string(),
        required: true,
        status: if report.passed() && command_mode_paths.is_empty() {
            GateStatus::Passed
        } else {
            GateStatus::Failed
        },
        detail: Some(format!(
            "{} attempted paths, {} passed, {} failed, {} skipped entries{}",
            report.attempted_paths,
            report.passed_paths,
            report.failed_paths,
            report.skipped_entries,
            command_mode_detail
        )),
        command: None,
    }
}

fn run_command(cwd: &Path, program: &str, args: &[&str]) -> CommandResult {
    run_command_with_env(cwd, program, args, &[])
}

#[derive(Debug, Clone)]
struct CapturedCommandResult {
    command: CommandResult,
    stdout: String,
    cargo_dep_info_sources: BTreeSet<PathBuf>,
    cargo_dep_info_error: Option<String>,
}

fn run_command_with_env(
    cwd: &Path,
    program: &str,
    args: &[&str],
    env: &[(&str, &str)],
) -> CommandResult {
    run_command_with_env_capture(cwd, program, args, env).command
}

fn run_command_with_env_capture(
    cwd: &Path,
    program: &str,
    args: &[&str],
    env: &[(&str, &str)],
) -> CapturedCommandResult {
    run_command_with_env_capture_timeout(cwd, program, args, env, evidence_command_timeout())
}

fn run_command_with_env_capture_timeout(
    cwd: &Path,
    program: &str,
    args: &[&str],
    env: &[(&str, &str)],
    timeout: Option<Duration>,
) -> CapturedCommandResult {
    let start = Instant::now();
    let mut command = Command::new(program);
    command
        .args(args)
        .env_clear()
        .envs(sanitized_command_env())
        .envs(env.iter().copied())
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .current_dir(cwd);
    isolate_child_process_group(&mut command);
    let child = command.spawn();
    match child {
        Ok(mut child) => {
            let stdout_reader = child.stdout.take().map(spawn_pipe_reader);
            let stderr_reader = child.stderr.take().map(spawn_pipe_reader);
            let (status_result, timeout_detail) =
                wait_for_child_with_timeout(&mut child, start, timeout);
            let mut stderr_messages = Vec::new();
            let stdout_bytes = collect_pipe_reader(stdout_reader, "stdout", &mut stderr_messages);
            let mut stderr_bytes =
                collect_pipe_reader(stderr_reader, "stderr", &mut stderr_messages);
            for message in stderr_messages {
                append_stderr_bytes(&mut stderr_bytes, &message);
            }
            if let Some(detail) = timeout_detail {
                append_stderr_bytes(&mut stderr_bytes, &detail);
            }
            let status = match status_result {
                Ok(status) => status,
                Err(err) => {
                    append_stderr_bytes(&mut stderr_bytes, &err.to_string());
                    exit_status_command_error()
                }
            };
            let stdout = String::from_utf8_lossy(&stdout_bytes).into_owned();
            let stderr = String::from_utf8_lossy(&stderr_bytes).into_owned();
            CapturedCommandResult {
                command: CommandResult {
                    program: program.to_string(),
                    args: args.iter().map(|arg| (*arg).to_string()).collect(),
                    cwd: cwd.to_path_buf(),
                    exit_code: status.code(),
                    duration_ms: start.elapsed().as_millis(),
                    stdout_tail: tail_string(&stdout, 16_384),
                    stderr_tail: tail_string(&stderr, 16_384),
                },
                stdout,
                cargo_dep_info_sources: BTreeSet::new(),
                cargo_dep_info_error: None,
            }
        }
        Err(err) => CapturedCommandResult {
            command: CommandResult {
                program: program.to_string(),
                args: args.iter().map(|arg| (*arg).to_string()).collect(),
                cwd: cwd.to_path_buf(),
                exit_code: Some(127),
                duration_ms: start.elapsed().as_millis(),
                stdout_tail: String::new(),
                stderr_tail: err.to_string(),
            },
            stdout: String::new(),
            cargo_dep_info_sources: BTreeSet::new(),
            cargo_dep_info_error: None,
        },
    }
}

fn wait_for_child_with_timeout(
    child: &mut Child,
    start: Instant,
    timeout: Option<Duration>,
) -> (std::io::Result<std::process::ExitStatus>, Option<String>) {
    loop {
        match child.try_wait() {
            Ok(Some(status)) => return (Ok(status), None),
            Ok(None) => {
                if let Some(timeout) = timeout {
                    if start.elapsed() >= timeout {
                        let mut timeout_detail =
                            format!("command timed out after {:.3}s", timeout.as_secs_f64());
                        if let Some(error) = terminate_child_process_tree(child) {
                            timeout_detail.push_str(&format!(
                                "; failed to kill timed-out process cleanly: {error}"
                            ));
                        }
                        let status = child.wait().map(|_| exit_status_timeout());
                        return (status, Some(timeout_detail));
                    }
                }
                std::thread::sleep(Duration::from_millis(50));
            }
            Err(err) => {
                let _ = terminate_child_process_tree(child);
                return (Err(err), None);
            }
        }
    }
}

fn spawn_pipe_reader<R>(mut pipe: R) -> std::thread::JoinHandle<std::io::Result<Vec<u8>>>
where
    R: Read + Send + 'static,
{
    std::thread::spawn(move || {
        let mut output = Vec::new();
        pipe.read_to_end(&mut output)?;
        Ok(output)
    })
}

fn collect_pipe_reader(
    reader: Option<std::thread::JoinHandle<std::io::Result<Vec<u8>>>>,
    stream_name: &str,
    stderr_messages: &mut Vec<String>,
) -> Vec<u8> {
    let Some(reader) = reader else {
        return Vec::new();
    };
    match reader.join() {
        Ok(Ok(output)) => output,
        Ok(Err(error)) => {
            stderr_messages.push(format!("failed to read command {stream_name}: {error}"));
            Vec::new()
        }
        Err(_) => {
            stderr_messages.push(format!("command {stream_name} reader thread panicked"));
            Vec::new()
        }
    }
}

fn append_stderr_bytes(stderr: &mut Vec<u8>, message: &str) {
    if !stderr.is_empty() {
        stderr.push(b'\n');
    }
    stderr.extend_from_slice(message.as_bytes());
}

#[cfg(unix)]
fn isolate_child_process_group(command: &mut Command) {
    use std::os::unix::process::CommandExt;

    command.process_group(0);
}

#[cfg(not(unix))]
fn isolate_child_process_group(_command: &mut Command) {}

fn terminate_child_process_tree(child: &mut Child) -> Option<String> {
    #[cfg(unix)]
    {
        if let Err(group_error) = kill_child_process_group(child) {
            let mut detail = format!("process group {}: {group_error}", child.id());
            if let Err(child_error) = child.kill() {
                detail.push_str(&format!("; child process: {child_error}"));
            }
            return Some(detail);
        }
        None
    }
    #[cfg(not(unix))]
    {
        child.kill().err().map(|error| error.to_string())
    }
}

#[cfg(unix)]
fn kill_child_process_group(child: &Child) -> std::io::Result<()> {
    // The child is started in its own process group, so this targets the shell/cargo
    // wrapper and any descendants that inherited its group.
    let status = unsafe { libc::killpg(child.id() as libc::pid_t, libc::SIGKILL) };
    if status == 0 {
        Ok(())
    } else {
        Err(std::io::Error::last_os_error())
    }
}

fn evidence_command_timeout() -> Option<Duration> {
    match std::env::var(EVIDENCE_COMMAND_TIMEOUT_ENV) {
        Ok(value) if value.trim() == "0" => None,
        Ok(value) => value
            .trim()
            .parse::<u64>()
            .ok()
            .map(Duration::from_secs)
            .or_else(default_evidence_command_timeout),
        Err(_) => default_evidence_command_timeout(),
    }
}

fn default_evidence_command_timeout() -> Option<Duration> {
    Some(Duration::from_secs(
        DEFAULT_EVIDENCE_COMMAND_TIMEOUT_SECONDS,
    ))
}

#[cfg(unix)]
fn exit_status_timeout() -> std::process::ExitStatus {
    use std::os::unix::process::ExitStatusExt;

    std::process::ExitStatus::from_raw(124 << 8)
}

#[cfg(windows)]
fn exit_status_timeout() -> std::process::ExitStatus {
    use std::os::windows::process::ExitStatusExt;

    std::process::ExitStatus::from_raw(124)
}

#[cfg(unix)]
fn exit_status_command_error() -> std::process::ExitStatus {
    use std::os::unix::process::ExitStatusExt;

    std::process::ExitStatus::from_raw(127 << 8)
}

#[cfg(windows)]
fn exit_status_command_error() -> std::process::ExitStatus {
    use std::os::windows::process::ExitStatusExt;

    std::process::ExitStatus::from_raw(127)
}

fn command_result_detail(command: &CommandResult) -> Option<String> {
    let mut detail = command
        .exit_code
        .map(|code| format!("exit code {code}"))
        .unwrap_or_else(|| "terminated by signal or unavailable exit code".to_string());
    if let Some(timeout_line) = command
        .stderr_tail
        .lines()
        .rev()
        .find(|line| line.contains("command timed out after"))
    {
        detail.push_str("; ");
        detail.push_str(timeout_line);
    }
    Some(detail)
}

fn gate_status_from_exit(exit_code: Option<i32>) -> GateStatus {
    if exit_code == Some(0) {
        GateStatus::Passed
    } else {
        GateStatus::Failed
    }
}

fn display_exit_code(exit_code: Option<i32>) -> String {
    exit_code
        .map(|code| code.to_string())
        .unwrap_or_else(|| "signal or unavailable exit code".to_string())
}

fn sanitized_command_env() -> BTreeMap<String, String> {
    sanitized_command_env_with(sanitized_toolchain_env())
}

/// Build the hermetic command environment, optionally injecting the detected
/// active rustup toolchain (`toolchain`). Pure over its input so the injection
/// is unit-testable without depending on the process-global `OnceLock`.
fn sanitized_command_env_with(
    toolchain: Option<&SanitizedToolchainEnv>,
) -> BTreeMap<String, String> {
    let mut env = BTreeMap::new();
    env.insert("PATH".to_string(), sanitized_path_with_toolchain(toolchain));
    if let Some(active_toolchain) = toolchain.and_then(|t| t.active_toolchain.as_deref()) {
        // Direct the rustup shims at the active toolchain even in cwds without
        // a rust-toolchain.toml (corpus fixtures run in isolated dirs). Never
        // masks a real failure: the toolchain still compiles/verifies honestly,
        // it just is not the wrong (stale) compiler.
        env.insert("RUSTUP_TOOLCHAIN".to_string(), active_toolchain.to_string());
        // Also pin RUSTC at the active toolchain's rustup `rustc` shim. The PATH
        // prepend + RUSTUP_TOOLCHAIN above only cover tooling that resolves the
        // compiler from PATH; they do NOT cover tooling that resolves `rustc`
        // from the sibling of `$CARGO`. The cargo-trust-vc integration-test
        // witnesses (owner #2780) do exactly that — they compile a fake-cargo
        // recorder with `rustc -Ztrust-verify=off`, and their `rustc_command()`
        // takes the sibling of the isolated stable `$CARGO` (e.g. Homebrew's),
        // which rejects the Trust-only flag and spuriously fails the witness.
        // Exporting RUSTC makes that CARGO-sibling resolution land on the Trust
        // toolchain instead. The shim honours the RUSTUP_TOOLCHAIN set above, so
        // this never masks a real failure: the fake recorder is still compiled by
        // the honest Trust `rustc`. Only set when the rustup shim dir is known;
        // absent it, the pre-existing behaviour is preserved.
        if let Some(rustup_bin_dir) = toolchain.and_then(|t| t.rustup_bin_dir.as_deref()) {
            env.insert(
                "RUSTC".to_string(),
                Path::new(rustup_bin_dir)
                    .join("rustc")
                    .to_string_lossy()
                    .into_owned(),
            );
        }
    }
    env.insert("GIT_CONFIG_NOSYSTEM".to_string(), "1".to_string());
    env.insert("GIT_CONFIG_GLOBAL".to_string(), "/dev/null".to_string());
    env.insert("GIT_CONFIG_SYSTEM".to_string(), "/dev/null".to_string());
    env.insert("GIT_CONFIG_COUNT".to_string(), "0".to_string());
    env.insert("GIT_TERMINAL_PROMPT".to_string(), "0".to_string());
    env.insert(
        "CARGO_NET_GIT_FETCH_WITH_CLI".to_string(),
        "false".to_string(),
    );
    for key in [
        "HOME",
        "USER",
        "LOGNAME",
        "TMPDIR",
        "SSH_AUTH_SOCK",
        "SSL_CERT_FILE",
        "SSL_CERT_DIR",
        "GIT_SSL_CAINFO",
        "RUSTUP_HOME",
    ] {
        if let Some(value) = std::env::var_os(key) {
            env.insert(key.to_string(), value.to_string_lossy().into_owned());
        }
    }
    env
}

/// The sanitized system PATH with the rustup shim directory prepended (when
/// detected) so shim `cargo`/`rustc` win over any non-rustup compiler already
/// on the system PATH.
fn sanitized_path_with_toolchain(toolchain: Option<&SanitizedToolchainEnv>) -> String {
    match toolchain.and_then(|t| t.rustup_bin_dir.as_deref()) {
        Some(dir) => prepend_path_dir(dir, SANITIZED_PATH),
        None => SANITIZED_PATH.to_string(),
    }
}

/// Prepend `dir` to the colon-separated `base` PATH, unless `dir` is already
/// its leading entry (avoids a duplicate leading component).
fn prepend_path_dir(dir: &str, base: &str) -> String {
    if dir.is_empty() || base == dir || base.starts_with(&format!("{dir}:")) {
        base.to_string()
    } else {
        format!("{dir}:{base}")
    }
}

fn evidence_environment_blocking_reasons(
    args: &EvidenceArgs,
    cargo_evidence: &CargoEvidence,
) -> Vec<String> {
    let mut reasons = Vec::new();
    if args.run_trust_vc
        && !cargo_evidence
            .failures
            .iter()
            .any(|reason| reason.contains("requires an absolute default cargo command"))
        && !Path::new(&args.cargo_command).is_absolute()
    {
        reasons.push(format!(
            "replacement evidence requires an absolute default cargo command, got `{}`",
            args.cargo_command
        ));
    }
    if args.run_trust_vc
        && cargo_command_is_home_relative(&args.cargo_command)
        && !cargo_evidence.default_rustup_cargo
    {
        reasons.push(format!(
            "replacement evidence cannot trust a cargo binary under HOME: `{}`",
            args.cargo_command
        ));
    }
    if active_git_url_rewrite_detected(&args.crate_root) {
        reasons.push(
            "replacement evidence requires effective repo-local git url.*.insteadOf rewrites and git config includes to be absent"
                .to_string(),
        );
    }
    if active_cargo_config_override_detected(&args.crate_root, Some(&cargo_gate_home(args))) {
        reasons.push(
            "replacement evidence requires Cargo path/source/rustc-wrapper/rustflags overrides to be absent"
                .to_string(),
        );
    }
    let cargo_home = cargo_gate_home(args);
    let active_cargo_home_configs = cargo_home_config_paths(&cargo_home)
        .iter()
        .filter(|path| cargo_config_has_effective_lines(path))
        .map(|path| path.display().to_string())
        .collect::<Vec<_>>();
    if !active_cargo_home_configs.is_empty() {
        reasons.push(format!(
            "replacement evidence requires isolated CARGO_HOME to have no active config files: {}",
            active_cargo_home_configs.join(", ")
        ));
    }
    for key in [
        "RUSTC_WRAPPER",
        "RUSTFLAGS",
        "CARGO_ENCODED_RUSTFLAGS",
        "DYLD_INSERT_LIBRARIES",
        "LD_PRELOAD",
        // SOUNDNESS: this variable carries dependency semantic facts, and a fact
        // imported through it installs each callee `ensures` as an ASSUME in the
        // caller — flipping a dependency's postconditions from BLOCKED to
        // trusted. The env carrier is strictly weaker than the file carrier:
        // `dependency_semantic_artifacts_from_env` is a plain
        // `serde_json::from_str`, and its `DependencySemanticArtifact` has no
        // rmeta binding (no metadata path/len/sha256) at all. Nothing in it is a
        // receipt that a verifier ever ran.
        //
        // The clause-equality check downstream means a forger cannot INVENT a
        // postcondition, only assert that the dependency's real declared clauses
        // were proven — so this is bounded, not unbounded. It is still a
        // false-verify whenever the dependency's body does not satisfy its own
        // `ensures`.
        //
        // Blocking it here does not fix the channel; it stops a run that used
        // the channel from being reported as clean replacement evidence.
        TRUST_VC_DEPENDENCY_FACTS_ENV,
    ] {
        if std::env::var_os(key).is_some() {
            reasons.push(format!("replacement evidence requires `{key}` to be unset"));
        }
    }
    reasons
}

fn cargo_command_is_home_relative(command: &str) -> bool {
    let command_path = Path::new(command);
    if !command_path.is_absolute() {
        return false;
    }
    let Some(home) = std::env::var_os("HOME").map(PathBuf::from) else {
        return false;
    };
    path_starts_with(command_path, &home)
}

fn standard_home_cargo_path(home: &Path) -> PathBuf {
    home.join(".cargo").join("bin").join("cargo")
}

fn is_symlink_to_rustup(command: &Path, home: &Path) -> bool {
    let Ok(target) = fs::read_link(command) else {
        return false;
    };
    let expected_rustup = home.join(".cargo").join("bin").join("rustup");
    if target == Path::new("rustup") {
        return true;
    }
    let target = if target.is_absolute() {
        target
    } else {
        command
            .parent()
            .map(|parent| parent.join(&target))
            .unwrap_or(target)
    };
    same_filesystem_path(&target, &expected_rustup)
}

fn same_filesystem_path(left: &Path, right: &Path) -> bool {
    match (left.canonicalize(), right.canonicalize()) {
        (Ok(left), Ok(right)) => left == right,
        _ => left == right,
    }
}

fn rustup_toolchain_cargo_matches(path: &Path, rustup_home: &Path, active_toolchain: &str) -> bool {
    let expected = rustup_home
        .join("toolchains")
        .join(active_toolchain)
        .join("bin")
        .join("cargo");
    same_filesystem_path(path, &expected)
}

fn active_git_url_rewrite_detected(crate_root: &Path) -> bool {
    local_git_config_paths(crate_root)
        .iter()
        .any(|path| git_config_url_rewrite_in_file(path))
}

fn local_git_config_paths(crate_root: &Path) -> Vec<PathBuf> {
    let dot_git = crate_root.join(".git");
    if dot_git.is_dir() {
        return git_config_paths_for_gitdir(&dot_git);
    }
    if let Ok(text) = fs::read_to_string(&dot_git) {
        for raw_line in text.lines() {
            let line = raw_line.trim();
            let Some(gitdir) = line.strip_prefix("gitdir:") else {
                continue;
            };
            let gitdir = gitdir.trim();
            let gitdir_path = if Path::new(gitdir).is_absolute() {
                PathBuf::from(gitdir)
            } else {
                crate_root.join(gitdir)
            };
            return git_config_paths_for_gitdir(&gitdir_path);
        }
    }
    git_config_paths_for_gitdir(&dot_git)
}

fn git_config_paths_for_gitdir(gitdir: &Path) -> Vec<PathBuf> {
    let mut paths = vec![gitdir.join("config"), gitdir.join("config.worktree")];
    if let Ok(text) = fs::read_to_string(gitdir.join("commondir")) {
        if let Some(commondir) = text.lines().map(str::trim).find(|line| !line.is_empty()) {
            let commondir = Path::new(commondir);
            let commondir = if commondir.is_absolute() {
                commondir.to_path_buf()
            } else {
                gitdir.join(commondir)
            };
            paths.push(commondir.join("config"));
            paths.push(commondir.join("config.worktree"));
        }
    }
    paths
}

fn git_config_url_rewrite_in_file(path: &Path) -> bool {
    let Ok(text) = fs::read_to_string(path) else {
        return false;
    };
    text.lines().any(|raw_line| {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('#') || line.starts_with(';') {
            return false;
        }
        let lower = line.to_ascii_lowercase();
        lower.contains("insteadof") || lower.starts_with("[include")
    })
}

fn active_cargo_config_override_detected(crate_root: &Path, cargo_home: Option<&Path>) -> bool {
    cargo_config_paths(crate_root, cargo_home)
        .iter()
        .any(|path| {
            if path.file_name().is_some_and(|name| name == "Cargo.toml") {
                cargo_manifest_override_in_file(path)
            } else {
                cargo_config_override_in_file(path)
            }
        })
}

fn cargo_config_paths(crate_root: &Path, cargo_home: Option<&Path>) -> Vec<PathBuf> {
    let mut paths = Vec::new();
    let mut seen = BTreeSet::new();
    push_unique_path(&mut paths, &mut seen, crate_root.join("Cargo.toml"));
    for path in effective_cargo_config_paths(crate_root) {
        push_unique_path(&mut paths, &mut seen, path);
    }
    for path in repo_local_cargo_config_paths(crate_root) {
        push_unique_path(&mut paths, &mut seen, path);
    }
    if let Some(cargo_home) = cargo_home {
        for path in cargo_home_config_paths(cargo_home) {
            push_unique_path(&mut paths, &mut seen, path);
        }
    }
    paths
}

fn push_unique_path(paths: &mut Vec<PathBuf>, seen: &mut BTreeSet<PathBuf>, path: PathBuf) {
    if seen.insert(path.clone()) {
        paths.push(path);
    }
}

fn effective_cargo_config_paths(cwd: &Path) -> Vec<PathBuf> {
    let start = cwd.canonicalize().unwrap_or_else(|_| cwd.to_path_buf());
    let mut paths = Vec::new();
    for ancestor in start.ancestors() {
        paths.push(ancestor.join(".cargo/config.toml"));
        paths.push(ancestor.join(".cargo/config"));
    }
    paths
}

fn repo_local_cargo_config_paths(crate_root: &Path) -> Vec<PathBuf> {
    let mut paths = Vec::new();
    collect_repo_local_cargo_config_paths(crate_root, &mut paths);
    paths
}

fn collect_repo_local_cargo_config_paths(dir: &Path, paths: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let Ok(file_type) = entry.file_type() else {
            continue;
        };
        if !file_type.is_dir() {
            continue;
        }
        let name = entry.file_name();
        let name = name.to_string_lossy();
        match name.as_ref() {
            ".git" | ".trust_vc" | "target" => continue,
            ".cargo" => {
                paths.push(path.join("config.toml"));
                paths.push(path.join("config"));
            }
            _ => collect_repo_local_cargo_config_paths(&path, paths),
        }
    }
}

fn cargo_home_config_paths(cargo_home: &Path) -> Vec<PathBuf> {
    vec![cargo_home.join("config.toml"), cargo_home.join("config")]
}

fn cargo_config_has_effective_lines(path: &Path) -> bool {
    let Ok(text) = fs::read_to_string(path) else {
        return false;
    };
    text.lines().any(|raw_line| {
        let line = raw_line.trim();
        !line.is_empty() && !line.starts_with('#') && !line.starts_with(';')
    })
}

fn cargo_config_override_in_file(path: &Path) -> bool {
    let Ok(text) = fs::read_to_string(path) else {
        return false;
    };
    text.lines().any(|raw_line| {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('#') || line.starts_with(';') {
            return false;
        }
        let lower = line.to_ascii_lowercase();
        lower.starts_with("paths")
            || lower.contains("replace-with")
            || lower.contains("rustc-wrapper")
            || lower.contains("rustflags")
            || lower.contains("linker")
            || lower.contains("runner")
            || lower.contains("build-std")
            || lower.starts_with("[source.")
            || lower.starts_with("[patch.")
            || lower.starts_with("[target.")
            || lower.starts_with("[unstable]")
    })
}

fn cargo_manifest_override_in_file(path: &Path) -> bool {
    let Ok(text) = fs::read_to_string(path) else {
        return false;
    };
    text.lines().any(|raw_line| {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('#') || line.starts_with(';') {
            return false;
        }
        let lower = line.to_ascii_lowercase();
        lower.starts_with("[patch.") || lower.starts_with("[replace]")
    })
}

fn path_starts_with(path: &Path, parent: &Path) -> bool {
    match (path.canonicalize(), parent.canonicalize()) {
        (Ok(path), Ok(parent)) => path.starts_with(parent),
        _ => path.starts_with(parent),
    }
}

#[derive(Debug, Default)]
struct CorpusPathBucketAccumulator {
    entry_count: usize,
    classification_counts: BTreeMap<String, usize>,
    missing_trust_vc_paths: usize,
    missing_trust_vc_path_files: usize,
}

fn load_corpus_triage_report(
    manifest_path: &Path,
    crate_root: &Path,
) -> Result<CorpusTriageReport, EvidenceError> {
    let manifest = load_manifest(manifest_path)?;
    let replacement_summary = verus_replacement_summary(&manifest.entries);
    let mut accepted_executable_ports = Vec::new();
    let mut unsupported_gap_evidence = Vec::new();
    let mut classification_counts = BTreeMap::new();
    let mut buckets: BTreeMap<String, CorpusPathBucketAccumulator> = BTreeMap::new();
    let mut missing_trust_vc_paths = Vec::new();
    let mut missing_trust_vc_path_files = Vec::new();
    let mut invalid_classification_entries = Vec::new();

    for entry in &manifest.entries {
        let path_bucket = upstream_path_bucket(&entry.upstream_path, &manifest.test_roots);
        *classification_counts
            .entry(entry.classification.clone())
            .or_insert(0) += 1;

        let bucket = buckets.entry(path_bucket.clone()).or_default();
        bucket.entry_count += 1;
        *bucket
            .classification_counts
            .entry(entry.classification.clone())
            .or_insert(0) += 1;

        if !is_allowed_classification(&entry.classification) {
            invalid_classification_entries.push(corpus_triage_entry(entry, &path_bucket));
        }

        if requires_trust_vc_paths(&entry.classification) {
            accepted_executable_ports.push(verus_manifest_entry_evidence(entry));
        }

        if entry.classification == "unsupported-gap"
            && (!entry.trust_vc_paths.is_empty() || !entry.expected_cases.is_empty())
        {
            unsupported_gap_evidence.push(verus_manifest_entry_evidence(entry));
        }

        if requires_trust_vc_paths(&entry.classification) && entry.trust_vc_paths.is_empty() {
            bucket.missing_trust_vc_paths += 1;
            missing_trust_vc_paths.push(corpus_triage_entry(entry, &path_bucket));
        }

        for trust_vc_path in &entry.trust_vc_paths {
            if validate_repo_trust_vc_path(crate_root, trust_vc_path).is_err() {
                bucket.missing_trust_vc_path_files += 1;
                missing_trust_vc_path_files.push(CorpusMissingTrustVcPathFile {
                    upstream_path: entry.upstream_path.clone(),
                    classification: entry.classification.clone(),
                    trust_vc_path: trust_vc_path.clone(),
                });
            }
        }
    }

    missing_trust_vc_paths.sort_by(|left, right| {
        left.upstream_path
            .cmp(&right.upstream_path)
            .then_with(|| left.classification.cmp(&right.classification))
    });
    missing_trust_vc_path_files.sort_by(|left, right| {
        left.upstream_path
            .cmp(&right.upstream_path)
            .then_with(|| left.trust_vc_path.cmp(&right.trust_vc_path))
    });
    invalid_classification_entries.sort_by(|left, right| {
        left.upstream_path
            .cmp(&right.upstream_path)
            .then_with(|| left.classification.cmp(&right.classification))
    });

    Ok(CorpusTriageReport {
        schema_version: 1,
        manifest_schema_version: manifest.schema_version,
        manifest_path: report_path_string(manifest_path, crate_root),
        upstream_repo: manifest.upstream_repo,
        upstream_ref: manifest.upstream_ref,
        upstream_test_roots: manifest.test_roots,
        entry_count: manifest.entries.len(),
        classification_counts,
        replacement_summary,
        accepted_executable_ports,
        unsupported_gap_evidence,
        path_buckets: buckets
            .into_iter()
            .map(|(bucket, summary)| CorpusPathBucketSummary {
                bucket,
                entry_count: summary.entry_count,
                classification_counts: summary.classification_counts,
                missing_trust_vc_paths: summary.missing_trust_vc_paths,
                missing_trust_vc_path_files: summary.missing_trust_vc_path_files,
            })
            .collect(),
        missing_trust_vc_paths,
        missing_trust_vc_path_files,
        duplicate_entries: duplicate_manifest_paths(&manifest.entries),
        invalid_classification_entries,
    })
}

#[cfg(test)]
fn load_corpus_report(
    manifest_path: &Path,
    crate_root: &Path,
    verus_path: Option<&Path>,
) -> Result<VerusCorpusReport, EvidenceError> {
    load_corpus_report_with_options(
        manifest_path,
        crate_root,
        verus_path,
        CorpusLoadOptions::default(),
    )
}

fn load_corpus_report_with_options(
    manifest_path: &Path,
    crate_root: &Path,
    verus_path: Option<&Path>,
    options: CorpusLoadOptions,
) -> Result<VerusCorpusReport, EvidenceError> {
    let manifest = load_manifest(manifest_path)?;
    let (upstream_tests, mut invalid_entries) = match enumerate_upstream_tests_from_git_ref(
        verus_path,
        manifest.upstream_ref.as_deref(),
        &manifest.test_roots,
    ) {
        Ok(upstream_tests) => (upstream_tests, Vec::new()),
        Err(error) => (
            Vec::new(),
            vec![format!(
                "upstream inventory must be derived from manifest upstream.ref via git ls-tree: {error}"
            )],
        ),
    };
    let entry_paths: BTreeSet<String> = manifest
        .entries
        .iter()
        .map(|entry| entry.upstream_path.clone())
        .collect();
    let missing_entries: Vec<String> = upstream_tests
        .iter()
        .filter(|path| !entry_paths.contains(*path))
        .cloned()
        .collect();
    let upstream_test_paths: BTreeSet<String> = upstream_tests.iter().cloned().collect();
    let extra_entries: Vec<String> = entry_paths
        .iter()
        .filter(|path| !upstream_test_paths.contains(*path))
        .cloned()
        .collect();
    let mut seen_entries = BTreeSet::new();
    let mut duplicate_entries = Vec::new();
    let mut classification_counts = BTreeMap::new();
    let replacement_summary = verus_replacement_summary(&manifest.entries);
    let mut unsupported_entries = Vec::new();
    let mut failing_entries = Vec::new();
    let mut port_path_failures = Vec::new();
    let mut upstream_case_failures = Vec::new();
    let mut ignored_upstream_cases = Vec::new();
    let mut upstream_case_extraction_gaps = Vec::new();
    let mut accepted_executable_ports = Vec::new();
    let mut unsupported_gap_evidence = Vec::new();
    let porting_next_action =
        verus_corpus_porting_next_action(&manifest, manifest_path, crate_root);
    let mut accepted_trust_vc_source_hashes = Vec::new();
    let mut run_candidates = Vec::new();
    let git_head_available = git_rev_parse(crate_root, "HEAD").is_some();
    if git_head_available {
        match repo_relative_string(crate_root, manifest_path) {
            Ok(manifest_rel) => match git_head_path_kind(crate_root, &manifest_rel) {
                Ok(Some(GitHeadPathKind::Blob)) => {}
                Ok(Some(GitHeadPathKind::Tree)) => invalid_entries.push(format!(
                    "manifest path must be a tracked HEAD file, got tree `{manifest_rel}`"
                )),
                Ok(None) => invalid_entries.push(format!(
                    "manifest path must be tracked in HEAD: {manifest_rel}"
                )),
                Err(error) => invalid_entries.push(format!(
                    "failed to verify manifest HEAD tracking for `{manifest_rel}`: {error}"
                )),
            },
            Err(error) => invalid_entries.push(format!(
                "manifest path must be repo-local for HEAD tracking: {error}"
            )),
        }
    }
    if !manifest.failing_classifications.contains("unclassified") {
        invalid_entries.push("manifest gate must fail classification `unclassified`".to_string());
    }
    if !manifest.failing_classifications.contains("unsupported-gap") {
        invalid_entries
            .push("manifest gate must fail classification `unsupported-gap`".to_string());
    }
    if manifest.upstream_repo.as_deref() != Some(VERUS_REPO_URL) {
        invalid_entries.push(format!(
            "manifest upstream.repo must be `{VERUS_REPO_URL}`, got `{}`",
            manifest.upstream_repo.as_deref().unwrap_or("unavailable")
        ));
    }
    let required_roots = required_verus_test_roots();
    let legacy_root_only = [VERUS_TEST_ROOT.to_string()];
    if manifest.test_roots != required_roots && manifest.test_roots != legacy_root_only {
        invalid_entries.push(format!(
            "manifest upstream.test_roots must be exactly {:?}, got {:?}",
            required_roots, manifest.test_roots
        ));
    }
    for entry in &manifest.entries {
        let entry_port_path_failure_start = port_path_failures.len();
        if !seen_entries.insert(entry.upstream_path.clone()) {
            duplicate_entries.push(entry.upstream_path.clone());
        }
        *classification_counts
            .entry(entry.classification.clone())
            .or_insert(0) += 1;
        if entry.upstream_path.trim().is_empty() {
            invalid_entries.push("entry has empty upstream_path".to_string());
        }
        if !is_allowed_classification(&entry.classification) {
            invalid_entries.push(format!(
                "{}: invalid classification `{}`",
                entry.upstream_path, entry.classification
            ));
        }
        if entry.classification == "unsupported-gap" {
            unsupported_entries.push(format!(
                "{}: owner={}, reason={}",
                entry.upstream_path,
                empty_as_unavailable(&entry.owner_issue),
                empty_as_unavailable(&entry.reason)
            ));
            if unsupported_entry_has_partial_trust_vc_evidence(entry) {
                unsupported_gap_evidence.push(verus_manifest_entry_evidence(entry));
            }
        }
        if manifest
            .failing_classifications
            .contains(&entry.classification)
        {
            failing_entries.push(format!(
                "{}: classification={}, owner={}, reason={}",
                entry.upstream_path,
                entry.classification,
                empty_as_unavailable(&entry.owner_issue),
                empty_as_unavailable(&entry.reason)
            ));
        }
        if entry.owner_issue == "TBD" && entry.classification != "unclassified" {
            failing_entries.push(format!(
                "{}: accepted entry has TBD owner",
                entry.upstream_path
            ));
        }
        if entry.owner_issue.trim().is_empty() {
            invalid_entries.push(format!("{}: missing owner_issue", entry.upstream_path));
        }
        if entry.reason.trim().is_empty() {
            failing_entries.push(format!("{}: missing reason", entry.upstream_path));
        }
        if entry.classification == "not-applicable"
            && !not_applicable_scope_allowed(verus_path, &entry.upstream_path)
        {
            failing_entries.push(format!(
                "{}: not-applicable is reserved for approved shared helper infrastructure or upstream files whose extracted harness cases are all ignored",
                entry.upstream_path
            ));
        }
        if requires_trust_vc_paths(&entry.classification) && entry.trust_vc_paths.is_empty() {
            port_path_failures.push(format!(
                "{}: accepted executable entry has no trust_vc_paths",
                entry.upstream_path
            ));
        }
        if requires_trust_vc_paths(&entry.classification) && entry.expected_cases.is_empty() {
            port_path_failures.push(format!(
                "{}: accepted executable entry has no expected_cases",
                entry.upstream_path
            ));
        }
        let accepted_entry = requires_trust_vc_paths(&entry.classification);
        if accepted_entry {
            accepted_executable_ports.push(verus_manifest_entry_evidence(entry));
        }
        if accepted_entry && !entry.known_gaps.is_empty() {
            failing_entries.push(format!(
                "{}: accepted executable entry declares known replacement gaps: {}",
                entry.upstream_path,
                entry.known_gaps.join("; ")
            ));
        }
        if accepted_entry
            && entry.evidence_kind == VerusEvidenceKind::CargoTrustVcIntegrationTest
            && !entry.trust_vc_check_args.is_empty()
        {
            port_path_failures.push(format!(
                "{}: cargo_trust_vc_integration_test evidence must not declare trust_vc_check_args",
                entry.upstream_path
            ));
        }
        append_trust_vc_check_arg_failures(entry, accepted_entry, &mut port_path_failures);
        let entry_trust_vc_path_set: BTreeSet<&str> =
            entry.trust_vc_paths.iter().map(String::as_str).collect();
        let uses_case_trust_vc_paths = expected_cases_use_trust_vc_paths(&entry.expected_cases);
        let requires_case_trust_vc_paths = accepted_entry && entry.trust_vc_paths.len() > 1;
        let requires_upstream_case_ids =
            accepted_entry && (entry.expected_cases.len() > 1 || entry.trust_vc_paths.len() > 1);
        let requires_pinned_evidence = accepted_entry && manifest.schema_version >= 2;
        let mut used_case_trust_vc_paths = BTreeSet::new();
        let mut seen_expected_cases = BTreeSet::new();
        for expected_case in &entry.expected_cases {
            if !valid_expected_case_id(&expected_case.case_id) {
                port_path_failures.push(format!(
                    "{}: expected_cases.case_id must be a Rust function identifier: {}",
                    entry.upstream_path, expected_case.case_id
                ));
            }
            if let Some(upstream_case_id) = &expected_case.upstream_case_id {
                if !valid_expected_case_id(upstream_case_id) {
                    port_path_failures.push(format!(
                        "{}: expected_cases.upstream_case_id must be a Rust function identifier: {}",
                        entry.upstream_path, upstream_case_id
                    ));
                }
            } else if requires_upstream_case_ids {
                port_path_failures.push(format!(
                    "{}: expected_cases entry `{}` must declare upstream_case_id because accepted entries with multiple expected_cases or split trust_vc_paths require explicit upstream coverage mapping",
                    entry.upstream_path, expected_case.case_id
                ));
            }
            if expected_case.min_obligations == 0
                && entry.evidence_kind == VerusEvidenceKind::ProofObligation
                && expected_case.expected_verdict != VerusExpectedVerdict::Error
            {
                port_path_failures.push(format!(
                    "{}: expected_cases entry `{}` must declare min_obligations >= 1 unless expected_verdict is error",
                    entry.upstream_path, expected_case.case_id
                ));
            }
            if expected_case.expected_verdict == VerusExpectedVerdict::Error
                && expected_case.min_obligations == 0
                && expected_case.expected_error_patterns.is_empty()
            {
                port_path_failures.push(format!(
                    "{}: expected_cases entry `{}` mirrors a source/compile error and must declare expected_error_patterns",
                    entry.upstream_path, expected_case.case_id
                ));
            }
            if expected_case.expected_verdict != VerusExpectedVerdict::Error
                && !expected_case.expected_error_patterns.is_empty()
            {
                port_path_failures.push(format!(
                    "{}: expected_cases entry `{}` declares expected_error_patterns but its expected_verdict is not error",
                    entry.upstream_path, expected_case.case_id
                ));
            }
            if expected_case.expected_verdict != VerusExpectedVerdict::Error
                && !expected_case
                    .expected_rust_diagnostic_pattern_sets
                    .is_empty()
            {
                port_path_failures.push(format!(
                    "{}: expected_cases entry `{}` declares expected_rust_diagnostic_pattern_sets but its expected_verdict is not error",
                    entry.upstream_path, expected_case.case_id
                ));
            }
            if let Some(empty_pattern) = expected_case
                .expected_error_patterns
                .iter()
                .find(|pattern| pattern.trim().is_empty())
            {
                port_path_failures.push(format!(
                    "{}: expected_cases entry `{}` declares an empty expected_error_patterns value: {:?}",
                    entry.upstream_path, expected_case.case_id, empty_pattern
                ));
            }
            if let Some(empty_pattern) = expected_case
                .expected_warning_patterns
                .iter()
                .find(|pattern| pattern.trim().is_empty())
            {
                port_path_failures.push(format!(
                    "{}: expected_cases entry `{}` declares an empty expected_warning_patterns value: {:?}",
                    entry.upstream_path, expected_case.case_id, empty_pattern
                ));
            }
            if !expected_case
                .expected_rust_diagnostic_pattern_sets
                .is_empty()
            {
                if expected_case.min_obligations != 0 {
                    port_path_failures.push(format!(
                        "{}: expected_cases entry `{}` declares expected_rust_diagnostic_pattern_sets but min_obligations is {}; Rust compiler diagnostics must use min_obligations 0",
                        entry.upstream_path, expected_case.case_id, expected_case.min_obligations
                    ));
                }
                for (index, pattern_set) in expected_case
                    .expected_rust_diagnostic_pattern_sets
                    .iter()
                    .enumerate()
                {
                    if pattern_set.is_empty() {
                        port_path_failures.push(format!(
                            "{}: expected_cases entry `{}` declares an empty expected_rust_diagnostic_pattern_sets value at index {}",
                            entry.upstream_path, expected_case.case_id, index
                        ));
                    }
                    if let Some(empty_pattern) =
                        pattern_set.iter().find(|pattern| pattern.trim().is_empty())
                    {
                        port_path_failures.push(format!(
                            "{}: expected_cases entry `{}` declares an empty expected_rust_diagnostic_pattern_sets pattern at index {}: {:?}",
                            entry.upstream_path, expected_case.case_id, index, empty_pattern
                        ));
                    }
                }
                for trust_vc_path in expected_case_trust_vc_paths(entry, expected_case) {
                    if !entry_trust_vc_path_set.contains(trust_vc_path) {
                        continue;
                    }
                    match validate_repo_trust_vc_path(crate_root, trust_vc_path) {
                        Ok(path) if is_cargo_fixture_root(&path) => {}
                        Ok(_) => port_path_failures.push(format!(
                            "{}: expected_cases entry `{}` declares expected_rust_diagnostic_pattern_sets but does not map to a cargo fixture trust_vc_path: `{}`",
                            entry.upstream_path, expected_case.case_id, trust_vc_path
                        )),
                        Err(_) => {}
                    }
                }
            }
            if let Some(empty_pattern) = expected_case
                .forbidden_diagnostic_patterns
                .iter()
                .find(|pattern| pattern.trim().is_empty())
            {
                port_path_failures.push(format!(
                    "{}: expected_cases entry `{}` declares an empty forbidden_diagnostic_patterns value: {:?}",
                    entry.upstream_path, expected_case.case_id, empty_pattern
                ));
            }
            append_expected_case_obligation_pin_failures(
                entry,
                expected_case,
                requires_pinned_evidence,
                options.refresh_evidence_pins,
                &mut port_path_failures,
            );
            if !seen_expected_cases.insert(expected_case.case_id.as_str()) {
                port_path_failures.push(format!(
                    "{}: duplicate expected_cases.case_id `{}`",
                    entry.upstream_path, expected_case.case_id
                ));
            }
            match expected_case.trust_vc_path.as_deref() {
                Some(trust_vc_path) if !entry_trust_vc_path_set.contains(trust_vc_path) => {
                    port_path_failures.push(format!(
                        "{}: expected_cases entry `{}` trust_vc_path `{}` must match an entry-level trust_vc_paths value",
                        entry.upstream_path, expected_case.case_id, trust_vc_path
                    ));
                }
                Some(trust_vc_path) => {
                    used_case_trust_vc_paths.insert(trust_vc_path);
                }
                None if uses_case_trust_vc_paths || requires_case_trust_vc_paths => {
                    port_path_failures.push(format!(
                        "{}: expected_cases entry `{}` must declare trust_vc_path because accepted entries with split trust_vc_paths require case-level path binding",
                        entry.upstream_path, expected_case.case_id
                    ));
                }
                _ => {}
            }
        }
        if accepted_entry && uses_case_trust_vc_paths {
            for trust_vc_path in entry_trust_vc_path_set.difference(&used_case_trust_vc_paths) {
                port_path_failures.push(format!(
                    "{}: entry-level trust_vc_paths value `{}` is not assigned to any expected_cases entry",
                    entry.upstream_path, trust_vc_path
                ));
            }
        }
        if entry.classification == "unsupported-gap" {
            append_unsupported_scout_inventory_failures(entry, crate_root, &mut port_path_failures);
        }
        let mut trust_vc_source_hashes = Vec::new();
        for trust_vc_path in &entry.trust_vc_paths {
            match validate_repo_trust_vc_path(crate_root, trust_vc_path) {
                Ok(path) => {
                    if accepted_entry && path.is_dir() && !is_cargo_fixture_root(&path) {
                        port_path_failures.push(format!(
                            "{}: direct-source trust_vc_path `{}` names a directory; accepted directory ports must be cargo fixtures with Cargo.toml",
                            entry.upstream_path, trust_vc_path
                        ));
                    }
                    if accepted_entry
                        && !entry.trust_vc_check_args.is_empty()
                        && !is_cargo_fixture_root(&path)
                    {
                        port_path_failures.push(format!(
                            "{}: trust_vc_check_args require a cargo fixture trust_vc_path with Cargo.toml, got `{}`",
                            entry.upstream_path, trust_vc_path
                        ));
                    }
                    if accepted_entry {
                        let cargo_trust_vc_test_target =
                            cargo_trust_vc_integration_test_target(crate_root, &path);
                        match (entry.evidence_kind, cargo_trust_vc_test_target.is_some()) {
                            (VerusEvidenceKind::ProofObligation, true) => {
                                port_path_failures.push(format!(
                                    "{}: accepted trust_vc_path `{}` is a cargo-trust-vc integration test; integration tests are wrapper execution witnesses, not TrustVc proof-obligation fingerprint evidence",
                                    entry.upstream_path, trust_vc_path
                                ));
                            }
                            (VerusEvidenceKind::CargoTrustVcIntegrationTest, false) => {
                                port_path_failures.push(format!(
                                    "{}: cargo_trust_vc_integration_test evidence trust_vc_path `{}` must be under crates/cargo-trust-vc/tests/*.rs",
                                    entry.upstream_path, trust_vc_path
                                ));
                            }
                            _ => {}
                        }
                    }
                    if accepted_entry {
                        match trust_vc_source_path_hash(
                            crate_root,
                            trust_vc_path,
                            &path,
                            git_head_available && !options.refresh_evidence_pins,
                        ) {
                            Ok(source_hash) => trust_vc_source_hashes.push(source_hash),
                            Err(error) => {
                                port_path_failures.push(format!("{}: {error}", entry.upstream_path))
                            }
                        }
                    }
                }
                Err(error) => port_path_failures.push(format!("{}: {error}", entry.upstream_path)),
            }
        }
        if accepted_entry {
            append_trust_vc_source_hash_pin_failures(
                entry,
                &trust_vc_source_hashes,
                requires_pinned_evidence,
                options.refresh_evidence_pins,
                &mut port_path_failures,
            );
            if !entry.trust_vc_paths.is_empty()
                && trust_vc_source_hashes.len() == entry.trust_vc_paths.len()
            {
                accepted_trust_vc_source_hashes.push(AcceptedTrustVcSourceHashes {
                    upstream_path: entry.upstream_path.clone(),
                    classification: entry.classification.clone(),
                    trust_vc_paths: trust_vc_source_hashes,
                });
            }
            match upstream_verus_harness_cases(verus_path, &entry.upstream_path) {
                Ok(Some(upstream_cases)) if !upstream_cases.is_empty() => {
                    ignored_upstream_cases
                        .extend(ignored_upstream_case_evidence(entry, &upstream_cases));
                    let expected_ids: BTreeSet<&str> =
                        entry.expected_cases.iter().map(upstream_case_id).collect();
                    let upstream_ids: BTreeSet<&str> = upstream_cases
                        .iter()
                        .map(|case| case.case_id.as_str())
                        .collect();
                    let ignored_upstream_ids: BTreeSet<&str> = upstream_cases
                        .iter()
                        .filter(|case| case.ignored)
                        .map(|case| case.case_id.as_str())
                        .collect();
                    let upstream_cases_by_id: BTreeMap<&str, &UpstreamVerusHarnessCase> =
                        upstream_cases
                            .iter()
                            .map(|case| (case.case_id.as_str(), case))
                            .collect();
                    for upstream_case in &upstream_cases {
                        if upstream_case.ignored {
                            continue;
                        }
                        let mapped_count = entry
                            .expected_cases
                            .iter()
                            .filter(|expected_case| {
                                upstream_case_id(expected_case) == upstream_case.case_id
                            })
                            .count();
                        if mapped_count < upstream_case.expected_occurrences {
                            upstream_case_failures.push(format!(
                                "{}: upstream Verus harness case `{}` requires at least {} mapped TrustVc expected case(s), but manifest maps {}",
                                entry.upstream_path,
                                upstream_case.case_id,
                                upstream_case.expected_occurrences,
                                mapped_count
                            ));
                        }
                    }
                    for missing_case in upstream_ids.difference(&expected_ids) {
                        let missing_case = *missing_case;
                        if ignored_upstream_ids.contains(missing_case) {
                            continue;
                        }
                        upstream_case_failures.push(format!(
                            "{}: expected_cases missing upstream Verus case `{}`",
                            entry.upstream_path, missing_case
                        ));
                    }
                    for extra_case in expected_ids.difference(&upstream_ids) {
                        upstream_case_failures.push(format!(
                            "{}: expected_cases entry `{}` does not match an upstream Verus harness case",
                            entry.upstream_path, extra_case
                        ));
                    }
                    for expected_case in &entry.expected_cases {
                        let upstream_id = upstream_case_id(expected_case);
                        if let Some(upstream_case) = upstream_cases_by_id.get(upstream_id) {
                            if expected_case.expected_verdict != upstream_case.expected_verdict {
                                upstream_case_failures.push(format!(
                                    "{}: expected_cases entry `{}` declares `{}`, but upstream Verus harness case `{}` expects `{}`",
                                    entry.upstream_path,
                                    expected_case.case_id,
                                    expected_verdict_label(expected_case.expected_verdict),
                                    upstream_id,
                                    expected_verdict_label(upstream_case.expected_verdict)
                                ));
                            }
                            if upstream_case.expected_verdict == VerusExpectedVerdict::Error {
                                for pattern in &upstream_case.error_patterns {
                                    if !expected_case
                                        .expected_error_patterns
                                        .iter()
                                        .any(|declared| declared == pattern)
                                    {
                                        upstream_case_failures.push(format!(
                                            "{}: expected_cases entry `{}` is missing upstream error diagnostic pattern {:?}",
                                            entry.upstream_path, expected_case.case_id, pattern
                                        ));
                                    }
                                }
                            }
                            // An upstream warning assertion may not be silently
                            // dropped by a port: every message upstream
                            // content-checks must be declared.
                            for pattern in &upstream_case.warning_patterns {
                                if !expected_case
                                    .expected_warning_patterns
                                    .iter()
                                    .any(|declared| declared == pattern)
                                {
                                    upstream_case_failures.push(format!(
                                        "{}: expected_cases entry `{}` is missing upstream verifier-warning pattern {:?}",
                                        entry.upstream_path, expected_case.case_id, pattern
                                    ));
                                }
                            }
                            if upstream_case.warning_patterns.is_empty()
                                && !expected_case.expected_warning_patterns.is_empty()
                            {
                                upstream_case_failures.push(format!(
                                    "{}: expected_cases entry `{}` declares expected_warning_patterns but upstream Verus harness case `{}` asserts no verifier warning",
                                    entry.upstream_path, expected_case.case_id, upstream_id
                                ));
                            }
                            if upstream_case.rust_error {
                                if upstream_case.error_patterns.is_empty() {
                                    upstream_case_failures.push(format!(
                                        "{}: upstream Rust-error harness case `{}` has no extracted diagnostic pattern",
                                        entry.upstream_path, upstream_id
                                    ));
                                }
                                for trust_vc_path in
                                    expected_case_trust_vc_paths(entry, expected_case)
                                {
                                    if !entry_trust_vc_path_set.contains(trust_vc_path) {
                                        continue;
                                    }
                                    match validate_repo_trust_vc_path(crate_root, trust_vc_path) {
                                        Ok(path) if is_cargo_fixture_root(&path) => {}
                                        Ok(_) => port_path_failures.push(format!(
                                            "{}: upstream Rust-error expected_cases entry `{}` must map to a cargo fixture trust_vc_path, got `{}`",
                                            entry.upstream_path,
                                            expected_case.case_id,
                                            trust_vc_path
                                        )),
                                        Err(_) => {}
                                    }
                                }
                            }
                            if !upstream_case.forbidden_diagnostic_patterns.is_empty() {
                                for pattern in &upstream_case.forbidden_diagnostic_patterns {
                                    if !expected_case
                                        .forbidden_diagnostic_patterns
                                        .iter()
                                        .any(|declared| declared == pattern)
                                    {
                                        upstream_case_failures.push(format!(
                                            "{}: expected_cases entry `{}` is missing upstream forbidden diagnostic-context pattern {:?}",
                                            entry.upstream_path, expected_case.case_id, pattern
                                        ));
                                    }
                                }
                            } else if !expected_case.forbidden_diagnostic_patterns.is_empty() {
                                upstream_case_failures.push(format!(
                                    "{}: expected_cases entry `{}` declares forbidden_diagnostic_patterns but upstream Verus harness case `{}` has no diagnostic-context exclusion",
                                    entry.upstream_path, expected_case.case_id, upstream_id
                                ));
                            }
                        }
                    }
                }
                Ok(Some(upstream_cases))
                    if upstream_cases.is_empty()
                        && upstream_case_extraction_bypassed(&entry.upstream_path) =>
                {
                    upstream_case_extraction_gaps.push(format!(
                        "{}: coverage gap because upstream case extraction could not derive a concrete fixture inventory for this /cargo-tests/ entry; classify it as unclassified or unsupported-gap until case extraction can prove the fixture inventory",
                        entry.upstream_path
                    ));
                }
                Ok(Some(upstream_cases)) if upstream_cases.is_empty() => {
                    upstream_case_extraction_gaps.push(format!(
                        "{}: coverage gap because upstream case extraction found no concrete Verus harness cases for this accepted entry; classify it as unsupported-gap or not-applicable until upstream case inventory can be proven",
                        entry.upstream_path
                    ));
                }
                Ok(_) => {}
                Err(error) => {
                    upstream_case_failures.push(format!("{}: {error}", entry.upstream_path));
                }
            }
            if upstream_case_extraction_bypassed(&entry.upstream_path) {
                if let Some(verus_path) = verus_path {
                    append_cargo_fixture_inventory_failures(
                        entry,
                        crate_root,
                        verus_path,
                        &mut port_path_failures,
                    );
                }
            }
            if port_path_failures.len() == entry_port_path_failure_start {
                run_candidates.extend(run_candidates_for_manifest_entry(entry, options));
            }
        }
    }
    Ok(VerusCorpusReport {
        manifest_path: manifest_path.to_path_buf(),
        manifest_schema_version: manifest.schema_version,
        upstream_repo: manifest.upstream_repo,
        upstream_ref: manifest.upstream_ref,
        upstream_test_roots: manifest.test_roots,
        upstream_test_count: upstream_tests.len(),
        entry_count: manifest.entries.len(),
        classification_counts,
        replacement_summary,
        duplicate_entries,
        invalid_entries,
        missing_entries,
        extra_entries,
        unsupported_entries,
        failing_entries,
        port_path_failures,
        upstream_case_failures,
        ignored_upstream_cases,
        upstream_case_extraction_gaps,
        porting_next_action,
        accepted_executable_ports,
        unsupported_gap_evidence,
        accepted_trust_vc_source_hashes,
        run_candidates,
    })
}

fn verus_corpus_porting_next_action(
    manifest: &VerusManifest,
    manifest_path: &Path,
    crate_root: &Path,
) -> Option<VerusCorpusPortingAction> {
    let mut classifications = BTreeSet::new();
    let mut blocking_entries = 0;
    for entry in &manifest.entries {
        if matches!(
            entry.classification.as_str(),
            "unsupported-gap" | "unclassified"
        ) {
            blocking_entries += 1;
            classifications.insert(entry.classification.clone());
        }
    }
    if blocking_entries == 0 {
        return None;
    }

    let manifest_display = report_path_string(manifest_path, crate_root);
    Some(VerusCorpusPortingAction {
        command: format!(
            "cargo trust_vc evidence . --manifest {} --scaffold-verus-port-stubs",
            shell_quote(&manifest_display)
        ),
        working_directory: crate_root.display().to_string(),
        manifest_path: manifest_display,
        blocking_entries,
        classifications: classifications.into_iter().collect(),
    })
}

fn unsupported_entry_has_partial_trust_vc_evidence(entry: &VerusManifestEntry) -> bool {
    !entry.trust_vc_paths.is_empty() || !entry.expected_cases.is_empty()
}

fn append_unsupported_scout_inventory_failures(
    entry: &VerusManifestEntry,
    crate_root: &Path,
    failures: &mut Vec<String>,
) {
    if entry.trust_vc_paths.is_empty() {
        return;
    }

    let mut source_cases = Vec::new();
    let mut inspected_paths = Vec::new();
    for trust_vc_path in &entry.trust_vc_paths {
        let Ok(path) = validate_repo_trust_vc_path(crate_root, trust_vc_path) else {
            continue;
        };
        if !path.is_file() || path.extension().and_then(|ext| ext.to_str()) != Some("rs") {
            continue;
        }
        inspected_paths.push(trust_vc_path.clone());
        match read_scout_expected_case_inventory(&path) {
            Ok(mut cases) => source_cases.append(&mut cases),
            Err(_) => continue,
        }
    }

    if source_cases.is_empty() {
        return;
    }

    let mut source_by_id: BTreeMap<&str, &ScoutExpectedCaseInventory> = BTreeMap::new();
    let mut duplicate_source_ids = Vec::new();
    for source_case in &source_cases {
        if source_by_id
            .insert(source_case.case_id.as_str(), source_case)
            .is_some()
        {
            duplicate_source_ids.push(source_case.case_id.clone());
        }
    }

    let manifest_by_id: BTreeMap<&str, &VerusExpectedCase> = entry
        .expected_cases
        .iter()
        .map(|expected_case| (expected_case.case_id.as_str(), expected_case))
        .collect();
    let source_ids: BTreeSet<&str> = source_by_id.keys().copied().collect();
    let manifest_ids: BTreeSet<&str> = manifest_by_id.keys().copied().collect();
    let missing_from_manifest: Vec<String> = source_ids
        .difference(&manifest_ids)
        .map(|case_id| (*case_id).to_string())
        .collect();
    let missing_from_source: Vec<String> = manifest_ids
        .difference(&source_ids)
        .map(|case_id| (*case_id).to_string())
        .collect();
    let mut mismatches = Vec::new();
    for case_id in source_ids.intersection(&manifest_ids) {
        let (Some(source_case), Some(manifest_case)) =
            (source_by_id.get(*case_id), manifest_by_id.get(*case_id))
        else {
            continue;
        };
        if source_case.expected_verdict != manifest_case.expected_verdict {
            mismatches.push(format!(
                "{} verdict source={} manifest={}",
                case_id,
                expected_verdict_label(source_case.expected_verdict),
                expected_verdict_label(manifest_case.expected_verdict)
            ));
        }
        if source_case.min_obligations != manifest_case.min_obligations {
            mismatches.push(format!(
                "{} min_obligations source={} manifest={}",
                case_id, source_case.min_obligations, manifest_case.min_obligations
            ));
        }
    }

    if duplicate_source_ids.is_empty()
        && missing_from_manifest.is_empty()
        && missing_from_source.is_empty()
        && mismatches.is_empty()
    {
        return;
    }

    let mut details = Vec::new();
    if !duplicate_source_ids.is_empty() {
        details.push(format!(
            "duplicate source ids [{}]",
            limited_case_id_sample(&duplicate_source_ids)
        ));
    }
    if !missing_from_manifest.is_empty() {
        details.push(format!(
            "source-only ids [{}]",
            limited_case_id_sample(&missing_from_manifest)
        ));
    }
    if !missing_from_source.is_empty() {
        details.push(format!(
            "manifest-only ids [{}]",
            limited_case_id_sample(&missing_from_source)
        ));
    }
    if !mismatches.is_empty() {
        details.push(format!(
            "mismatches [{}]",
            limited_case_id_sample(&mismatches)
        ));
    }
    failures.push(format!(
        "{}: unsupported scout expected_cases drift for {}: {}",
        entry.upstream_path,
        joined_or_none(&inspected_paths),
        details.join("; ")
    ));
}

fn read_scout_expected_case_inventory(
    path: &Path,
) -> Result<Vec<ScoutExpectedCaseInventory>, String> {
    let source = fs::read_to_string(path)
        .map_err(|error| format!("failed to read `{}`: {error}", path.display()))?;
    parse_scout_expected_case_inventory(&source)
        .map_err(|error| format!("failed to parse `{}`: {error}", path.display()))
}

fn parse_scout_expected_case_inventory(
    source: &str,
) -> Result<Vec<ScoutExpectedCaseInventory>, String> {
    let file = syn::parse_file(source).map_err(|error| error.to_string())?;
    let mut cases = Vec::new();
    for item in file.items {
        let syn::Item::Const(item_const) = item else {
            continue;
        };
        if !item_const.ident.to_string().ends_with("EXPECTED_CASES") {
            continue;
        }
        let Some(array) = expected_case_array_expr(&item_const.expr) else {
            continue;
        };
        for expr in &array.elems {
            if let Some(case) = scout_expected_case_from_expr(expr)? {
                cases.push(case);
            }
        }
    }
    Ok(cases)
}

fn expected_case_array_expr(expr: &syn::Expr) -> Option<&syn::ExprArray> {
    match expr {
        syn::Expr::Array(array) => Some(array),
        syn::Expr::Paren(paren) => expected_case_array_expr(&paren.expr),
        syn::Expr::Reference(reference) => expected_case_array_expr(&reference.expr),
        _ => None,
    }
}

fn scout_expected_case_from_expr(
    expr: &syn::Expr,
) -> Result<Option<ScoutExpectedCaseInventory>, String> {
    match unwrap_paren_expr(expr) {
        syn::Expr::Tuple(tuple) => scout_expected_case_from_tuple(tuple),
        syn::Expr::Struct(struct_expr) => scout_expected_case_from_struct(struct_expr),
        _ => Ok(None),
    }
}

fn scout_expected_case_from_tuple(
    tuple: &syn::ExprTuple,
) -> Result<Option<ScoutExpectedCaseInventory>, String> {
    if tuple.elems.len() != 4 {
        return Ok(None);
    }
    let Some(case_id_expr) = tuple.elems.first() else {
        return Ok(None);
    };
    let Some(status_expr) = tuple.elems.iter().nth(2) else {
        return Ok(None);
    };
    let case_id = string_lit_expr(case_id_expr)?;
    let status = string_lit_expr(status_expr)?;
    let Some(expected_verdict) = scout_expected_verdict_label(&status) else {
        return Ok(None);
    };
    Ok(Some(ScoutExpectedCaseInventory {
        case_id,
        expected_verdict,
        min_obligations: match tuple.elems.iter().nth(3) {
            Some(expr) => usize_lit_expr(expr)?,
            None => return Ok(None),
        },
    }))
}

fn scout_expected_case_from_struct(
    struct_expr: &syn::ExprStruct,
) -> Result<Option<ScoutExpectedCaseInventory>, String> {
    let mut case_id = None;
    let mut status = None;
    let mut min_obligations = None;
    for field in &struct_expr.fields {
        let field_name = match &field.member {
            syn::Member::Named(ident) => ident.to_string(),
            syn::Member::Unnamed(_) => continue,
        };
        match field_name.as_str() {
            "case" | "case_id" => case_id = Some(string_lit_expr(&field.expr)?),
            "evidence_status" | "status" | "expected_verdict" => {
                status = Some(string_lit_expr(&field.expr)?)
            }
            "min_obligations" => min_obligations = Some(usize_lit_expr(&field.expr)?),
            _ => {}
        }
    }
    let Some(case_id) = case_id else {
        return Ok(None);
    };
    let Some(status) = status else {
        return Ok(None);
    };
    let Some(min_obligations) = min_obligations else {
        return Ok(None);
    };
    let Some(expected_verdict) = scout_expected_verdict_label(&status) else {
        return Ok(None);
    };
    Ok(Some(ScoutExpectedCaseInventory {
        case_id,
        expected_verdict,
        min_obligations,
    }))
}

fn unwrap_paren_expr(expr: &syn::Expr) -> &syn::Expr {
    match expr {
        syn::Expr::Paren(paren) => unwrap_paren_expr(&paren.expr),
        _ => expr,
    }
}

fn string_lit_expr(expr: &syn::Expr) -> Result<String, String> {
    match unwrap_paren_expr(expr) {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(value),
            ..
        }) => Ok(value.value()),
        other => Err(format!(
            "expected string literal in expected-case inventory, got `{}`",
            other.to_token_stream()
        )),
    }
}

fn usize_lit_expr(expr: &syn::Expr) -> Result<usize, String> {
    match unwrap_paren_expr(expr) {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(value),
            ..
        }) => value
            .base10_parse()
            .map_err(|error| format!("expected usize literal in expected-case inventory: {error}")),
        other => Err(format!(
            "expected usize literal in expected-case inventory, got `{}`",
            other.to_token_stream()
        )),
    }
}

fn scout_expected_verdict_label(value: &str) -> Option<VerusExpectedVerdict> {
    match value {
        "verified" => Some(VerusExpectedVerdict::Verified),
        "counterexample" => Some(VerusExpectedVerdict::Counterexample),
        "error" => Some(VerusExpectedVerdict::Error),
        // "verified-blocker" and "unknown" are intentionally excluded from scout drift detection.
        _ => None,
    }
}

fn limited_case_id_sample(values: &[String]) -> String {
    let mut sample = values
        .iter()
        .take(CORPUS_BLOCKER_SUMMARY_LIMIT)
        .cloned()
        .collect::<Vec<_>>();
    let remaining = values.len().saturating_sub(sample.len());
    if remaining > 0 {
        sample.push(format!("{remaining} more"));
    }
    sample.join(", ")
}

fn verus_manifest_entry_evidence(entry: &VerusManifestEntry) -> VerusManifestEntryEvidence {
    VerusManifestEntryEvidence {
        upstream_path: entry.upstream_path.clone(),
        classification: entry.classification.clone(),
        evidence_kind: evidence_kind_label(entry.evidence_kind).to_string(),
        owner_issue: entry.owner_issue.clone(),
        owner_issue_url: owner_issue_url(&entry.owner_issue),
        reason: entry.reason.clone(),
        trust_vc_paths: entry.trust_vc_paths.clone(),
        expected_cases: entry
            .expected_cases
            .iter()
            .map(verus_expected_case_evidence)
            .collect(),
        known_gaps: entry.known_gaps.clone(),
        notes: entry.notes.clone(),
    }
}

fn verus_expected_case_evidence(expected_case: &VerusExpectedCase) -> VerusExpectedCaseEvidence {
    VerusExpectedCaseEvidence {
        case_id: expected_case.case_id.clone(),
        upstream_case_id: expected_case.upstream_case_id.clone(),
        trust_vc_path: expected_case.trust_vc_path.clone(),
        expected_verdict: expected_verdict_label(expected_case.expected_verdict).to_string(),
        min_obligations: expected_case.min_obligations,
        obligation_fingerprints: expected_case.obligation_fingerprints.clone(),
        expected_error_patterns: expected_case.expected_error_patterns.clone(),
        expected_rust_diagnostic_pattern_sets: expected_case
            .expected_rust_diagnostic_pattern_sets
            .clone(),
        forbidden_diagnostic_patterns: expected_case.forbidden_diagnostic_patterns.clone(),
        expected_warning_patterns: expected_case.expected_warning_patterns.clone(),
    }
}

fn append_trust_vc_source_hash_pin_failures(
    entry: &VerusManifestEntry,
    observed_hashes: &[TrustVcSourcePathHash],
    require_pins: bool,
    refresh_pins: bool,
    failures: &mut Vec<String>,
) {
    if refresh_pins {
        return;
    }
    if !require_pins && entry.trust_vc_source_hashes.is_empty() {
        return;
    }

    let trust_vc_path_set: BTreeSet<&str> =
        entry.trust_vc_paths.iter().map(String::as_str).collect();
    let mut pins_by_path: BTreeMap<&str, &TrustVcSourcePathHash> = BTreeMap::new();
    for pin in &entry.trust_vc_source_hashes {
        if !valid_sha256_digest_label(&pin.sha256) {
            failures.push(format!(
                "{}: trust_vc_source_hashes entry `{}` has invalid sha256 digest `{}`",
                entry.upstream_path, pin.path, pin.sha256
            ));
        }
        if !trust_vc_path_set.contains(pin.path.as_str()) {
            failures.push(format!(
                "{}: trust_vc_source_hashes entry `{}` must match an entry-level trust_vc_paths value",
                entry.upstream_path, pin.path
            ));
        }
        if pins_by_path.insert(pin.path.as_str(), pin).is_some() {
            failures.push(format!(
                "{}: duplicate trust_vc_source_hashes entry for `{}`",
                entry.upstream_path, pin.path
            ));
        }
    }

    if require_pins {
        for trust_vc_path in &entry.trust_vc_paths {
            if !pins_by_path.contains_key(trust_vc_path.as_str()) {
                failures.push(format!(
                    "{}: accepted schema v2 entry must pin trust_vc_source_hashes for `{}`",
                    entry.upstream_path, trust_vc_path
                ));
            }
        }
    }

    for observed in observed_hashes {
        let Some(pin) = pins_by_path.get(observed.path.as_str()) else {
            continue;
        };
        if pin.kind != observed.kind {
            failures.push(format!(
                "{}: trust_vc_source_hashes entry `{}` expected kind {}, observed {}",
                entry.upstream_path, observed.path, pin.kind, observed.kind
            ));
        }
        if pin.sha256 != observed.sha256 {
            failures.push(format!(
                "{}: trust_vc_source_hashes entry `{}` expected {}, observed {}",
                entry.upstream_path, observed.path, pin.sha256, observed.sha256
            ));
        }
    }
}

fn append_expected_case_obligation_pin_failures(
    entry: &VerusManifestEntry,
    expected_case: &VerusExpectedCase,
    require_pins: bool,
    refresh_pins: bool,
    failures: &mut Vec<String>,
) {
    let upstream_path = &entry.upstream_path;
    if entry.evidence_kind == VerusEvidenceKind::CargoTrustVcIntegrationTest {
        if expected_case.expected_verdict != VerusExpectedVerdict::Verified {
            failures.push(format!(
                "{}: cargo_trust_vc_integration_test expected case `{}` must use expected_verdict `verified`",
                upstream_path, expected_case.case_id
            ));
        }
        if expected_case.min_obligations != 0 {
            failures.push(format!(
                "{}: cargo_trust_vc_integration_test expected case `{}` must declare min_obligations 0",
                upstream_path, expected_case.case_id
            ));
        }
        if !expected_case.obligation_fingerprints.is_empty() {
            failures.push(format!(
                "{}: cargo_trust_vc_integration_test expected case `{}` must not declare obligation_fingerprints",
                upstream_path, expected_case.case_id
            ));
        }
        return;
    }
    if refresh_pins {
        return;
    }
    if !require_pins && expected_case.obligation_fingerprints.is_empty() {
        return;
    }

    for fingerprint in &expected_case.obligation_fingerprints {
        if !valid_sha256_digest_label(fingerprint) {
            failures.push(format!(
                "{}: expected_cases entry `{}` has invalid obligation_fingerprints value `{}`",
                upstream_path, expected_case.case_id, fingerprint
            ));
        }
    }
    for fingerprint in duplicate_obligation_fingerprints(&expected_case.obligation_fingerprints) {
        failures.push(format!(
            "{}: expected_cases entry `{}` has duplicate obligation_fingerprints value `{}`",
            upstream_path, expected_case.case_id, fingerprint
        ));
    }

    if require_pins
        && expected_case.min_obligations > 0
        && expected_case.obligation_fingerprints.is_empty()
    {
        failures.push(format!(
            "{}: schema v2 expected_cases entry `{}` must pin obligation_fingerprints when min_obligations is {}",
            upstream_path, expected_case.case_id, expected_case.min_obligations
        ));
    }

    if !expected_case.obligation_fingerprints.is_empty()
        && expected_case.min_obligations != expected_case.obligation_fingerprints.len()
    {
        failures.push(format!(
            "{}: expected_cases entry `{}` min_obligations {} must equal pinned obligation_fingerprints count {}",
            upstream_path,
            expected_case.case_id,
            expected_case.min_obligations,
            expected_case.obligation_fingerprints.len()
        ));
    }
}

fn append_trust_vc_check_arg_failures(
    entry: &VerusManifestEntry,
    accepted_entry: bool,
    failures: &mut Vec<String>,
) {
    if entry.trust_vc_check_args.is_empty() {
        return;
    }
    if !accepted_entry {
        failures.push(format!(
            "{}: trust_vc_check_args are only valid on accepted executable entries",
            entry.upstream_path
        ));
    }
    let mut seen = BTreeSet::new();
    for arg in &entry.trust_vc_check_args {
        if !SUPPORTED_TRUST_VC_CHECK_ARGS.contains(&arg.as_str()) {
            failures.push(format!(
                "{}: unsupported trust_vc_check_args value `{}`; supported values: {}",
                entry.upstream_path,
                arg,
                SUPPORTED_TRUST_VC_CHECK_ARGS.join(", ")
            ));
        }
        if !seen.insert(arg.as_str()) {
            failures.push(format!(
                "{}: duplicate trust_vc_check_args value `{}`",
                entry.upstream_path, arg
            ));
        }
    }
    if entry
        .trust_vc_check_args
        .iter()
        .any(|arg| arg == "--no-cheating")
    {
        for expected_case in &entry.expected_cases {
            if expected_case.expected_verdict != VerusExpectedVerdict::Error {
                failures.push(format!(
                    "{}: --no-cheating expected case `{}` must use expected_verdict `error`",
                    entry.upstream_path, expected_case.case_id
                ));
            }
            if no_cheating_expected_case_source_file_pattern(expected_case).is_none() {
                failures.push(format!(
                    "{}: --no-cheating expected case `{}` must include a source file pattern like `src/<case>.rs` in expected_error_patterns",
                    entry.upstream_path, expected_case.case_id
                ));
            }
        }
    }
}

fn no_cheating_expected_case_source_file_pattern(
    expected_case: &VerusExpectedCase,
) -> Option<&str> {
    expected_case
        .expected_error_patterns
        .iter()
        .map(String::as_str)
        .find(|pattern| {
            let pattern = pattern.trim();
            pattern.starts_with("src/")
                && pattern.ends_with(".rs")
                && !pattern.contains('*')
                && !pattern.contains('\n')
        })
}

fn expected_cases_use_trust_vc_paths(expected_cases: &[VerusExpectedCase]) -> bool {
    expected_cases
        .iter()
        .any(|expected_case| expected_case.trust_vc_path.is_some())
}

fn ignored_upstream_case_evidence(
    entry: &VerusManifestEntry,
    upstream_cases: &[UpstreamVerusHarnessCase],
) -> Vec<IgnoredUpstreamCaseEvidence> {
    upstream_cases
        .iter()
        .filter(|case| case.ignored)
        .map(|case| IgnoredUpstreamCaseEvidence {
            upstream_path: entry.upstream_path.clone(),
            case_id: case.case_id.clone(),
            expected_verdict: expected_verdict_label(case.expected_verdict).to_string(),
            expected_case_ids: entry
                .expected_cases
                .iter()
                .filter(|expected_case| upstream_case_id(expected_case) == case.case_id)
                .map(|expected_case| expected_case.case_id.clone())
                .collect(),
        })
        .collect()
}

fn expected_case_trust_vc_paths<'a>(
    entry: &'a VerusManifestEntry,
    expected_case: &'a VerusExpectedCase,
) -> Vec<&'a str> {
    match expected_case.trust_vc_path.as_deref() {
        Some(trust_vc_path) => vec![trust_vc_path],
        None => entry.trust_vc_paths.iter().map(String::as_str).collect(),
    }
}

fn run_candidates_for_manifest_entry(
    entry: &VerusManifestEntry,
    options: CorpusLoadOptions,
) -> Vec<TrustVcCorpusRunCandidate> {
    let mut candidates = if !expected_cases_use_trust_vc_paths(&entry.expected_cases) {
        vec![TrustVcCorpusRunCandidate {
            upstream_path: entry.upstream_path.clone(),
            classification: entry.classification.clone(),
            evidence_kind: entry.evidence_kind,
            trust_vc_paths: entry.trust_vc_paths.clone(),
            trust_vc_check_args: entry.trust_vc_check_args.clone(),
            expected_cases: entry.expected_cases.clone(),
        }]
    } else {
        let mut expected_cases_by_path: BTreeMap<String, Vec<VerusExpectedCase>> = BTreeMap::new();
        for expected_case in &entry.expected_cases {
            if let Some(trust_vc_path) = &expected_case.trust_vc_path {
                expected_cases_by_path
                    .entry(trust_vc_path.clone())
                    .or_default()
                    .push(expected_case.clone());
            }
        }
        expected_cases_by_path
            .into_iter()
            .map(
                |(trust_vc_path, expected_cases)| TrustVcCorpusRunCandidate {
                    upstream_path: entry.upstream_path.clone(),
                    classification: entry.classification.clone(),
                    evidence_kind: entry.evidence_kind,
                    trust_vc_paths: vec![trust_vc_path],
                    trust_vc_check_args: entry.trust_vc_check_args.clone(),
                    expected_cases,
                },
            )
            .collect()
    };
    if options.refresh_evidence_pins {
        relax_refresh_run_candidate_pins(&mut candidates);
    }
    candidates
}

fn relax_refresh_run_candidate_pins(candidates: &mut [TrustVcCorpusRunCandidate]) {
    for candidate in candidates {
        for expected_case in &mut candidate.expected_cases {
            expected_case.obligation_fingerprints.clear();
            if expected_case.expected_verdict == VerusExpectedVerdict::Error {
                expected_case.min_obligations = 0;
            } else if expected_case.min_obligations > 1 {
                expected_case.min_obligations = 1;
            }
        }
    }
}

#[cfg(test)]
fn run_trust_vc_corpus(
    crate_root: &Path,
    corpus: &VerusCorpusReport,
    command_template: Option<&str>,
) -> TrustVcCorpusRunReport {
    run_trust_vc_corpus_with_env(crate_root, corpus, command_template, &[], &BTreeMap::new())
}

fn run_trust_vc_corpus_with_env(
    crate_root: &Path,
    corpus: &VerusCorpusReport,
    command_template: Option<&str>,
    env: &[(String, String)],
    cargo_fixture_preflight_failures: &BTreeMap<PathBuf, Vec<String>>,
) -> TrustVcCorpusRunReport {
    run_trust_vc_corpus_with_trust_vc_binary_and_env(
        crate_root,
        corpus,
        command_template,
        env,
        None,
        cargo_fixture_preflight_failures,
    )
}

fn run_trust_vc_corpus_with_trust_vc_binary_and_env(
    crate_root: &Path,
    corpus: &VerusCorpusReport,
    command_template: Option<&str>,
    env: &[(String, String)],
    trust_vc_binary: Option<&Path>,
    cargo_fixture_preflight_failures: &BTreeMap<PathBuf, Vec<String>>,
) -> TrustVcCorpusRunReport {
    let mut results = Vec::new();
    let mut skipped_entries = 0;
    for candidate in &corpus.run_candidates {
        if candidate.trust_vc_paths.is_empty() {
            skipped_entries += 1;
            continue;
        }
        match command_template {
            Some(template) => {
                for trust_vc_path in &candidate.trust_vc_paths {
                    results.push(run_trust_vc_corpus_command(
                        crate_root,
                        candidate,
                        trust_vc_path,
                        template,
                        env,
                    ));
                }
            }
            None if candidate.evidence_kind == VerusEvidenceKind::CargoTrustVcIntegrationTest => {
                if candidate_has_cargo_trust_vc_integration_test_path(crate_root, candidate) {
                    results.push(run_trust_vc_corpus_cargo_trust_vc_integration_test(
                        crate_root, candidate, env,
                    ));
                } else {
                    results.push(failed_trust_vc_corpus_run_result(
                        candidate,
                        TrustVcCorpusExecutionMode::CargoTrustVcIntegrationTest,
                        Some(
                            "cargo_trust_vc_integration_test evidence requires a cargo-trust-vc integration test path",
                        ),
                        vec![
                            "cargo_trust_vc_integration_test evidence requires trust_vc_path under crates/cargo-trust-vc/tests/*.rs".to_string(),
                        ],
                        None,
                        Vec::new(),
                    ));
                }
            }
            None if candidate_has_cargo_fixture_path(crate_root, candidate) => {
                results.push(run_trust_vc_corpus_cargo_fixture(
                    crate_root,
                    candidate,
                    env,
                    trust_vc_binary,
                    cargo_fixture_preflight_failures,
                ));
            }
            None if candidate_has_cargo_trust_vc_integration_test_path(crate_root, candidate) => {
                results.push(failed_trust_vc_corpus_run_result(
                    candidate,
                    TrustVcCorpusExecutionMode::CargoTrustVcIntegrationTest,
                    Some(
                        "cargo-trust-vc integration tests require explicit cargo_trust_vc_integration_test evidence_kind",
                    ),
                    vec![
                        "proof_obligation evidence cannot be satisfied by cargo-trust-vc integration-test witnesses".to_string(),
                    ],
                    None,
                    Vec::new(),
                ));
            }
            None => results.push(run_trust_vc_corpus_direct(crate_root, candidate)),
        }
    }
    let attempted_paths: usize = results
        .iter()
        .map(|result| result.trust_vc_paths.len().max(1))
        .sum();
    let passed_paths = results
        .iter()
        .filter(|result| result.status == GateStatus::Passed)
        .map(|result| result.trust_vc_paths.len().max(1))
        .sum();
    let failed_paths = attempted_paths.saturating_sub(passed_paths);
    TrustVcCorpusRunReport {
        attempted_paths,
        passed_paths,
        failed_paths,
        skipped_entries,
        results,
    }
}

fn refresh_trust_vc_corpus_evidence_gate(
    manifest_path: &Path,
    corpus: &VerusCorpusReport,
    run_report: Option<&TrustVcCorpusRunReport>,
) -> GateResult {
    match refresh_trust_vc_corpus_evidence_manifest(manifest_path, corpus, run_report) {
        Ok(summary) => GateResult {
            name: "TrustVc corpus evidence refresh".to_string(),
            required: true,
            status: GateStatus::Passed,
            detail: Some(format!(
                "updated {} accepted entry source-hash set(s), {} source path hash(es), {} expected case fingerprint set(s), {} obligation fingerprint(s)",
                summary.accepted_entries,
                summary.source_hash_paths,
                summary.obligation_cases,
                summary.obligation_fingerprints
            )),
            command: None,
        },
        Err(error) => GateResult {
            name: "TrustVc corpus evidence refresh".to_string(),
            required: true,
            status: GateStatus::Failed,
            detail: Some(error.to_string()),
            command: None,
        },
    }
}

fn refresh_trust_vc_corpus_evidence_manifest(
    manifest_path: &Path,
    corpus: &VerusCorpusReport,
    run_report: Option<&TrustVcCorpusRunReport>,
) -> Result<TrustVcCorpusEvidenceRefreshSummary, EvidenceError> {
    if manifest_path.extension().and_then(|ext| ext.to_str()) != Some("json") {
        return Err(EvidenceError::new(
            "--refresh-trust-vc-corpus-evidence requires a JSON manifest",
        ));
    }
    let run_report = run_report.ok_or_else(|| {
        EvidenceError::new(
            "--refresh-trust-vc-corpus-evidence requires --run-trust-vc-corpus so obligation fingerprints are refreshed from a passing corpus run",
        )
    })?;
    if !run_report.passed() {
        return Err(EvidenceError::new(format!(
            "--refresh-trust-vc-corpus-evidence requires a passing TrustVc corpus run, got {} attempted, {} failed",
            run_report.attempted_paths, run_report.failed_paths
        )));
    }
    // Integration-test entries are WRAPPER EXECUTION WITNESSES: they are validated by
    // their cargo-trust-vc integration test PASSING in this run (the run-passed gate
    // above), not by proof-obligation fingerprints — they produce none. We therefore
    // refresh their `trust_vc_source_hashes` (a content commitment) but DELIBERATELY do
    // NOT synthesize obligation fingerprints from wrapper execution. (Previously the
    // refresh refused outright if ANY integration test executed, which made the
    // all-or-nothing refresh impossible once the cargo fixtures became fetchable; that
    // blanket refusal is replaced by the per-entry skip below, guarded by a
    // declared-vs-actual cross-check so the witness path cannot be used to dodge
    // fingerprinting a genuine proof entry.) Map each upstream to whether it actually
    // executed as an integration test, for that cross-check.
    let mut ran_as_integration_test: BTreeMap<&str, bool> = BTreeMap::new();
    for result in &run_report.results {
        let entry = ran_as_integration_test
            .entry(result.upstream_path.as_str())
            .or_insert(false);
        if result.execution_mode == TrustVcCorpusExecutionMode::CargoTrustVcIntegrationTest {
            *entry = true;
        }
    }

    let text = fs::read_to_string(manifest_path).map_err(|err| {
        EvidenceError::new(format!(
            "failed to read manifest `{}` for evidence refresh: {err}",
            manifest_path.display()
        ))
    })?;
    let mut manifest: JsonVerusManifest = serde_json::from_str(&text).map_err(|err| {
        EvidenceError::new(format!(
            "failed to parse JSON manifest `{}` for evidence refresh: {err}",
            manifest_path.display()
        ))
    })?;
    validate_json_manifest_schema(&manifest)?;

    let source_hashes_by_upstream = accepted_source_hashes_by_upstream(corpus)?;
    let observed_cases_by_key = observed_cases_by_upstream_and_case(run_report)?;
    let mut summary = TrustVcCorpusEvidenceRefreshSummary {
        accepted_entries: 0,
        source_hash_paths: 0,
        obligation_cases: 0,
        obligation_fingerprints: 0,
    };

    for entry in &mut manifest.entries {
        if !requires_trust_vc_paths(&entry.classification) {
            continue;
        }
        summary.accepted_entries += 1;
        let source_hashes = source_hashes_by_upstream
            .get(entry.upstream_path.as_str())
            .ok_or_else(|| {
                EvidenceError::new(format!(
                    "{}: no observed trust_vc_source_hashes available for accepted entry",
                    entry.upstream_path
                ))
            })?;
        ensure_refresh_source_paths_match(entry, &source_hashes.trust_vc_paths)?;
        entry.trust_vc_source_hashes = source_hashes.trust_vc_paths.clone();
        summary.source_hash_paths += entry.trust_vc_source_hashes.len();

        // Witness entries (cargo-trust-vc integration tests) carry NO proof
        // obligations; their source_hashes are pinned above and their validity comes
        // from the integration test passing in this run. Cross-check the manifest's
        // declared evidence_kind against how the entry ACTUALLY executed, then skip
        // obligation fingerprinting for genuine witnesses. A mismatch — a proof entry
        // that executed as an integration test, or a declared witness that did not — is
        // REFUSED, so the witness path can never be used to dodge fingerprinting a real
        // proof entry, and wrapper execution is never minted as fingerprint evidence.
        let declared_witness =
            entry.evidence_kind == VerusEvidenceKind::CargoTrustVcIntegrationTest;
        let executed_as_witness = ran_as_integration_test
            .get(entry.upstream_path.as_str())
            .copied()
            .unwrap_or(false);
        if declared_witness != executed_as_witness {
            return Err(EvidenceError::new(format!(
                "{}: declared evidence_kind `{}` disagrees with execution \
                 (declared_witness={declared_witness}, executed_as_integration_test={executed_as_witness}); \
                 refusing to refresh",
                entry.upstream_path,
                evidence_kind_label(entry.evidence_kind),
            )));
        }
        if declared_witness {
            continue;
        }

        for expected_case in &mut entry.expected_cases {
            let key = (entry.upstream_path.clone(), expected_case.case_id.clone());
            let observed_case = observed_cases_by_key.get(&key).ok_or_else(|| {
                EvidenceError::new(format!(
                    "{}: no observed TrustVc corpus case `{}` available for obligation fingerprint refresh",
                    entry.upstream_path, expected_case.case_id
                ))
            })?;
            let mut fingerprints = observed_case.obligation_fingerprints.clone();
            fingerprints.sort();
            // Canonical SET commitment: schema validation rejects duplicate
            // pinned fingerprints and the corpus runner compares the pins
            // against the DEDUPED observed set (and checks `min_obligations`
            // against the unique count), so the refresh must write the
            // deduplicated set or its own output fails the next validation.
            // Repeated identical obligations (e.g. the same scoped `requires`
            // re-checked by several queries of one case) hash identically;
            // deduping loses no evidence — the fingerprints are a content
            // commitment, not a multiplicity count.
            fingerprints.dedup();
            if let Some(invalid) = fingerprints
                .iter()
                .find(|fingerprint| !valid_sha256_digest_label(fingerprint))
            {
                return Err(EvidenceError::new(format!(
                    "{}: observed case `{}` produced invalid obligation fingerprint `{}`",
                    entry.upstream_path, expected_case.case_id, invalid
                )));
            }
            if expected_case.expected_verdict != VerusExpectedVerdict::Error
                && fingerprints.is_empty()
            {
                return Err(EvidenceError::new(format!(
                    "{}: observed non-error case `{}` has no obligation fingerprints",
                    entry.upstream_path, expected_case.case_id
                )));
            }
            expected_case.min_obligations = fingerprints.len();
            expected_case.obligation_fingerprints = fingerprints;
            summary.obligation_cases += 1;
            summary.obligation_fingerprints += expected_case.obligation_fingerprints.len();
        }
    }

    let json = serde_json::to_string_pretty(&manifest).map_err(|err| {
        EvidenceError::new(format!(
            "failed to serialize refreshed manifest `{}`: {err}",
            manifest_path.display()
        ))
    })?;
    fs::write(manifest_path, format!("{json}\n")).map_err(|err| {
        EvidenceError::new(format!(
            "failed to write refreshed manifest `{}`: {err}",
            manifest_path.display()
        ))
    })?;
    Ok(summary)
}

fn accepted_source_hashes_by_upstream(
    corpus: &VerusCorpusReport,
) -> Result<BTreeMap<&str, &AcceptedTrustVcSourceHashes>, EvidenceError> {
    let mut by_upstream = BTreeMap::new();
    for source_hashes in &corpus.accepted_trust_vc_source_hashes {
        if by_upstream
            .insert(source_hashes.upstream_path.as_str(), source_hashes)
            .is_some()
        {
            return Err(EvidenceError::new(format!(
                "{}: duplicate accepted source hash evidence",
                source_hashes.upstream_path
            )));
        }
    }
    Ok(by_upstream)
}

fn observed_cases_by_upstream_and_case(
    run_report: &TrustVcCorpusRunReport,
) -> Result<BTreeMap<(String, String), &TrustVcCorpusObservedCase>, EvidenceError> {
    let mut by_key = BTreeMap::new();
    for result in &run_report.results {
        for observed_case in &result.observed_cases {
            let key = (result.upstream_path.clone(), observed_case.case_id.clone());
            if by_key.insert(key.clone(), observed_case).is_some() {
                return Err(EvidenceError::new(format!(
                    "{}: duplicate observed TrustVc corpus case `{}`",
                    key.0, key.1
                )));
            }
        }
    }
    Ok(by_key)
}

fn ensure_refresh_source_paths_match(
    entry: &VerusManifestEntry,
    observed_hashes: &[TrustVcSourcePathHash],
) -> Result<(), EvidenceError> {
    let expected_paths = entry
        .trust_vc_paths
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let observed_paths = observed_hashes
        .iter()
        .map(|source_hash| source_hash.path.as_str())
        .collect::<BTreeSet<_>>();
    if expected_paths == observed_paths {
        return Ok(());
    }
    Err(EvidenceError::new(format!(
        "{}: observed trust_vc_source_hashes paths [{}] do not match trust_vc_paths [{}]",
        entry.upstream_path,
        observed_paths.into_iter().collect::<Vec<_>>().join(", "),
        expected_paths.into_iter().collect::<Vec<_>>().join(", ")
    )))
}

fn candidate_has_cargo_fixture_path(
    crate_root: &Path,
    candidate: &TrustVcCorpusRunCandidate,
) -> bool {
    candidate.trust_vc_paths.iter().any(|trust_vc_path| {
        validate_repo_trust_vc_path(crate_root, trust_vc_path)
            .ok()
            .is_some_and(|path| is_cargo_fixture_root(&path))
    })
}

fn candidate_has_cargo_trust_vc_integration_test_path(
    crate_root: &Path,
    candidate: &TrustVcCorpusRunCandidate,
) -> bool {
    candidate.trust_vc_paths.iter().any(|trust_vc_path| {
        validate_repo_trust_vc_path(crate_root, trust_vc_path)
            .ok()
            .is_some_and(|path| cargo_trust_vc_integration_test_target(crate_root, &path).is_some())
    })
}

fn cargo_trust_vc_integration_test_target(crate_root: &Path, path: &Path) -> Option<String> {
    if path.extension().and_then(|ext| ext.to_str()) != Some("rs") {
        return None;
    }
    let rel = repo_relative_string(crate_root, path).ok()?;
    let rest = rel.strip_prefix("crates/cargo-trust-vc/tests/")?;
    if rest.contains('/') {
        return None;
    }
    path.file_stem()
        .and_then(|stem| stem.to_str())
        .filter(|stem| !stem.trim().is_empty())
        .map(str::to_string)
}

fn is_cargo_fixture_root(path: &Path) -> bool {
    path.is_dir() && path.join("Cargo.toml").is_file()
}

fn trust_vc_corpus_fixture_fetch_gates(
    crate_root: &Path,
    corpus: &VerusCorpusReport,
    env: &[(String, String)],
) -> Vec<GateResult> {
    let mut fixture_roots = BTreeSet::new();
    for candidate in &corpus.run_candidates {
        for trust_vc_path in &candidate.trust_vc_paths {
            let Ok(path) = validate_repo_trust_vc_path(crate_root, trust_vc_path) else {
                continue;
            };
            if is_cargo_fixture_root(&path) {
                fixture_roots.insert(path);
            }
        }
    }

    fixture_roots
        .into_iter()
        .map(|fixture_root| {
            let rel = report_path_string(&fixture_root, crate_root);
            let output = run_cargo_fetch_for_fixture(&fixture_root, env);
            let status = gate_status_from_exit(output.command.exit_code);
            let detail = if output.command.exit_code == Some(0) {
                format!("{rel}: locked fixture dependencies fetched for offline corpus evidence")
            } else {
                let mut detail = format!(
                    "{rel}: cargo fetch failed for locked fixture dependencies with {}",
                    display_exit_code(output.command.exit_code)
                );
                if let Some(context) = command_failure_context(&output.command) {
                    detail.push_str(": ");
                    detail.push_str(&context);
                }
                detail
            };
            GateResult {
                name: format!("cargo fetch --locked {rel}"),
                required: true,
                status,
                detail: Some(detail),
                command: Some(output.command),
            }
        })
        .collect()
}

#[derive(Debug, Clone)]
struct DirectSourceTypecheckInput {
    trust_vc_path: String,
    path: PathBuf,
}

fn direct_source_rust_typecheck_gate(
    crate_root: &Path,
    output_dir: &Path,
    corpus: &VerusCorpusReport,
    env: &[(String, String)],
) -> GateResult {
    let (inputs, mut failures) = direct_source_typecheck_inputs(crate_root, corpus);
    if inputs.is_empty() && failures.is_empty() {
        return GateResult {
            name: "direct-source Rust typecheck".to_string(),
            required: true,
            status: GateStatus::Passed,
            detail: Some(
                "0 direct-source TrustVc port file(s) require Rust typechecking".to_string(),
            ),
            command: None,
        };
    }

    let scratch = output_dir
        .join("direct-source-typecheck")
        .join(evidence_process_run_id());
    if let Err(err) = write_direct_source_typecheck_crate(crate_root, &scratch, &inputs) {
        failures.push(err);
    }

    let mut command = None;
    if failures.is_empty() {
        let lock = run_direct_source_typecheck_lockfile(crate_root, &scratch, env);
        if lock.command.exit_code != Some(0) {
            failures.push(format!(
                "cargo generate-lockfile failed for normalized direct-source TrustVc ports with {}",
                display_exit_code(lock.command.exit_code)
            ));
            command = Some(lock.command);
        }
    }
    if failures.is_empty() {
        let run = run_direct_source_typecheck(crate_root, &scratch, env);
        if run.command.exit_code != Some(0) {
            failures.push(format!(
                "cargo check failed for normalized direct-source TrustVc ports with {}",
                display_exit_code(run.command.exit_code)
            ));
        }
        command = Some(run.command);
    }

    GateResult {
        name: "direct-source Rust typecheck".to_string(),
        required: true,
        status: if failures.is_empty() {
            GateStatus::Passed
        } else {
            GateStatus::Failed
        },
        detail: Some(if failures.is_empty() {
            format!(
                "{} direct-source TrustVc port file(s) typechecked as normalized Rust",
                inputs.len()
            )
        } else {
            format!(
                "{} direct-source TrustVc port file(s), {} failure(s): {}",
                inputs.len(),
                failures.len(),
                failures.join("; ")
            )
        }),
        command,
    }
}

fn direct_source_typecheck_inputs(
    crate_root: &Path,
    corpus: &VerusCorpusReport,
) -> (Vec<DirectSourceTypecheckInput>, Vec<String>) {
    let mut seen = BTreeSet::new();
    let mut inputs = Vec::new();
    let mut failures = Vec::new();
    for candidate in &corpus.run_candidates {
        for trust_vc_path in &candidate.trust_vc_paths {
            let path = match validate_repo_trust_vc_path(crate_root, trust_vc_path) {
                Ok(path) => path,
                Err(error) => {
                    failures.push(error);
                    continue;
                }
            };
            if is_cargo_fixture_root(&path) {
                continue;
            }
            if cargo_trust_vc_integration_test_target(crate_root, &path).is_some() {
                continue;
            }
            if !path.is_file() {
                failures.push(format!(
                    "direct-source Rust typecheck requires file trust_vc_paths or cargo fixtures: {trust_vc_path}"
                ));
                continue;
            }
            if path.extension().and_then(|ext| ext.to_str()) != Some("rs") {
                failures.push(format!(
                    "direct-source Rust typecheck requires .rs source files: {trust_vc_path}"
                ));
                continue;
            }
            if seen.insert(path.clone()) {
                inputs.push(DirectSourceTypecheckInput {
                    trust_vc_path: trust_vc_path.clone(),
                    path,
                });
            }
        }
    }
    (inputs, failures)
}

fn write_direct_source_typecheck_crate(
    crate_root: &Path,
    scratch: &Path,
    inputs: &[DirectSourceTypecheckInput],
) -> Result<(), String> {
    match fs::remove_dir_all(scratch) {
        Ok(()) => {}
        Err(err) if err.kind() == ErrorKind::NotFound => {}
        Err(err) => {
            return Err(format!(
                "failed to remove stale direct-source typecheck crate `{}`: {err}",
                scratch.display()
            ));
        }
    }
    fs::create_dir_all(scratch.join("src")).map_err(|err| {
        format!(
            "failed to create direct-source typecheck crate `{}`: {err}",
            scratch.display()
        )
    })?;
    fs::write(
        scratch.join("Cargo.toml"),
        render_direct_source_typecheck_cargo_toml(crate_root),
    )
    .map_err(|err| {
        format!(
            "failed to write direct-source typecheck Cargo.toml `{}`: {err}",
            scratch.join("Cargo.toml").display()
        )
    })?;
    let mut lib = String::new();
    for (index, input) in inputs.iter().enumerate() {
        let source = fs::read_to_string(&input.path).map_err(|err| {
            format!(
                "failed to read direct-source TrustVc port `{}`: {err}",
                input.trust_vc_path
            )
        })?;
        let rendered = render_direct_source_typecheck_lib(&source).map_err(|err| {
            format!(
                "{}: failed to normalize direct-source TrustVc port for Rust typechecking: {err}",
                input.trust_vc_path
            )
        })?;
        let module_name = format!("port_{index}");
        let module_path = scratch.join("src").join(format!("{module_name}.rs"));
        fs::write(&module_path, rendered).map_err(|err| {
            format!(
                "failed to write normalized direct-source typecheck module `{}`: {err}",
                module_path.display()
            )
        })?;
        writeln!(lib, "mod {module_name};")
            .map_err(|err| format!("failed to render direct-source typecheck lib.rs: {err}"))?;
    }
    fs::write(scratch.join("src/lib.rs"), lib).map_err(|err| {
        format!(
            "failed to write direct-source typecheck lib.rs `{}`: {err}",
            scratch.join("src/lib.rs").display()
        )
    })?;
    Ok(())
}

fn render_direct_source_typecheck_cargo_toml(crate_root: &Path) -> String {
    format!(
        r#"[package]
name = "trust_vc_direct_source_typecheck"
version = "0.0.0"
edition = "2021"

[workspace]

[dependencies]
trust-vc-types = {{ path = "{}" }}
trust-vc-std = {{ path = "{}" }}
"#,
        crate_root.join("crates/trust-vc-types").display(),
        crate_root.join("crates/trust-vc-std").display()
    )
}

fn render_direct_source_typecheck_lib(source: &str) -> Result<String, String> {
    let mut ast = trust_vc_core::parse_file_allow_tracked(source).map_err(|err| err.to_string())?;
    let mut normalizer = DirectSourceTypecheckNormalizer::default();
    syn::visit_mut::VisitMut::visit_file_mut(&mut normalizer, &mut ast);
    if normalizer.errors.is_empty() {
        Ok(ast.into_token_stream().to_string())
    } else {
        Err(normalizer.errors.join("; "))
    }
}

#[derive(Default)]
struct DirectSourceTypecheckNormalizer {
    errors: Vec<String>,
}

impl DirectSourceTypecheckNormalizer {
    fn strip_trust_vc_attrs(attrs: &mut Vec<syn::Attribute>) {
        attrs.retain(|attr| !is_trust_vc_verification_attr_path(attr.path()));
    }
}

impl syn::visit_mut::VisitMut for DirectSourceTypecheckNormalizer {
    fn visit_item_mut(&mut self, node: &mut syn::Item) {
        if let syn::Item::Macro(item_macro) = node {
            if let Some(name) = trust_vc_macro_name(&item_macro.mac.path) {
                if is_known_trust_vc_proof_macro(&name) {
                    *node = syn::parse_quote! { const _: () = (); };
                    return;
                }
                self.errors
                    .push(format!("unknown trust_vc item macro `{name}!`"));
                return;
            }
        }
        syn::visit_mut::visit_item_mut(self, node);
    }

    fn visit_item_fn_mut(&mut self, node: &mut syn::ItemFn) {
        Self::strip_trust_vc_attrs(&mut node.attrs);
        syn::visit_mut::visit_item_fn_mut(self, node);
    }

    fn visit_impl_item_fn_mut(&mut self, node: &mut syn::ImplItemFn) {
        Self::strip_trust_vc_attrs(&mut node.attrs);
        syn::visit_mut::visit_impl_item_fn_mut(self, node);
    }

    fn visit_trait_item_fn_mut(&mut self, node: &mut syn::TraitItemFn) {
        Self::strip_trust_vc_attrs(&mut node.attrs);
        syn::visit_mut::visit_trait_item_fn_mut(self, node);
    }

    fn visit_item_mod_mut(&mut self, node: &mut syn::ItemMod) {
        Self::strip_trust_vc_attrs(&mut node.attrs);
        syn::visit_mut::visit_item_mod_mut(self, node);
    }

    fn visit_item_impl_mut(&mut self, node: &mut syn::ItemImpl) {
        Self::strip_trust_vc_attrs(&mut node.attrs);
        syn::visit_mut::visit_item_impl_mut(self, node);
    }

    fn visit_item_trait_mut(&mut self, node: &mut syn::ItemTrait) {
        Self::strip_trust_vc_attrs(&mut node.attrs);
        syn::visit_mut::visit_item_trait_mut(self, node);
    }

    fn visit_item_struct_mut(&mut self, node: &mut syn::ItemStruct) {
        Self::strip_trust_vc_attrs(&mut node.attrs);
        syn::visit_mut::visit_item_struct_mut(self, node);
    }

    fn visit_item_enum_mut(&mut self, node: &mut syn::ItemEnum) {
        Self::strip_trust_vc_attrs(&mut node.attrs);
        syn::visit_mut::visit_item_enum_mut(self, node);
    }

    fn visit_field_mut(&mut self, node: &mut syn::Field) {
        Self::strip_trust_vc_attrs(&mut node.attrs);
        syn::visit_mut::visit_field_mut(self, node);
    }

    fn visit_variant_mut(&mut self, node: &mut syn::Variant) {
        Self::strip_trust_vc_attrs(&mut node.attrs);
        syn::visit_mut::visit_variant_mut(self, node);
    }

    fn visit_stmt_mut(&mut self, node: &mut syn::Stmt) {
        if let syn::Stmt::Macro(stmt_macro) = node {
            if let Some(name) = trust_vc_macro_name(&stmt_macro.mac.path) {
                if is_known_trust_vc_proof_macro(&name) {
                    *node = syn::parse_quote! { let _ = (); };
                    return;
                }
                self.errors
                    .push(format!("unknown trust_vc proof macro `{name}!`"));
                return;
            }
        }
        syn::visit_mut::visit_stmt_mut(self, node);
    }

    fn visit_expr_mut(&mut self, node: &mut syn::Expr) {
        if let syn::Expr::Macro(expr_macro) = node {
            if let Some(name) = trust_vc_macro_name(&expr_macro.mac.path) {
                if is_known_trust_vc_bool_macro(&name) {
                    *node = syn::parse_quote! { true };
                    return;
                }
                if is_known_trust_vc_value_macro(&name) {
                    *node = syn::parse_quote! { unimplemented!() };
                    return;
                }
                if is_known_trust_vc_proof_macro(&name) {
                    *node = syn::parse_quote! { () };
                    return;
                }
                self.errors
                    .push(format!("unknown trust_vc proof macro `{name}!`"));
                return;
            }
        }
        syn::visit_mut::visit_expr_mut(self, node);
    }
}

fn is_trust_vc_verification_attr_path(path: &syn::Path) -> bool {
    let segments = path
        .segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect::<Vec<_>>();
    match segments.as_slice() {
        [name] => is_unqualified_trust_vc_verification_attr(name),
        [prefix, name] if prefix == "trust_vc" => is_trust_vc_verification_attr(name),
        _ => false,
    }
}

fn is_unqualified_trust_vc_verification_attr(name: &str) -> bool {
    matches!(
        name,
        "requires"
            | "ensures"
            | "recommends"
            | "returns"
            | "decreases"
            | "proof"
            | "spec"
            | "external"
            | "external_body"
            | "broadcast"
            | "broadcast_group"
            | "trigger"
            | "auto_trigger"
            | "all_triggers"
            | "trait_spec"
            | "trait_impl"
            | "spec_mode"
            | "memoize"
            | "opens_invariants"
            | "via_fn"
            | "contract"
            | "opaque"
            | "protocol"
            | "action"
            | "safety"
            | "liveness"
    )
}

fn is_trust_vc_verification_attr(name: &str) -> bool {
    is_unqualified_trust_vc_verification_attr(name) || name == "inline"
}

fn trust_vc_macro_name(path: &syn::Path) -> Option<String> {
    let mut segments = path.segments.iter();
    let first = segments.next()?;
    let second = segments.next()?;
    if segments.next().is_none() && first.ident == "trust_vc" {
        Some(second.ident.to_string())
    } else {
        None
    }
}

fn is_known_trust_vc_bool_macro(name: &str) -> bool {
    matches!(name, "forall" | "exists" | "ext_eq" | "ext_ne")
}

fn is_known_trust_vc_value_macro(name: &str) -> bool {
    matches!(name, "old" | "choose" | "arbitrary" | "closure")
}

fn is_known_trust_vc_proof_macro(name: &str) -> bool {
    matches!(
        name,
        "assert"
            | "assume"
            | "requires"
            | "recommends"
            | "ensures"
            | "ghost_requires"
            | "ghost_ensures"
            | "proof_block"
            | "calc"
            | "decreases_to"
            | "track_let"
            | "assume_by"
            | "assert_by"
            | "assert_with_proof"
            | "assert_by_contradiction"
            | "assert_by_nonlinear"
            | "assert_by_bit_vector"
            | "assert_by_compute"
            | "reveal"
            | "reveal_with_fuel"
            | "reveal_group"
            | "hide"
            | "broadcast_use"
            | "invariant"
            | "invariant_except_break"
            | "loop_ensures"
            | "loop_decreases"
            | "tracked"
            | "ghost"
            | "proof_from"
            | "proof_for"
            | "extern_spec"
            | "external_spec"
            | "open_local_invariant"
    ) || is_known_trust_vc_bool_macro(name)
        || is_known_trust_vc_value_macro(name)
}

fn run_direct_source_typecheck_lockfile(
    crate_root: &Path,
    scratch: &Path,
    env: &[(String, String)],
) -> CapturedCommandResult {
    let cargo = env
        .iter()
        .find(|(key, _)| key == "CARGO")
        .map(|(_, value)| value.as_str())
        .unwrap_or("cargo");
    let manifest_path = scratch.join("Cargo.toml");
    let manifest = manifest_path.to_string_lossy().into_owned();
    run_command_with_env_capture(
        crate_root,
        cargo,
        &[
            "generate-lockfile",
            "--manifest-path",
            manifest.as_str(),
            "--offline",
        ],
        &borrowed_env(env),
    )
}

fn run_direct_source_typecheck(
    crate_root: &Path,
    scratch: &Path,
    env: &[(String, String)],
) -> CapturedCommandResult {
    let cargo = env
        .iter()
        .find(|(key, _)| key == "CARGO")
        .map(|(_, value)| value.as_str())
        .unwrap_or("cargo");
    let manifest_path = scratch.join("Cargo.toml");
    let manifest = manifest_path.to_string_lossy().into_owned();
    let mut env = env.to_vec();
    env.push((
        "CARGO_TARGET_DIR".to_string(),
        crate_root.join("target").to_string_lossy().into_owned(),
    ));
    run_command_with_env_capture(
        crate_root,
        cargo,
        &[
            "check",
            "--manifest-path",
            manifest.as_str(),
            "--message-format=json",
            "--locked",
            "--offline",
        ],
        &borrowed_env(&env),
    )
}

#[derive(Debug, Clone)]
struct TrustVcCorpusSourceError {
    trust_vc_path: PathBuf,
    case_id: Option<String>,
    detail: String,
}

fn run_trust_vc_corpus_direct(
    crate_root: &Path,
    candidate: &TrustVcCorpusRunCandidate,
) -> TrustVcCorpusRunResult {
    let trust_vc_path_summary = candidate.trust_vc_paths.join(", ");
    let mut failures = Vec::new();
    let mut functions = Vec::new();
    let mut source_errors = Vec::new();
    let expected_case_ids = expected_case_ids(&candidate.expected_cases);
    let expected_obligation_count = expected_obligation_count(&candidate.expected_cases);
    for trust_vc_path in &candidate.trust_vc_paths {
        let path = match validate_repo_trust_vc_path(crate_root, trust_vc_path) {
            Ok(path) => path,
            Err(error) => {
                failures.push(error);
                continue;
            }
        };
        if path.is_file() {
            scan_trust_vc_corpus_file(&path, &mut functions, &mut source_errors);
        } else if path.is_dir() {
            scan_trust_vc_corpus_dir(&path, &mut functions, &mut source_errors);
        } else {
            failures.push(format!("missing path {}", path.display()));
        }
    }
    if candidate.expected_cases.is_empty() {
        failures.push("no expected_cases declared for accepted corpus entry".to_string());
    }

    let verifications = functions
        .iter()
        .map(verify::verify_one_detailed)
        .collect::<Vec<_>>();
    let mut observed_cases = verifications
        .iter()
        .map(|verification| observed_case_from_verification(crate_root, verification))
        .collect::<Vec<_>>();
    let source_error_indices_used = append_source_error_observed_cases(
        crate_root,
        candidate,
        &mut observed_cases,
        &source_errors,
    );
    for (index, source_error) in source_errors.iter().enumerate() {
        if !source_error_indices_used.contains(&index) {
            failures.push(source_error_failure(crate_root, source_error));
        }
    }
    if functions.is_empty()
        && observed_cases.is_empty()
        && !failures
            .iter()
            .any(|failure| failure == "no TrustVc-annotated functions found")
    {
        failures.push("no TrustVc-annotated functions found".to_string());
    }
    let observed_case_ids = observed_case_ids(&observed_cases);
    let observed_obligation_count = observed_cases
        .iter()
        .map(|case| case.obligation_count)
        .sum();

    append_trust_vc_corpus_case_failures(crate_root, candidate, &observed_cases, &mut failures);
    let function_count = functions.len();
    TrustVcCorpusRunResult {
        upstream_path: candidate.upstream_path.clone(),
        trust_vc_path: trust_vc_path_summary,
        trust_vc_paths: candidate.trust_vc_paths.clone(),
        execution_mode: TrustVcCorpusExecutionMode::DirectSource,
        status: if failures.is_empty() {
            GateStatus::Passed
        } else {
            GateStatus::Failed
        },
        detail: Some(format!(
            "{} function{} checked against {} expected case{}",
            function_count,
            if function_count == 1 { "" } else { "s" },
            candidate.expected_cases.len(),
            if candidate.expected_cases.len() == 1 {
                ""
            } else {
                "s"
            }
        )),
        function_count,
        expected_case_count: candidate.expected_cases.len(),
        observed_case_count: observed_cases.len(),
        expected_obligation_count,
        observed_obligation_count,
        expected_case_ids,
        observed_case_ids,
        observed_cases,
        failures,
        command: None,
        commands: Vec::new(),
    }
}

fn append_trust_vc_corpus_case_failures(
    crate_root: &Path,
    candidate: &TrustVcCorpusRunCandidate,
    observed_cases: &[TrustVcCorpusObservedCase],
    failures: &mut Vec<String>,
) {
    let expected_duplicates = duplicate_expected_case_ids(&candidate.expected_cases);
    for case_id in expected_duplicates {
        failures.push(format!("duplicate expected case {case_id}"));
    }

    let mut expected_by_id = BTreeMap::new();
    for expected_case in &candidate.expected_cases {
        expected_by_id.insert(expected_case.case_id.as_str(), expected_case);
    }
    let mut observed_by_id = BTreeMap::new();
    for observed_case in observed_cases {
        if observed_by_id
            .insert(observed_case.case_id.as_str(), observed_case)
            .is_some()
        {
            failures.push(format!("duplicate observed case {}", observed_case.case_id));
        }
    }
    for expected_case in &candidate.expected_cases {
        let Some(observed_case) = observed_by_id.get(expected_case.case_id.as_str()) else {
            failures.push(format!("missing expected case {}", expected_case.case_id));
            continue;
        };
        let expected_verdict = expected_verdict_label(expected_case.expected_verdict);
        if observed_case.verdict != expected_verdict {
            failures.push(format!(
                "{} expected verdict {}, observed {}",
                expected_case.case_id, expected_verdict, observed_case.verdict
            ));
        }
        if observed_case.obligation_count < expected_case.min_obligations {
            failures.push(format!(
                "{} expected at least {} captured obligation(s), observed {}",
                expected_case.case_id,
                expected_case.min_obligations,
                observed_case.obligation_count
            ));
        }
        append_obligation_fingerprint_failures(expected_case, observed_case, failures);
        match expected_case_effective_trust_vc_path(candidate, expected_case) {
            Some(expected_trust_vc_path)
                if !observed_case_matches_declared_trust_vc_path(
                    crate_root,
                    observed_case,
                    expected_trust_vc_path,
                ) =>
            {
                failures.push(format!(
                    "{} observed in `{}`, expected source under declared trust_vc_path `{}`",
                    expected_case.case_id, observed_case.trust_vc_path, expected_trust_vc_path
                ));
            }
            None => failures.push(format!(
                "{} cannot be path-checked because it has no case-level trust_vc_path and the entry declares {} trust_vc_paths",
                expected_case.case_id,
                candidate.trust_vc_paths.len()
            )),
            _ => {}
        }
        append_expected_error_pattern_failures(expected_case, observed_case, failures);
        append_forbidden_diagnostic_context_failures(expected_case, observed_case, failures);
        append_expected_warning_failures(expected_case, observed_case, failures);
    }
    for observed_case in observed_cases {
        if !expected_by_id.contains_key(observed_case.case_id.as_str()) {
            failures.push(format!(
                "unexpected observed case {}",
                observed_case.case_id
            ));
        }
    }
}

fn append_obligation_fingerprint_failures(
    expected_case: &VerusExpectedCase,
    observed_case: &TrustVcCorpusObservedCase,
    failures: &mut Vec<String>,
) {
    for fingerprint in &observed_case.obligation_fingerprints {
        if !valid_sha256_digest_label(fingerprint) {
            failures.push(format!(
                "{} has invalid observed obligation_fingerprints value `{}`",
                expected_case.case_id, fingerprint
            ));
        }
    }
    if observed_case.obligation_count > 0 && observed_case.obligation_fingerprints.is_empty() {
        failures.push(format!(
            "{} observed obligation_count {} but reported no obligation_fingerprints",
            expected_case.case_id, observed_case.obligation_count
        ));
    }
    if observed_case.obligation_count > 0
        && observed_case.obligation_count != observed_case.obligation_fingerprints.len()
    {
        failures.push(format!(
            "{} observed obligation_count {} must equal obligation_fingerprints count {}",
            expected_case.case_id,
            observed_case.obligation_count,
            observed_case.obligation_fingerprints.len()
        ));
    }
    let unique_observed_fingerprint_count = observed_case
        .obligation_fingerprints
        .iter()
        .collect::<BTreeSet<_>>()
        .len();
    if unique_observed_fingerprint_count < expected_case.min_obligations {
        failures.push(format!(
            "{} expected at least {} unique obligation_fingerprints, observed {}",
            expected_case.case_id, expected_case.min_obligations, unique_observed_fingerprint_count
        ));
    }
    if expected_case.obligation_fingerprints.is_empty() {
        return;
    }
    let mut expected = expected_case.obligation_fingerprints.clone();
    expected.sort();
    let mut observed = observed_case
        .obligation_fingerprints
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    observed.sort();
    if expected != observed {
        failures.push(format!(
            "{} expected obligation fingerprints [{}], observed [{}]",
            expected_case.case_id,
            expected.join(", "),
            observed.join(", ")
        ));
    }
}

fn duplicate_obligation_fingerprints(fingerprints: &[String]) -> Vec<&str> {
    let mut seen = BTreeSet::new();
    let mut duplicates = BTreeSet::new();
    for fingerprint in fingerprints {
        if !seen.insert(fingerprint.as_str()) {
            duplicates.insert(fingerprint.as_str());
        }
    }
    duplicates.into_iter().collect()
}

fn expected_case_effective_trust_vc_path<'a>(
    candidate: &'a TrustVcCorpusRunCandidate,
    expected_case: &'a VerusExpectedCase,
) -> Option<&'a str> {
    expected_case
        .trust_vc_path
        .as_deref()
        .or(match candidate.trust_vc_paths.as_slice() {
            [single] => Some(single.as_str()),
            _ => None,
        })
}

fn observed_case_matches_declared_trust_vc_path(
    crate_root: &Path,
    observed_case: &TrustVcCorpusObservedCase,
    expected_trust_vc_path: &str,
) -> bool {
    let observed_path = resolve_repo_path(crate_root, Path::new(&observed_case.trust_vc_path));
    let expected_path = resolve_repo_path(crate_root, Path::new(expected_trust_vc_path));
    match (observed_path.canonicalize(), expected_path.canonicalize()) {
        (Ok(observed_path), Ok(expected_path)) if expected_path.is_file() => {
            observed_path == expected_path
        }
        (Ok(observed_path), Ok(expected_path)) => observed_path.starts_with(expected_path),
        _ => false,
    }
}

fn append_expected_error_pattern_failures(
    expected_case: &VerusExpectedCase,
    observed_case: &TrustVcCorpusObservedCase,
    failures: &mut Vec<String>,
) {
    if expected_case.expected_error_patterns.is_empty()
        || expected_case.expected_verdict != VerusExpectedVerdict::Error
    {
        return;
    }
    if observed_case.diagnostic_context.is_empty() {
        failures.push(format!(
            "{} expected error diagnostic patterns {:?}, but no diagnostic context was captured",
            expected_case.case_id, expected_case.expected_error_patterns
        ));
        return;
    }
    let joined_context = observed_case.diagnostic_context.join("\n");
    for pattern in &expected_case.expected_error_patterns {
        if !joined_context.contains(pattern) {
            failures.push(format!(
                "{} diagnostic context did not contain expected error pattern {:?}",
                expected_case.case_id, pattern
            ));
        }
    }
}

/// Checks a case's VERIFIER WARNINGS against the manifest pin.
///
/// Upstream's default `=> Ok(())` harness arm asserts `err.warnings.len() == 0`,
/// so an empty `expected_warning_patterns` is a POSITIVE claim of "no warnings",
/// not an absence of checking. A case that declares patterns must emit exactly
/// that many warnings, the i-th containing the i-th declared pattern — which is
/// how upstream `assert_forall_by.rs::test_forallstmt_implies` reads its
/// warnings (`warns.next().expect(..).message.contains(..)`).
fn append_expected_warning_failures(
    expected_case: &VerusExpectedCase,
    observed_case: &TrustVcCorpusObservedCase,
    failures: &mut Vec<String>,
) {
    let expected = &expected_case.expected_warning_patterns;
    let observed = &observed_case.warnings;
    if expected.len() != observed.len() {
        failures.push(format!(
            "{} expected {} verifier warning(s) {:?}, observed {} {:?}",
            expected_case.case_id,
            expected.len(),
            expected,
            observed.len(),
            observed
        ));
        return;
    }
    for (index, pattern) in expected.iter().enumerate() {
        let Some(warning) = observed.get(index) else {
            continue;
        };
        if !warning.contains(pattern) {
            failures.push(format!(
                "{} warning {} did not contain expected pattern {:?}; observed {:?}",
                expected_case.case_id, index, pattern, warning
            ));
        }
    }
}

fn append_forbidden_diagnostic_context_failures(
    expected_case: &VerusExpectedCase,
    observed_case: &TrustVcCorpusObservedCase,
    failures: &mut Vec<String>,
) {
    if expected_case.forbidden_diagnostic_patterns.is_empty() {
        return;
    }
    if observed_case.diagnostic_context.is_empty() {
        failures.push(format!(
            "{} expected diagnostic context evidence excluding {:?}, but no diagnostic context was captured",
            expected_case.case_id, expected_case.forbidden_diagnostic_patterns
        ));
        return;
    }
    let joined_context = observed_case.diagnostic_context.join("\n");
    for pattern in &expected_case.forbidden_diagnostic_patterns {
        if joined_context.contains(pattern) {
            failures.push(format!(
                "{} diagnostic context unexpectedly contained forbidden pattern {:?}",
                expected_case.case_id, pattern
            ));
        }
    }
}

fn run_trust_vc_corpus_cargo_trust_vc_integration_test(
    crate_root: &Path,
    candidate: &TrustVcCorpusRunCandidate,
    env: &[(String, String)],
) -> TrustVcCorpusRunResult {
    let trust_vc_path_summary = candidate.trust_vc_paths.join(", ");
    let expected_case_ids = expected_case_ids(&candidate.expected_cases);
    let expected_obligation_count = expected_obligation_count(&candidate.expected_cases);
    let mut failures = Vec::new();
    let mut commands = Vec::new();
    let mut observed_cases = Vec::new();

    if candidate.evidence_kind != VerusEvidenceKind::CargoTrustVcIntegrationTest {
        failures.push(format!(
            "cargo-trust-vc integration-test evidence requires evidence_kind `{}`",
            evidence_kind_label(VerusEvidenceKind::CargoTrustVcIntegrationTest)
        ));
    }
    if candidate.trust_vc_paths.len() != 1 {
        failures.push(format!(
            "cargo-trust-vc integration-test evidence requires exactly one trust_vc_path, got {}",
            candidate.trust_vc_paths.len()
        ));
    }
    if candidate.expected_cases.is_empty() {
        failures.push("no expected_cases declared for accepted corpus entry".to_string());
    }

    let mut test_binding = None;
    if let Some(trust_vc_path) = candidate.trust_vc_paths.first() {
        match validate_repo_trust_vc_path(crate_root, trust_vc_path) {
            Ok(path) => {
                if let Some(test_target) = cargo_trust_vc_integration_test_target(crate_root, &path)
                {
                    test_binding = Some((trust_vc_path.clone(), path, test_target));
                } else {
                    failures.push(format!(
                        "cargo-trust-vc integration-test evidence requires trust_vc_path under crates/cargo-trust-vc/tests/*.rs, got `{trust_vc_path}`"
                    ));
                }
            }
            Err(error) => failures.push(error),
        }
    }

    if let Some((trust_vc_path, test_path, test_target)) = test_binding {
        let declared_cases = match rust_integration_test_cases_from_file(&test_path) {
            Ok(cases) => cases,
            Err(error) => {
                failures.push(error);
                BTreeMap::new()
            }
        };
        for expected_case in &candidate.expected_cases {
            match declared_cases.get(&expected_case.case_id) {
                Some(case) if case.ignored => failures.push(format!(
                    "{}: cargo-trust-vc integration test `{}` is #[ignore] and cannot prove accepted evidence",
                    trust_vc_path, expected_case.case_id
                )),
                Some(_) => {}
                None => failures.push(format!(
                    "{}: cargo-trust-vc integration test source does not declare #[test] `{}`",
                    trust_vc_path, expected_case.case_id
                )),
            }
            if expected_case.expected_verdict != VerusExpectedVerdict::Verified {
                failures.push(format!(
                    "{}: cargo-trust-vc integration test expected case `{}` must use expected_verdict `verified`",
                    trust_vc_path, expected_case.case_id
                ));
            }
            if expected_case.min_obligations != 0 {
                failures.push(format!(
                    "{}: cargo-trust-vc integration test expected case `{}` must declare min_obligations 0",
                    trust_vc_path, expected_case.case_id
                ));
            }
            if !expected_case.obligation_fingerprints.is_empty() {
                failures.push(format!(
                    "{}: cargo-trust-vc integration test expected case `{}` must not declare obligation_fingerprints",
                    trust_vc_path, expected_case.case_id
                ));
            }
        }

        if failures.is_empty() {
            for expected_case in &candidate.expected_cases {
                let output = run_cargo_trust_vc_integration_test_case(
                    crate_root,
                    &test_target,
                    &expected_case.case_id,
                    env,
                );
                let command = output.command.clone();
                if command.exit_code == Some(0)
                    && cargo_test_output_reports_exactly_one_pass(&output.stdout)
                {
                    observed_cases.push(TrustVcCorpusObservedCase {
                        case_id: expected_case.case_id.clone(),
                        trust_vc_path: trust_vc_path.clone(),
                        verdict: expected_verdict_label(VerusExpectedVerdict::Verified).to_string(),
                        obligation_count: 0,
                        obligation_fingerprints: Vec::new(),
                        diagnostic_context: Vec::new(),
                        warnings: Vec::new(),
                    });
                } else {
                    failures.push(format!(
                        "{}: cargo test --test {} -- --exact {} did not report exactly one passing test with {}",
                        trust_vc_path,
                        test_target,
                        expected_case.case_id,
                        display_exit_code(command.exit_code)
                    ));
                    if let Some(context) = command_failure_context(&command) {
                        failures.push(format!(
                            "{}: cargo integration-test output: {}",
                            trust_vc_path, context
                        ));
                    }
                }
                commands.push(command);
            }
        }
    }

    let observed_case_ids = observed_case_ids(&observed_cases);
    let observed_obligation_count = observed_cases
        .iter()
        .map(|case| case.obligation_count)
        .sum();
    append_trust_vc_corpus_case_failures(crate_root, candidate, &observed_cases, &mut failures);
    let command = if commands.len() == 1 {
        commands.first().cloned()
    } else {
        None
    };
    TrustVcCorpusRunResult {
        upstream_path: candidate.upstream_path.clone(),
        trust_vc_path: trust_vc_path_summary,
        trust_vc_paths: candidate.trust_vc_paths.clone(),
        execution_mode: TrustVcCorpusExecutionMode::CargoTrustVcIntegrationTest,
        status: if failures.is_empty() {
            GateStatus::Passed
        } else {
            GateStatus::Failed
        },
        detail: Some(format!(
            "{} cargo-trust-vc integration test case{} checked against {} expected case{}",
            observed_cases.len(),
            if observed_cases.len() == 1 { "" } else { "s" },
            candidate.expected_cases.len(),
            if candidate.expected_cases.len() == 1 {
                ""
            } else {
                "s"
            }
        )),
        function_count: observed_cases.len(),
        expected_case_count: candidate.expected_cases.len(),
        observed_case_count: observed_cases.len(),
        expected_obligation_count,
        observed_obligation_count,
        expected_case_ids,
        observed_case_ids,
        observed_cases,
        failures,
        command,
        commands,
    }
}

fn run_cargo_trust_vc_integration_test_case(
    crate_root: &Path,
    test_target: &str,
    case_id: &str,
    env: &[(String, String)],
) -> CapturedCommandResult {
    let cargo = env
        .iter()
        .find(|(key, _)| key == "CARGO")
        .map(|(_, value)| value.as_str())
        .unwrap_or("cargo");
    run_command_with_env_capture(
        crate_root,
        cargo,
        &[
            "test",
            "--locked",
            "--offline",
            "-p",
            "cargo-trust-vc",
            "--test",
            test_target,
            "--",
            "--exact",
            case_id,
        ],
        &borrowed_env(env),
    )
}

fn cargo_test_output_reports_exactly_one_pass(stdout: &str) -> bool {
    parse_libtest_summary(stdout).is_some_and(|summary| {
        summary.passed == 1 && summary.failed == 0 && summary.ignored == 0 && summary.measured == 0
    })
}

#[derive(Debug, Clone, Copy)]
struct LibtestSummary {
    passed: usize,
    failed: usize,
    ignored: usize,
    measured: usize,
}

fn parse_libtest_summary(stdout: &str) -> Option<LibtestSummary> {
    let line = stdout
        .lines()
        .rev()
        .map(str::trim)
        .find(|line| line.starts_with("test result: "))?;
    Some(LibtestSummary {
        passed: parse_libtest_count(line, &["passed"])?,
        failed: parse_libtest_count(line, &["failed"])?,
        ignored: parse_libtest_count(line, &["ignored"])?,
        measured: parse_libtest_count(line, &["measured"])?,
    })
}

fn parse_libtest_count(line: &str, label: &[&str]) -> Option<usize> {
    for segment in line.split(';') {
        let words = segment
            .split_whitespace()
            .map(|word| word.trim_matches(|ch: char| !ch.is_ascii_alphanumeric()))
            .filter(|word| !word.is_empty())
            .collect::<Vec<_>>();
        if words.len() <= label.len() || !words.ends_with(label) {
            continue;
        }
        let count_index = words.len().checked_sub(label.len() + 1)?;
        return words[count_index].parse::<usize>().ok();
    }
    None
}

fn run_trust_vc_corpus_cargo_fixture(
    crate_root: &Path,
    candidate: &TrustVcCorpusRunCandidate,
    env: &[(String, String)],
    trust_vc_binary: Option<&Path>,
    cargo_fixture_preflight_failures: &BTreeMap<PathBuf, Vec<String>>,
) -> TrustVcCorpusRunResult {
    if candidate_expects_errors_and_non_errors(candidate) {
        return failed_trust_vc_corpus_run_result(
            candidate,
            TrustVcCorpusExecutionMode::CargoFixture,
            Some("cargo fixture execution cannot mix expected Rust-error and non-error cases"),
            vec![
                "cargo fixture candidates cannot mix expected Rust-error cases with non-error cases; assign them to separate expected_cases[].trust_vc_path values".to_string(),
            ],
            None,
            Vec::new(),
        );
    }
    if candidate_expects_only_errors(candidate) && !candidate_uses_no_cheating(candidate) {
        return run_trust_vc_corpus_cargo_fixture_source_errors(crate_root, candidate, env);
    }

    let binary = match trust_vc_binary {
        Some(path) => Ok(path.to_path_buf()),
        None => current_trust_vc_binary(),
    };
    match binary {
        Ok(binary) => run_trust_vc_corpus_cargo_fixture_with_binary(
            crate_root,
            candidate,
            env,
            &binary,
            cargo_fixture_preflight_failures,
        ),
        Err(error) => failed_trust_vc_corpus_run_result(
            candidate,
            TrustVcCorpusExecutionMode::CargoFixture,
            Some("cargo fixture execution could not locate the current cargo-trust-vc binary"),
            vec![error],
            None,
            Vec::new(),
        ),
    }
}

fn run_trust_vc_corpus_cargo_fixture_with_binary(
    crate_root: &Path,
    candidate: &TrustVcCorpusRunCandidate,
    env: &[(String, String)],
    trust_vc_binary: &Path,
    cargo_fixture_preflight_failures: &BTreeMap<PathBuf, Vec<String>>,
) -> TrustVcCorpusRunResult {
    let trust_vc_path_summary = candidate.trust_vc_paths.join(", ");
    let expected_case_ids = expected_case_ids(&candidate.expected_cases);
    let expected_obligation_count = expected_obligation_count(&candidate.expected_cases);
    let mut failures = Vec::new();
    let mut fixture_roots = Vec::new();
    for trust_vc_path in &candidate.trust_vc_paths {
        let path = match validate_repo_trust_vc_path(crate_root, trust_vc_path) {
            Ok(path) => path,
            Err(error) => {
                failures.push(error);
                continue;
            }
        };
        if is_cargo_fixture_root(&path) {
            fixture_roots.push((trust_vc_path.clone(), path));
        } else {
            failures.push(format!(
                "cargo fixture trust_vc_path must name a directory containing Cargo.toml: {trust_vc_path}"
            ));
        }
    }
    if candidate.expected_cases.is_empty() {
        failures.push("no expected_cases declared for accepted corpus entry".to_string());
    }
    if fixture_roots.is_empty() {
        failures.push("no cargo fixture trust_vc_path found".to_string());
    }
    let mut prerequisite_failed = false;
    if failures.is_empty() {
        for (_, fixture_root) in &fixture_roots {
            if let Some(preflight_failures) = cargo_fixture_preflight_failures.get(fixture_root) {
                prerequisite_failed = true;
                failures.extend(preflight_failures.iter().cloned());
            }
        }
    }

    let mut commands = Vec::new();
    let mut trust_vc_commands = Vec::new();
    let mut cargo_typechecks = Vec::new();
    let mut observed_cases = Vec::new();
    let no_cheating_source_rejection =
        candidate_uses_no_cheating(candidate) && candidate_expects_only_errors(candidate);
    if failures.is_empty() && !no_cheating_source_rejection {
        for (_, fixture_root) in &fixture_roots {
            let output = run_cargo_check_for_fixture(crate_root, fixture_root, env);
            if output.command.exit_code != Some(0) {
                failures.push(format!(
                    "{}: cargo check failed for accepted cargo fixture with {}",
                    report_path_string(fixture_root, crate_root),
                    display_exit_code(output.command.exit_code)
                ));
                append_cargo_check_failure_context(
                    crate_root,
                    fixture_root,
                    &output,
                    &mut failures,
                );
            } else if let Some(error) = &output.cargo_dep_info_error {
                failures.push(format!(
                    "{}: cargo check dep-info evidence could not be read: {error}",
                    report_path_string(fixture_root, crate_root)
                ));
            } else if output.cargo_dep_info_sources.is_empty() {
                failures.push(format!(
                    "{}: cargo check produced no dep-info source evidence",
                    report_path_string(fixture_root, crate_root)
                ));
            }
            commands.push(output.command.clone());
            cargo_typechecks.push((fixture_root.clone(), output));
        }
    }
    if failures.is_empty() {
        for (_, fixture_root) in &fixture_roots {
            match run_current_trust_vc_on_cargo_fixture(
                crate_root,
                fixture_root,
                trust_vc_binary,
                &candidate.trust_vc_check_args,
                &candidate.expected_cases,
                env,
            ) {
                CargoFixtureRunOutput {
                    command,
                    setup_commands,
                    observed_cases: Ok(mut fixture_cases),
                    stdout_json_valid,
                    prerequisite_failed: output_prerequisite_failed,
                } => {
                    if output_prerequisite_failed {
                        prerequisite_failed = true;
                    }
                    commands.extend(setup_commands);
                    if !matches!(command.exit_code, Some(0) | Some(1)) {
                        failures.push(format!(
                            "{}: cargo fixture check exited with {}",
                            report_path_string(fixture_root, crate_root),
                            command
                                .exit_code
                                .map(|code| code.to_string())
                                .unwrap_or_else(|| "no exit code".to_string())
                        ));
                    }
                    if let Err(error) = stdout_json_valid {
                        failures.push(format!(
                            "{}: cargo fixture check did not emit valid JSON: {error}",
                            report_path_string(fixture_root, crate_root)
                        ));
                    }
                    observed_cases.append(&mut fixture_cases);
                    trust_vc_commands.push(command.clone());
                    commands.push(command);
                }
                CargoFixtureRunOutput {
                    command,
                    setup_commands,
                    observed_cases: Err(error),
                    stdout_json_valid,
                    prerequisite_failed: output_prerequisite_failed,
                } => {
                    if output_prerequisite_failed {
                        prerequisite_failed = true;
                    }
                    commands.extend(setup_commands);
                    if !matches!(command.exit_code, Some(0) | Some(1)) {
                        failures.push(format!(
                            "{}: cargo fixture check exited with {}",
                            report_path_string(fixture_root, crate_root),
                            command
                                .exit_code
                                .map(|code| code.to_string())
                                .unwrap_or_else(|| "no exit code".to_string())
                        ));
                    }
                    if let Err(json_error) = stdout_json_valid {
                        failures.push(format!(
                            "{}: cargo fixture check did not emit valid JSON: {json_error}",
                            report_path_string(fixture_root, crate_root)
                        ));
                    }
                    failures.push(format!(
                        "{}: {error}",
                        report_path_string(fixture_root, crate_root)
                    ));
                    trust_vc_commands.push(command.clone());
                    commands.push(command);
                }
            }
        }
    }

    let observed_case_ids = observed_case_ids(&observed_cases);
    let observed_obligation_count = observed_cases
        .iter()
        .map(|case| case.obligation_count)
        .sum();
    if !prerequisite_failed {
        append_trust_vc_corpus_case_failures(crate_root, candidate, &observed_cases, &mut failures);
    }
    if !no_cheating_source_rejection {
        append_cargo_fixture_compiled_source_failures(
            crate_root,
            candidate,
            &observed_cases,
            &cargo_typechecks,
            &mut failures,
        );
    }
    let command = if trust_vc_commands.len() == 1 {
        trust_vc_commands.first().cloned()
    } else {
        None
    };
    TrustVcCorpusRunResult {
        upstream_path: candidate.upstream_path.clone(),
        trust_vc_path: trust_vc_path_summary,
        trust_vc_paths: candidate.trust_vc_paths.clone(),
        execution_mode: TrustVcCorpusExecutionMode::CargoFixture,
        status: if failures.is_empty() {
            GateStatus::Passed
        } else {
            GateStatus::Failed
        },
        detail: Some(format!(
            "{} cargo fixture{} passed Rust typecheck and current cargo-trust-vc binary check with {} observed case{} against {} expected case{}",
            fixture_roots.len(),
            if fixture_roots.len() == 1 { "" } else { "s" },
            observed_cases.len(),
            if observed_cases.len() == 1 { "" } else { "s" },
            candidate.expected_cases.len(),
            if candidate.expected_cases.len() == 1 {
                ""
            } else {
                "s"
            }
        )),
        function_count: observed_cases.len(),
        expected_case_count: candidate.expected_cases.len(),
        observed_case_count: observed_cases.len(),
        expected_obligation_count,
        observed_obligation_count,
        expected_case_ids,
        observed_case_ids,
        observed_cases,
        failures,
        command,
        commands,
    }
}

fn append_cargo_fixture_compiled_source_failures(
    crate_root: &Path,
    candidate: &TrustVcCorpusRunCandidate,
    observed_cases: &[TrustVcCorpusObservedCase],
    cargo_typechecks: &[(PathBuf, CapturedCommandResult)],
    failures: &mut Vec<String>,
) {
    for expected_case in &candidate.expected_cases {
        if let Some(expected_trust_vc_path) =
            expected_case_effective_trust_vc_path(candidate, expected_case)
        {
            let Ok(path) = validate_repo_trust_vc_path(crate_root, expected_trust_vc_path) else {
                continue;
            };
            if path.is_file() {
                append_cargo_fixture_source_file_compiled_failure(
                    crate_root,
                    &path,
                    cargo_typechecks,
                    failures,
                    &format!(
                        "{} expected source `{}`",
                        expected_case.case_id, expected_trust_vc_path
                    ),
                );
            }
        }
    }

    for observed_case in observed_cases {
        let Ok(path) = validate_repo_trust_vc_path(crate_root, &observed_case.trust_vc_path) else {
            failures.push(format!(
                "{} observed source `{}` is not a valid repo path for cargo dep-info checking",
                observed_case.case_id, observed_case.trust_vc_path
            ));
            continue;
        };
        if !path.is_file() {
            failures.push(format!(
                "{} observed source `{}` is not a source file compiled by cargo",
                observed_case.case_id, observed_case.trust_vc_path
            ));
            continue;
        }
        append_cargo_fixture_source_file_compiled_failure(
            crate_root,
            &path,
            cargo_typechecks,
            failures,
            &format!(
                "{} observed source `{}`",
                observed_case.case_id, observed_case.trust_vc_path
            ),
        );
    }
}

fn append_cargo_fixture_source_file_compiled_failure(
    crate_root: &Path,
    source_path: &Path,
    cargo_typechecks: &[(PathBuf, CapturedCommandResult)],
    failures: &mut Vec<String>,
    label: &str,
) {
    let Some((fixture_root, output)) = cargo_typechecks
        .iter()
        .find(|(fixture_root, _)| path_starts_with(source_path, fixture_root))
    else {
        failures.push(format!(
            "{label} is not under a cargo fixture that was typechecked"
        ));
        return;
    };
    if output
        .cargo_dep_info_sources
        .iter()
        .any(|compiled_source| same_path(compiled_source, source_path, crate_root))
    {
        return;
    }
    failures.push(format!(
        "{label} was not present in cargo check dep-info for `{}`; fixture evidence must compile every TrustVc source observed by the replacement run",
        report_path_string(fixture_root, crate_root)
    ));
}

fn candidate_expects_errors_and_non_errors(candidate: &TrustVcCorpusRunCandidate) -> bool {
    let has_error = candidate
        .expected_cases
        .iter()
        .any(|case| case.expected_verdict == VerusExpectedVerdict::Error);
    let has_non_error = candidate
        .expected_cases
        .iter()
        .any(|case| case.expected_verdict != VerusExpectedVerdict::Error);
    has_error && has_non_error
}

fn candidate_expects_only_errors(candidate: &TrustVcCorpusRunCandidate) -> bool {
    !candidate.expected_cases.is_empty()
        && candidate
            .expected_cases
            .iter()
            .all(|case| case.expected_verdict == VerusExpectedVerdict::Error)
}

fn candidate_uses_no_cheating(candidate: &TrustVcCorpusRunCandidate) -> bool {
    candidate
        .trust_vc_check_args
        .iter()
        .any(|arg| arg == "--no-cheating")
}

fn run_trust_vc_corpus_cargo_fixture_source_errors(
    crate_root: &Path,
    candidate: &TrustVcCorpusRunCandidate,
    env: &[(String, String)],
) -> TrustVcCorpusRunResult {
    let trust_vc_path_summary = candidate.trust_vc_paths.join(", ");
    let expected_case_ids = expected_case_ids(&candidate.expected_cases);
    let expected_obligation_count = expected_obligation_count(&candidate.expected_cases);
    let mut failures = Vec::new();
    let mut fixture_roots = Vec::new();
    for trust_vc_path in &candidate.trust_vc_paths {
        let path = match validate_repo_trust_vc_path(crate_root, trust_vc_path) {
            Ok(path) => path,
            Err(error) => {
                failures.push(error);
                continue;
            }
        };
        if is_cargo_fixture_root(&path) {
            fixture_roots.push((trust_vc_path.clone(), path));
        } else {
            failures.push(format!(
                "cargo fixture trust_vc_path must name a directory containing Cargo.toml: {trust_vc_path}"
            ));
        }
    }
    if fixture_roots.is_empty() {
        failures.push("no cargo fixture trust_vc_path found".to_string());
    }

    let mut commands = Vec::new();
    let mut diagnostics = Vec::new();
    let expected_source_rel = upstream_cargo_fixture_parts(&candidate.upstream_path)
        .map(|(_, source_rel)| PathBuf::from(source_rel))
        .unwrap_or_else(|| PathBuf::from("src/lib.rs"));
    if failures.is_empty() {
        for (_, fixture_root) in &fixture_roots {
            let expected_source = fixture_root.join(&expected_source_rel);
            let output = run_cargo_check_for_source_diagnostics(crate_root, fixture_root, env);
            let fixture_diagnostics = match rust_source_error_diagnostics_from_cargo_json(
                crate_root,
                fixture_root,
                &output.stdout,
            ) {
                Ok(diagnostics) => diagnostics,
                Err(error) => {
                    failures.push(format!(
                        "{}: {error}",
                        report_path_string(fixture_root, crate_root)
                    ));
                    Vec::new()
                }
            };
            if output.command.exit_code == Some(0) {
                failures.push(format!(
                    "{}: cargo check succeeded for expected source-error fixture",
                    report_path_string(fixture_root, crate_root)
                ));
            } else if output.command.exit_code != Some(101) {
                failures.push(format!(
                    "{}: expected cargo check source-error exit code 101, got {}",
                    report_path_string(fixture_root, crate_root),
                    display_exit_code(output.command.exit_code)
                ));
            }
            if fixture_diagnostics.is_empty() {
                failures.push(format!(
                    "{}: cargo check failed without Rust compiler error diagnostics with primary source spans",
                    report_path_string(fixture_root, crate_root)
                ));
            }
            for diagnostic in &fixture_diagnostics {
                if !diagnostic_source_is_in_fixture(crate_root, fixture_root, diagnostic) {
                    failures.push(format!(
                        "{}: Rust compiler diagnostic source is outside cargo fixture `{}`: {}",
                        report_path_string(&diagnostic.trust_vc_path, crate_root),
                        report_path_string(fixture_root, crate_root),
                        diagnostic.detail
                    ));
                } else if !same_path(&diagnostic.trust_vc_path, &expected_source, crate_root) {
                    failures.push(format!(
                        "{}: Rust compiler diagnostic source does not match mirrored upstream cargo fixture source `{}`: {}",
                        report_path_string(&diagnostic.trust_vc_path, crate_root),
                        report_path_string(&expected_source, crate_root),
                        diagnostic.detail
                    ));
                }
            }
            diagnostics.extend(fixture_diagnostics);
            commands.push(output.command);
        }
    }

    let expected_error_cases = candidate
        .expected_cases
        .iter()
        .filter(|case| case.expected_verdict == VerusExpectedVerdict::Error)
        .collect::<Vec<_>>();
    let expected_rust_diagnostic_count = expected_error_cases
        .iter()
        .map(|case| expected_case_rust_diagnostic_count(case))
        .sum::<usize>();
    if diagnostics.len() != expected_rust_diagnostic_count {
        failures.push(format!(
            "expected exactly {} Rust compiler error diagnostic(s), observed {}",
            expected_rust_diagnostic_count,
            diagnostics.len()
        ));
    }
    let mut observed_cases = Vec::new();
    if failures.is_empty() {
        let mut used_diagnostics = BTreeSet::new();
        for expected_case in expected_error_cases {
            let Some(matched_indices) =
                match_source_error_pattern_sets(&diagnostics, &used_diagnostics, expected_case)
            else {
                let expected_patterns = if expected_case
                    .expected_rust_diagnostic_pattern_sets
                    .is_empty()
                {
                    format!(
                        "expected_error_patterns {:?}",
                        expected_case.expected_error_patterns
                    )
                } else {
                    format!(
                        "expected_rust_diagnostic_pattern_sets {:?}",
                        expected_case.expected_rust_diagnostic_pattern_sets
                    )
                };
                failures.push(format!(
                    "{}: no Rust compiler diagnostic set matched {}",
                    expected_case.case_id, expected_patterns
                ));
                continue;
            };
            used_diagnostics.extend(matched_indices.iter().copied());
            let diagnostic_context = matched_indices
                .iter()
                .map(|index| diagnostics[*index].detail.clone())
                .collect::<Vec<_>>();
            let trust_vc_path = matched_indices
                .first()
                .and_then(|index| diagnostics.get(*index))
                .map(|diagnostic| report_path_string(&diagnostic.trust_vc_path, crate_root))
                .unwrap_or_else(|| expected_case.case_id.clone());
            observed_cases.push(TrustVcCorpusObservedCase {
                case_id: expected_case.case_id.clone(),
                trust_vc_path,
                verdict: expected_verdict_label(VerusExpectedVerdict::Error).to_string(),
                obligation_count: 0,
                obligation_fingerprints: Vec::new(),
                diagnostic_context,
                warnings: Vec::new(),
            });
        }
        for (index, diagnostic) in diagnostics.iter().enumerate() {
            if !used_diagnostics.contains(&index) {
                failures.push(format!(
                    "{}: unmatched Rust compiler diagnostic: {}",
                    report_path_string(&diagnostic.trust_vc_path, crate_root),
                    diagnostic.detail
                ));
            }
        }
    }

    let observed_case_ids = observed_case_ids(&observed_cases);
    let observed_obligation_count = observed_cases
        .iter()
        .map(|case| case.obligation_count)
        .sum();
    append_trust_vc_corpus_case_failures(crate_root, candidate, &observed_cases, &mut failures);
    let command = if commands.len() == 1 {
        commands.first().cloned()
    } else {
        None
    };
    TrustVcCorpusRunResult {
        upstream_path: candidate.upstream_path.clone(),
        trust_vc_path: trust_vc_path_summary,
        trust_vc_paths: candidate.trust_vc_paths.clone(),
        execution_mode: TrustVcCorpusExecutionMode::CargoFixture,
        status: if failures.is_empty() {
            GateStatus::Passed
        } else {
            GateStatus::Failed
        },
        detail: Some(format!(
            "{} cargo fixture{} checked with cargo for {} expected source-error case{}",
            fixture_roots.len(),
            if fixture_roots.len() == 1 { "" } else { "s" },
            candidate.expected_cases.len(),
            if candidate.expected_cases.len() == 1 {
                ""
            } else {
                "s"
            }
        )),
        function_count: 0,
        expected_case_count: candidate.expected_cases.len(),
        observed_case_count: observed_cases.len(),
        expected_obligation_count,
        observed_obligation_count,
        expected_case_ids,
        observed_case_ids,
        observed_cases,
        failures,
        command,
        commands,
    }
}

fn run_cargo_check_for_source_diagnostics(
    crate_root: &Path,
    fixture_root: &Path,
    env: &[(String, String)],
) -> CapturedCommandResult {
    run_cargo_check_for_fixture(crate_root, fixture_root, env)
}

fn run_cargo_fetch_for_fixture(
    fixture_root: &Path,
    env: &[(String, String)],
) -> CapturedCommandResult {
    let cargo = env
        .iter()
        .find(|(key, _)| key == "CARGO")
        .map(|(_, value)| value.as_str())
        .unwrap_or("cargo");
    let lock_path = fixture_root.join("Cargo.lock");
    let lock_snapshot = match fs::read(&lock_path) {
        Ok(contents) => contents,
        Err(err) if err.kind() == ErrorKind::NotFound => {
            return cargo_fixture_command_not_run(
                cargo,
                fixture_root,
                &["fetch", "--locked"],
                &format!(
                    "accepted cargo fixture must include Cargo.lock for locked dependency fetch evidence: {}",
                    lock_path.display()
                ),
            );
        }
        Err(err) => {
            return cargo_fixture_command_not_run(
                cargo,
                fixture_root,
                &["fetch", "--locked"],
                &format!(
                    "accepted cargo fixture must include Cargo.lock for locked dependency fetch evidence; failed to read {}: {err}",
                    lock_path.display()
                ),
            );
        }
    };
    let mut captured = run_command_with_env_capture(
        fixture_root,
        cargo,
        &["fetch", "--locked"],
        &borrowed_env(env),
    );
    if let Err(err) = restore_cargo_lock_snapshot(&lock_path, &lock_snapshot) {
        if captured.command.exit_code == Some(0) {
            captured.command.exit_code = Some(127);
        }
        append_command_stderr(
            &mut captured.command,
            &format!("failed to restore cargo fixture lockfile: {err}"),
        );
    }
    captured
}

fn run_cargo_check_for_fixture(
    crate_root: &Path,
    fixture_root: &Path,
    env: &[(String, String)],
) -> CapturedCommandResult {
    let cargo = env
        .iter()
        .find(|(key, _)| key == "CARGO")
        .map(|(_, value)| value.as_str())
        .unwrap_or("cargo");
    let lock_path = fixture_root.join("Cargo.lock");
    let lock_snapshot = match fs::read(&lock_path) {
        Ok(contents) => contents,
        Err(err) if err.kind() == ErrorKind::NotFound => {
            return cargo_fixture_command_not_run(
                cargo,
                fixture_root,
                &[
                    "check",
                    "--message-format=json",
                    "--all-targets",
                    "--locked",
                    "--offline",
                ],
                &format!(
                    "accepted cargo fixture must include Cargo.lock for locked offline evidence: {}",
                    lock_path.display()
                ),
            );
        }
        Err(err) => {
            return cargo_fixture_command_not_run(
                cargo,
                fixture_root,
                &[
                    "check",
                    "--message-format=json",
                    "--all-targets",
                    "--locked",
                    "--offline",
                ],
                &format!(
                    "accepted cargo fixture must include Cargo.lock for locked offline evidence; failed to read {}: {err}",
                    lock_path.display()
                ),
            );
        }
    };
    let target_dir = cargo_fixture_target_dir(crate_root, fixture_root);
    match fs::remove_dir_all(&target_dir) {
        Ok(()) => {}
        Err(err) if err.kind() == ErrorKind::NotFound => {}
        Err(err) => {
            return cargo_fixture_command_not_run(
                cargo,
                fixture_root,
                &[
                    "check",
                    "--message-format=json",
                    "--all-targets",
                    "--locked",
                    "--offline",
                ],
                &format!(
                    "failed to remove stale cargo fixture target dir {}: {err}",
                    target_dir.display()
                ),
            );
        }
    }
    let mut cargo_env = env.to_vec();
    cargo_env.retain(|(key, _)| key != "CARGO_TARGET_DIR");
    cargo_env.push((
        "CARGO_TARGET_DIR".to_string(),
        target_dir.to_string_lossy().into_owned(),
    ));
    let mut captured = run_command_with_env_capture(
        fixture_root,
        cargo,
        &[
            "check",
            "--message-format=json",
            "--all-targets",
            "--locked",
            "--offline",
        ],
        &borrowed_env(&cargo_env),
    );
    match cargo_dep_info_sources(&target_dir, fixture_root) {
        Ok(sources) => captured.cargo_dep_info_sources = sources,
        Err(error) => captured.cargo_dep_info_error = Some(error),
    }
    if let Err(err) = restore_cargo_lock_snapshot(&lock_path, &lock_snapshot) {
        if captured.command.exit_code == Some(0) {
            captured.command.exit_code = Some(127);
        }
        append_command_stderr(
            &mut captured.command,
            &format!("failed to restore cargo fixture lockfile: {err}"),
        );
    }
    captured
}

fn cargo_fixture_command_not_run(
    cargo: &str,
    fixture_root: &Path,
    args: &[&str],
    error: &str,
) -> CapturedCommandResult {
    CapturedCommandResult {
        command: CommandResult {
            program: cargo.to_string(),
            args: args.iter().map(|arg| (*arg).to_string()).collect(),
            cwd: fixture_root.to_path_buf(),
            exit_code: Some(127),
            duration_ms: 0,
            stdout_tail: String::new(),
            stderr_tail: error.to_string(),
        },
        stdout: String::new(),
        cargo_dep_info_sources: BTreeSet::new(),
        cargo_dep_info_error: None,
    }
}

fn append_command_stderr(command: &mut CommandResult, message: &str) {
    if !command.stderr_tail.is_empty() {
        command.stderr_tail.push('\n');
    }
    command.stderr_tail.push_str(message);
}

fn command_failure_context(command: &CommandResult) -> Option<String> {
    let context = if !command.stderr_tail.trim().is_empty() {
        command.stderr_tail.trim()
    } else {
        command.stdout_tail.trim()
    };
    if context.is_empty() {
        None
    } else {
        Some(tail_string(context, 2048))
    }
}

fn cargo_fixture_target_dir(crate_root: &Path, fixture_root: &Path) -> PathBuf {
    let rel = git_relative_path(crate_root, fixture_root);
    let digest = sha256_digest_bytes(rel.to_string_lossy().as_bytes());
    let digest = digest
        .strip_prefix("sha256:")
        .unwrap_or(digest.as_str())
        .chars()
        .take(16)
        .collect::<String>();
    crate_root
        .join("target")
        .join("trust-vc-corpus-fixtures")
        .join("runs")
        .join(evidence_process_run_id())
        .join(format!("fixture-{digest}"))
}

fn cargo_dep_info_sources(
    target_dir: &Path,
    fixture_root: &Path,
) -> Result<BTreeSet<PathBuf>, String> {
    let mut dep_info_files = Vec::new();
    collect_dep_info_files(target_dir, &mut dep_info_files).map_err(|err| {
        format!(
            "failed to scan cargo dep-info directory {}: {err}",
            target_dir.display()
        )
    })?;
    let mut sources = BTreeSet::new();
    for dep_info_file in dep_info_files {
        let contents = fs::read_to_string(&dep_info_file).map_err(|err| {
            format!(
                "failed to read cargo dep-info file {}: {err}",
                dep_info_file.display()
            )
        })?;
        for dep in cargo_dep_info_dependencies(&contents) {
            let path = Path::new(&dep);
            let path = if path.is_absolute() {
                path.to_path_buf()
            } else {
                fixture_root.join(path)
            };
            if path.extension().and_then(|ext| ext.to_str()) != Some("rs") {
                continue;
            }
            let Ok(canonical_path) = path.canonicalize() else {
                continue;
            };
            let Ok(canonical_fixture_root) = fixture_root.canonicalize() else {
                continue;
            };
            if canonical_path.starts_with(&canonical_fixture_root) {
                sources.insert(canonical_path);
            }
        }
    }
    Ok(sources)
}

fn collect_dep_info_files(dir: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
    if !dir.exists() {
        return Ok(());
    }
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            collect_dep_info_files(&path, out)?;
        } else if path.extension().and_then(|ext| ext.to_str()) == Some("d") {
            out.push(path);
        }
    }
    Ok(())
}

fn cargo_dep_info_dependencies(contents: &str) -> Vec<String> {
    let normalized = contents.replace("\\\n", " ");
    let mut deps = Vec::new();
    for line in normalized.lines() {
        let Some((_, dependency_text)) = split_dep_info_rule(line) else {
            continue;
        };
        deps.extend(makefile_words(dependency_text));
    }
    deps
}

fn split_dep_info_rule(line: &str) -> Option<(&str, &str)> {
    let mut escaped = false;
    for (index, ch) in line.char_indices() {
        if escaped {
            escaped = false;
            continue;
        }
        if ch == '\\' {
            escaped = true;
            continue;
        }
        if ch == ':' {
            return Some((&line[..index], &line[index + 1..]));
        }
    }
    None
}

fn makefile_words(input: &str) -> Vec<String> {
    let mut words = Vec::new();
    let mut current = String::new();
    let mut escaped = false;
    for ch in input.chars() {
        if escaped {
            current.push(ch);
            escaped = false;
            continue;
        }
        if ch == '\\' {
            escaped = true;
            continue;
        }
        if ch.is_whitespace() {
            if !current.is_empty() {
                words.push(std::mem::take(&mut current));
            }
            continue;
        }
        current.push(ch);
    }
    if !current.is_empty() {
        words.push(current);
    }
    words
}

fn restore_cargo_lock_snapshot(lock_path: &Path, snapshot: &[u8]) -> Result<(), String> {
    fs::write(lock_path, snapshot)
        .map_err(|err| format!("failed to restore {}: {err}", lock_path.display()))
}

fn append_cargo_check_failure_context(
    crate_root: &Path,
    fixture_root: &Path,
    output: &CapturedCommandResult,
    failures: &mut Vec<String>,
) {
    match rust_source_error_diagnostics_from_cargo_json(crate_root, fixture_root, &output.stdout) {
        Ok(diagnostics) if diagnostics.is_empty() => {
            let context = if !output.command.stderr_tail.trim().is_empty() {
                output.command.stderr_tail.trim()
            } else {
                output.command.stdout_tail.trim()
            };
            if !context.is_empty() {
                failures.push(format!(
                    "{}: cargo check output: {}",
                    report_path_string(fixture_root, crate_root),
                    tail_string(context, 2048)
                ));
            }
        }
        Ok(diagnostics) => {
            for diagnostic in diagnostics {
                failures.push(format!(
                    "{}: cargo check diagnostic: {}",
                    report_path_string(fixture_root, crate_root),
                    source_error_failure(crate_root, &diagnostic)
                ));
            }
        }
        Err(error) => failures.push(format!(
            "{}: cargo check did not emit valid diagnostic JSON: {error}",
            report_path_string(fixture_root, crate_root)
        )),
    }
}

#[derive(Debug, Deserialize)]
struct CargoCheckJsonMessage {
    reason: String,
    message: Option<CargoCheckDiagnostic>,
}

#[derive(Debug, Deserialize)]
struct CargoCheckDiagnostic {
    #[serde(default)]
    level: String,
    #[serde(default)]
    message: String,
    code: Option<CargoCheckDiagnosticCode>,
    #[serde(default)]
    spans: Vec<CargoCheckDiagnosticSpan>,
    rendered: Option<String>,
}

#[derive(Debug, Deserialize)]
struct CargoCheckDiagnosticCode {
    code: String,
}

#[derive(Debug, Deserialize)]
struct CargoCheckDiagnosticSpan {
    file_name: String,
    #[serde(default)]
    is_primary: bool,
    #[serde(default)]
    line_start: usize,
    #[serde(default)]
    column_start: usize,
}

fn rust_source_error_diagnostics_from_cargo_json(
    _crate_root: &Path,
    fixture_root: &Path,
    stdout: &str,
) -> Result<Vec<TrustVcCorpusSourceError>, String> {
    let mut diagnostics = Vec::new();
    let mut seen_diagnostics = BTreeSet::new();
    for line in stdout
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
    {
        let message = serde_json::from_str::<CargoCheckJsonMessage>(line).map_err(|err| {
            format!(
                "cargo check emitted malformed JSON message line: {err}: {}",
                tail_string(line, 512)
            )
        })?;
        if message.reason != "compiler-message" {
            continue;
        }
        let Some(diagnostic) = message.message else {
            continue;
        };
        if diagnostic.level != "error" {
            continue;
        }
        let Some(span) = primary_diagnostic_span(&diagnostic) else {
            continue;
        };
        let source_path = diagnostic_span_source_path(fixture_root, span);
        let detail = rust_source_diagnostic_detail(&diagnostic);
        let key = (
            source_path.clone(),
            span.line_start,
            span.column_start,
            detail.clone(),
        );
        if !seen_diagnostics.insert(key) {
            continue;
        }
        diagnostics.push(TrustVcCorpusSourceError {
            trust_vc_path: source_path,
            case_id: None,
            detail,
        });
    }
    Ok(diagnostics)
}

fn primary_diagnostic_span(diagnostic: &CargoCheckDiagnostic) -> Option<&CargoCheckDiagnosticSpan> {
    diagnostic
        .spans
        .iter()
        .find(|span| span.is_primary && !span.file_name.trim().is_empty())
}

fn diagnostic_span_source_path(fixture_root: &Path, span: &CargoCheckDiagnosticSpan) -> PathBuf {
    let path = Path::new(&span.file_name);
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        fixture_root.join(path)
    }
}

fn diagnostic_source_is_in_fixture(
    crate_root: &Path,
    fixture_root: &Path,
    diagnostic: &TrustVcCorpusSourceError,
) -> bool {
    let source_path = resolve_repo_path(crate_root, &diagnostic.trust_vc_path);
    match (source_path.canonicalize(), fixture_root.canonicalize()) {
        (Ok(source_path), Ok(fixture_root)) => source_path.starts_with(fixture_root),
        _ => false,
    }
}

fn rust_source_diagnostic_detail(diagnostic: &CargoCheckDiagnostic) -> String {
    let code = diagnostic
        .code
        .as_ref()
        .map(|code| code.code.as_str())
        .filter(|code| !code.trim().is_empty())
        .unwrap_or("rustc_error");
    let summary = diagnostic
        .rendered
        .as_deref()
        .unwrap_or(diagnostic.message.as_str())
        .lines()
        .find(|line| !line.trim().is_empty())
        .unwrap_or("Rust compiler error diagnostic");
    format!("{code}: {summary}")
}

fn current_trust_vc_binary() -> Result<PathBuf, String> {
    std::env::current_exe()
        .map_err(|err| format!("failed to resolve current cargo-trust-vc executable: {err}"))
}

#[derive(Debug)]
struct CargoFixtureDependencySidecarSetup {
    dependency_facts_json: Option<String>,
    commands: Vec<CommandResult>,
}

#[derive(Debug)]
struct CargoFixtureDependencySidecarError {
    message: String,
    commands: Vec<CommandResult>,
}

#[derive(Debug)]
struct CargoFixtureDependencySidecarProducer {
    alias: String,
    root: PathBuf,
    package_name: String,
    package_version: String,
    build_dependencies: Vec<CargoFixtureDependencySidecarProducer>,
    import_dependency_aliases: Vec<String>,
}

#[derive(Debug)]
struct CargoFixtureManifest {
    package_name: String,
    package_version: String,
    dependencies: BTreeMap<String, CargoFixtureDependencySpec>,
}

#[derive(Debug)]
struct CargoFixtureDependencySpec {
    path: PathBuf,
    package: Option<String>,
}

fn prepare_cargo_fixture_dependency_sidecars(
    crate_root: &Path,
    fixture_root: &Path,
    trust_vc_binary: &Path,
    env: &[(String, String)],
) -> Result<CargoFixtureDependencySidecarSetup, CargoFixtureDependencySidecarError> {
    let Some(producers) =
        cargo_fixture_dependency_sidecar_producers(fixture_root).map_err(|message| {
            CargoFixtureDependencySidecarError {
                message,
                commands: Vec::new(),
            }
        })?
    else {
        return Ok(CargoFixtureDependencySidecarSetup {
            dependency_facts_json: None,
            commands: Vec::new(),
        });
    };

    let mut commands = Vec::new();
    let mut artifacts = Vec::new();
    for producer in producers {
        let output = run_cargo_fixture_dependency_sidecar_build(
            crate_root,
            fixture_root,
            trust_vc_binary,
            env,
            &producer,
        );
        let command = output.command.clone();
        commands.push(command.clone());
        if command.exit_code != Some(0) {
            return Err(CargoFixtureDependencySidecarError {
                message: format!(
                    "{}: dependency sidecar build for `{}` failed with {}",
                    report_path_string(fixture_root, crate_root),
                    producer.alias,
                    display_exit_code(command.exit_code)
                ),
                commands,
            });
        }
        match dependency_sidecar_artifact_from_target(
            crate_root,
            &producer,
            &cargo_fixture_dependency_sidecar_target_dir(crate_root, fixture_root, &producer.root),
        ) {
            Ok(artifact) => artifacts.push(artifact),
            Err(message) => {
                return Err(CargoFixtureDependencySidecarError { message, commands });
            }
        }
    }

    let dependency_facts_json =
        serde_json::to_string(&artifacts).map_err(|err| CargoFixtureDependencySidecarError {
            message: format!(
                "{}: failed to encode dependency sidecar facts: {err}",
                report_path_string(fixture_root, crate_root)
            ),
            commands: commands.clone(),
        })?;

    Ok(CargoFixtureDependencySidecarSetup {
        dependency_facts_json: Some(dependency_facts_json),
        commands,
    })
}

fn cargo_fixture_dependency_sidecar_producers(
    fixture_root: &Path,
) -> Result<Option<Vec<CargoFixtureDependencySidecarProducer>>, String> {
    let manifest = read_cargo_fixture_manifest(&fixture_root.join("Cargo.toml"))?;
    match manifest.package_name.as_str() {
        "spec_use" => Ok(Some(spec_use_dependency_sidecar_producers(
            fixture_root,
            &manifest,
        )?)),
        "spec_use_unverified" => Ok(Some(spec_use_unverified_dependency_sidecar_producers(
            fixture_root,
            &manifest,
        )?)),
        _ => Ok(None),
    }
}

fn spec_use_dependency_sidecar_producers(
    fixture_root: &Path,
    manifest: &CargoFixtureManifest,
) -> Result<Vec<CargoFixtureDependencySidecarProducer>, String> {
    let spec_def = required_dependency_sidecar_producer(
        fixture_root,
        manifest,
        "spec_def",
        "spec_def",
        "0.1.0",
        None,
    )?;
    let spec_def2 = required_dependency_sidecar_producer(
        fixture_root,
        manifest,
        "spec_def2",
        "spec_def",
        "0.2.0",
        Some("spec_def"),
    )?;
    Ok(vec![spec_def, spec_def2])
}

fn spec_use_unverified_dependency_sidecar_producers(
    fixture_root: &Path,
    manifest: &CargoFixtureManifest,
) -> Result<Vec<CargoFixtureDependencySidecarProducer>, String> {
    let mut spec_use = required_dependency_sidecar_producer(
        fixture_root,
        manifest,
        "spec_use",
        "spec_use",
        "0.1.0",
        None,
    )?;
    let spec_use_manifest = read_cargo_fixture_manifest(&spec_use.root.join("Cargo.toml"))?;
    let spec_use_dependencies =
        spec_use_dependency_sidecar_producers(&spec_use.root, &spec_use_manifest)?;
    spec_use.import_dependency_aliases = spec_use_dependencies
        .iter()
        .map(|producer| producer.alias.clone())
        .collect();
    spec_use.build_dependencies = spec_use_dependencies;
    Ok(vec![spec_use])
}

fn required_dependency_sidecar_producer(
    fixture_root: &Path,
    manifest: &CargoFixtureManifest,
    alias: &str,
    expected_package_name: &str,
    expected_package_version: &str,
    expected_dependency_package: Option<&str>,
) -> Result<CargoFixtureDependencySidecarProducer, String> {
    let dep = manifest.dependencies.get(alias).ok_or_else(|| {
        format!(
            "{}: cargo_spec_use dependency sidecar orchestration requires path dependency `{alias}`",
            fixture_root.display()
        )
    })?;
    let dependency_package = dep.package.as_deref().unwrap_or(alias);
    if Some(dependency_package) != expected_dependency_package.or(Some(alias))
        || dependency_package != expected_package_name
    {
        return Err(format!(
            "{}: cargo_spec_use dependency `{alias}` has unsupported package identity `{dependency_package}`; expected `{expected_package_name}`",
            fixture_root.display()
        ));
    }

    let root = if dep.path.is_absolute() {
        dep.path.clone()
    } else {
        fixture_root.join(&dep.path)
    };
    let producer_manifest = read_cargo_fixture_manifest(&root.join("Cargo.toml"))?;
    if producer_manifest.package_name != expected_package_name
        || producer_manifest.package_version != expected_package_version
    {
        return Err(format!(
            "{}: cargo_spec_use dependency `{alias}` points at unsupported producer {} {}; expected {} {}",
            fixture_root.display(),
            producer_manifest.package_name,
            producer_manifest.package_version,
            expected_package_name,
            expected_package_version
        ));
    }

    Ok(CargoFixtureDependencySidecarProducer {
        alias: alias.to_string(),
        root,
        package_name: producer_manifest.package_name,
        package_version: producer_manifest.package_version,
        build_dependencies: Vec::new(),
        import_dependency_aliases: Vec::new(),
    })
}

fn run_cargo_fixture_dependency_sidecar_build(
    crate_root: &Path,
    fixture_root: &Path,
    trust_vc_binary: &Path,
    env: &[(String, String)],
    producer: &CargoFixtureDependencySidecarProducer,
) -> CapturedCommandResult {
    let cargo = env
        .iter()
        .find(|(key, _)| key == "CARGO")
        .map(|(_, value)| value.as_str())
        .unwrap_or("cargo");
    let args = ["check", "--lib", "--locked", "--offline"];
    let lock_path = producer.root.join("Cargo.lock");
    let lock_snapshot = match fs::read(&lock_path) {
        Ok(contents) => contents,
        Err(err) if err.kind() == ErrorKind::NotFound => {
            return cargo_fixture_command_not_run(
                cargo,
                &producer.root,
                &args,
                &format!(
                    "dependency sidecar producer must include Cargo.lock for locked offline evidence: {}",
                    lock_path.display()
                ),
            );
        }
        Err(err) => {
            return cargo_fixture_command_not_run(
                cargo,
                &producer.root,
                &args,
                &format!(
                    "dependency sidecar producer must include Cargo.lock for locked offline evidence; failed to read {}: {err}",
                    lock_path.display()
                ),
            );
        }
    };
    let target_dir =
        cargo_fixture_dependency_sidecar_target_dir(crate_root, fixture_root, &producer.root);
    match fs::remove_dir_all(&target_dir) {
        Ok(()) => {}
        Err(err) if err.kind() == ErrorKind::NotFound => {}
        Err(err) => {
            return cargo_fixture_command_not_run(
                cargo,
                &producer.root,
                &args,
                &format!(
                    "failed to remove stale dependency sidecar target dir {}: {err}",
                    target_dir.display()
                ),
            );
        }
    }

    let mut cargo_env = env.to_vec();
    cargo_env.retain(|(key, _)| {
        key != "CARGO_TARGET_DIR"
            && key != "RUSTC_WRAPPER"
            && key != CARGO_DEFAULT_LIB_METADATA_ENV
            && key != VERUS_DRIVER_ARGS_ENV
            && key != VERUS_DRIVER_VIA_CARGO_ENV
            && !key.starts_with(VERUS_DRIVER_ARGS_FOR_ENV_PREFIX)
            && !key.starts_with(VERUS_DRIVER_VERIFY_ENV_PREFIX)
    });
    cargo_env.push((
        "CARGO_TARGET_DIR".to_string(),
        target_dir.to_string_lossy().into_owned(),
    ));
    cargo_env.push((
        "RUSTC_WRAPPER".to_string(),
        trust_vc_binary.to_string_lossy().into_owned(),
    ));
    cargo_env.push((
        CARGO_DEFAULT_LIB_METADATA_ENV.to_string(),
        "verus".to_string(),
    ));
    cargo_env.push((VERUS_DRIVER_VIA_CARGO_ENV.to_string(), "1".to_string()));
    cargo_env.push((
        VERUS_DRIVER_ARGS_ENV.to_string(),
        pack_verus_driver_args(["--VIA-CARGO", "compile-when-not-primary-package"].into_iter()),
    ));
    append_cargo_fixture_dependency_sidecar_producer_env(&mut cargo_env, producer);

    let mut captured =
        run_command_with_env_capture(&producer.root, cargo, &args, &borrowed_env(&cargo_env));
    if let Err(err) = restore_cargo_lock_snapshot(&lock_path, &lock_snapshot) {
        if captured.command.exit_code == Some(0) {
            captured.command.exit_code = Some(127);
        }
        append_command_stderr(
            &mut captured.command,
            &format!("failed to restore dependency sidecar producer lockfile: {err}"),
        );
    }
    captured
}

fn append_cargo_fixture_dependency_sidecar_producer_env(
    cargo_env: &mut Vec<(String, String)>,
    producer: &CargoFixtureDependencySidecarProducer,
) {
    let mut seen_package_ids = BTreeSet::new();
    append_cargo_fixture_dependency_sidecar_producer_env_inner(
        cargo_env,
        producer,
        &mut seen_package_ids,
    );
}

fn append_cargo_fixture_dependency_sidecar_producer_env_inner(
    cargo_env: &mut Vec<(String, String)>,
    producer: &CargoFixtureDependencySidecarProducer,
    seen_package_ids: &mut BTreeSet<String>,
) {
    let manifest_path = producer.root.join("Cargo.toml");
    let package_env_id = package_env_id_from_manifest_path(
        &producer.package_name,
        &producer.package_version,
        &manifest_path,
    );
    if seen_package_ids.insert(package_env_id.clone()) {
        cargo_env.push((
            format!("{VERUS_DRIVER_VERIFY_ENV_PREFIX}{package_env_id}"),
            "1".to_string(),
        ));
        if !producer.import_dependency_aliases.is_empty() {
            let import_args = producer
                .import_dependency_aliases
                .iter()
                .map(|alias| format!("import-dep-if-present={alias}"))
                .collect::<Vec<_>>();
            cargo_env.push((
                format!("{VERUS_DRIVER_ARGS_FOR_ENV_PREFIX}{package_env_id}"),
                pack_verus_driver_args(import_args.iter().map(String::as_str)),
            ));
        }
    }
    for dependency in &producer.build_dependencies {
        append_cargo_fixture_dependency_sidecar_producer_env_inner(
            cargo_env,
            dependency,
            seen_package_ids,
        );
    }
}

fn cargo_fixture_dependency_sidecar_target_dir(
    crate_root: &Path,
    fixture_root: &Path,
    producer_root: &Path,
) -> PathBuf {
    let rel = format!(
        "{}\0{}",
        git_relative_path(crate_root, fixture_root).to_string_lossy(),
        git_relative_path(crate_root, producer_root).to_string_lossy()
    );
    let digest = sha256_digest_bytes(rel.as_bytes());
    let digest = digest
        .strip_prefix("sha256:")
        .unwrap_or(digest.as_str())
        .chars()
        .take(16)
        .collect::<String>();
    crate_root
        .join("target")
        .join("trust-vc-corpus-fixtures")
        .join("runs")
        .join(evidence_process_run_id())
        .join(format!("dependency-sidecars-{digest}"))
}

fn evidence_process_run_id() -> String {
    format!("pid-{}", std::process::id())
}

fn dependency_sidecar_artifact_from_target(
    crate_root: &Path,
    producer: &CargoFixtureDependencySidecarProducer,
    target_dir: &Path,
) -> Result<serde_json::Value, String> {
    let mut artifacts = Vec::new();
    collect_dependency_sidecar_artifact_files(target_dir, &mut artifacts).map_err(|err| {
        format!(
            "{}: failed to scan dependency sidecar target dir {}: {err}",
            report_path_string(&producer.root, crate_root),
            target_dir.display()
        )
    })?;
    if artifacts.is_empty() {
        return Err(format!(
            "{}: dependency sidecar build for `{}` produced {} cargo-trust-vc sidecar artifact(s), expected exactly 1",
            report_path_string(&producer.root, crate_root),
            producer.alias,
            artifacts.len()
        ));
    }
    let mut matching_artifacts = Vec::new();
    for artifact_path in artifacts {
        let artifact = read_dependency_sidecar_artifact_json(crate_root, producer, &artifact_path)?;
        if dependency_sidecar_artifact_matches_producer(producer, &artifact) {
            matching_artifacts.push((artifact_path, artifact));
        }
    }
    if matching_artifacts.len() != 1 {
        Err(format!(
            "{}: dependency sidecar build for `{}` produced {} matching cargo-trust-vc sidecar artifact(s), expected exactly 1",
            report_path_string(&producer.root, crate_root),
            producer.alias,
            matching_artifacts.len()
        ))
    } else {
        let (artifact_path, artifact) = matching_artifacts.remove(0);
        validate_dependency_sidecar_artifact(crate_root, producer, &artifact_path, &artifact)?;
        Ok(artifact)
    }
}

fn read_dependency_sidecar_artifact_json(
    crate_root: &Path,
    producer: &CargoFixtureDependencySidecarProducer,
    artifact_path: &Path,
) -> Result<serde_json::Value, String> {
    let content = fs::read_to_string(artifact_path).map_err(|err| {
        format!(
            "{}: failed to read dependency sidecar artifact {}: {err}",
            report_path_string(&producer.root, crate_root),
            artifact_path.display()
        )
    })?;
    let body = content
        .strip_prefix(TRUST_VC_RUSTC_WRAPPER_ARTIFACT_MAGIC)
        .ok_or_else(|| {
            format!(
                "{}: dependency sidecar artifact {} is not a cargo-trust-vc rustc-wrapper artifact",
                report_path_string(&producer.root, crate_root),
                artifact_path.display()
            )
        })?;
    serde_json::from_str::<serde_json::Value>(body.trim()).map_err(|err| {
        format!(
            "{}: dependency sidecar artifact {} does not contain valid JSON: {err}",
            report_path_string(&producer.root, crate_root),
            artifact_path.display()
        )
    })
}

fn dependency_sidecar_artifact_matches_producer(
    producer: &CargoFixtureDependencySidecarProducer,
    artifact: &serde_json::Value,
) -> bool {
    let manifest_path = canonical_manifest_path_for_hash(&producer.root.join("Cargo.toml"));
    let source_path = canonical_manifest_path_for_hash(&producer.root.join("src/lib.rs"));
    artifact
        .get("artifact_kind")
        .and_then(serde_json::Value::as_str)
        == Some(TRUST_VC_RUSTC_WRAPPER_ARTIFACT_KIND)
        && artifact
            .get("package_name")
            .and_then(serde_json::Value::as_str)
            == Some(producer.package_name.as_str())
        && artifact
            .get("package_version")
            .and_then(serde_json::Value::as_str)
            == Some(producer.package_version.as_str())
        && artifact
            .get("manifest_path")
            .and_then(serde_json::Value::as_str)
            == Some(manifest_path.as_str())
        && artifact
            .get("source_path")
            .and_then(serde_json::Value::as_str)
            == Some(source_path.as_str())
}

fn collect_dependency_sidecar_artifact_files(
    dir: &Path,
    out: &mut Vec<PathBuf>,
) -> std::io::Result<()> {
    if !dir.exists() {
        return Ok(());
    }
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            collect_dependency_sidecar_artifact_files(&path, out)?;
        } else if path.extension().and_then(|ext| ext.to_str()) == Some("vir") {
            out.push(path);
        }
    }
    Ok(())
}

fn validate_dependency_sidecar_artifact(
    crate_root: &Path,
    producer: &CargoFixtureDependencySidecarProducer,
    artifact_path: &Path,
    artifact: &serde_json::Value,
) -> Result<(), String> {
    let manifest_path = canonical_manifest_path_for_hash(&producer.root.join("Cargo.toml"));
    let source_path = canonical_manifest_path_for_hash(&producer.root.join("src/lib.rs"));
    let payload = artifact.get("semantic_payload").ok_or_else(|| {
        dependency_sidecar_artifact_error(
            crate_root,
            producer,
            artifact_path,
            "missing semantic_payload",
        )
    })?;
    let concrete_functions = payload
        .get("concrete_functions")
        .and_then(serde_json::Value::as_array)
        .map(Vec::len)
        .unwrap_or(0);
    let checks = [
        (
            artifact
                .get("artifact_kind")
                .and_then(serde_json::Value::as_str),
            TRUST_VC_RUSTC_WRAPPER_ARTIFACT_KIND,
            "artifact_kind",
        ),
        (
            artifact
                .get("package_name")
                .and_then(serde_json::Value::as_str),
            producer.package_name.as_str(),
            "package_name",
        ),
        (
            artifact
                .get("package_version")
                .and_then(serde_json::Value::as_str),
            producer.package_version.as_str(),
            "package_version",
        ),
        (
            artifact
                .get("manifest_path")
                .and_then(serde_json::Value::as_str),
            manifest_path.as_str(),
            "manifest_path",
        ),
        (
            artifact
                .get("source_path")
                .and_then(serde_json::Value::as_str),
            source_path.as_str(),
            "source_path",
        ),
        (
            payload.get("kind").and_then(serde_json::Value::as_str),
            TRUST_VC_RUSTC_WRAPPER_SEMANTIC_FACTS_PAYLOAD_KIND,
            "semantic_payload.kind",
        ),
    ];
    for (observed, expected, label) in checks {
        if observed != Some(expected) {
            return Err(dependency_sidecar_artifact_error(
                crate_root,
                producer,
                artifact_path,
                &format!("unexpected {label}; expected `{expected}`"),
            ));
        }
    }
    if payload
        .get("proof_facts_exported")
        .and_then(serde_json::Value::as_bool)
        != Some(true)
    {
        return Err(dependency_sidecar_artifact_error(
            crate_root,
            producer,
            artifact_path,
            "semantic payload did not export proof facts",
        ));
    }
    if concrete_functions == 0 {
        return Err(dependency_sidecar_artifact_error(
            crate_root,
            producer,
            artifact_path,
            "semantic payload exported no concrete function facts",
        ));
    }
    Ok(())
}

fn dependency_sidecar_artifact_error(
    crate_root: &Path,
    producer: &CargoFixtureDependencySidecarProducer,
    artifact_path: &Path,
    detail: &str,
) -> String {
    format!(
        "{}: dependency sidecar artifact for `{}` at {} is unsupported: {detail}",
        report_path_string(&producer.root, crate_root),
        producer.alias,
        artifact_path.display()
    )
}

fn read_cargo_fixture_manifest(manifest_path: &Path) -> Result<CargoFixtureManifest, String> {
    let text = fs::read_to_string(manifest_path).map_err(|err| {
        format!(
            "failed to read cargo fixture manifest {}: {err}",
            manifest_path.display()
        )
    })?;
    let mut table = CargoFixtureManifestTable::Other;
    let mut package_name = None;
    let mut package_version = None;
    let mut dependencies = BTreeMap::new();

    for raw_line in text.lines() {
        let line = strip_toml_comment(raw_line);
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        if let Some(header) = line
            .strip_prefix('[')
            .and_then(|line| line.strip_suffix(']'))
        {
            table = match header.trim() {
                "package" => CargoFixtureManifestTable::Package,
                "dependencies" => CargoFixtureManifestTable::Dependencies,
                _ => CargoFixtureManifestTable::Other,
            };
            continue;
        }
        let Some((key, value)) = line.split_once('=') else {
            continue;
        };
        let key = key.trim();
        let value = value.trim();
        match table {
            CargoFixtureManifestTable::Package if key == "name" => {
                package_name = parse_toml_string(value);
            }
            CargoFixtureManifestTable::Package if key == "version" => {
                package_version = parse_toml_string(value);
            }
            CargoFixtureManifestTable::Dependencies => {
                if let Some(spec) = parse_cargo_fixture_dependency_spec(value)? {
                    dependencies.insert(key.to_string(), spec);
                }
            }
            CargoFixtureManifestTable::Package | CargoFixtureManifestTable::Other => {}
        }
    }

    Ok(CargoFixtureManifest {
        package_name: package_name.ok_or_else(|| {
            format!(
                "cargo fixture manifest {} is missing [package].name",
                manifest_path.display()
            )
        })?,
        package_version: package_version.ok_or_else(|| {
            format!(
                "cargo fixture manifest {} is missing [package].version",
                manifest_path.display()
            )
        })?,
        dependencies,
    })
}

#[derive(Debug, Clone, Copy)]
enum CargoFixtureManifestTable {
    Package,
    Dependencies,
    Other,
}

fn parse_cargo_fixture_dependency_spec(
    value: &str,
) -> Result<Option<CargoFixtureDependencySpec>, String> {
    let value = value.trim();
    if !value.starts_with('{') {
        return Ok(None);
    }
    let fields = parse_toml_inline_table_string_fields(value)?;
    let Some(path) = fields.get("path") else {
        return Ok(None);
    };
    Ok(Some(CargoFixtureDependencySpec {
        path: PathBuf::from(path),
        package: fields.get("package").cloned(),
    }))
}

fn parse_toml_inline_table_string_fields(value: &str) -> Result<BTreeMap<String, String>, String> {
    let body = value
        .trim()
        .strip_prefix('{')
        .and_then(|value| value.strip_suffix('}'))
        .ok_or_else(|| format!("unsupported inline dependency table `{value}`"))?;
    let mut fields = BTreeMap::new();
    for field in split_toml_inline_table_fields(body) {
        let Some((key, value)) = field.split_once('=') else {
            return Err(format!("unsupported inline dependency field `{field}`"));
        };
        if let Some(value) = parse_toml_string(value.trim()) {
            fields.insert(key.trim().to_string(), value);
        }
    }
    Ok(fields)
}

fn split_toml_inline_table_fields(value: &str) -> Vec<&str> {
    let mut fields = Vec::new();
    let mut start = 0;
    let mut in_string = false;
    let mut escaped = false;
    for (index, ch) in value.char_indices() {
        if escaped {
            escaped = false;
            continue;
        }
        match ch {
            '\\' if in_string => escaped = true,
            '"' => in_string = !in_string,
            ',' if !in_string => {
                let field = value[start..index].trim();
                if !field.is_empty() {
                    fields.push(field);
                }
                start = index + ch.len_utf8();
            }
            _ => {}
        }
    }
    let field = value[start..].trim();
    if !field.is_empty() {
        fields.push(field);
    }
    fields
}

fn strip_toml_comment(line: &str) -> String {
    let mut in_string = false;
    let mut escaped = false;
    let mut out = String::new();
    for ch in line.chars() {
        if escaped {
            out.push(ch);
            escaped = false;
            continue;
        }
        match ch {
            '\\' if in_string => {
                out.push(ch);
                escaped = true;
            }
            '"' => {
                in_string = !in_string;
                out.push(ch);
            }
            '#' if !in_string => break,
            _ => out.push(ch),
        }
    }
    out
}

fn parse_toml_string(value: &str) -> Option<String> {
    let value = value.trim();
    let body = value.strip_prefix('"')?.strip_suffix('"')?;
    Some(body.replace("\\\"", "\"").replace("\\\\", "\\"))
}

fn package_env_id_from_manifest_path(name: &str, version: &str, manifest_path: &Path) -> String {
    let manifest_path = canonical_manifest_path_for_hash(manifest_path);
    let digest = Sha256::digest(manifest_path.as_bytes());
    let mut manifest_path_hash = String::with_capacity(12);
    for byte in &digest[..6] {
        manifest_path_hash.push_str(&format!("{byte:02x}"));
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

struct CargoFixtureRunOutput {
    command: CommandResult,
    setup_commands: Vec<CommandResult>,
    observed_cases: Result<Vec<TrustVcCorpusObservedCase>, String>,
    stdout_json_valid: Result<(), String>,
    prerequisite_failed: bool,
}

fn trust_vc_fixture_check_args(trust_vc_check_args: &[String]) -> Vec<String> {
    let mut args = vec![
        "check".to_string(),
        "--json".to_string(),
        "--emit-certificate".to_string(),
    ];
    args.extend(trust_vc_check_args.iter().cloned());
    args.push(".".to_string());
    args
}

fn run_current_trust_vc_on_cargo_fixture(
    crate_root: &Path,
    fixture_root: &Path,
    trust_vc_binary: &Path,
    trust_vc_check_args: &[String],
    expected_cases: &[VerusExpectedCase],
    env: &[(String, String)],
) -> CargoFixtureRunOutput {
    let sidecar_setup = match prepare_cargo_fixture_dependency_sidecars(
        crate_root,
        fixture_root,
        trust_vc_binary,
        env,
    ) {
        Ok(setup) => setup,
        Err(error) => {
            let command = trust_vc_fixture_command_not_run(
                trust_vc_binary,
                fixture_root,
                trust_vc_check_args,
                &error.message,
            );
            return CargoFixtureRunOutput {
                command,
                setup_commands: error.commands,
                observed_cases: Err(error.message),
                stdout_json_valid: Err("command was not run".to_string()),
                prerequisite_failed: true,
            };
        }
    };
    let certificate_path = fixture_root
        .join(certificate::CERTIFICATE_DIR)
        .join(certificate::CERTIFICATE_FILENAME);
    let backup = match backup_trust_vc_certificate(&certificate_path) {
        Ok(backup) => backup,
        Err(error) => {
            let command = trust_vc_fixture_command_not_run(
                trust_vc_binary,
                fixture_root,
                trust_vc_check_args,
                &error,
            );
            return CargoFixtureRunOutput {
                command,
                setup_commands: sidecar_setup.commands,
                observed_cases: Err(error),
                stdout_json_valid: Err("command was not run".to_string()),
                prerequisite_failed: false,
            };
        }
    };
    if let Err(error) = remove_trust_vc_certificate_before_run(&certificate_path) {
        let command = trust_vc_fixture_command_not_run(
            trust_vc_binary,
            fixture_root,
            trust_vc_check_args,
            &error,
        );
        return CargoFixtureRunOutput {
            command,
            setup_commands: sidecar_setup.commands,
            observed_cases: Err(error),
            stdout_json_valid: Err("command was not run".to_string()),
            prerequisite_failed: false,
        };
    }

    let binary = trust_vc_binary.to_string_lossy().into_owned();
    let command_args = trust_vc_fixture_check_args(trust_vc_check_args);
    let borrowed_args = command_args.iter().map(String::as_str).collect::<Vec<_>>();
    let mut trust_vc_env = env.to_vec();
    if let Some(dependency_facts_json) = &sidecar_setup.dependency_facts_json {
        trust_vc_env.retain(|(key, _)| key != TRUST_VC_DEPENDENCY_FACTS_ENV);
        trust_vc_env.push((
            TRUST_VC_DEPENDENCY_FACTS_ENV.to_string(),
            dependency_facts_json.clone(),
        ));
    }
    let captured = run_command_with_env_capture(
        fixture_root,
        &binary,
        &borrowed_args,
        &borrowed_env(&trust_vc_env),
    );
    let stdout_json_valid = validate_trust_vc_check_json(&captured.stdout);
    let observed_cases = if trust_vc_check_args.iter().any(|arg| arg == "--no-cheating")
        && captured.command.exit_code == Some(1)
        && trust_vc_check_stdout_is_no_cheating_failure(&captured.stdout)
    {
        observed_cases_from_no_cheating_json(
            crate_root,
            fixture_root,
            &captured.stdout,
            expected_cases,
        )
    } else {
        observed_cases_from_trust_vc_certificate(crate_root, fixture_root, &certificate_path)
    };
    let mut restore_error = None;
    if let Err(error) = restore_trust_vc_certificate(&certificate_path, backup) {
        restore_error = Some(error);
    }
    let observed_cases = match (observed_cases, restore_error) {
        (Ok(cases), None) => Ok(cases),
        (Ok(_), Some(error)) => Err(error),
        (Err(error), None) => Err(error),
        (Err(error), Some(restore_error)) => Err(format!("{error}; {restore_error}")),
    };
    CargoFixtureRunOutput {
        command: captured.command,
        setup_commands: sidecar_setup.commands,
        observed_cases,
        stdout_json_valid,
        prerequisite_failed: false,
    }
}

fn trust_vc_fixture_command_not_run(
    trust_vc_binary: &Path,
    fixture_root: &Path,
    trust_vc_check_args: &[String],
    error: &str,
) -> CommandResult {
    CommandResult {
        program: trust_vc_binary.to_string_lossy().into_owned(),
        args: trust_vc_fixture_check_args(trust_vc_check_args),
        cwd: fixture_root.to_path_buf(),
        exit_code: Some(127),
        duration_ms: 0,
        stdout_tail: String::new(),
        stderr_tail: error.to_string(),
    }
}

fn backup_trust_vc_certificate(path: &Path) -> Result<Option<Vec<u8>>, String> {
    match fs::read(path) {
        Ok(contents) => Ok(Some(contents)),
        Err(err) if err.kind() == ErrorKind::NotFound => Ok(None),
        Err(err) => Err(format!(
            "failed to back up existing proof certificate {}: {err}",
            path.display()
        )),
    }
}

fn remove_trust_vc_certificate_before_run(path: &Path) -> Result<(), String> {
    match fs::remove_file(path) {
        Ok(()) => Ok(()),
        Err(err) if err.kind() == ErrorKind::NotFound => Ok(()),
        Err(err) => Err(format!(
            "failed to remove stale proof certificate {}: {err}",
            path.display()
        )),
    }
}

fn restore_trust_vc_certificate(path: &Path, backup: Option<Vec<u8>>) -> Result<(), String> {
    match backup {
        Some(contents) => {
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent).map_err(|err| {
                    format!(
                        "failed to recreate proof certificate directory {}: {err}",
                        parent.display()
                    )
                })?;
            }
            fs::write(path, contents).map_err(|err| {
                format!(
                    "failed to restore proof certificate {}: {err}",
                    path.display()
                )
            })
        }
        None => {
            match fs::remove_file(path) {
                Ok(()) => {}
                Err(err) if err.kind() == ErrorKind::NotFound => {}
                Err(err) => {
                    return Err(format!(
                        "failed to remove generated proof certificate {}: {err}",
                        path.display()
                    ));
                }
            }
            if let Some(parent) = path.parent() {
                match fs::remove_dir(parent) {
                    Ok(()) => {}
                    Err(err)
                        if matches!(
                            err.kind(),
                            ErrorKind::NotFound | ErrorKind::DirectoryNotEmpty
                        ) => {}
                    Err(err) => {
                        return Err(format!(
                            "failed to remove generated proof certificate directory {}: {err}",
                            parent.display()
                        ));
                    }
                }
            }
            Ok(())
        }
    }
}

#[derive(Debug, Deserialize)]
struct TrustVcCheckJsonReport {
    #[serde(default)]
    functions: Vec<TrustVcCheckJsonFunction>,
}

#[derive(Debug, Deserialize)]
struct TrustVcCheckJsonFunction {
    name: String,
}

#[derive(Debug, Deserialize)]
struct TrustVcNoCheatingJsonReport {
    result: String,
    #[serde(default)]
    findings: Vec<TrustVcNoCheatingJsonFinding>,
}

#[derive(Debug, Deserialize)]
struct TrustVcNoCheatingJsonFinding {
    file: String,
    line: usize,
    construct: String,
    detail: String,
}

fn validate_trust_vc_check_json(stdout: &str) -> Result<(), String> {
    let report: TrustVcCheckJsonReport = serde_json::from_str(stdout.trim())
        .map_err(|err| format!("failed to parse cargo-trust-vc JSON stdout: {err}"))?;
    for function in report.functions {
        if function.name.trim().is_empty() {
            return Err("cargo-trust-vc JSON stdout contained an empty function name".to_string());
        }
    }
    Ok(())
}

fn trust_vc_check_stdout_is_no_cheating_failure(stdout: &str) -> bool {
    serde_json::from_str::<TrustVcNoCheatingJsonReport>(stdout.trim())
        .map(|report| report.result == "no_cheating_failed")
        .unwrap_or(false)
}

fn observed_cases_from_no_cheating_json(
    crate_root: &Path,
    fixture_root: &Path,
    stdout: &str,
    expected_cases: &[VerusExpectedCase],
) -> Result<Vec<TrustVcCorpusObservedCase>, String> {
    let report: TrustVcNoCheatingJsonReport = serde_json::from_str(stdout.trim())
        .map_err(|err| format!("failed to parse cargo-trust-vc no-cheating JSON stdout: {err}"))?;
    if report.result != "no_cheating_failed" {
        return Err(format!(
            "cargo-trust-vc JSON result was `{}`, expected `no_cheating_failed`",
            report.result
        ));
    }
    if report.findings.is_empty() {
        return Err("cargo-trust-vc no-cheating JSON contained no findings".to_string());
    }

    let finding_groups = no_cheating_finding_groups(&report.findings);
    let mut used_groups = BTreeSet::new();
    let mut observed_cases = Vec::new();
    for expected_case in expected_cases
        .iter()
        .filter(|case| case.expected_verdict == VerusExpectedVerdict::Error)
    {
        let Some(expected_file) = no_cheating_expected_case_source_file_pattern(expected_case)
        else {
            return Err(format!(
                "no-cheating expected case `{}` must include a source file expected_error_patterns value like `src/<case>.rs`",
                expected_case.case_id
            ));
        };
        let Some((group_index, group)) =
            finding_groups.iter().enumerate().find(|(index, group)| {
                !used_groups.contains(index)
                    && group.file == expected_file
                    && expected_case
                        .expected_error_patterns
                        .iter()
                        .all(|pattern| group.diagnostic_context.contains(pattern))
            })
        else {
            continue;
        };
        used_groups.insert(group_index);
        observed_cases.push(TrustVcCorpusObservedCase {
            case_id: expected_case.case_id.clone(),
            trust_vc_path: report_path_string(&fixture_root.join(&group.file), crate_root),
            verdict: expected_verdict_label(VerusExpectedVerdict::Error).to_string(),
            obligation_count: 0,
            obligation_fingerprints: Vec::new(),
            diagnostic_context: vec![group.diagnostic_context.clone()],
            warnings: Vec::new(),
        });
    }

    for (index, group) in finding_groups.iter().enumerate() {
        if used_groups.contains(&index) {
            continue;
        }
        observed_cases.push(TrustVcCorpusObservedCase {
            case_id: format!("unexpected_no_cheating_finding_{}", index + 1),
            trust_vc_path: report_path_string(&fixture_root.join(&group.file), crate_root),
            verdict: expected_verdict_label(VerusExpectedVerdict::Error).to_string(),
            obligation_count: 0,
            obligation_fingerprints: Vec::new(),
            diagnostic_context: vec![group.diagnostic_context.clone()],
            warnings: Vec::new(),
        });
    }

    Ok(observed_cases)
}

struct NoCheatingFindingGroup {
    file: String,
    diagnostic_context: String,
}

fn no_cheating_finding_groups(
    findings: &[TrustVcNoCheatingJsonFinding],
) -> Vec<NoCheatingFindingGroup> {
    let mut grouped = BTreeMap::<String, Vec<String>>::new();
    for finding in findings {
        grouped
            .entry(finding.file.clone())
            .or_default()
            .push(no_cheating_finding_context(finding));
    }
    grouped
        .into_iter()
        .map(|(file, mut contexts)| {
            contexts.sort();
            NoCheatingFindingGroup {
                file,
                diagnostic_context: contexts.join("\n"),
            }
        })
        .collect()
}

fn no_cheating_finding_context(finding: &TrustVcNoCheatingJsonFinding) -> String {
    format!(
        "{}:{}: {} ({})",
        finding.file, finding.line, finding.construct, finding.detail
    )
}

#[derive(Debug, Deserialize)]
struct TrustVcProofCertificateJson {
    #[serde(default)]
    functions: Vec<TrustVcProofFunctionJson>,
}

#[derive(Debug, Deserialize)]
struct TrustVcProofFunctionJson {
    name: String,
    file: String,
    status: String,
    #[serde(default)]
    obligations: Vec<TrustVcProofObligationJson>,
}

#[derive(Debug, Deserialize)]
struct TrustVcProofObligationJson {
    condition_hash: String,
    status: String,
}

fn observed_cases_from_trust_vc_certificate(
    crate_root: &Path,
    fixture_root: &Path,
    certificate_path: &Path,
) -> Result<Vec<TrustVcCorpusObservedCase>, String> {
    let certificate = fs::read_to_string(certificate_path).map_err(|err| {
        format!(
            "failed to read proof certificate {}: {err}",
            certificate_path.display()
        )
    })?;
    let certificate: TrustVcProofCertificateJson =
        serde_json::from_str(&certificate).map_err(|err| {
            format!(
                "failed to parse proof certificate {}: {err}",
                certificate_path.display()
            )
        })?;
    let fixture_root = fixture_root.canonicalize().map_err(|err| {
        format!(
            "failed to canonicalize cargo fixture root {}: {err}",
            fixture_root.display()
        )
    })?;
    let mut observed_cases = Vec::new();
    for function in certificate.functions {
        if function.status == "skipped" {
            continue;
        }
        if function.name.trim().is_empty() {
            return Err("proof certificate contains a function with an empty name".to_string());
        }
        let source_path = if Path::new(&function.file).is_absolute() {
            PathBuf::from(&function.file)
        } else {
            fixture_root.join(&function.file)
        };
        let source_path = source_path.canonicalize().map_err(|err| {
            format!(
                "failed to canonicalize proof certificate source file `{}`: {err}",
                source_path.display()
            )
        })?;
        if !source_path.starts_with(&fixture_root) {
            return Err(format!(
                "proof certificate source file `{}` is outside cargo fixture `{}`",
                source_path.display(),
                fixture_root.display()
            ));
        }
        let mut obligation_fingerprints = Vec::new();
        for obligation in function
            .obligations
            .into_iter()
            .filter(|obligation| captured_certificate_obligation_status(&obligation.status))
        {
            if !valid_sha256_digest_label(&obligation.condition_hash) {
                return Err(format!(
                    "proof certificate function `{}` has invalid obligation condition_hash `{}`",
                    function.name, obligation.condition_hash
                ));
            }
            obligation_fingerprints.push(obligation.condition_hash);
        }
        observed_cases.push(TrustVcCorpusObservedCase {
            case_id: function.name,
            trust_vc_path: report_path_string(&source_path, crate_root),
            verdict: function.status,
            obligation_count: obligation_fingerprints.len(),
            obligation_fingerprints,
            diagnostic_context: Vec::new(),
            warnings: Vec::new(),
        });
    }
    Ok(observed_cases)
}

fn captured_certificate_obligation_status(status: &str) -> bool {
    matches!(status, "verified" | "counterexample" | "unknown" | "error")
}

fn failed_trust_vc_corpus_run_result(
    candidate: &TrustVcCorpusRunCandidate,
    execution_mode: TrustVcCorpusExecutionMode,
    detail: Option<&str>,
    failures: Vec<String>,
    command: Option<CommandResult>,
    commands: Vec<CommandResult>,
) -> TrustVcCorpusRunResult {
    TrustVcCorpusRunResult {
        upstream_path: candidate.upstream_path.clone(),
        trust_vc_path: candidate.trust_vc_paths.join(", "),
        trust_vc_paths: candidate.trust_vc_paths.clone(),
        execution_mode,
        status: GateStatus::Failed,
        detail: detail.map(str::to_string),
        function_count: 0,
        expected_case_count: candidate.expected_cases.len(),
        observed_case_count: 0,
        expected_obligation_count: expected_obligation_count(&candidate.expected_cases),
        observed_obligation_count: 0,
        expected_case_ids: expected_case_ids(&candidate.expected_cases),
        observed_case_ids: Vec::new(),
        observed_cases: Vec::new(),
        failures,
        command,
        commands,
    }
}

fn scan_trust_vc_corpus_file(
    path: &Path,
    functions: &mut Vec<scan::AnnotatedFunction>,
    source_errors: &mut Vec<TrustVcCorpusSourceError>,
) {
    let source = match fs::read_to_string(path) {
        Ok(source) => source,
        Err(err) => {
            source_errors.push(TrustVcCorpusSourceError {
                trust_vc_path: path.to_path_buf(),
                case_id: None,
                detail: format!("failed to read TrustVc source: {err}"),
            });
            return;
        }
    };
    let ast = match trust_vc_core::parse_file_allow_tracked(&source) {
        Ok(ast) => ast,
        Err(err) => {
            source_errors.push(TrustVcCorpusSourceError {
                trust_vc_path: path.to_path_buf(),
                case_id: None,
                detail: format!("failed to parse TrustVc source: {err}"),
            });
            return;
        }
    };
    let static_errors = trust_vc_corpus_static_source_errors(path, &ast);
    let blocked_case_ids = static_errors
        .iter()
        .filter_map(|error| error.case_id.clone())
        .collect::<BTreeSet<_>>();
    source_errors.extend(static_errors);
    let signature_only_helpers = signature_only_proof_helper_names(&ast);
    let mut file_functions = scan::scan_file(path);
    file_functions.retain(|function| {
        !blocked_case_ids.contains(&function.name)
            && !is_trust_vc_corpus_helper_only_function(function)
            && !signature_only_helpers.contains(&function.name)
    });
    functions.extend(file_functions);
}

/// Names of SIGNATURE-ONLY proof helpers: `#[trust_vc::proof]` functions with an
/// EMPTY body and NO contract (`requires` / `ensures` / `contract`).
///
/// Upstream test bodies routinely declare such helpers purely to give a call a
/// signature to type/mode-check against — e.g. `assert_forall_by.rs`'s
/// `proof fn consume(tracked x: bool) { }` and `proof fn no_consume(x: bool) { }`,
/// which exist only so the by-block can CALL them. They are not upstream cases
/// and must not appear as corpus cases.
///
/// This CANNOT hide a proof obligation: with no contract there is no
/// requires/ensures obligation, and with an empty body there is no body
/// obligation — the set is empty by construction. (A proof fn with a non-empty
/// body or any contract is NOT filtered, so the existing forcing function that
/// makes a port schedule its proof-fn obligations is untouched.)
fn signature_only_proof_helper_names(ast: &syn::File) -> BTreeSet<String> {
    fn walk(items: &[syn::Item], names: &mut BTreeSet<String>) {
        for item in items {
            match item {
                syn::Item::Fn(func) => {
                    let is_proof = function_has_trust_vc_attr(&func.attrs, "proof");
                    let has_contract = ["requires", "ensures", "contract"]
                        .iter()
                        .any(|name| function_has_trust_vc_attr(&func.attrs, name));
                    if is_proof && !has_contract && func.block.stmts.is_empty() {
                        names.insert(func.sig.ident.to_string());
                    }
                }
                syn::Item::Mod(module) => {
                    if let Some((_, inner)) = &module.content {
                        walk(inner, names);
                    }
                }
                _ => {}
            }
        }
    }
    let mut names = BTreeSet::new();
    walk(&ast.items, &mut names);
    names
}

fn is_trust_vc_corpus_helper_only_function(function: &scan::AnnotatedFunction) -> bool {
    !function.attributes.is_empty()
        && function.attributes.iter().all(|attr| {
            matches!(
                attr.as_str(),
                "spec" | "decreases" | "opaque" | "inline" | "rlimit" | "broadcast" | "trigger"
            )
        })
}

fn trust_vc_corpus_static_source_errors(
    path: &Path,
    ast: &syn::File,
) -> Vec<TrustVcCorpusSourceError> {
    let mut errors = Vec::new();
    collect_trust_vc_corpus_static_source_errors(path, &ast.items, &mut errors);
    errors
}

fn collect_trust_vc_corpus_static_source_errors(
    path: &Path,
    items: &[syn::Item],
    errors: &mut Vec<TrustVcCorpusSourceError>,
) {
    for item in items {
        match item {
            syn::Item::Fn(func)
                if function_has_trust_vc_attr(&func.attrs, "proof")
                    && func.sig.unsafety.is_some() =>
            {
                errors.push(TrustVcCorpusSourceError {
                    trust_vc_path: path.to_path_buf(),
                    case_id: Some(func.sig.ident.to_string()),
                    detail: "'unsafe' only makes sense on exec-mode functions".to_string(),
                });
            }
            syn::Item::Fn(_) => {}
            syn::Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    collect_trust_vc_corpus_static_source_errors(path, inner_items, errors);
                }
            }
            _ => {}
        }
    }
}

fn function_has_trust_vc_attr(attrs: &[syn::Attribute], name: &str) -> bool {
    attrs.iter().any(|attr| {
        let segments = attr
            .path()
            .segments
            .iter()
            .map(|segment| segment.ident.to_string())
            .collect::<Vec<_>>();
        match segments.as_slice() {
            [single] => single == name,
            [prefix, suffix] => prefix == "trust_vc" && suffix == name,
            _ => false,
        }
    })
}

fn item_has_attr(attrs: &[syn::Attribute], name: &str) -> bool {
    attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == name)
    })
}

fn compact_tokens(tokens: impl quote::ToTokens) -> String {
    quote::quote!(#tokens)
        .to_string()
        .chars()
        .filter(|ch| !ch.is_whitespace())
        .collect()
}

fn count_token_ident(tokens: impl quote::ToTokens, ident: &str) -> usize {
    compact_tokens(tokens).matches(ident).count()
}

fn manual_verus_harness_case(
    func: &syn::ItemFn,
) -> Result<Option<UpstreamVerusHarnessCase>, String> {
    if !item_has_attr(&func.attrs, "test") {
        return Ok(None);
    }
    let body = compact_tokens(&func.block);
    if !body.contains("verify_one_file") {
        return Ok(None);
    }
    if count_token_ident(&func.block, "verify_one_file") != 1 {
        return Err(format!(
            "ordinary upstream #[test] `{}` contains multiple verify_one_file calls that this evidence extractor cannot map soundly",
            func.sig.ident
        ));
    }
    let rust_error = body.contains("assert_rust_error_msg");
    let expected_verdict = if rust_error
        || body.contains("assert_vir_error_msg")
        || body.contains("assert_any_vir_error_msg")
        || body.contains("assert_help_error_msg")
    {
        VerusExpectedVerdict::Error
    } else if manual_harness_has_positive_is_ok_assert(func) {
        VerusExpectedVerdict::Verified
    } else if body.contains("unwrap_err()") {
        VerusExpectedVerdict::Counterexample
    } else {
        return Err(format!(
            "ordinary upstream #[test] `{}` calls verify_one_file but this evidence extractor cannot infer its expected verdict",
            func.sig.ident
        ));
    };
    Ok(Some(UpstreamVerusHarnessCase {
        case_id: func.sig.ident.to_string(),
        expected_verdict,
        ignored: item_has_attr(&func.attrs, "ignore"),
        rust_error,
        error_patterns: if expected_verdict == VerusExpectedVerdict::Error {
            helper_error_patterns(func.block.to_token_stream())
        } else {
            Vec::new()
        },
        forbidden_diagnostic_patterns: Vec::new(),
        expected_occurrences: 1,
        warning_patterns: Vec::new(),
    }))
}

fn manual_harness_has_positive_is_ok_assert(func: &syn::ItemFn) -> bool {
    func.block.stmts.iter().any(|stmt| match stmt {
        syn::Stmt::Expr(syn::Expr::Macro(expr_macro), _) => {
            assert_macro_tokens_are_positive_verify_is_ok(&expr_macro.mac)
        }
        syn::Stmt::Macro(stmt_macro) => {
            assert_macro_tokens_are_positive_verify_is_ok(&stmt_macro.mac)
        }
        _ => false,
    })
}

fn assert_macro_tokens_are_positive_verify_is_ok(mac: &syn::Macro) -> bool {
    let is_assert = mac
        .path
        .segments
        .last()
        .is_some_and(|segment| segment.ident == "assert");
    if !is_assert {
        return false;
    }
    let tokens = compact_tokens(mac.tokens.clone());
    tokens.starts_with("verify_one_file(")
        && tokens.ends_with(").is_ok()")
        && tokens.matches("verify_one_file").count() == 1
}

fn duplicate_upstream_case_ids(cases: &[UpstreamVerusHarnessCase]) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut duplicates = BTreeSet::new();
    for case in cases {
        if !seen.insert(case.case_id.as_str()) {
            duplicates.insert(case.case_id.clone());
        }
    }
    duplicates.into_iter().collect()
}

fn err_helper_verdict(helper: &str) -> Option<(VerusExpectedVerdict, bool)> {
    if helper.starts_with("assert_rust_error_msg") {
        return Some((VerusExpectedVerdict::Error, true));
    }
    if helper.starts_with("assert_vir_error_msg")
        || helper.starts_with("assert_any_vir_error_msg")
        || helper.starts_with("assert_help_error_msg")
        || helper == "assert_spec_borrowed"
        || helper == "assert_spec_borrowed_field"
        || helper == "assert_spec_eq_type_err"
        || helper == "assert_fails_type_invariant_error"
    {
        return Some((VerusExpectedVerdict::Error, false));
    }
    if helper == "assert_fails"
        || helper == "assert_one_fails"
        || helper == "assert_has_recommends_failure"
        || helper.starts_with("assert_fails_bv_")
    {
        return Some((VerusExpectedVerdict::Counterexample, false));
    }
    None
}

fn err_helper_expected_occurrences(helper: &str, args: Option<&proc_macro2::Group>) -> usize {
    if helper != "assert_fails" {
        return 1;
    }
    args.and_then(|group| {
        integer_literals_in_tokens(group.stream())
            .into_iter()
            .last()
    })
    .filter(|count| *count > 0)
    .unwrap_or(1)
}

fn helper_error_patterns(tokens: TokenStream) -> Vec<String> {
    let tokens = tokens.into_iter().collect::<Vec<_>>();
    let mut patterns = Vec::new();
    collect_helper_error_patterns(&tokens, &mut patterns);
    patterns.sort();
    patterns.dedup();
    patterns
}

fn integer_literals_in_tokens(tokens: TokenStream) -> Vec<usize> {
    let mut integers = Vec::new();
    for token in tokens {
        match token {
            TokenTree::Literal(literal) => {
                let rendered = literal.to_string();
                let digits = rendered
                    .chars()
                    .take_while(|ch| ch.is_ascii_digit())
                    .collect::<String>();
                if !digits.is_empty() {
                    if let Ok(value) = digits.parse::<usize>() {
                        integers.push(value);
                    }
                }
            }
            TokenTree::Group(group) => integers.extend(integer_literals_in_tokens(group.stream())),
            _ => {}
        }
    }
    integers
}

fn string_literals_in_tokens(tokens: TokenStream) -> Vec<String> {
    let mut patterns = Vec::new();
    collect_string_literals(tokens, &mut patterns);
    patterns.sort();
    patterns.dedup();
    patterns
}

fn collect_helper_error_patterns(tokens: &[TokenTree], patterns: &mut Vec<String>) {
    let mut index = 0;
    while let Some(token) = tokens.get(index) {
        match token {
            TokenTree::Ident(ident)
                if error_helper_carries_diagnostic_pattern(&ident.to_string()) =>
            {
                if let Some(TokenTree::Group(group)) = tokens.get(index + 1) {
                    collect_string_literals(group.stream(), patterns);
                }
                index += 2;
                continue;
            }
            TokenTree::Group(group) => collect_helper_error_patterns(
                &group.stream().into_iter().collect::<Vec<_>>(),
                patterns,
            ),
            _ => {}
        }
        index += 1;
    }
}

fn error_helper_carries_diagnostic_pattern(helper: &str) -> bool {
    helper.starts_with("assert_rust_error_msg")
        || helper.starts_with("assert_vir_error_msg")
        || helper.starts_with("assert_any_vir_error_msg")
        || helper.starts_with("assert_help_error_msg")
}

fn collect_string_literals(tokens: TokenStream, patterns: &mut Vec<String>) {
    for token in tokens {
        match token {
            TokenTree::Literal(literal) => {
                if let Ok(lit) = syn::parse_str::<syn::LitStr>(&literal.to_string()) {
                    patterns.push(lit.value());
                }
            }
            TokenTree::Group(group) => collect_string_literals(group.stream(), patterns),
            _ => {}
        }
    }
}

fn source_error_failure(crate_root: &Path, source_error: &TrustVcCorpusSourceError) -> String {
    let case = source_error
        .case_id
        .as_deref()
        .map(|case_id| format!("{case_id}: "))
        .unwrap_or_default();
    format!(
        "{}: {}{}",
        report_path_string(&source_error.trust_vc_path, crate_root),
        case,
        source_error.detail
    )
}

fn source_error_matches_expected_case(
    source_error: &TrustVcCorpusSourceError,
    expected_case: &VerusExpectedCase,
) -> bool {
    source_error_matches_expected_case_patterns(
        source_error,
        expected_case,
        &expected_case.expected_error_patterns,
    )
}

fn source_error_matches_expected_case_patterns(
    source_error: &TrustVcCorpusSourceError,
    expected_case: &VerusExpectedCase,
    patterns: &[String],
) -> bool {
    source_error
        .case_id
        .as_deref()
        .is_none_or(|case_id| case_id == expected_case.case_id)
        && patterns
            .iter()
            .all(|pattern| source_error.detail.contains(pattern))
}

fn expected_case_rust_diagnostic_pattern_sets(expected_case: &VerusExpectedCase) -> Vec<&[String]> {
    if expected_case
        .expected_rust_diagnostic_pattern_sets
        .is_empty()
    {
        vec![expected_case.expected_error_patterns.as_slice()]
    } else {
        expected_case
            .expected_rust_diagnostic_pattern_sets
            .iter()
            .map(Vec::as_slice)
            .collect()
    }
}

fn expected_case_rust_diagnostic_count(expected_case: &VerusExpectedCase) -> usize {
    if expected_case
        .expected_rust_diagnostic_pattern_sets
        .is_empty()
    {
        1
    } else {
        expected_case.expected_rust_diagnostic_pattern_sets.len()
    }
}

fn match_source_error_pattern_sets(
    source_errors: &[TrustVcCorpusSourceError],
    unavailable_indices: &BTreeSet<usize>,
    expected_case: &VerusExpectedCase,
) -> Option<Vec<usize>> {
    let pattern_sets = expected_case_rust_diagnostic_pattern_sets(expected_case);
    let mut used_indices = unavailable_indices.clone();
    let mut matched_indices = Vec::new();
    if match_source_error_pattern_sets_from(
        0,
        &pattern_sets,
        source_errors,
        expected_case,
        &mut used_indices,
        &mut matched_indices,
    ) {
        Some(matched_indices)
    } else {
        None
    }
}

fn match_source_error_pattern_sets_from(
    position: usize,
    pattern_sets: &[&[String]],
    source_errors: &[TrustVcCorpusSourceError],
    expected_case: &VerusExpectedCase,
    used_indices: &mut BTreeSet<usize>,
    matched_indices: &mut Vec<usize>,
) -> bool {
    if position == pattern_sets.len() {
        return true;
    }
    for (index, source_error) in source_errors.iter().enumerate() {
        if used_indices.contains(&index) {
            continue;
        }
        if !source_error_matches_expected_case_patterns(
            source_error,
            expected_case,
            pattern_sets[position],
        ) {
            continue;
        }
        used_indices.insert(index);
        matched_indices.push(index);
        if match_source_error_pattern_sets_from(
            position + 1,
            pattern_sets,
            source_errors,
            expected_case,
            used_indices,
            matched_indices,
        ) {
            return true;
        }
        matched_indices.pop();
        used_indices.remove(&index);
    }
    false
}

fn append_source_error_observed_cases(
    crate_root: &Path,
    candidate: &TrustVcCorpusRunCandidate,
    observed_cases: &mut Vec<TrustVcCorpusObservedCase>,
    source_errors: &[TrustVcCorpusSourceError],
) -> BTreeSet<usize> {
    if source_errors.is_empty() {
        return BTreeSet::new();
    }
    let mut observed_ids = observed_cases
        .iter()
        .map(|case| case.case_id.clone())
        .collect::<BTreeSet<_>>();
    let mut source_errors_used = BTreeSet::new();
    for expected_case in &candidate.expected_cases {
        if expected_case.expected_verdict != VerusExpectedVerdict::Error
            || observed_ids.contains(&expected_case.case_id)
        {
            continue;
        }
        let Some((index, source_error)) =
            source_errors
                .iter()
                .enumerate()
                .find(|(index, source_error)| {
                    !source_errors_used.contains(index)
                        && source_error.case_id.as_deref() == Some(expected_case.case_id.as_str())
                        && source_error_matches_expected_case(source_error, expected_case)
                })
        else {
            break;
        };
        source_errors_used.insert(index);
        observed_ids.insert(expected_case.case_id.clone());
        observed_cases.push(TrustVcCorpusObservedCase {
            case_id: expected_case.case_id.clone(),
            trust_vc_path: report_path_string(&source_error.trust_vc_path, crate_root),
            verdict: expected_verdict_label(VerusExpectedVerdict::Error).to_string(),
            obligation_count: 0,
            obligation_fingerprints: Vec::new(),
            diagnostic_context: vec![source_error.detail.clone()],
            warnings: Vec::new(),
        });
    }
    source_errors_used
}

fn scan_trust_vc_corpus_dir(
    dir: &Path,
    functions: &mut Vec<scan::AnnotatedFunction>,
    source_errors: &mut Vec<TrustVcCorpusSourceError>,
) {
    let entries = match fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(err) => {
            source_errors.push(TrustVcCorpusSourceError {
                trust_vc_path: dir.to_path_buf(),
                case_id: None,
                detail: format!("failed to read TrustVc source directory: {err}"),
            });
            return;
        }
    };
    let mut paths = entries
        .flatten()
        .map(|entry| entry.path())
        .collect::<Vec<_>>();
    paths.sort();
    for path in paths {
        if path.is_dir() {
            scan_trust_vc_corpus_dir(&path, functions, source_errors);
        } else if path.extension().is_some_and(|ext| ext == "rs") {
            scan_trust_vc_corpus_file(&path, functions, source_errors);
        }
    }
}

fn run_trust_vc_corpus_command(
    crate_root: &Path,
    candidate: &TrustVcCorpusRunCandidate,
    trust_vc_path: &str,
    command_template: &str,
    env: &[(String, String)],
) -> TrustVcCorpusRunResult {
    let path = match validate_repo_trust_vc_path(crate_root, trust_vc_path) {
        Ok(path) => path,
        Err(error) => {
            return TrustVcCorpusRunResult {
                upstream_path: candidate.upstream_path.clone(),
                trust_vc_path: trust_vc_path.to_string(),
                trust_vc_paths: vec![trust_vc_path.to_string()],
                execution_mode: TrustVcCorpusExecutionMode::Command,
                status: GateStatus::Failed,
                detail: Some(error.clone()),
                function_count: 0,
                expected_case_count: candidate.expected_cases.len(),
                observed_case_count: 0,
                expected_obligation_count: expected_obligation_count(&candidate.expected_cases),
                observed_obligation_count: 0,
                expected_case_ids: expected_case_ids(&candidate.expected_cases),
                observed_case_ids: Vec::new(),
                observed_cases: Vec::new(),
                failures: vec![error],
                command: None,
                commands: Vec::new(),
            };
        }
    };
    let command_line = render_trust_vc_corpus_command(
        command_template,
        crate_root,
        &candidate.upstream_path,
        &path,
    );
    let command = run_shell_command(crate_root, &command_line, env);
    let status = gate_status_from_exit(command.exit_code);
    TrustVcCorpusRunResult {
        upstream_path: candidate.upstream_path.clone(),
        trust_vc_path: trust_vc_path.to_string(),
        trust_vc_paths: vec![trust_vc_path.to_string()],
        execution_mode: TrustVcCorpusExecutionMode::Command,
        status,
        detail: command_result_detail(&command),
        function_count: 0,
        expected_case_count: candidate.expected_cases.len(),
        observed_case_count: 0,
        expected_obligation_count: expected_obligation_count(&candidate.expected_cases),
        observed_obligation_count: 0,
        expected_case_ids: expected_case_ids(&candidate.expected_cases),
        observed_case_ids: Vec::new(),
        observed_cases: Vec::new(),
        failures: if status == GateStatus::Passed {
            Vec::new()
        } else {
            vec![format!("command failed: {command_line}")]
        },
        command: Some(command),
        commands: Vec::new(),
    }
}

fn run_shell_command(cwd: &Path, shell_command: &str, env: &[(String, String)]) -> CommandResult {
    run_command_with_env(
        cwd,
        DEFAULT_SH_COMMAND,
        &["-c", shell_command],
        &borrowed_env(env),
    )
}

fn render_trust_vc_corpus_command(
    template: &str,
    crate_root: &Path,
    upstream_path: &str,
    trust_vc_path: &Path,
) -> String {
    template
        .replace("{crate_root}", &shell_quote(&crate_root.to_string_lossy()))
        .replace("{upstream_path}", &shell_quote(upstream_path))
        .replace(
            "{trust_vc_path}",
            &shell_quote(&trust_vc_path.to_string_lossy()),
        )
}

fn shell_quote(value: &str) -> String {
    format!("'{}'", value.replace('\'', "'\\''"))
}

fn expected_case_ids(expected_cases: &[VerusExpectedCase]) -> Vec<String> {
    expected_cases
        .iter()
        .map(|expected_case| expected_case.case_id.clone())
        .collect()
}

fn upstream_case_id(expected_case: &VerusExpectedCase) -> &str {
    expected_case
        .upstream_case_id
        .as_deref()
        .unwrap_or(expected_case.case_id.as_str())
}

fn expected_obligation_count(expected_cases: &[VerusExpectedCase]) -> usize {
    expected_cases
        .iter()
        .map(|expected_case| expected_case.min_obligations)
        .sum()
}

fn observed_case_ids(observed_cases: &[TrustVcCorpusObservedCase]) -> Vec<String> {
    observed_cases
        .iter()
        .map(|observed_case| observed_case.case_id.clone())
        .collect()
}

fn duplicate_expected_case_ids(expected_cases: &[VerusExpectedCase]) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut duplicates = BTreeSet::new();
    for expected_case in expected_cases {
        if !seen.insert(expected_case.case_id.as_str()) {
            duplicates.insert(expected_case.case_id.clone());
        }
    }
    duplicates.into_iter().collect()
}

fn valid_expected_case_id(value: &str) -> bool {
    let mut chars = value.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first == '_' || first.is_ascii_alphabetic())
        && chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
}

fn expected_verdict_label(verdict: VerusExpectedVerdict) -> &'static str {
    match verdict {
        VerusExpectedVerdict::Verified => "verified",
        VerusExpectedVerdict::Counterexample => "counterexample",
        VerusExpectedVerdict::Error => "error",
        VerusExpectedVerdict::VerifiedBlocker => "verified-blocker",
    }
}

fn observed_case_from_verification(
    crate_root: &Path,
    verification: &verify::FunctionVerification,
) -> TrustVcCorpusObservedCase {
    let obligation_fingerprints = captured_obligation_fingerprints(verification);
    TrustVcCorpusObservedCase {
        case_id: verification.verdict.function.name.clone(),
        trust_vc_path: report_path_string(&verification.verdict.function.file_path, crate_root),
        verdict: verdict_kind_label(&verification.verdict.result).to_string(),
        obligation_count: obligation_fingerprints.len(),
        obligation_fingerprints,
        diagnostic_context: diagnostic_context_from_verification(crate_root, verification),
        warnings: verification.warnings.clone(),
    }
}

fn diagnostic_context_from_verification(
    crate_root: &Path,
    verification: &verify::FunctionVerification,
) -> Vec<String> {
    let mut context = Vec::new();
    if let Some(detail) = &verification.verdict.detail {
        context.push(format!("detail: {detail}"));
    }
    if let Some(failure) = &verification.verdict.localized_failure {
        context.push(format!(
            "localized_failure: {} {} {:?}",
            failure.phase, failure.label, failure.result
        ));
        if let Some(location) = &failure.location {
            push_diagnostic_location_context(crate_root, location, &mut context);
        }
    }
    for obligation in &verification.obligations {
        if !matches!(
            obligation.status,
            verify::ObligationStatus::Counterexample
                | verify::ObligationStatus::Unknown
                | verify::ObligationStatus::Error
        ) {
            continue;
        }
        context.push(format!(
            "obligation: {} {} {:?}",
            obligation.kind, obligation.name, obligation.status
        ));
        if let Some(location) = &obligation.location {
            push_diagnostic_location_context(crate_root, location, &mut context);
        }
    }
    if verification.verdict.result != verify::VerdictKind::Verified {
        context.extend(diagnostic_assertion_source_lines(
            crate_root,
            &verification.verdict.function,
        ));
    }
    let mut seen = BTreeSet::new();
    context
        .into_iter()
        .filter(|entry| seen.insert(entry.clone()))
        .collect()
}

fn push_diagnostic_location_context(crate_root: &Path, location: &str, context: &mut Vec<String>) {
    context.push(format!("location: {location}"));
    if let Some(line) = diagnostic_source_line(crate_root, location) {
        context.push(line);
    }
}

fn diagnostic_source_line(crate_root: &Path, location: &str) -> Option<String> {
    let (source_path, line_number) = parse_diagnostic_location(location)?;
    let source_path = if source_path.is_absolute() {
        source_path
    } else {
        crate_root.join(source_path)
    };
    let source = fs::read_to_string(&source_path).ok()?;
    let line_text = source.lines().nth(line_number.checked_sub(1)?)?;
    Some(format!(
        "{}:{}: {}",
        report_path_string(&source_path, crate_root),
        line_number,
        line_text.trim_end()
    ))
}

fn parse_diagnostic_location(location: &str) -> Option<(PathBuf, usize)> {
    let (prefix, last_segment) = location.rsplit_once(':')?;
    if let Some((file, line_segment)) = prefix.rsplit_once(':') {
        if let Ok(line_number) = line_segment.parse::<usize>() {
            return Some((PathBuf::from(file), line_number));
        }
    }
    let line_number = last_segment.parse::<usize>().ok()?;
    Some((PathBuf::from(prefix), line_number))
}

fn diagnostic_assertion_source_lines(
    crate_root: &Path,
    function: &scan::AnnotatedFunction,
) -> Vec<String> {
    let Ok(source) = fs::read_to_string(&function.file_path) else {
        return Vec::new();
    };
    let Ok(ast) = trust_vc_core::parse_file_allow_tracked(&source) else {
        return Vec::new();
    };
    let Some((start_line, end_line)) = function_body_line_range(&ast.items, &function.name) else {
        return Vec::new();
    };
    source
        .lines()
        .enumerate()
        .skip(start_line.saturating_sub(1))
        .take(end_line.saturating_sub(start_line).saturating_add(1))
        .filter(|(_, line)| line.contains("trust_vc::assert!") || line.contains("assert!("))
        .map(|(index, line)| {
            format!(
                "{}:{}: {}",
                report_path_string(&function.file_path, crate_root),
                index + 1,
                line.trim_end()
            )
        })
        .collect()
}

fn function_body_line_range(items: &[syn::Item], name: &str) -> Option<(usize, usize)> {
    for item in items {
        match item {
            syn::Item::Fn(func) if func.sig.ident == name => {
                return Some(block_line_range(&func.block));
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    if let Some(range) = function_body_line_range(inner_items, name) {
                        return Some(range);
                    }
                }
            }
            syn::Item::Impl(impl_block) => {
                for impl_item in &impl_block.items {
                    if let syn::ImplItem::Fn(method) = impl_item {
                        if method.sig.ident == name {
                            return Some(block_line_range(&method.block));
                        }
                    }
                }
            }
            syn::Item::Trait(trait_block) => {
                for trait_item in &trait_block.items {
                    if let syn::TraitItem::Fn(method) = trait_item {
                        if method.sig.ident == name {
                            if let Some(block) = &method.default {
                                return Some(block_line_range(block));
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
    None
}

fn block_line_range(block: &syn::Block) -> (usize, usize) {
    (
        block.brace_token.span.open().start().line,
        block.brace_token.span.close().end().line,
    )
}

fn captured_obligation_fingerprints(verification: &verify::FunctionVerification) -> Vec<String> {
    verification
        .obligations
        .iter()
        .filter(|obligation| {
            matches!(
                obligation.status,
                verify::ObligationStatus::Verified
                    | verify::ObligationStatus::Counterexample
                    | verify::ObligationStatus::Unknown
                    | verify::ObligationStatus::Error
            )
        })
        .map(|obligation| obligation.condition_hash.clone())
        .collect()
}

fn verdict_kind_label(kind: &verify::VerdictKind) -> &'static str {
    match kind {
        verify::VerdictKind::Verified => "verified",
        verify::VerdictKind::Counterexample => "counterexample",
        verify::VerdictKind::Unknown => "unknown",
        verify::VerdictKind::Error => "error",
        verify::VerdictKind::Skipped => "skipped",
        verify::VerdictKind::NotAnalyzed => "not_analyzed",
    }
}

fn update_verus_tests_manifest(
    args: &EvidenceArgs,
    verus_head: Option<&str>,
) -> Result<(), EvidenceError> {
    let verus_path = args
        .verus_path
        .as_deref()
        .ok_or_else(|| EvidenceError::new("--update-verus-tests-manifest requires --verus-path"))?;
    let template_path = if args.canonical_manifest_path.exists() {
        Some(args.canonical_manifest_path.as_path())
    } else {
        args.manifest_path
            .as_deref()
            .filter(|manifest_path| manifest_path.exists())
    };
    let template = template_path.map(load_manifest).transpose()?;
    let template_entries = template
        .as_ref()
        .map(|manifest| manifest.entries.as_slice())
        .unwrap_or(&[]);
    let duplicate_entries = duplicate_manifest_paths(template_entries);
    if !duplicate_entries.is_empty() {
        return Err(EvidenceError::new(format!(
            "cannot update Verus tests manifest with duplicate upstream_path entries: {}",
            duplicate_entries.join(", ")
        )));
    }

    let upstream_ref = args
        .verus_rev
        .as_deref()
        .or(verus_head)
        .or_else(|| {
            template
                .as_ref()
                .and_then(|manifest| manifest.upstream_ref.as_deref())
        })
        .map(str::trim)
        .filter(|reference| !reference.is_empty())
        .ok_or_else(|| {
            EvidenceError::new(
                "--update-verus-tests-manifest requires --verus-rev, a discoverable Verus HEAD, or an existing manifest upstream.ref",
            )
        })?
        .to_string();
    let required_roots = required_verus_test_roots();
    let upstream_tests = enumerate_upstream_tests_from_git_ref(
        Some(verus_path),
        Some(upstream_ref.as_str()),
        &required_roots,
    )
    .map_err(|error| {
        EvidenceError::new(format!(
            "failed to enumerate upstream Verus tests at `{upstream_ref}` via git ls-tree: {error}"
        ))
    })?;
    if upstream_tests.is_empty() {
        return Err(EvidenceError::new(format!(
            "no upstream Verus tests found under {:?} at `{upstream_ref}`",
            required_roots
        )));
    }

    let existing_by_path: BTreeMap<String, VerusManifestEntry> = template_entries
        .iter()
        .cloned()
        .map(|entry| (entry.upstream_path.clone(), entry))
        .collect();
    let mut entries = Vec::with_capacity(upstream_tests.len());
    for upstream_path in upstream_tests {
        if let Some(existing) = existing_by_path.get(&upstream_path) {
            entries.push(existing.clone());
        } else {
            entries.push(VerusManifestEntry {
                upstream_path,
                classification: "unclassified".to_string(),
                evidence_kind: VerusEvidenceKind::ProofObligation,
                owner_issue: "TBD".to_string(),
                reason: "Pending classification from upstream Verus corpus manifest generation."
                    .to_string(),
                trust_vc_paths: Vec::new(),
                trust_vc_source_hashes: Vec::new(),
                trust_vc_check_args: Vec::new(),
                expected_cases: Vec::new(),
                known_gaps: Vec::new(),
                notes: String::new(),
            });
        }
    }

    let upstream_repo = template
        .as_ref()
        .and_then(|manifest| manifest.upstream_repo.clone())
        .unwrap_or_else(|| "https://github.com/verus-lang/verus".to_string());
    let schema_version = template
        .as_ref()
        .map(|manifest| manifest.schema_version)
        .unwrap_or(1);
    let manifest = GeneratedVerusManifest {
        schema_version,
        manifest_id: "upstream-verus-corpus".to_string(),
        description: "Evidence manifest for upstream Verus tests used by TrustVc parity gates."
            .to_string(),
        upstream: GeneratedUpstream {
            repo: upstream_repo,
            upstream_ref,
            test_roots: required_roots,
        },
        gate: GeneratedGate {
            missing_entry: "fail".to_string(),
            failing_classifications: vec![
                "unclassified".to_string(),
                "unsupported-gap".to_string(),
            ],
        },
        entries,
    };
    if let Some(parent) = args.canonical_manifest_path.parent() {
        fs::create_dir_all(parent).map_err(|err| {
            EvidenceError::new(format!(
                "failed to create manifest dir `{}`: {err}",
                parent.display()
            ))
        })?;
    }
    let json = serde_json::to_string_pretty(&manifest).map_err(|err| {
        EvidenceError::new(format!("failed to serialize Verus tests manifest: {err}"))
    })?;
    fs::write(&args.canonical_manifest_path, format!("{json}\n")).map_err(|err| {
        EvidenceError::new(format!(
            "failed to write Verus tests manifest `{}`: {err}",
            args.canonical_manifest_path.display()
        ))
    })
}

fn duplicate_manifest_paths(entries: &[VerusManifestEntry]) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut duplicates = BTreeSet::new();
    for entry in entries {
        if !seen.insert(entry.upstream_path.clone()) {
            duplicates.insert(entry.upstream_path.clone());
        }
    }
    duplicates.into_iter().collect()
}

fn load_manifest(path: &Path) -> Result<VerusManifest, EvidenceError> {
    let text = fs::read_to_string(path).map_err(|err| {
        EvidenceError::new(format!(
            "failed to read manifest `{}`: {err}",
            path.display()
        ))
    })?;
    if path.extension().and_then(|ext| ext.to_str()) == Some("json") {
        let parsed: JsonVerusManifest = serde_json::from_str(&text).map_err(|err| {
            EvidenceError::new(format!(
                "failed to parse JSON manifest `{}`: {err}",
                path.display()
            ))
        })?;
        validate_json_manifest_schema(&parsed)?;
        return Ok(VerusManifest {
            schema_version: parsed.schema_version,
            upstream_repo: Some(parsed.upstream.repo),
            upstream_ref: Some(parsed.upstream.upstream_ref),
            test_roots: parsed.upstream.test_roots,
            failing_classifications: parsed.gate.failing_classifications.into_iter().collect(),
            entries: parsed.entries,
        });
    }
    parse_seed_yaml_manifest(&text)
}

fn validate_json_manifest_schema(manifest: &JsonVerusManifest) -> Result<(), EvidenceError> {
    if !matches!(manifest.schema_version, 1 | 2) {
        return Err(EvidenceError::new(format!(
            "manifest schema_version must be 1 or 2, got {}",
            manifest.schema_version
        )));
    }
    if !valid_manifest_id(&manifest.manifest_id) {
        return Err(EvidenceError::new(format!(
            "manifest_id must match ^[a-z][a-z0-9-]*$, got `{}`",
            manifest.manifest_id
        )));
    }
    if manifest.description.trim().is_empty() {
        return Err(EvidenceError::new("manifest description must be non-empty"));
    }
    if manifest.gate.missing_entry != "fail" {
        return Err(EvidenceError::new(format!(
            "manifest gate.missing_entry must be `fail`, got `{}`",
            manifest.gate.missing_entry
        )));
    }
    for entry in &manifest.entries {
        if !valid_owner_issue(&entry.owner_issue) {
            return Err(EvidenceError::new(format!(
                "{}: owner_issue must be a GitHub issue URL, owner/repo#number, #number, or TBD: `{}`",
                entry.upstream_path, entry.owner_issue
            )));
        }
    }
    Ok(())
}

fn valid_manifest_id(value: &str) -> bool {
    let mut chars = value.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    first.is_ascii_lowercase()
        && chars.all(|ch| ch.is_ascii_lowercase() || ch.is_ascii_digit() || ch == '-')
}

fn valid_owner_issue(value: &str) -> bool {
    value == "TBD"
        || valid_local_issue(value)
        || valid_repo_issue(value)
        || valid_github_issue_url(value)
}

fn valid_local_issue(value: &str) -> bool {
    value
        .strip_prefix('#')
        .is_some_and(|issue| !issue.is_empty() && issue.chars().all(|ch| ch.is_ascii_digit()))
}

fn valid_repo_issue(value: &str) -> bool {
    let Some((repo, issue)) = value.split_once('#') else {
        return false;
    };
    if issue.is_empty() || !issue.chars().all(|ch| ch.is_ascii_digit()) {
        return false;
    }
    let Some((owner, name)) = repo.split_once('/') else {
        return false;
    };
    !owner.is_empty()
        && !name.is_empty()
        && !name.contains('/')
        && owner.chars().all(valid_issue_repo_char)
        && name.chars().all(valid_issue_repo_char)
}

fn valid_github_issue_url(value: &str) -> bool {
    let Some(rest) = value.strip_prefix("https://github.com/") else {
        return false;
    };
    let parts = rest.split('/').collect::<Vec<_>>();
    matches!(parts.as_slice(), [owner, repo, "issues", issue]
        if !owner.is_empty()
            && !repo.is_empty()
            && owner.chars().all(valid_issue_repo_char)
            && repo.chars().all(valid_issue_repo_char)
            && !issue.is_empty()
            && issue.chars().all(|ch| ch.is_ascii_digit()))
}

fn owner_issue_url(value: &str) -> Option<String> {
    if valid_github_issue_url(value) {
        return Some(value.to_string());
    }
    if let Some(issue) = value.strip_prefix('#') {
        if !issue.is_empty() && issue.chars().all(|ch| ch.is_ascii_digit()) {
            return Some(format!("{TRUST_VC_REPO_URL}/issues/{issue}"));
        }
    }
    if let Some((repo, issue)) = value.split_once('#') {
        if valid_repo_issue(value) {
            return Some(format!("https://github.com/{repo}/issues/{issue}"));
        }
    }
    None
}

fn valid_issue_repo_char(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || matches!(ch, '_' | '.' | '-')
}

fn parse_seed_yaml_manifest(text: &str) -> Result<VerusManifest, EvidenceError> {
    let mut upstream_repo = None;
    let mut upstream_ref = None;
    let mut test_roots = Vec::new();
    let mut failing_classifications = BTreeSet::new();
    let mut entries = Vec::new();
    let mut section = "";
    let mut pending_entry: Option<VerusManifestEntry> = None;
    let mut entry_list_field = "";

    for raw_line in text.lines() {
        let line = raw_line.trim_end();
        let trimmed = line.trim();
        let indent = line.len().saturating_sub(line.trim_start().len());
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        match trimmed {
            "upstream:" => {
                section = "upstream";
                continue;
            }
            "gate:" => {
                section = "gate";
                continue;
            }
            "entries:" => {
                section = "entries";
                continue;
            }
            "test_roots:" => {
                section = "test_roots";
                continue;
            }
            "failing_classifications:" => {
                section = "failing_classifications";
                continue;
            }
            "trust_vc_paths:" => {
                entry_list_field = "trust_vc_paths";
                continue;
            }
            "known_gaps:" => {
                entry_list_field = "known_gaps";
                continue;
            }
            _ => {}
        }

        if trimmed.starts_with("- ") && section == "test_roots" {
            test_roots.push(unquote(trimmed.trim_start_matches("- ").trim()));
            continue;
        }
        if trimmed.starts_with("- ") && section == "failing_classifications" {
            failing_classifications.insert(unquote(trimmed.trim_start_matches("- ").trim()));
            continue;
        }
        if trimmed.starts_with("- ") && !entry_list_field.is_empty() && indent > 2 {
            if let Some(entry) = pending_entry.as_mut() {
                let value = unquote(trimmed.trim_start_matches("- ").trim());
                if entry_list_field == "trust_vc_paths" {
                    entry.trust_vc_paths.push(value);
                } else if entry_list_field == "known_gaps" {
                    entry.known_gaps.push(value);
                }
            }
            continue;
        }
        if trimmed.starts_with("- ") && section == "entries" {
            if let Some(entry) = pending_entry.take() {
                entries.push(entry);
            }
            entry_list_field = "";
            let mut entry = VerusManifestEntry {
                upstream_path: String::new(),
                classification: String::new(),
                evidence_kind: VerusEvidenceKind::ProofObligation,
                owner_issue: String::new(),
                reason: String::new(),
                trust_vc_paths: Vec::new(),
                trust_vc_source_hashes: Vec::new(),
                trust_vc_check_args: Vec::new(),
                expected_cases: Vec::new(),
                known_gaps: Vec::new(),
                notes: String::new(),
            };
            let rest = trimmed.trim_start_matches("- ").trim();
            if let Some((key, value)) = rest.split_once(':') {
                set_entry_field(&mut entry, key.trim(), value.trim());
            }
            pending_entry = Some(entry);
            continue;
        }
        if let Some((key, value)) = trimmed.split_once(':') {
            let key = key.trim();
            let value = value.trim();
            match section {
                "upstream" => match key {
                    "repo" => upstream_repo = Some(unquote(value)),
                    "ref" => upstream_ref = Some(unquote(value)),
                    _ => {}
                },
                "entries" => {
                    if let Some(entry) = pending_entry.as_mut() {
                        set_entry_field(entry, key, value);
                    }
                }
                _ => {}
            }
        }
    }
    if let Some(entry) = pending_entry.take() {
        entries.push(entry);
    }
    if test_roots.is_empty() {
        return Err(EvidenceError::new(
            "manifest does not declare upstream.test_roots",
        ));
    }
    Ok(VerusManifest {
        schema_version: 1,
        upstream_repo,
        upstream_ref,
        test_roots,
        failing_classifications,
        entries,
    })
}

fn set_entry_field(entry: &mut VerusManifestEntry, key: &str, value: &str) {
    match key {
        "upstream_path" => entry.upstream_path = unquote(value),
        "classification" => entry.classification = unquote(value),
        "evidence_kind" => {
            entry.evidence_kind = match unquote(value).as_str() {
                "cargo_trust_vc_integration_test" => VerusEvidenceKind::CargoTrustVcIntegrationTest,
                _ => VerusEvidenceKind::ProofObligation,
            };
        }
        "owner_issue" => entry.owner_issue = unquote(value),
        "reason" => entry.reason = unquote(value),
        _ => {}
    }
}

fn is_allowed_classification(value: &str) -> bool {
    matches!(
        value,
        "unclassified" | "unchanged" | "ported" | "unsupported-gap" | "not-applicable"
    )
}

fn requires_trust_vc_paths(classification: &str) -> bool {
    matches!(classification, "ported" | "unchanged")
}

fn verus_replacement_summary(entries: &[VerusManifestEntry]) -> VerusReplacementSummary {
    let mut summary = VerusReplacementSummary {
        total_entries: entries.len(),
        ..VerusReplacementSummary::default()
    };
    for entry in entries {
        if requires_trust_vc_paths(&entry.classification) {
            summary.accepted_executable_entries += 1;
            summary.accepted_trust_vc_path_count += entry.trust_vc_paths.len();
            summary.accepted_expected_case_count += entry.expected_cases.len();
            if !entry.known_gaps.is_empty() {
                summary.accepted_known_gap_entries += 1;
            }
            if entry.trust_vc_paths.is_empty() {
                summary.accepted_entries_missing_trust_vc_paths += 1;
            }
            if entry.expected_cases.is_empty() {
                summary.accepted_entries_missing_expected_cases += 1;
            }
        }
        match entry.classification.as_str() {
            "unsupported-gap" => summary.unsupported_gap_entries += 1,
            "unclassified" => summary.unclassified_entries += 1,
            "not-applicable" => summary.not_applicable_entries += 1,
            _ => {}
        }
    }
    summary
}

fn not_applicable_scope_allowed(verus_path: Option<&Path>, upstream_path: &str) -> bool {
    if matches!(
        upstream_path,
        "source/rust_verify_test/tests/common/mod.rs"
            | "source/cargo-verus/tests/src/fake_cargo.rs"
            | "source/cargo-verus/tests/src/utils.rs"
    ) {
        return true;
    }
    upstream_file_has_only_ignored_harness_cases(verus_path, upstream_path)
}

fn upstream_file_has_only_ignored_harness_cases(
    verus_path: Option<&Path>,
    upstream_path: &str,
) -> bool {
    let Ok(Some(cases)) = upstream_verus_harness_cases(verus_path, upstream_path) else {
        return false;
    };
    !cases.is_empty() && cases.iter().all(|case| case.ignored)
}

fn corpus_triage_entry(entry: &VerusManifestEntry, path_bucket: &str) -> CorpusTriageEntry {
    CorpusTriageEntry {
        upstream_path: entry.upstream_path.clone(),
        classification: entry.classification.clone(),
        path_bucket: path_bucket.to_string(),
        owner_issue: entry.owner_issue.clone(),
        reason: entry.reason.clone(),
    }
}

fn upstream_path_bucket(upstream_path: &str, test_roots: &[String]) -> String {
    let upstream_path = upstream_path.trim_matches('/');
    for root in test_roots {
        let root = root.trim_matches('/');
        if upstream_path == root {
            return "root".to_string();
        }
        let Some(rest) = upstream_path
            .strip_prefix(root)
            .and_then(|rest| rest.strip_prefix('/'))
        else {
            continue;
        };
        if let Some((bucket, _)) = rest.split_once('/') {
            return if bucket.is_empty() {
                "root".to_string()
            } else {
                bucket.to_string()
            };
        }
        return "root".to_string();
    }
    "outside-roots".to_string()
}

fn enumerate_upstream_tests_from_git_ref(
    verus_path: Option<&Path>,
    upstream_ref: Option<&str>,
    roots: &[String],
) -> Result<Vec<String>, String> {
    let verus_path = verus_path
        .ok_or_else(|| "a Verus checkout is required to enumerate the pinned corpus".to_string())?;
    let upstream_ref = upstream_ref
        .map(str::trim)
        .filter(|reference| !reference.is_empty())
        .ok_or_else(|| {
            "manifest upstream.ref is required to enumerate the pinned corpus".to_string()
        })?;
    if roots.is_empty() {
        return Err("manifest upstream.test_roots must not be empty".to_string());
    }

    let mut tests = BTreeSet::new();
    for root in roots {
        let root = root.trim_matches('/');
        if root.is_empty() {
            return Err("manifest upstream.test_roots must not contain an empty root".to_string());
        }
        let output = git_stdout_bytes(
            verus_path,
            &["ls-tree", "-r", "-z", upstream_ref, "--", root],
        )?;
        for raw_entry in output.split(|byte| *byte == 0) {
            if raw_entry.is_empty() {
                continue;
            }
            let entry = std::str::from_utf8(raw_entry).map_err(|err| {
                format!("git ls-tree emitted non-UTF-8 path under `{root}`: {err}")
            })?;
            let (metadata, path) = entry
                .split_once('\t')
                .ok_or_else(|| format!("could not parse git ls-tree entry `{entry}`"))?;
            let mut metadata_parts = metadata.split_whitespace();
            let mode = metadata_parts.next().unwrap_or("");
            let kind = metadata_parts.next().unwrap_or("");
            if mode == "120000" {
                return Err(format!(
                    "upstream inventory rejects git symlink `{path}` at `{upstream_ref}`"
                ));
            }
            if kind != "blob" {
                return Err(format!(
                    "upstream inventory expected git blob under `{root}`, got `{kind}` for `{path}` at `{upstream_ref}`"
                ));
            }
            if path.ends_with(".rs") {
                tests.insert(path.replace('\\', "/"));
            }
        }
    }
    Ok(tests.into_iter().collect())
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct UpstreamVerusHarnessCase {
    case_id: String,
    expected_verdict: VerusExpectedVerdict,
    ignored: bool,
    rust_error: bool,
    error_patterns: Vec<String>,
    forbidden_diagnostic_patterns: Vec<String>,
    expected_occurrences: usize,
    /// Verifier-warning messages the upstream harness CONTENT-CHECKS, i.e. the
    /// string literals passed to `.contains(..)` inside an `Ok(err) => { .. }`
    /// arm that reads `err.warnings`. A manifest entry mapped to such a case
    /// must declare each of them, so an upstream warning assertion can never be
    /// silently dropped by a port.
    warning_patterns: Vec<String>,
}

fn upstream_verus_harness_cases(
    verus_path: Option<&Path>,
    upstream_path: &str,
) -> Result<Option<Vec<UpstreamVerusHarnessCase>>, String> {
    let Some(verus_path) = verus_path else {
        return Ok(None);
    };
    if upstream_case_extraction_bypassed(upstream_path) {
        return upstream_cargo_fixture_cases(verus_path, upstream_path).map(Some);
    }
    if upstream_path.starts_with(&format!("{VERUS_CARGO_VERUS_TEST_ROOT}/")) {
        return upstream_cargo_verus_integration_test_cases(verus_path, upstream_path).map(Some);
    }
    let source_path = verus_path.join(upstream_path);
    let source = fs::read_to_string(&source_path).map_err(|err| {
        format!(
            "failed to read upstream Verus test source `{}`: {err}",
            source_path.display()
        )
    })?;
    let ast = syn::parse_file(&source).map_err(|err| {
        format!(
            "failed to parse upstream Verus test source `{}`: {err}",
            source_path.display()
        )
    })?;
    let unknown_macros = unknown_harness_item_macros(&ast.items, upstream_path);
    if !unknown_macros.is_empty() {
        return Err(format!(
            "upstream Verus test source `{}` contains unexpanded item macro invocation(s) that this evidence extractor cannot enumerate soundly: {}",
            source_path.display(),
            unknown_macros.join(", ")
        ));
    }
    let mut cases = Vec::new();
    let mut case_errors = Vec::new();
    collect_cargo_wrapper_harness_cases(
        verus_path,
        upstream_path,
        &ast.items,
        &mut cases,
        &mut case_errors,
    );
    collect_verus_harness_cases(&ast.items, &mut cases, &mut case_errors);
    if !case_errors.is_empty() {
        return Err(format!(
            "upstream Verus test source `{}` contains harness case(s) this evidence extractor cannot enumerate soundly: {}",
            source_path.display(),
            case_errors.join("; ")
        ));
    }
    let duplicate_case_ids = duplicate_upstream_case_ids(&cases);
    if !duplicate_case_ids.is_empty() {
        return Err(format!(
            "upstream Verus test source `{}` contains duplicate harness case id(s) this evidence extractor cannot map unambiguously: {}",
            source_path.display(),
            duplicate_case_ids.join(", ")
        ));
    }
    cases.sort_by(|left, right| {
        left.case_id.cmp(&right.case_id).then_with(|| {
            expected_verdict_label(left.expected_verdict)
                .cmp(expected_verdict_label(right.expected_verdict))
        })
    });
    Ok(Some(cases))
}

#[derive(Debug, Clone)]
struct RustIntegrationTestCase {
    ignored: bool,
}

fn upstream_cargo_verus_integration_test_cases(
    verus_path: &Path,
    upstream_path: &str,
) -> Result<Vec<UpstreamVerusHarnessCase>, String> {
    let source_path = verus_path.join(upstream_path);
    let cases = rust_integration_test_cases_from_file(&source_path)?;
    Ok(cases
        .into_iter()
        .map(|(case_id, case)| UpstreamVerusHarnessCase {
            case_id,
            expected_verdict: VerusExpectedVerdict::Verified,
            ignored: case.ignored,
            rust_error: false,
            error_patterns: Vec::new(),
            forbidden_diagnostic_patterns: Vec::new(),
            expected_occurrences: 1,
            warning_patterns: Vec::new(),
        })
        .collect())
}

fn rust_integration_test_cases_from_file(
    source_path: &Path,
) -> Result<BTreeMap<String, RustIntegrationTestCase>, String> {
    let source = fs::read_to_string(source_path).map_err(|err| {
        format!(
            "failed to read Rust integration test source `{}`: {err}",
            source_path.display()
        )
    })?;
    let ast = syn::parse_file(&source).map_err(|err| {
        format!(
            "failed to parse Rust integration test source `{}`: {err}",
            source_path.display()
        )
    })?;
    let mut cases = BTreeMap::new();
    let mut errors = Vec::new();
    collect_rust_integration_test_cases(&ast.items, "", &mut cases, &mut errors);
    if !errors.is_empty() {
        return Err(format!(
            "Rust integration test source `{}` contains case(s) this evidence extractor cannot enumerate soundly: {}",
            source_path.display(),
            errors.join("; ")
        ));
    }
    Ok(cases)
}

fn collect_rust_integration_test_cases(
    items: &[syn::Item],
    module_path: &str,
    cases: &mut BTreeMap<String, RustIntegrationTestCase>,
    errors: &mut Vec<String>,
) {
    for item in items {
        match item {
            syn::Item::Fn(func) if item_has_attr(&func.attrs, "test") => {
                let ident = func.sig.ident.to_string();
                let case_id = if module_path.is_empty() {
                    ident
                } else {
                    format!("{module_path}::{ident}")
                };
                if cases
                    .insert(
                        case_id.clone(),
                        RustIntegrationTestCase {
                            ignored: item_has_attr(&func.attrs, "ignore"),
                        },
                    )
                    .is_some()
                {
                    errors.push(format!("duplicate #[test] function `{case_id}`"));
                }
            }
            syn::Item::Macro(item_macro) => {
                let name = item_macro
                    .mac
                    .path
                    .segments
                    .last()
                    .map(|segment| segment.ident.to_string())
                    .unwrap_or_else(|| "<unknown>".to_string());
                errors.push(format!("unexpanded item macro invocation `{name}`"));
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    let module_name = module.ident.to_string();
                    let nested = if module_path.is_empty() {
                        module_name
                    } else {
                        format!("{module_path}::{module_name}")
                    };
                    collect_rust_integration_test_cases(inner_items, &nested, cases, errors);
                }
            }
            _ => {}
        }
    }
}

fn upstream_case_extraction_bypassed(upstream_path: &str) -> bool {
    upstream_path.contains("/cargo-tests/")
}

fn upstream_cargo_fixture_cases(
    verus_path: &Path,
    upstream_path: &str,
) -> Result<Vec<UpstreamVerusHarnessCase>, String> {
    let Some((fixture_root, source_rel)) = upstream_cargo_fixture_parts(upstream_path) else {
        return Ok(Vec::new());
    };
    let source_path = verus_path.join(upstream_path);
    if !source_path.is_file() {
        return Err(format!(
            "failed to read upstream cargo fixture source `{}`",
            source_path.display()
        ));
    }
    let cargo_toml = verus_path.join(&fixture_root).join("Cargo.toml");
    if !cargo_toml.is_file() {
        return Ok(Vec::new());
    }
    let Some(case_id) = cargo_fixture_case_id(&source_rel) else {
        return Ok(Vec::new());
    };
    Ok(vec![UpstreamVerusHarnessCase {
        case_id,
        expected_verdict: VerusExpectedVerdict::Verified,
        ignored: false,
        rust_error: false,
        error_patterns: Vec::new(),
        forbidden_diagnostic_patterns: Vec::new(),
        expected_occurrences: 1,
        warning_patterns: Vec::new(),
    }])
}

fn upstream_cargo_fixture_parts(upstream_path: &str) -> Option<(String, String)> {
    let (fixture_root, source_rel) = upstream_path.split_once("/src/")?;
    if !fixture_root.contains("/cargo-tests/") {
        return None;
    }
    Some((fixture_root.to_string(), format!("src/{source_rel}")))
}

fn cargo_fixture_case_id(source_rel: &str) -> Option<String> {
    let path = Path::new(source_rel);
    if path.extension()? != std::ffi::OsStr::new("rs") {
        return None;
    }
    let stem = path.file_stem()?.to_string_lossy();
    if valid_expected_case_id(&stem) {
        Some(stem.into_owned())
    } else {
        None
    }
}

#[derive(Debug, Clone, Default)]
struct CargoFixtureManifestShape {
    package_name: Option<String>,
    dependencies: BTreeSet<String>,
}

fn append_cargo_fixture_inventory_failures(
    entry: &VerusManifestEntry,
    crate_root: &Path,
    verus_path: &Path,
    failures: &mut Vec<String>,
) {
    let Some((upstream_fixture_root, source_rel)) =
        upstream_cargo_fixture_parts(&entry.upstream_path)
    else {
        return;
    };
    let upstream_root = verus_path.join(&upstream_fixture_root);
    let upstream_source = verus_path.join(&entry.upstream_path);
    let upstream_cargo_toml = upstream_root.join("Cargo.toml");
    if !upstream_source.is_file() || !upstream_cargo_toml.is_file() {
        return;
    }
    let Some(expected_case_id) = cargo_fixture_case_id(&source_rel) else {
        failures.push(format!(
            "{}: cargo fixture source path does not produce a concrete case id",
            entry.upstream_path
        ));
        return;
    };
    let expected_ids = entry
        .expected_cases
        .iter()
        .map(upstream_case_id)
        .collect::<BTreeSet<_>>();
    if !expected_ids.contains(expected_case_id.as_str()) {
        failures.push(format!(
            "{}: cargo fixture expected_cases must include upstream source case `{}`",
            entry.upstream_path, expected_case_id
        ));
    }

    let upstream_manifest = match read_cargo_fixture_manifest_shape(&upstream_cargo_toml) {
        Ok(manifest) => manifest,
        Err(error) => {
            failures.push(format!("{}: {error}", entry.upstream_path));
            return;
        }
    };
    let upstream_package = upstream_manifest.package_name.as_deref().unwrap_or("");
    let upstream_dependencies = upstream_manifest
        .dependencies
        .iter()
        .filter(|name| name.as_str() != "vstd")
        .collect::<BTreeSet<_>>();

    for trust_vc_path in &entry.trust_vc_paths {
        let trust_vc_root = match validate_repo_trust_vc_path(crate_root, trust_vc_path) {
            Ok(path) => path,
            Err(_) => continue,
        };
        if !is_cargo_fixture_root(&trust_vc_root) {
            failures.push(format!(
                "{}: accepted cargo-tests entry must use a cargo fixture root trust_vc_path, got `{}`",
                entry.upstream_path, trust_vc_path
            ));
            continue;
        }
        let trust_vc_source = trust_vc_root.join(&source_rel);
        if !trust_vc_source.is_file() {
            failures.push(format!(
                "{}: cargo fixture trust_vc_path `{}` must contain `{}` to mirror the upstream target",
                entry.upstream_path, trust_vc_path, source_rel
            ));
        }
        let trust_vc_manifest =
            match read_cargo_fixture_manifest_shape(&trust_vc_root.join("Cargo.toml")) {
                Ok(manifest) => manifest,
                Err(error) => {
                    failures.push(format!("{}: {error}", entry.upstream_path));
                    continue;
                }
            };
        let trust_vc_package = trust_vc_manifest.package_name.as_deref().unwrap_or("");
        let source_is_bin = source_rel == "src/main.rs";
        let upstream_has_lib = upstream_root.join("src/lib.rs").is_file();
        let trust_vc_keeps_same_package = trust_vc_package == upstream_package;
        let trust_vc_depends_on_upstream_package = !upstream_package.is_empty()
            && trust_vc_manifest.dependencies.contains(upstream_package);
        if !(trust_vc_keeps_same_package
            || source_is_bin && upstream_has_lib && trust_vc_depends_on_upstream_package)
        {
            failures.push(format!(
                "{}: cargo fixture trust_vc_path `{}` package name `{}` does not match upstream package `{}` or depend on that paired library package",
                entry.upstream_path, trust_vc_path, trust_vc_package, upstream_package
            ));
        }
        for dependency in &upstream_dependencies {
            if !trust_vc_manifest.dependencies.contains(dependency.as_str()) {
                failures.push(format!(
                    "{}: cargo fixture trust_vc_path `{}` is missing upstream dependency `{}`",
                    entry.upstream_path, trust_vc_path, dependency
                ));
            }
        }
    }
}

fn read_cargo_fixture_manifest_shape(
    cargo_toml: &Path,
) -> Result<CargoFixtureManifestShape, String> {
    let source = fs::read_to_string(cargo_toml).map_err(|err| {
        format!(
            "failed to read cargo fixture manifest `{}`: {err}",
            cargo_toml.display()
        )
    })?;
    let mut shape = CargoFixtureManifestShape::default();
    let mut section = String::new();
    for line in source.lines() {
        let trimmed = strip_cargo_toml_comment(line).trim();
        if trimmed.is_empty() {
            continue;
        }
        if trimmed.starts_with('[') && trimmed.ends_with(']') {
            section = trimmed
                .trim_start_matches('[')
                .trim_end_matches(']')
                .trim()
                .to_string();
            continue;
        }
        match section.as_str() {
            "package" => {
                if let Some(value) = parse_cargo_toml_string_key(trimmed, "name") {
                    shape.package_name = Some(value);
                }
            }
            "dependencies" => {
                if let Some((name, _value)) = trimmed.split_once('=') {
                    let dependency = name.trim().trim_matches('"').trim_matches('\'');
                    if !dependency.is_empty() {
                        shape.dependencies.insert(dependency.to_string());
                    }
                }
            }
            _ => {}
        }
    }
    if shape.package_name.is_none() {
        return Err(format!(
            "cargo fixture manifest `{}` has no [package].name",
            cargo_toml.display()
        ));
    }
    Ok(shape)
}

fn strip_cargo_toml_comment(line: &str) -> &str {
    line.split_once('#')
        .map(|(prefix, _)| prefix)
        .unwrap_or(line)
}

fn parse_cargo_toml_string_key(line: &str, key: &str) -> Option<String> {
    let (actual_key, value) = line.split_once('=')?;
    if actual_key.trim() != key {
        return None;
    }
    let value = value.trim();
    if value.len() < 2 {
        return None;
    }
    if (value.starts_with('"') && value.ends_with('"'))
        || (value.starts_with('\'') && value.ends_with('\''))
    {
        Some(value[1..value.len() - 1].to_string())
    } else {
        None
    }
}

fn unknown_harness_item_macros(items: &[syn::Item], upstream_path: &str) -> Vec<String> {
    let mut macros = Vec::new();
    collect_unknown_harness_item_macros(items, upstream_path, &mut macros);
    macros.sort();
    macros.dedup();
    macros
}

fn collect_unknown_harness_item_macros(
    items: &[syn::Item],
    upstream_path: &str,
    out: &mut Vec<String>,
) {
    for item in items {
        match item {
            syn::Item::Macro(item_macro) => {
                let name = item_macro
                    .mac
                    .path
                    .segments
                    .last()
                    .map(|segment| segment.ident.to_string())
                    .unwrap_or_else(|| "<unknown>".to_string());
                if !name.starts_with("test_verify_one_file")
                    && !known_enumerated_harness_item_macro(upstream_path, &name)
                {
                    out.push(name);
                }
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    collect_unknown_harness_item_macros(inner_items, upstream_path, out);
                }
            }
            _ => {}
        }
    }
}

fn known_enumerated_harness_item_macro(upstream_path: &str, name: &str) -> bool {
    upstream_path == VERUS_CARGO_WRAPPER_TEST_PATH && name == "cargo_examples"
}

fn collect_cargo_wrapper_harness_cases(
    verus_path: &Path,
    upstream_path: &str,
    items: &[syn::Item],
    out: &mut Vec<UpstreamVerusHarnessCase>,
    errors: &mut Vec<String>,
) {
    if upstream_path != VERUS_CARGO_WRAPPER_TEST_PATH {
        return;
    }
    for item in items {
        match item {
            syn::Item::Fn(func) => match cargo_wrapper_explicit_harness_case(func) {
                Ok(Some(case)) => out.push(case),
                Ok(None) => {}
                Err(error) => errors.push(error),
            },
            syn::Item::Macro(item_macro)
                if item_macro
                    .mac
                    .path
                    .segments
                    .last()
                    .is_some_and(|segment| segment.ident == "cargo_examples") =>
            {
                match cargo_examples_harness_cases(verus_path, item_macro.mac.tokens.clone()) {
                    Ok(mut cases) => out.append(&mut cases),
                    Err(error) => errors.push(error),
                }
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    collect_cargo_wrapper_harness_cases(
                        verus_path,
                        upstream_path,
                        inner_items,
                        out,
                        errors,
                    );
                }
            }
            _ => {}
        }
    }
}

fn cargo_wrapper_explicit_harness_case(
    func: &syn::ItemFn,
) -> Result<Option<UpstreamVerusHarnessCase>, String> {
    if !item_has_attr(&func.attrs, "test") {
        return Ok(None);
    }
    let body = compact_tokens(&func.block);
    if body.contains("verify_one_file") {
        return Ok(None);
    }
    if !body.contains("run_cargo_verus") || !body.contains(".status.success()") {
        return Err(format!(
            "cargo wrapper #[test] `{}` does not match the supported cargo command success-harness shape",
            func.sig.ident
        ));
    }
    Ok(Some(UpstreamVerusHarnessCase {
        case_id: func.sig.ident.to_string(),
        expected_verdict: VerusExpectedVerdict::Verified,
        ignored: item_has_attr(&func.attrs, "ignore"),
        rust_error: false,
        error_patterns: Vec::new(),
        forbidden_diagnostic_patterns: Vec::new(),
        expected_occurrences: 1,
        warning_patterns: Vec::new(),
    }))
}

fn cargo_examples_harness_cases(
    verus_path: &Path,
    tokens: TokenStream,
) -> Result<Vec<UpstreamVerusHarnessCase>, String> {
    let verified = syn::parse2::<syn::LitBool>(tokens)
        .map_err(|err| format!("cargo_examples! argument must be a boolean literal: {err}"))?
        .value;
    let group = if verified { "verified" } else { "unverified" };
    let fixtures_dir = verus_path
        .join(VERUS_TEST_ROOT)
        .join("cargo-tests")
        .join(group);
    let entries = fs::read_dir(&fixtures_dir).map_err(|err| {
        format!(
            "failed to enumerate upstream cargo_examples! fixture directory `{}`: {err}",
            fixtures_dir.display()
        )
    })?;
    let mut fixture_paths = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|err| {
            format!(
                "failed to read upstream cargo_examples! fixture entry in `{}`: {err}",
                fixtures_dir.display()
            )
        })?;
        fixture_paths.push(entry.path());
    }
    fixture_paths.sort();

    let mut cases = Vec::new();
    for fixture_path in fixture_paths {
        if !fixture_path.is_dir() {
            return Err(format!(
                "cargo_examples! fixture inventory contains non-directory entry `{}`",
                fixture_path.display()
            ));
        }
        if !fixture_path.join("Cargo.toml").is_file() {
            return Err(format!(
                "cargo_examples! fixture directory `{}` has no Cargo.toml",
                fixture_path.display()
            ));
        }
        let case_id = cargo_examples_case_id(group, &fixture_path)?;
        cases.push(UpstreamVerusHarnessCase {
            case_id,
            expected_verdict: VerusExpectedVerdict::Verified,
            ignored: false,
            rust_error: false,
            error_patterns: Vec::new(),
            forbidden_diagnostic_patterns: Vec::new(),
            expected_occurrences: 1,
            warning_patterns: Vec::new(),
        });
    }
    Ok(cases)
}

fn cargo_examples_case_id(group: &str, fixture_path: &Path) -> Result<String, String> {
    let name = fixture_path
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| {
            format!(
                "cargo_examples! fixture path `{}` has no UTF-8 file name",
                fixture_path.display()
            )
        })?;
    if name.contains('.') {
        return Err(format!(
            "cargo_examples! fixture path `{}` contains `.` and cannot be mirrored soundly",
            fixture_path.display()
        ));
    }
    let case_id = format!("{}_{}", group, name.replace('-', "_"));
    if !valid_expected_case_id(&case_id) {
        return Err(format!(
            "cargo_examples! fixture path `{}` produces invalid Rust test case id `{}`",
            fixture_path.display(),
            case_id
        ));
    }
    Ok(case_id)
}

fn collect_verus_harness_cases(
    items: &[syn::Item],
    out: &mut Vec<UpstreamVerusHarnessCase>,
    errors: &mut Vec<String>,
) {
    for item in items {
        match item {
            syn::Item::Fn(func) => match manual_verus_harness_case(func) {
                Ok(Some(case)) => out.push(case),
                Ok(None) => {}
                Err(error) => errors.push(error),
            },
            syn::Item::Macro(item_macro)
                if item_macro.mac.path.segments.last().is_some_and(|segment| {
                    segment
                        .ident
                        .to_string()
                        .starts_with("test_verify_one_file")
                }) =>
            {
                let (cases, macro_errors) =
                    verus_harness_cases_from_tokens(item_macro.mac.tokens.clone());
                out.extend(cases);
                errors.extend(macro_errors);
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    collect_verus_harness_cases(inner_items, out, errors);
                }
            }
            _ => {}
        }
    }
}

struct PendingVerusHarnessCase {
    case_id: String,
    ignored: bool,
    no_cheating: bool,
}

fn verus_harness_cases_from_tokens(
    tokens: TokenStream,
) -> (Vec<UpstreamVerusHarnessCase>, Vec<String>) {
    let tokens = tokens.into_iter().collect::<Vec<_>>();
    let mut cases = Vec::new();
    let mut errors = Vec::new();
    let mut saw_test_attr = false;
    let mut saw_ignore_attr = false;
    let mut pending_case = None;
    let mut index = 0;

    while index < tokens.len() {
        if let TokenTree::Punct(punct) = &tokens[index] {
            if punct.as_char() == '#' {
                if let Some(TokenTree::Group(group)) = tokens.get(index + 1) {
                    if group.delimiter() == Delimiter::Bracket {
                        let attr = group.stream().to_string().replace(' ', "");
                        match attr.as_str() {
                            "test" => saw_test_attr = true,
                            "ignore" => saw_ignore_attr = true,
                            _ => {}
                        }
                        index += 2;
                        continue;
                    }
                }
            }
        }

        if saw_test_attr {
            if let TokenTree::Ident(ident) = &tokens[index] {
                pending_case = Some(PendingVerusHarnessCase {
                    case_id: ident.to_string(),
                    ignored: saw_ignore_attr,
                    no_cheating: false,
                });
                saw_test_attr = false;
                saw_ignore_attr = false;
            }
        }
        if let Some(case) = pending_case.as_mut() {
            if let TokenTree::Group(group) = &tokens[index] {
                if group.delimiter() == Delimiter::Bracket
                    && string_literals_in_tokens(group.stream())
                        .iter()
                        .any(|option| option == "--no-cheating")
                {
                    case.no_cheating = true;
                }
            }
            if token_is_fat_arrow(&tokens, index) {
                match harness_verdict_after_arrow(&tokens, index + 2) {
                    Ok(Some((
                        mut expected_verdict,
                        rust_error,
                        error_patterns,
                        forbidden_diagnostic_patterns,
                        expected_occurrences,
                        warning_patterns,
                    ))) => {
                        if case.no_cheating
                            && expected_verdict == VerusExpectedVerdict::Counterexample
                        {
                            expected_verdict = VerusExpectedVerdict::Error;
                        }
                        cases.push(UpstreamVerusHarnessCase {
                            case_id: case.case_id.clone(),
                            expected_verdict,
                            ignored: case.ignored,
                            rust_error,
                            error_patterns,
                            forbidden_diagnostic_patterns,
                            expected_occurrences,
                            warning_patterns,
                        });
                        pending_case = None;
                        index += 2;
                        continue;
                    }
                    Ok(None) => {}
                    Err(error) => {
                        errors.push(format!("{}: {error}", case.case_id));
                        pending_case = None;
                        index += 2;
                        continue;
                    }
                }
            }
        }
        index += 1;
    }

    (cases, errors)
}

fn token_is_fat_arrow(tokens: &[TokenTree], index: usize) -> bool {
    matches!(tokens.get(index), Some(TokenTree::Punct(punct)) if punct.as_char() == '=')
        && matches!(tokens.get(index + 1), Some(TokenTree::Punct(punct)) if punct.as_char() == '>')
}

type HarnessVerdict = (
    VerusExpectedVerdict,
    bool,
    Vec<String>,
    Vec<String>,
    usize,
    Vec<String>,
);

fn harness_verdict_after_arrow(
    tokens: &[TokenTree],
    mut index: usize,
) -> Result<Option<HarnessVerdict>, String> {
    while let Some(token) = tokens.get(index) {
        match token {
            TokenTree::Ident(ident) if ident == "Ok" => {
                return Ok(Some((
                    VerusExpectedVerdict::Verified,
                    false,
                    Vec::new(),
                    Vec::new(),
                    1,
                    ok_harness_warning_patterns(tokens, index + 1),
                )));
            }
            TokenTree::Ident(ident) if ident == "Err" => {
                return err_harness_verdict(tokens, index + 1).map(Some);
            }
            TokenTree::Punct(punct) if punct.as_char() == ';' => return Ok(None),
            _ => index += 1,
        }
    }
    Ok(None)
}

/// Extracts the verifier-warning messages an upstream `=> Ok(err) => { .. }`
/// arm CONTENT-CHECKS.
///
/// Upstream `assert_forall_by.rs::test_forallstmt_implies`:
/// ```text
/// } => Ok(err) => {
///     assert!(err.errors.is_empty());
///     let mut warns = err.warnings.iter();
///     assert!(warns.next().expect("one warning").message.contains("using ==> in `assert forall` …"));
///     assert!(warns.next().is_some());
///     assert!(warns.next().is_none());
/// }
/// ```
/// Only literals actually passed to `.contains(..)` are extracted — the bare
/// `warns.next().is_some()` assertion checks no content. (Measured against the
/// pinned Verus build: that second "warning" is rustc's own `1 warning emitted`
/// emitter summary line, not a verifier warning — see the
/// `assert_forall_by.rs` manifest row.)
fn ok_harness_warning_patterns(tokens: &[TokenTree], mut index: usize) -> Vec<String> {
    while let Some(token) = tokens.get(index) {
        match token {
            TokenTree::Group(group) if group.delimiter() == Delimiter::Brace => {
                let body = compact_tokens(group.stream());
                if body.contains(".warnings") {
                    return contains_call_string_literals(group.stream());
                }
            }
            TokenTree::Punct(punct) if punct.as_char() == ';' => break,
            _ => {}
        }
        index += 1;
    }
    Vec::new()
}

/// Collects every string literal that is an argument of a `.contains(..)` call
/// in `tokens`, recursing into groups.
fn contains_call_string_literals(tokens: TokenStream) -> Vec<String> {
    let trees: Vec<TokenTree> = tokens.into_iter().collect();
    let mut patterns = Vec::new();
    for (index, tree) in trees.iter().enumerate() {
        match tree {
            TokenTree::Ident(ident) if ident == "contains" => {
                if let Some(TokenTree::Group(args)) = trees.get(index + 1) {
                    if args.delimiter() == Delimiter::Parenthesis {
                        patterns.extend(
                            string_literals_in_tokens(args.stream())
                                .into_iter()
                                .filter(|pattern| !pattern.trim().is_empty()),
                        );
                    }
                }
            }
            TokenTree::Group(group) => {
                // Do not double-harvest the argument group of a `contains(..)`
                // already handled above.
                let is_contains_args = index
                    .checked_sub(1)
                    .and_then(|prev| trees.get(prev))
                    .is_some_and(|prev| matches!(prev, TokenTree::Ident(id) if id == "contains"));
                if !is_contains_args {
                    patterns.extend(contains_call_string_literals(group.stream()));
                }
            }
            _ => {}
        }
    }
    patterns
}

fn err_harness_forbidden_diagnostic_patterns(
    tokens: &[TokenTree],
    mut index: usize,
) -> Option<Vec<String>> {
    while let Some(token) = tokens.get(index) {
        match token {
            TokenTree::Group(group) if group.delimiter() == Delimiter::Brace => {
                let body = compact_tokens(group.stream());
                if body.contains("assert!(!")
                    && body.contains(".errors")
                    && body.contains(".spans")
                    && body.contains(".contains(")
                {
                    let patterns = string_literals_in_tokens(group.stream())
                        .into_iter()
                        .filter(|pattern| !pattern.trim().is_empty())
                        .collect::<Vec<_>>();
                    if !patterns.is_empty() {
                        return Some(patterns);
                    }
                }
            }
            TokenTree::Punct(punct) if punct.as_char() == ';' => break,
            _ => {}
        }
        index += 1;
    }
    None
}

fn err_harness_verdict(tokens: &[TokenTree], mut index: usize) -> Result<HarnessVerdict, String> {
    if let Some(forbidden_patterns) = err_harness_forbidden_diagnostic_patterns(tokens, index) {
        return Ok((
            VerusExpectedVerdict::Counterexample,
            false,
            Vec::new(),
            forbidden_patterns,
            1,
            Vec::new(),
        ));
    }
    if let Some(error_patterns) = err_harness_direct_error_message_patterns(tokens, index) {
        return Ok((
            VerusExpectedVerdict::Error,
            true,
            error_patterns,
            Vec::new(),
            1,
            Vec::new(),
        ));
    }
    while let Some(token) = tokens.get(index) {
        match token {
            TokenTree::Group(group) if group.delimiter() == Delimiter::Brace => {
                let inner_tokens = group.stream().into_iter().collect::<Vec<_>>();
                match err_harness_verdict(&inner_tokens, 0) {
                    Ok(verdict) => return Ok(verdict),
                    Err(error) if error == "missing Err harness verdict helper" => {}
                    Err(error) => return Err(error),
                }
            }
            TokenTree::Ident(ident) if ident.to_string().starts_with("assert") => {
                let helper = ident.to_string();
                let (expected_verdict, rust_error) = err_helper_verdict(&helper)
                    .ok_or_else(|| format!("unknown Err harness helper `{helper}`"))?;
                let helper_group = tokens.get(index + 1).and_then(|token| match token {
                    TokenTree::Group(group) => Some(group),
                    _ => None,
                });
                let error_patterns = if expected_verdict == VerusExpectedVerdict::Error {
                    helper_group
                        .map(|group| string_literals_in_tokens(group.stream()))
                        .unwrap_or_default()
                } else {
                    Vec::new()
                };
                let expected_occurrences = err_helper_expected_occurrences(&helper, helper_group);
                return Ok((
                    expected_verdict,
                    rust_error,
                    error_patterns,
                    Vec::new(),
                    expected_occurrences,
                    Vec::new(),
                ));
            }
            TokenTree::Punct(punct) if punct.as_char() == ';' => break,
            _ => index += 1,
        }
    }
    Err("missing Err harness verdict helper".to_string())
}

fn err_harness_direct_error_message_patterns(
    tokens: &[TokenTree],
    mut index: usize,
) -> Option<Vec<String>> {
    while let Some(token) = tokens.get(index) {
        match token {
            TokenTree::Group(group) if group.delimiter() == Delimiter::Brace => {
                let body = compact_tokens(group.stream());
                if body.contains("err.errors")
                    && body.contains(".message==")
                    && body.contains(".is_some()")
                {
                    let patterns = string_literals_in_tokens(group.stream())
                        .into_iter()
                        .filter(|pattern| !pattern.trim().is_empty())
                        .collect::<Vec<_>>();
                    if !patterns.is_empty() {
                        return Some(patterns);
                    }
                }
            }
            TokenTree::Punct(punct) if punct.as_char() == ';' => break,
            _ => {}
        }
        index += 1;
    }
    None
}

fn git_rev_parse(cwd: &Path, rev: &str) -> Option<String> {
    command_stdout(cwd, DEFAULT_GIT_COMMAND, &["rev-parse", rev])
}

fn git_worktree_root(cwd: &Path) -> Option<PathBuf> {
    command_stdout(cwd, DEFAULT_GIT_COMMAND, &["rev-parse", "--show-toplevel"]).map(PathBuf::from)
}

fn git_remote_url(cwd: &Path, remote: &str) -> Option<String> {
    command_stdout(cwd, DEFAULT_GIT_COMMAND, &["remote", "get-url", remote])
}

fn git_dirty(cwd: &Path) -> Option<bool> {
    command_stdout(
        cwd,
        DEFAULT_GIT_COMMAND,
        &[
            "-c",
            "status.showUntrackedFiles=all",
            "status",
            "--short",
            "--untracked-files=all",
        ],
    )
    .map(|stdout| !stdout.trim().is_empty())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum GitHeadPathKind {
    Blob,
    Tree,
}

fn git_head_path_kind(cwd: &Path, rel_path: &str) -> Result<Option<GitHeadPathKind>, String> {
    let result = run_command(
        cwd,
        DEFAULT_GIT_COMMAND,
        &["ls-tree", "HEAD", "--", rel_path],
    );
    if result.exit_code != Some(0) {
        return Err(format!(
            "git ls-tree failed with exit {:?}: {}",
            result.exit_code, result.stderr_tail
        ));
    }
    let mut entries = result
        .stdout_tail
        .lines()
        .filter(|line| !line.trim().is_empty());
    let Some(entry) = entries.next() else {
        return Ok(None);
    };
    if entries.next().is_some() {
        return Err(format!(
            "git ls-tree returned multiple entries for `{rel_path}`"
        ));
    }
    let metadata = entry
        .split_once('\t')
        .map(|(metadata, _)| metadata)
        .unwrap_or(entry);
    match metadata.split_whitespace().nth(1) {
        Some("blob") => Ok(Some(GitHeadPathKind::Blob)),
        Some("tree") => Ok(Some(GitHeadPathKind::Tree)),
        Some(kind) => Err(format!(
            "unsupported HEAD object kind `{kind}` for `{rel_path}`"
        )),
        None => Err(format!(
            "could not parse git ls-tree entry for `{rel_path}`"
        )),
    }
}

fn git_stdout_bytes(cwd: &Path, args: &[&str]) -> Result<Vec<u8>, String> {
    let mut command = Command::new(DEFAULT_GIT_COMMAND);
    command
        .args(args)
        .env_clear()
        .envs(sanitized_command_env())
        .current_dir(cwd);
    let output = command
        .output()
        .map_err(|err| format!("failed to execute git: {err}"))?;
    if !output.status.success() {
        return Err(format!(
            "git {:?} failed with exit {:?}: {}",
            args,
            output.status.code(),
            tail_string(&String::from_utf8_lossy(&output.stderr), 4096)
        ));
    }
    Ok(output.stdout)
}

fn git_path_tracked(cwd: &Path, path: &Path) -> Option<bool> {
    let rel_path = git_relative_path(cwd, path);
    let rel_path = rel_path.to_string_lossy().into_owned();
    let result = run_command(
        cwd,
        DEFAULT_GIT_COMMAND,
        &["ls-files", "--error-unmatch", "--", &rel_path],
    );
    match result.exit_code {
        Some(0) => Some(true),
        Some(1) => Some(false),
        _ => None,
    }
}

fn git_path_ignored(cwd: &Path, path: &Path) -> bool {
    let rel_path = git_relative_path(cwd, path);
    let rel_path = rel_path.to_string_lossy().into_owned();
    run_command(
        cwd,
        DEFAULT_GIT_COMMAND,
        &["check-ignore", "-q", "--", &rel_path],
    )
    .exit_code
        == Some(0)
}

fn git_relative_path(cwd: &Path, path: &Path) -> PathBuf {
    if let Ok(relative) = path.strip_prefix(cwd) {
        return relative.to_path_buf();
    }
    path.to_path_buf()
}

fn ls_remote_head(url: &str) -> Option<String> {
    let cwd = std::env::temp_dir();
    for candidate in ls_remote_candidate_urls(url) {
        if let Some(head) = command_stdout(
            &cwd,
            DEFAULT_GIT_COMMAND,
            &["ls-remote", &candidate, "refs/heads/main"],
        )
        .and_then(|stdout| parse_explicit_main_ref(&stdout))
        {
            return Some(head);
        }
    }
    None
}

/// Parse the exact output contract of `git ls-remote <url> refs/heads/main`.
///
/// The latest-pin gate is an authority boundary, so it must not accept a
/// warning, a symbolic `HEAD` row, a different ref, or the first row of a
/// multiline response as a commit.  A valid response is exactly one non-empty
/// `<40 lowercase hex> refs/heads/main` row and nothing else.
fn parse_explicit_main_ref(stdout: &str) -> Option<String> {
    let mut rows = stdout.lines().filter(|line| !line.trim().is_empty());
    let row = rows.next()?;
    if rows.next().is_some() {
        return None;
    }

    let mut fields = row.split_whitespace();
    let revision = fields.next()?;
    let reference = fields.next()?;
    if fields.next().is_some()
        || reference != "refs/heads/main"
        || revision.len() != 40
        || !revision
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return None;
    }
    Some(revision.to_string())
}

fn ls_remote_candidate_urls(url: &str) -> Vec<String> {
    let mut urls = vec![url.to_string()];
    if let Some(repo) = url.strip_prefix("https://github.com/") {
        urls.push(format!("git@github.com:{repo}.git"));
    }
    urls
}

fn ay_remote_url_matches(url: &str) -> bool {
    normalized_github_repo_url(url) == normalized_github_repo_url(AY_REPO_URL)
}

fn normalized_github_repo_url(url: &str) -> String {
    let trimmed = url.trim().trim_end_matches(".git");
    if let Some(repo) = trimmed.strip_prefix("git@github.com:") {
        return format!("https://github.com/{repo}");
    }
    if let Some(repo) = trimmed.strip_prefix("ssh://git@github.com/") {
        return format!("https://github.com/{repo}");
    }
    trimmed.to_string()
}

fn command_stdout(cwd: &Path, program: &str, args: &[&str]) -> Option<String> {
    let mut command = Command::new(program);
    command
        .args(args)
        .env_clear()
        .envs(sanitized_command_env())
        .current_dir(cwd);
    let output = command.output().ok()?;
    if !output.status.success() {
        return None;
    }
    Some(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

#[derive(Debug, Clone, Default)]
struct AYDependencySpec {
    rev: Option<String>,
    git: Option<String>,
    path: Option<String>,
}

#[derive(Debug, Clone)]
struct VerifiedSiblingAYRepo {
    repo_root: PathBuf,
    head: String,
    origin_url: String,
    published: AYPublished,
}

/// Whether the verified sibling ay HEAD is reachable from the canonical
/// `origin/main`. This is *informational* provenance, never a gate failure: a
/// clean local checkout that is merely ahead of `origin/main` is still a fully
/// knowable ay identity (its HEAD is a faithful content commitment), it simply
/// has not been published to origin yet. On stale or absent remote refs we
/// classify `LocalOnly` rather than failing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AYPublished {
    /// `origin/main` contains the verified HEAD (reachable via merge-base).
    Reachable,
    /// HEAD is not (yet) reachable from `origin/main`, or remote refs are
    /// stale/absent. Never a failure — only recorded.
    LocalOnly,
}

impl AYPublished {
    fn label(self) -> &'static str {
        match self {
            Self::Reachable => "reachable",
            Self::LocalOnly => "local-only",
        }
    }
}

fn collect_ay_manifest_provenance(crate_root: &Path) -> AYManifestProvenance {
    let cargo_toml = crate_root.join("Cargo.toml");
    let specs = parse_ay_dependency_specs(&cargo_toml);
    let git_revs = ay_pins_from_specs(&specs);
    let sources = ay_sources_from_specs(&specs, None);
    if let Some(pin) = common_ay_pin(&git_revs) {
        // The committed checkout uses TWO simultaneous authorities: the exact
        // Git rev in Cargo.toml is the expected public identity, while the
        // repo-local [patch] makes Cargo compile the sibling worktree. Preserve
        // both instead of letting the manifest's rev hide the active Path
        // resolution. An invalid/dirty patch intentionally yields no identity;
        // active_local_ay_patch_detected then fails the strict gate below.
        let sibling_identity = verified_sibling_ay_patch_model(crate_root)
            .ok()
            .flatten()
            .map(ay_sibling_identity);
        let source_model = if sibling_identity.is_some() {
            AYSourceModel::GitRevWithVerifiedSiblingPath
        } else {
            AYSourceModel::GitRev
        };
        return AYManifestProvenance {
            pinned_rev: Some(pin),
            pinned_revs: git_revs,
            pinned_sources: sources,
            source_model,
            sibling_identity,
        };
    }

    if let Ok(sibling) = verified_sibling_ay_dependency_model(crate_root, &specs) {
        let head = sibling.head.clone();
        return AYManifestProvenance {
            pinned_rev: Some(head.clone()),
            pinned_revs: REQUIRED_AY_CRATES
                .iter()
                .map(|crate_name| ((*crate_name).to_string(), Some(head.clone())))
                .collect(),
            pinned_sources: ay_sources_from_specs(&specs, Some(&sibling.repo_root)),
            source_model: AYSourceModel::VerifiedSiblingPath,
            sibling_identity: Some(ay_sibling_identity(sibling)),
        };
    }

    AYManifestProvenance {
        pinned_rev: None,
        pinned_revs: git_revs,
        pinned_sources: sources,
        source_model: AYSourceModel::Unverified,
        sibling_identity: None,
    }
}

fn ay_sibling_identity(sibling: VerifiedSiblingAYRepo) -> AYSiblingIdentity {
    AYSiblingIdentity {
        head: sibling.head,
        repo_root: sibling.repo_root,
        origin_url: sibling.origin_url,
        // Identity construction requires a clean worktree; reaching here
        // implies it.
        worktree_clean: true,
        published: sibling.published,
    }
}

/// Evaluate the "latest private ay pin" gate, tolerating an absent
/// `latest_private_main` (e.g. offline / unreachable remote).
///
/// - Under the Path model the gate passes on *identity* (a clean,
///   origin-verified `../ay` sibling); it does not require the remote at all, so
///   a missing `latest_private_main` still yields `Some(true)`.
/// - Under the GitRev model the gate must compare the pin against the live
///   remote HEAD, so an absent `latest_private_main` yields `None` (fail: cannot
///   determine the latest).
fn ay_latest_private_main_gate_passes(
    provenance: &AYManifestProvenance,
    latest_private_main: Option<&str>,
    local_patch_detected: bool,
) -> Option<bool> {
    if local_patch_detected {
        return Some(false);
    }
    if provenance.source_model == AYSourceModel::VerifiedSiblingPath {
        return Some(provenance.sibling_identity.is_some());
    }
    latest_private_main
        .map(|latest| ay_latest_private_main_matches(provenance, latest, local_patch_detected))
}

fn ay_latest_private_main_matches(
    provenance: &AYManifestProvenance,
    latest_private_main: &str,
    local_patch_detected: bool,
) -> bool {
    if local_patch_detected {
        return false;
    }
    match provenance.source_model {
        AYSourceModel::GitRev | AYSourceModel::GitRevWithVerifiedSiblingPath => {
            let manifest_matches = REQUIRED_AY_CRATES.iter().all(|crate_name| {
                provenance
                    .pinned_revs
                    .get(*crate_name)
                    .and_then(|rev| rev.as_deref())
                    == Some(latest_private_main)
                    && provenance
                        .pinned_sources
                        .get(*crate_name)
                        .and_then(|source| source.as_deref())
                        .is_some_and(ay_remote_url_matches)
            });
            let sibling_matches = match provenance.source_model {
                AYSourceModel::GitRevWithVerifiedSiblingPath => provenance
                    .sibling_identity
                    .as_ref()
                    .is_some_and(|identity| identity.head == latest_private_main),
                AYSourceModel::GitRev => provenance.sibling_identity.is_none(),
                _ => false,
            };
            manifest_matches && sibling_matches
        }
        // Under the Path model the gate passes on *identity*: a clean,
        // origin-verified `../ay` sibling whose HEAD is the recorded pin. The
        // identity is constructed only when those soundness conditions hold
        // (single canonical sibling root, origin == canonical ay, clean
        // worktree), so we no longer require HEAD == ls-remote origin/main. The
        // `latest_private_main` argument is informational here (published vs.
        // local-only is carried separately on the sibling identity).
        AYSourceModel::VerifiedSiblingPath => provenance.sibling_identity.is_some(),
        AYSourceModel::Unverified => false,
    }
}

#[cfg(test)]
fn parse_ay_pins(cargo_toml: &Path) -> BTreeMap<String, Option<String>> {
    ay_pins_from_specs(&parse_ay_dependency_specs(cargo_toml))
}

#[cfg(test)]
fn parse_ay_sources(cargo_toml: &Path) -> BTreeMap<String, Option<String>> {
    ay_sources_from_specs(&parse_ay_dependency_specs(cargo_toml), None)
}

fn parse_ay_dependency_specs(cargo_toml: &Path) -> BTreeMap<String, AYDependencySpec> {
    let mut specs = empty_ay_dependency_specs();
    let Ok(text) = fs::read_to_string(cargo_toml) else {
        return specs;
    };
    for line in text.lines() {
        let trimmed = line.trim_start();
        for crate_name in REQUIRED_AY_CRATES {
            if trimmed.starts_with(&format!("{crate_name} =")) {
                specs.insert(
                    (*crate_name).to_string(),
                    AYDependencySpec {
                        rev: parse_rev_field(trimmed),
                        git: parse_git_field(trimmed),
                        path: parse_path_field(trimmed),
                    },
                );
            }
        }
    }
    specs
}

fn empty_ay_dependency_specs() -> BTreeMap<String, AYDependencySpec> {
    REQUIRED_AY_CRATES
        .iter()
        .map(|crate_name| ((*crate_name).to_string(), AYDependencySpec::default()))
        .collect()
}

/// Parse the repo-local AY patch that Cargo applies in the normal checkout.
///
/// Cargo.toml's exact Git rev remains the expected/public authority. This
/// parser independently captures the Path authority that selects the bytes
/// actually compiled. Missing/duplicate/malformed required entries fail closed
/// by preventing construction of a verified sibling identity.
fn repo_local_ay_patch_specs(
    crate_root: &Path,
) -> Result<Option<BTreeMap<String, AYDependencySpec>>, String> {
    let paths = [
        crate_root.join("Cargo.toml"),
        crate_root.join(".cargo/config.toml"),
        crate_root.join(".cargo/config"),
    ];
    let mut specs = empty_ay_dependency_specs();
    let mut seen = BTreeSet::new();
    let mut found_ay_patch = false;

    for path in paths {
        let Ok(text) = fs::read_to_string(&path) else {
            continue;
        };
        let mut in_ay_patch_section = false;
        for raw_line in text.lines() {
            let line = raw_line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            if line.starts_with('[') && line.ends_with(']') {
                in_ay_patch_section = ay_patch_section_matches(line);
                found_ay_patch |= in_ay_patch_section;
                continue;
            }
            if !in_ay_patch_section {
                continue;
            }
            for crate_name in REQUIRED_AY_CRATES {
                if !line.starts_with(&format!("{crate_name} =")) {
                    continue;
                }
                if !seen.insert((*crate_name).to_string()) {
                    return Err(format!(
                        "duplicate {crate_name} entry across repo-local ay patch tables"
                    ));
                }
                specs.insert(
                    (*crate_name).to_string(),
                    AYDependencySpec {
                        rev: parse_rev_field(line),
                        git: parse_git_field(line),
                        path: parse_path_field(line),
                    },
                );
            }
        }
    }

    if found_ay_patch {
        Ok(Some(specs))
    } else {
        Ok(None)
    }
}

fn verified_sibling_ay_patch_model(
    crate_root: &Path,
) -> Result<Option<VerifiedSiblingAYRepo>, String> {
    let Some(specs) = repo_local_ay_patch_specs(crate_root)? else {
        return Ok(None);
    };
    verified_sibling_ay_dependency_model(crate_root, &specs).map(Some)
}

fn ay_pins_from_specs(
    specs: &BTreeMap<String, AYDependencySpec>,
) -> BTreeMap<String, Option<String>> {
    REQUIRED_AY_CRATES
        .iter()
        .map(|crate_name| {
            (
                (*crate_name).to_string(),
                specs.get(*crate_name).and_then(|spec| spec.rev.clone()),
            )
        })
        .collect()
}

fn ay_sources_from_specs(
    specs: &BTreeMap<String, AYDependencySpec>,
    local_repo: Option<&Path>,
) -> BTreeMap<String, Option<String>> {
    REQUIRED_AY_CRATES
        .iter()
        .map(|crate_name| {
            let source = specs.get(*crate_name).and_then(|spec| {
                spec.git.clone().or_else(|| {
                    spec.path
                        .as_deref()
                        .map(|path| ay_path_source_label(path, local_repo))
                })
            });
            ((*crate_name).to_string(), source)
        })
        .collect()
}

fn ay_path_source_label(path: &str, local_repo: Option<&Path>) -> String {
    match local_repo {
        Some(local_repo) => format!("path:{path} (local git repo: {})", local_repo.display()),
        None => format!("path:{path}"),
    }
}

fn verified_sibling_ay_dependency_model(
    crate_root: &Path,
    specs: &BTreeMap<String, AYDependencySpec>,
) -> Result<VerifiedSiblingAYRepo, String> {
    let canonical_crate_root = crate_root
        .canonicalize()
        .map_err(|err| format!("failed to canonicalize crate root: {err}"))?;
    let expected_sibling_root = canonical_crate_root
        .parent()
        .ok_or_else(|| "crate root has no parent directory".to_string())?
        .join("ay")
        .canonicalize()
        .map_err(|err| format!("failed to canonicalize sibling ay repo: {err}"))?;

    let mut common_repo: Option<PathBuf> = None;
    for crate_name in REQUIRED_AY_CRATES {
        let spec = specs
            .get(*crate_name)
            .ok_or_else(|| format!("missing {crate_name} dependency"))?;
        let path = spec
            .path
            .as_deref()
            .ok_or_else(|| format!("{crate_name} is not a path dependency"))?;
        if spec.git.is_some() || spec.rev.is_some() {
            return Err(format!(
                "{crate_name} mixes path provenance with git/rev fields"
            ));
        }
        let dependency_path = resolve_repo_path(crate_root, Path::new(path))
            .canonicalize()
            .map_err(|err| format!("failed to canonicalize {crate_name} path {path}: {err}"))?;
        let repo_root = git_worktree_root(&dependency_path)
            .ok_or_else(|| format!("{crate_name} path is not inside a git worktree"))?
            .canonicalize()
            .map_err(|err| format!("failed to canonicalize {crate_name} git root: {err}"))?;
        if repo_root != expected_sibling_root {
            return Err(format!(
                "{crate_name} resolves under {}, expected sibling ay repo {}",
                repo_root.display(),
                expected_sibling_root.display()
            ));
        }
        match &common_repo {
            Some(common_repo) if common_repo != &repo_root => {
                return Err(format!(
                    "{crate_name} resolves under {}, expected {}",
                    repo_root.display(),
                    common_repo.display()
                ));
            }
            Some(_) => {}
            None => common_repo = Some(repo_root),
        }
    }

    let repo_root = common_repo.ok_or_else(|| "no ay dependency paths found".to_string())?;
    let origin_url = git_remote_url(&repo_root, "origin")
        .ok_or_else(|| "sibling ay repo has no origin remote".to_string())?;
    if !ay_remote_url_matches(&origin_url) {
        return Err(format!(
            "sibling ay repo origin {origin_url} does not match {AY_REPO_URL}"
        ));
    }
    match git_dirty(&repo_root) {
        Some(false) => {}
        Some(true) => return Err("sibling ay repo is dirty".to_string()),
        None => return Err("could not determine sibling ay repo dirty state".to_string()),
    }
    let head = git_rev_parse(&repo_root, "HEAD")
        .ok_or_else(|| "could not read sibling ay HEAD".to_string())?;
    // Identity is the clean, origin-verified HEAD above. Whether that HEAD is
    // already published to `origin/main` is *recorded*, never required: a clean
    // local-ahead ay is a perfectly knowable identity. Stale/absent remote refs
    // classify as `LocalOnly` and never fail.
    let published = ay_published_classification(&repo_root, &head);
    Ok(VerifiedSiblingAYRepo {
        repo_root,
        head,
        origin_url,
        published,
    })
}

/// Classify whether `head` is reachable from the canonical `origin/main` of the
/// verified sibling ay repo. Reachability requires up-to-date remote refs; on
/// stale or absent refs we return `LocalOnly` (never an error) since the
/// classification is informational only.
fn ay_published_classification(repo_root: &Path, head: &str) -> AYPublished {
    let Some(origin_main) = git_rev_parse(repo_root, "refs/remotes/origin/main") else {
        return AYPublished::LocalOnly;
    };
    if origin_main == head {
        return AYPublished::Reachable;
    }
    // `git merge-base --is-ancestor <head> origin/main` exits 0 iff origin/main
    // contains head. Any non-zero exit (including the "not an ancestor" exit 1)
    // or failure to run classifies as LocalOnly.
    if git_is_ancestor(repo_root, head, "refs/remotes/origin/main") {
        AYPublished::Reachable
    } else {
        AYPublished::LocalOnly
    }
}

/// Returns true iff `ancestor` is an ancestor of (i.e. is contained by)
/// `descendant` in the repo at `repo_root`. Uses `git merge-base --is-ancestor`,
/// which exits 0 on yes, 1 on no, and other codes on error; only exit 0 yields
/// true.
fn git_is_ancestor(repo_root: &Path, ancestor: &str, descendant: &str) -> bool {
    run_command(
        repo_root,
        DEFAULT_GIT_COMMAND,
        &["merge-base", "--is-ancestor", ancestor, descendant],
    )
    .exit_code
        == Some(0)
}

fn parse_ay_lock_sources(cargo_lock: &Path) -> Vec<AYLockSourceEntry> {
    let Ok(text) = fs::read_to_string(cargo_lock) else {
        return Vec::new();
    };
    let mut sources = Vec::new();
    let mut name: Option<String> = None;
    let mut source: Option<String> = None;
    for raw_line in text.lines().chain(std::iter::once("[[package]]")) {
        let line = raw_line.trim();
        if line == "[[package]]" {
            if let Some(package_name) = name.take() {
                if package_name.starts_with("ay-") {
                    sources.push(AYLockSourceEntry {
                        package_name,
                        source: source.take(),
                    });
                } else {
                    source = None;
                }
            }
            continue;
        }
        if let Some((key, value)) = line.split_once('=') {
            let key = key.trim();
            let value = value.trim();
            match key {
                "name" => name = Some(unquote(value)),
                "source" => {
                    let parsed = unquote(value);
                    source = if parsed == "null" { None } else { Some(parsed) };
                }
                _ => {}
            }
        }
    }
    sources
}

fn ay_lock_sources_by_package(entries: &[AYLockSourceEntry]) -> BTreeMap<String, Option<String>> {
    entries
        .iter()
        .map(|entry| (entry.package_name.clone(), entry.source.clone()))
        .collect()
}

fn ay_lock_source_matches_pin(source: &str, pinned_rev: &str) -> bool {
    let Some(source) = source.strip_prefix("git+") else {
        return false;
    };
    let Some((repo_and_rev, observed_rev)) = source.rsplit_once('#') else {
        return false;
    };
    if observed_rev != pinned_rev {
        return false;
    }
    let Some((repo_url, requested_rev)) = repo_and_rev.split_once("?rev=") else {
        return false;
    };
    requested_rev == pinned_rev && ay_remote_url_matches(repo_url)
}

fn ay_lock_source_observed_rev(source: &str) -> Option<&str> {
    source
        .rsplit_once('#')
        .and_then(|(_, rev)| if rev.is_empty() { None } else { Some(rev) })
}

fn common_ay_pin(pins: &BTreeMap<String, Option<String>>) -> Option<String> {
    let mut common = None;
    for crate_name in REQUIRED_AY_CRATES {
        let rev = pins.get(*crate_name)?.as_ref()?;
        match &common {
            Some(common_rev) if common_rev != rev => return None,
            Some(_) => {}
            None => common = Some(rev.clone()),
        }
    }
    common
}

/// Detect an *active, unsanctioned* local `[patch]` of ay.
///
/// An ay `[patch]` whose every ay entry redirects (via `path = "..."`) to the
/// verified `../ay` sibling root is the **sanctioned dev redirect** — the very
/// mechanism the Path identity model relies on — and is NOT a disqualifier.
/// `verified_ay_root` is the canonicalized verified sibling root (present only
/// when the Path identity was established). Any ay patch entry that is not a
/// path entry, or whose path resolves outside the verified root (or when the
/// verified root is unknown), is treated as an active local patch override.
fn active_local_ay_patch_detected(
    crate_root: &Path,
    cargo_home: Option<&Path>,
    verified_ay_root: Option<&Path>,
) -> bool {
    let mut paths = vec![
        crate_root.join("Cargo.toml"),
        crate_root.join(".cargo/config.toml"),
        crate_root.join(".cargo/config"),
    ];
    if let Some(cargo_home) = cargo_home {
        paths.extend(cargo_home_config_paths(cargo_home));
    }
    paths
        .iter()
        .any(|path| active_local_ay_patch_in_file(path, verified_ay_root))
}

fn active_local_ay_patch_in_file(path: &Path, verified_ay_root: Option<&Path>) -> bool {
    let Ok(text) = fs::read_to_string(path) else {
        return false;
    };
    // Cargo resolves paths in a repo's `.cargo/config*` from the directory
    // containing `.cargo`, while a manifest patch resolves from the manifest's
    // own directory. Mirroring that distinction is authority-critical: using
    // `.cargo` itself as the base falsely classified the committed `../ay`
    // redirect as a different, nonexistent checkout.
    let parent = path.parent().unwrap_or_else(|| Path::new("."));
    let base_dir = if parent.file_name().is_some_and(|name| name == ".cargo") {
        parent.parent().unwrap_or(parent)
    } else {
        parent
    };
    let mut in_ay_patch_section = false;
    for raw_line in text.lines() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if line.starts_with('[') && line.ends_with(']') {
            in_ay_patch_section = ay_patch_section_matches(line);
            continue;
        }
        // Every assignment in an AY patch table can replace code from AY,
        // including an aliased or transitive package name. Authenticate all of
        // them to the same sibling repo; checking only the four direct crate
        // names would leave an easy provenance bypass.
        if in_ay_patch_section
            && line.contains('=')
            && !ay_patch_entry_is_sanctioned(line, base_dir, verified_ay_root)
        {
            return true;
        }
    }
    false
}

/// True iff this ay `[patch]` entry redirects to the verified `../ay` sibling
/// root via a `path = "..."` field (tightly scoped to `verified_ay_root`). A
/// missing verified root, a non-path entry, mixed git/rev fields, or a path
/// resolving outside the verified root all make the entry unsanctioned.
fn ay_patch_entry_is_sanctioned(
    line: &str,
    base_dir: &Path,
    verified_ay_root: Option<&Path>,
) -> bool {
    let Some(verified_ay_root) = verified_ay_root else {
        return false;
    };
    // Never sanction an entry that also carries git/rev provenance — that would
    // be ambiguous about which ay actually resolves.
    if parse_git_field(line).is_some() || parse_rev_field(line).is_some() {
        return false;
    }
    let Some(path) = parse_path_field(line) else {
        return false;
    };
    let resolved = resolve_repo_path(base_dir, Path::new(&path));
    let Ok(resolved) = resolved.canonicalize() else {
        return false;
    };
    resolved.starts_with(verified_ay_root)
}

fn ay_patch_section_matches(line: &str) -> bool {
    line.starts_with("[patch.") && line.split('"').nth(1).is_some_and(ay_remote_url_matches)
}

fn parse_rev_field(line: &str) -> Option<String> {
    let marker = "rev = \"";
    let start = line.find(marker)? + marker.len();
    let rest = &line[start..];
    let end = rest.find('"')?;
    Some(rest[..end].to_string())
}

fn parse_git_field(line: &str) -> Option<String> {
    let marker = "git = \"";
    let start = line.find(marker)? + marker.len();
    let rest = &line[start..];
    let end = rest.find('"')?;
    Some(rest[..end].to_string())
}

fn parse_path_field(line: &str) -> Option<String> {
    let marker = "path = \"";
    let start = line.find(marker)? + marker.len();
    let rest = &line[start..];
    let end = rest.find('"')?;
    Some(rest[..end].to_string())
}

fn same_path(path: &Path, expected: &Path, crate_root: &Path) -> bool {
    let left = resolve_repo_path(crate_root, path);
    let right = resolve_repo_path(crate_root, expected);
    match (left.canonicalize(), right.canonicalize()) {
        (Ok(left), Ok(right)) => left == right,
        _ => false,
    }
}

fn resolve_repo_path(crate_root: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        crate_root.join(path)
    }
}

fn validate_repo_trust_vc_path(crate_root: &Path, trust_vc_path: &str) -> Result<PathBuf, String> {
    if trust_vc_path.trim().is_empty() {
        return Err("TrustVc port path must not be empty".to_string());
    }
    let path = Path::new(trust_vc_path);
    if path.is_absolute() {
        return Err(format!(
            "TrustVc port path must be repo-relative: {trust_vc_path}"
        ));
    }
    let mut normal_components = 0usize;
    for component in path.components() {
        if matches!(
            component,
            Component::CurDir | Component::ParentDir | Component::RootDir | Component::Prefix(_)
        ) {
            return Err(format!(
                "TrustVc port path must stay inside the repo: {trust_vc_path}"
            ));
        }
        if matches!(component, Component::Normal(_)) {
            normal_components += 1;
        }
    }
    if normal_components == 0 {
        return Err(format!(
            "TrustVc port path must name a repo file or directory: {trust_vc_path}"
        ));
    }

    let joined = crate_root.join(path);
    if !joined.exists() {
        return Err(format!("missing TrustVc port path {trust_vc_path}"));
    }
    let joined_metadata = fs::symlink_metadata(&joined)
        .map_err(|err| format!("failed to inspect TrustVc port path {trust_vc_path}: {err}"))?;
    if joined_metadata.file_type().is_symlink() {
        return Err(format!(
            "TrustVc port path must not be a symlink: {trust_vc_path}"
        ));
    }
    let canonical_root = crate_root
        .canonicalize()
        .map_err(|err| format!("failed to canonicalize repo root: {err}"))?;
    let canonical_path = joined.canonicalize().map_err(|err| {
        format!("failed to canonicalize TrustVc port path {trust_vc_path}: {err}")
    })?;
    if !canonical_path.starts_with(&canonical_root) {
        return Err(format!(
            "TrustVc port path must stay inside the repo: {trust_vc_path}"
        ));
    }
    if canonical_path == canonical_root {
        return Err(format!(
            "TrustVc port path must name a repo file or directory: {trust_vc_path}"
        ));
    }
    Ok(canonical_path)
}

fn trust_vc_source_path_hash(
    crate_root: &Path,
    trust_vc_path: &str,
    canonical_path: &Path,
    use_head: bool,
) -> Result<TrustVcSourcePathHash, String> {
    if use_head {
        return trust_vc_source_path_hash_from_head(crate_root, trust_vc_path, canonical_path);
    }
    trust_vc_source_path_hash_from_filesystem(trust_vc_path, canonical_path)
}

fn trust_vc_source_path_hash_from_head(
    crate_root: &Path,
    trust_vc_path: &str,
    canonical_path: &Path,
) -> Result<TrustVcSourcePathHash, String> {
    let repo_rel = repo_relative_string(crate_root, canonical_path)?;
    let kind = git_head_path_kind(crate_root, &repo_rel)?
        .ok_or_else(|| format!("TrustVc source path must be tracked in HEAD: {trust_vc_path}"))?;
    let (kind, sha256) = match kind {
        GitHeadPathKind::Blob => (
            TrustVcSourceHashKind::File,
            source_file_sha256_from_head(crate_root, &repo_rel)?,
        ),
        GitHeadPathKind::Tree => (
            TrustVcSourceHashKind::Directory,
            source_tree_sha256_from_head(crate_root, &repo_rel)?,
        ),
    };
    Ok(TrustVcSourcePathHash {
        path: trust_vc_path.to_string(),
        kind,
        sha256,
    })
}

fn trust_vc_source_path_hash_from_filesystem(
    trust_vc_path: &str,
    canonical_path: &Path,
) -> Result<TrustVcSourcePathHash, String> {
    let metadata = fs::symlink_metadata(canonical_path).map_err(|err| {
        format!("failed to inspect TrustVc source path {trust_vc_path} for hashing: {err}")
    })?;
    let (kind, sha256) = if metadata.is_file() {
        (
            TrustVcSourceHashKind::File,
            source_file_sha256(canonical_path).map_err(|err| {
                format!("failed to hash TrustVc source path {trust_vc_path}: {err}")
            })?,
        )
    } else if metadata.is_dir() {
        (
            TrustVcSourceHashKind::Directory,
            source_tree_sha256(canonical_path).map_err(|err| {
                format!("failed to hash TrustVc source path {trust_vc_path}: {err}")
            })?,
        )
    } else {
        return Err(format!(
            "TrustVc source path must be a file or directory for hashing: {trust_vc_path}"
        ));
    };
    Ok(TrustVcSourcePathHash {
        path: trust_vc_path.to_string(),
        kind,
        sha256,
    })
}

fn source_file_sha256(path: &Path) -> Result<String, std::io::Error> {
    fs::read(path).map(|bytes| sha256_digest_bytes(&bytes))
}

fn source_file_sha256_from_head(crate_root: &Path, rel_path: &str) -> Result<String, String> {
    let revspec = format!("HEAD:{rel_path}");
    let bytes = git_stdout_bytes(crate_root, &["show", &revspec])?;
    Ok(sha256_digest_bytes(&bytes))
}

fn source_tree_sha256(root: &Path) -> Result<String, String> {
    let mut files = Vec::new();
    collect_source_tree_files(root, root, &mut files)?;
    files.sort_by(|left, right| left.0.cmp(&right.0));

    let mut hasher = Sha256::new();
    hasher.update(b"trust-vc-evidence-source-tree-v1\0");
    for (relative_path, path) in files {
        let bytes = fs::read(&path).map_err(|err| {
            format!(
                "failed to read `{}` while hashing source tree: {err}",
                path.display()
            )
        })?;
        hasher.update(relative_path.as_bytes());
        hasher.update(b"\0");
        hasher.update((bytes.len() as u64).to_le_bytes());
        hasher.update(b"\0");
        hasher.update(&bytes);
        hasher.update(b"\0");
    }
    Ok(sha256_digest_hex(&hasher.finalize()))
}

fn source_tree_sha256_from_head(crate_root: &Path, rel_root: &str) -> Result<String, String> {
    let output = git_stdout_bytes(crate_root, &["ls-tree", "-r", "-z", "HEAD", "--", rel_root])?;
    let mut files = Vec::new();
    let prefix = format!("{}/", rel_root.trim_end_matches('/'));
    for raw_entry in output.split(|byte| *byte == 0) {
        if raw_entry.is_empty() {
            continue;
        }
        let entry = std::str::from_utf8(raw_entry).map_err(|err| {
            format!("git ls-tree emitted non-UTF-8 path under `{rel_root}`: {err}")
        })?;
        let (metadata, path) = entry
            .split_once('\t')
            .ok_or_else(|| format!("could not parse git ls-tree entry `{entry}`"))?;
        let mut metadata_parts = metadata.split_whitespace();
        let mode = metadata_parts.next().unwrap_or("");
        let kind = metadata_parts.next().unwrap_or("");
        if mode == "120000" {
            return Err(format!("source tree hashing rejects HEAD symlink `{path}`"));
        }
        if kind != "blob" {
            return Err(format!(
                "source tree hashing expected HEAD blob under `{rel_root}`, got `{kind}` for `{path}`"
            ));
        }
        let relative = path.strip_prefix(&prefix).unwrap_or(path);
        if source_tree_hash_skips_relative_str(relative) {
            continue;
        }
        files.push((relative.to_string(), path.to_string()));
    }
    files.sort_by(|left, right| left.0.cmp(&right.0));

    let mut hasher = Sha256::new();
    hasher.update(b"trust-vc-evidence-source-tree-v1\0");
    for (relative_path, git_path) in files {
        let bytes = git_stdout_bytes(crate_root, &["show", &format!("HEAD:{git_path}")])?;
        hasher.update(relative_path.as_bytes());
        hasher.update(b"\0");
        hasher.update((bytes.len() as u64).to_le_bytes());
        hasher.update(b"\0");
        hasher.update(&bytes);
        hasher.update(b"\0");
    }
    Ok(sha256_digest_hex(&hasher.finalize()))
}

fn collect_source_tree_files(
    root: &Path,
    dir: &Path,
    files: &mut Vec<(String, PathBuf)>,
) -> Result<(), String> {
    let entries = fs::read_dir(dir)
        .map_err(|err| format!("failed to read source tree dir `{}`: {err}", dir.display()))?;
    for entry in entries {
        let entry = entry.map_err(|err| {
            format!(
                "failed to read source tree entry under `{}`: {err}",
                dir.display()
            )
        })?;
        let path = entry.path();
        let relative = path.strip_prefix(root).unwrap_or(&path);
        if source_tree_hash_skips_relative_path(relative) {
            continue;
        }
        let metadata = fs::symlink_metadata(&path).map_err(|err| {
            format!(
                "failed to inspect source tree path `{}`: {err}",
                path.display()
            )
        })?;
        if metadata.file_type().is_symlink() {
            return Err(format!(
                "source tree hashing rejects symlink `{}`",
                path.display()
            ));
        }
        if metadata.is_dir() {
            collect_source_tree_files(root, &path, files)?;
        } else if metadata.is_file() {
            let Some(relative_path) = relative.to_str().map(|path| path.replace('\\', "/")) else {
                return Err(format!(
                    "source tree hashing rejects non-UTF-8 path `{}`",
                    path.display()
                ));
            };
            files.push((relative_path, path));
        }
    }
    Ok(())
}

fn source_tree_hash_skips_relative_path(path: &Path) -> bool {
    if path.components().count() == 1 && path == Path::new("Cargo.lock") {
        return true;
    }
    matches!(
        path.components()
            .next()
            .and_then(|component| match component {
                Component::Normal(name) => name.to_str(),
                _ => None,
            }),
        Some(".trust_vc" | ".git" | "target")
    )
}

fn source_tree_hash_skips_relative_str(path: &str) -> bool {
    if path.trim_matches('/') == "Cargo.lock" {
        return true;
    }
    matches!(
        path.split('/').find(|segment| !segment.is_empty()),
        Some(".trust_vc" | ".git" | "target")
    )
}

fn sha256_digest_bytes(bytes: &[u8]) -> String {
    sha256_digest_hex(&Sha256::digest(bytes))
}

fn sha256_digest_hex(digest: &[u8]) -> String {
    let mut output = String::with_capacity(7 + digest.len() * 2);
    output.push_str("sha256:");
    for byte in digest {
        output.push_str(&format!("{byte:02x}"));
    }
    output
}

fn valid_sha256_digest_label(value: &str) -> bool {
    value
        .strip_prefix("sha256:")
        .is_some_and(|hex| hex.len() == 64 && hex.chars().all(|ch| ch.is_ascii_hexdigit()))
}

fn ensure_repo_local_output_dir(
    crate_root: &Path,
    output_dir: &Path,
) -> Result<PathBuf, EvidenceError> {
    let canonical_root = crate_root
        .canonicalize()
        .map_err(|err| EvidenceError::new(format!("failed to canonicalize repo root: {err}")))?;
    let resolved = if output_dir.is_absolute() {
        output_dir.to_path_buf()
    } else {
        canonical_root.join(output_dir)
    };
    if output_dir
        .components()
        .any(|component| matches!(component, Component::ParentDir))
    {
        return Err(EvidenceError::new(format!(
            "Verus port output dir must stay inside the repo: {}",
            output_dir.display()
        )));
    }
    if resolved.exists() {
        let canonical_output = resolved.canonicalize().map_err(|err| {
            EvidenceError::new(format!(
                "failed to canonicalize Verus port output dir `{}`: {err}",
                resolved.display()
            ))
        })?;
        if !canonical_output.starts_with(&canonical_root) {
            return Err(EvidenceError::new(format!(
                "Verus port output dir must stay inside the repo: {}",
                output_dir.display()
            )));
        }
        return Ok(canonical_output);
    }
    if !resolved.starts_with(&canonical_root) {
        return Err(EvidenceError::new(format!(
            "Verus port output dir must stay inside the repo: {}",
            output_dir.display()
        )));
    }
    let existing_parent = nearest_existing_parent(&resolved).ok_or_else(|| {
        EvidenceError::new(format!(
            "failed to find existing parent for Verus port output dir `{}`",
            resolved.display()
        ))
    })?;
    let canonical_parent = existing_parent.canonicalize().map_err(|err| {
        EvidenceError::new(format!(
            "failed to canonicalize Verus port output parent `{}`: {err}",
            existing_parent.display()
        ))
    })?;
    if !canonical_parent.starts_with(&canonical_root) {
        return Err(EvidenceError::new(format!(
            "Verus port output dir must stay inside the repo: {}",
            output_dir.display()
        )));
    }
    fs::create_dir_all(&resolved).map_err(|err| {
        EvidenceError::new(format!(
            "failed to create Verus port output dir `{}`: {err}",
            resolved.display()
        ))
    })?;
    let canonical_output = resolved.canonicalize().map_err(|err| {
        EvidenceError::new(format!(
            "failed to canonicalize Verus port output dir `{}`: {err}",
            resolved.display()
        ))
    })?;
    if !canonical_output.starts_with(&canonical_root) {
        return Err(EvidenceError::new(format!(
            "Verus port output dir must stay inside the repo: {}",
            output_dir.display()
        )));
    }
    Ok(canonical_output)
}

fn nearest_existing_parent(path: &Path) -> Option<&Path> {
    let mut candidate = path;
    loop {
        if candidate.exists() {
            return Some(candidate);
        }
        candidate = candidate.parent()?;
    }
}

fn ensure_safe_relative_port_path(path: &str) -> Result<(), EvidenceError> {
    let path = Path::new(path);
    if path.is_absolute() {
        return Err(EvidenceError::new(format!(
            "Verus port scaffold path must be relative: {}",
            path.display()
        )));
    }
    for component in path.components() {
        if matches!(
            component,
            Component::ParentDir | Component::RootDir | Component::Prefix(_)
        ) {
            return Err(EvidenceError::new(format!(
                "Verus port scaffold path must stay inside the output directory: {}",
                path.display()
            )));
        }
    }
    Ok(())
}

fn scaffold_relative_port_path(
    upstream_path: &str,
    roots: &[String],
) -> Result<String, EvidenceError> {
    for root in roots {
        let root = root.trim_matches('/');
        let Some(relative) = upstream_path.strip_prefix(&format!("{root}/")) else {
            continue;
        };
        let scaffold_relative = if root == VERUS_TEST_ROOT {
            relative.to_string()
        } else {
            let root_relative = root.strip_prefix("source/").unwrap_or(root);
            join_slash_path(root_relative, relative)
        };
        ensure_safe_relative_port_path(&scaffold_relative)?;
        return Ok(scaffold_relative);
    }

    Err(EvidenceError::new(format!(
        "{}: upstream path is outside manifest roots {:?}",
        upstream_path, roots
    )))
}

fn repo_relative_display(crate_root: &Path, path: &Path) -> Result<String, EvidenceError> {
    repo_relative_string(crate_root, path).map_err(EvidenceError::new)
}

fn repo_relative_string(crate_root: &Path, path: &Path) -> Result<String, String> {
    let canonical_root = crate_root
        .canonicalize()
        .map_err(|err| format!("failed to canonicalize repo root: {err}"))?;
    let canonical_path = path.canonicalize().map_err(|err| {
        format!(
            "failed to canonicalize repo-local path `{}`: {err}",
            path.display()
        )
    })?;
    let relative = canonical_path
        .strip_prefix(&canonical_root)
        .map_err(|_| format!("path is outside the repo: {}", canonical_path.display()))?;
    Ok(relative.to_string_lossy().replace('\\', "/"))
}

fn join_slash_path(prefix: &str, suffix: &str) -> String {
    if prefix.is_empty() {
        suffix.replace('\\', "/")
    } else {
        format!(
            "{}/{}",
            prefix.trim_end_matches('/'),
            suffix.trim_start_matches('/').replace('\\', "/")
        )
    }
}

fn render_verus_port_stub(entry: &VerusManifestEntry) -> String {
    format!(
        "\
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Auto-scaffolded fail-closed TrustVc port placeholder.
//
// Upstream Verus test: {upstream_path}
// Current classification: {classification}
// Owner issue: {owner_issue}
// Reason: {reason}
//
// Replace this placeholder with a one-to-one executable TrustVc port, then update
// evals/verus/verus-tests.json to classification \"ported\" with this file in
// trust_vc_paths. This file intentionally contains no TrustVc-annotated functions,
// so --run-trust-vc-corpus cannot pass until a real port is written.
",
        upstream_path = entry.upstream_path,
        classification = entry.classification,
        owner_issue = entry.owner_issue,
        reason = entry.reason
    )
}

fn now_unix_seconds() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |duration| duration.as_secs())
}

fn tail_string(text: &str, max_bytes: usize) -> String {
    if text.len() <= max_bytes {
        return text.to_string();
    }
    let mut boundary = text.len().saturating_sub(max_bytes);
    while boundary < text.len() && !text.is_char_boundary(boundary) {
        boundary += 1;
    }
    format!("...{}", &text[boundary..])
}

fn unquote(value: &str) -> String {
    strip_inline_yaml_comment(value)
        .trim_matches('"')
        .trim_matches('\'')
        .to_string()
}

fn strip_inline_yaml_comment(value: &str) -> &str {
    let value = value.trim();
    if value.starts_with('"') || value.starts_with('\'') {
        return value;
    }
    match value.find(" #") {
        Some(index) => value[..index].trim_end(),
        None => value,
    }
}

fn empty_as_unavailable(value: &str) -> String {
    if value.trim().is_empty() {
        "unavailable".to_string()
    } else {
        value.trim().to_string()
    }
}

fn display_opt(value: &Option<String>) -> String {
    value.as_deref().unwrap_or("unavailable").to_string()
}

fn display_path_opt(value: &Option<PathBuf>) -> String {
    value
        .as_ref()
        .map(|path| path.display().to_string())
        .unwrap_or_else(|| "unavailable".to_string())
}

fn report_path_string(path: &Path, crate_root: &Path) -> String {
    path.strip_prefix(crate_root)
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/")
}

fn format_count_map(counts: &BTreeMap<String, usize>) -> String {
    counts
        .iter()
        .map(|(label, count)| format!("{label}={count}"))
        .collect::<Vec<_>>()
        .join(", ")
}

fn joined_or_none(values: &[String]) -> String {
    if values.is_empty() {
        "none".to_string()
    } else {
        values.join(", ")
    }
}

fn expected_case_summaries(cases: &[VerusExpectedCaseEvidence]) -> String {
    if cases.is_empty() {
        return "none".to_string();
    }
    cases
        .iter()
        .map(|case| {
            let mut summary = format!(
                "{}=>{} (min_obligations={})",
                case.case_id, case.expected_verdict, case.min_obligations
            );
            if let Some(upstream_case_id) = &case.upstream_case_id {
                summary.push_str(&format!(", upstream={upstream_case_id}"));
            }
            if let Some(trust_vc_path) = &case.trust_vc_path {
                summary.push_str(&format!(", path={trust_vc_path}"));
            }
            summary
        })
        .collect::<Vec<_>>()
        .join("; ")
}

fn issue_markdown_link(entry: &VerusManifestEntryEvidence) -> String {
    match &entry.owner_issue_url {
        Some(url) => format!("[{}]({})", escape_md(&entry.owner_issue), escape_md(url)),
        None => escape_md(&entry.owner_issue),
    }
}

fn escape_md(value: &str) -> String {
    value.replace('|', "\\|").replace('\n', " ")
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::path::{Path, PathBuf};

    fn assert_sha256_obligation_fingerprints(observed_case: &TrustVcCorpusObservedCase) {
        assert_eq!(
            observed_case.obligation_fingerprints.len(),
            observed_case.obligation_count,
            "fingerprints must align with captured obligation count: {observed_case:?}"
        );
        assert!(
            observed_case.obligation_count >= 1,
            "case should capture at least one obligation fingerprint: {observed_case:?}"
        );
        assert!(
            observed_case
                .obligation_fingerprints
                .iter()
                .all(|fingerprint| {
                    fingerprint.strip_prefix("sha256:").is_some_and(|hex| {
                        hex.len() == 64 && hex.chars().all(|c| c.is_ascii_hexdigit())
                    })
                }),
            "obligation fingerprints must be sha256 hashes: {observed_case:?}"
        );
    }

    fn manifest_entry_for_expected_case(
        evidence_kind: VerusEvidenceKind,
        expected_case: VerusExpectedCase,
    ) -> VerusManifestEntry {
        VerusManifestEntry {
            upstream_path: "source/rust_verify_test/tests/foo.rs".to_string(),
            classification: "ported".to_string(),
            evidence_kind,
            owner_issue: "#123".to_string(),
            reason: "test manifest entry".to_string(),
            trust_vc_paths: vec!["ported/right.rs".to_string()],
            trust_vc_source_hashes: Vec::new(),
            trust_vc_check_args: Vec::new(),
            expected_cases: vec![expected_case],
            known_gaps: Vec::new(),
            notes: String::new(),
        }
    }

    fn test_expected_case(
        case_id: &str,
        expected_verdict: VerusExpectedVerdict,
        min_obligations: usize,
    ) -> VerusExpectedCase {
        VerusExpectedCase {
            case_id: case_id.to_string(),
            upstream_case_id: None,
            trust_vc_path: None,
            expected_verdict,
            min_obligations,
            obligation_fingerprints: Vec::new(),
            expected_error_patterns: Vec::new(),
            expected_rust_diagnostic_pattern_sets: Vec::new(),
            forbidden_diagnostic_patterns: Vec::new(),
            expected_warning_patterns: Vec::new(),
        }
    }

    fn unsupported_scout_entry(expected_cases: Vec<VerusExpectedCase>) -> VerusManifestEntry {
        VerusManifestEntry {
            upstream_path: "source/rust_verify_test/tests/foo.rs".to_string(),
            classification: "unsupported-gap".to_string(),
            evidence_kind: VerusEvidenceKind::ProofObligation,
            owner_issue: "#123".to_string(),
            reason: "partial scout coverage".to_string(),
            trust_vc_paths: vec!["evals/verus/ported/foo.rs".to_string()],
            trust_vc_source_hashes: Vec::new(),
            trust_vc_check_args: Vec::new(),
            expected_cases,
            known_gaps: Vec::new(),
            notes: String::new(),
        }
    }

    fn write_scout_inventory(crate_root: &Path, source: &str) {
        let path = crate_root.join("evals/verus/ported/foo.rs");
        fs::create_dir_all(path.parent().expect("ported path should have parent"))
            .expect("ported dir should be created");
        fs::write(path, source).expect("scout source should be written");
    }

    #[test]
    fn unsupported_scout_inventory_drift_detects_missing_manifest_cases() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-scout-drift-missing");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");
        write_scout_inventory(
            &temp_dir,
            r#"
pub const FOO_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    ("foo_verified", "foo_upstream", "verified", 1),
    ("foo_counterexample", "foo_upstream", "counterexample", 2),
    ("foo_unknown", "foo_upstream", "unknown", 0),
    ("foo_verified_blocker", "foo_upstream", "verified-blocker", 1),
];
"#,
        );
        let entry = unsupported_scout_entry(vec![test_expected_case(
            "foo_verified",
            VerusExpectedVerdict::Verified,
            1,
        )]);
        let mut failures = Vec::new();

        append_unsupported_scout_inventory_failures(&entry, &temp_dir, &mut failures);

        assert_eq!(failures.len(), 1);
        assert!(failures[0].contains("source-only ids [foo_counterexample]"));
        assert!(!failures[0].contains("foo_unknown"));
        assert!(!failures[0].contains("foo_verified_blocker"));
        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn unsupported_scout_inventory_drift_detects_stale_manifest_metadata() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-scout-drift-stale");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");
        write_scout_inventory(
            &temp_dir,
            r#"
pub const FOO_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    ("foo_verified", "foo_upstream", "verified", 3),
    ("foo_error", "foo_upstream", "error", 0),
];
"#,
        );
        let entry = unsupported_scout_entry(vec![
            test_expected_case("foo_verified", VerusExpectedVerdict::Counterexample, 1),
            test_expected_case("foo_error", VerusExpectedVerdict::Error, 0),
        ]);
        let mut failures = Vec::new();

        append_unsupported_scout_inventory_failures(&entry, &temp_dir, &mut failures);

        assert_eq!(failures.len(), 1);
        assert!(
            failures[0].contains("foo_verified verdict source=verified manifest=counterexample")
        );
        assert!(failures[0].contains("foo_verified min_obligations source=3 manifest=1"));
        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn unsupported_scout_inventory_allows_synced_manifest_and_local_blockers() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-scout-drift-synced");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");
        write_scout_inventory(
            &temp_dir,
            r#"
pub const FOO_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    ("foo_verified", "foo_upstream", "verified", 1),
    ("foo_counterexample", "foo_upstream", "counterexample", 2),
    ("foo_unknown", "foo_upstream", "unknown", 0),
];
"#,
        );
        let entry = unsupported_scout_entry(vec![
            test_expected_case("foo_verified", VerusExpectedVerdict::Verified, 1),
            test_expected_case(
                "foo_counterexample",
                VerusExpectedVerdict::Counterexample,
                2,
            ),
        ]);
        let mut failures = Vec::new();

        append_unsupported_scout_inventory_failures(&entry, &temp_dir, &mut failures);

        assert!(failures.is_empty(), "unexpected failures: {failures:?}");
        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn unsupported_scout_inventory_reads_named_struct_entries() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-scout-drift-struct");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");
        write_scout_inventory(
            &temp_dir,
            r#"
pub struct FooExpectedCase {
    pub case: &'static str,
    pub upstream_case: &'static str,
    pub evidence_status: &'static str,
    pub min_obligations: usize,
}

pub const FOO_RS_EXPECTED_CASES: &[FooExpectedCase] = &[
    FooExpectedCase {
        case: "foo_verified",
        upstream_case: "foo_upstream",
        evidence_status: "verified",
        min_obligations: 1,
    },
    FooExpectedCase {
        case: "foo_error",
        upstream_case: "foo_upstream",
        evidence_status: "error",
        min_obligations: 0,
    },
];
"#,
        );
        let entry = unsupported_scout_entry(vec![
            test_expected_case("foo_verified", VerusExpectedVerdict::Verified, 1),
            test_expected_case("foo_error", VerusExpectedVerdict::Error, 0),
        ]);
        let mut failures = Vec::new();

        append_unsupported_scout_inventory_failures(&entry, &temp_dir, &mut failures);

        assert!(failures.is_empty(), "unexpected failures: {failures:?}");
        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    fn corpus_run_report(
        attempted_paths: usize,
        passed_paths: usize,
        failed_paths: usize,
        skipped_entries: usize,
    ) -> TrustVcCorpusRunReport {
        TrustVcCorpusRunReport {
            attempted_paths,
            passed_paths,
            failed_paths,
            skipped_entries,
            results: Vec::new(),
        }
    }

    #[test]
    fn trust_vc_corpus_gate_rejects_skipped_entries() {
        let report = corpus_run_report(1, 1, 0, 1);

        assert!(!report.passed());
        assert_eq!(trust_vc_corpus_gate(&report).status, GateStatus::Failed);
    }

    #[test]
    fn trust_vc_corpus_gate_rejects_path_count_mismatch() {
        let report = corpus_run_report(2, 1, 0, 0);

        assert!(!report.passed());
        assert_eq!(trust_vc_corpus_gate(&report).status, GateStatus::Failed);
    }

    #[test]
    fn trust_vc_corpus_gate_rejects_command_mode_as_replacement_evidence() {
        let mut report = corpus_run_report(1, 1, 0, 0);
        report.results.push(TrustVcCorpusRunResult {
            upstream_path: "source/rust_verify_test/tests/foo.rs".to_string(),
            trust_vc_path: "evals/verus/ported/foo.rs".to_string(),
            trust_vc_paths: vec!["evals/verus/ported/foo.rs".to_string()],
            execution_mode: TrustVcCorpusExecutionMode::Command,
            status: GateStatus::Passed,
            detail: Some("exit code 0".to_string()),
            function_count: 0,
            expected_case_count: 1,
            observed_case_count: 0,
            expected_obligation_count: 1,
            observed_obligation_count: 0,
            expected_case_ids: vec!["foo".to_string()],
            observed_case_ids: Vec::new(),
            observed_cases: Vec::new(),
            failures: Vec::new(),
            command: None,
            commands: Vec::new(),
        });

        assert!(report.passed());
        let gate = trust_vc_corpus_gate(&report);
        assert_eq!(gate.status, GateStatus::Failed);
        assert!(
            gate.detail
                .as_deref()
                .is_some_and(|detail| detail.contains("command-mode")),
            "command-mode corpus execution must not look like pinned replacement evidence: {gate:?}"
        );
    }

    #[cfg(unix)]
    fn write_executable(path: &Path, contents: &str) {
        use std::os::unix::fs::PermissionsExt;

        fs::write(path, contents).expect("executable test script should be written");
        let mut permissions = fs::metadata(path)
            .expect("executable test script metadata should be readable")
            .permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(path, permissions).expect("executable test script should be runnable");
    }

    #[cfg(unix)]
    const SYNTHETIC_PROVEN_E2E_ENV: &str = "TRUST_VC_RUN_SYNTHETIC_PROVEN_E2E";
    #[cfg(unix)]
    const SYNTHETIC_PROVEN_CHILD_ENV: &str = "TRUST_VC_SYNTHETIC_PROVEN_CHILD";
    #[cfg(unix)]
    const SYNTHETIC_PROVEN_CRATE_ROOT_ENV: &str = "TRUST_VC_SYNTHETIC_PROVEN_CRATE_ROOT";
    #[cfg(unix)]
    const SYNTHETIC_PROVEN_VERUS_ROOT_ENV: &str = "TRUST_VC_SYNTHETIC_PROVEN_VERUS_ROOT";
    #[cfg(unix)]
    const SYNTHETIC_PROVEN_CARGO_ENV: &str = "TRUST_VC_SYNTHETIC_PROVEN_CARGO";
    #[cfg(unix)]
    const SYNTHETIC_PROVEN_OUTPUT_DIR_ENV: &str = "TRUST_VC_SYNTHETIC_PROVEN_OUTPUT_DIR";

    #[cfg(unix)]
    #[test]
    fn replacement_evidence_synthetic_success_path_runs_when_enabled() {
        if std::env::var_os(SYNTHETIC_PROVEN_CHILD_ENV).is_some() {
            return;
        }
        // The proof path still has one non-synthetic dependency under test-only ownership:
        // `latest private ay pin` calls the real private ay remote with no injection point.
        if std::env::var_os(SYNTHETIC_PROVEN_E2E_ENV).is_none() {
            eprintln!(
                "skipping synthetic proven replacement-evidence e2e; set {SYNTHETIC_PROVEN_E2E_ENV}=1 when the real private ay ls-remote gate is available"
            );
            return;
        }

        assert_ne!(
            TVC_BUILD_GIT_HEAD, "unknown",
            "the proven e2e harness needs an embedded build git HEAD"
        );
        let latest_ay = ls_remote_head(AY_REPO_URL)
            .expect("the proven e2e harness needs access to the real private ay main ref");
        let source_repo = cargo_trust_vc_repo_root();
        let temp_dir = unique_temp_dir("trust-vc-evidence-proven-e2e");
        fs::remove_dir_all(&temp_dir).ok();
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");
        let crate_root = temp_dir.join("trust_vc");
        let source_repo_arg = source_repo.to_string_lossy().into_owned();
        let crate_root_arg = crate_root.to_string_lossy().into_owned();
        let clone = run_command(
            &temp_dir,
            DEFAULT_GIT_COMMAND,
            &["clone", "--shared", &source_repo_arg, &crate_root_arg],
        );
        assert_eq!(
            clone.exit_code,
            Some(0),
            "synthetic repo clone should succeed: {}",
            clone.stderr_tail
        );
        let checkout = run_command(
            &crate_root,
            DEFAULT_GIT_COMMAND,
            &["checkout", "--detach", TVC_BUILD_GIT_HEAD],
        );
        assert_eq!(
            checkout.exit_code,
            Some(0),
            "synthetic repo checkout should match the test binary build HEAD: {}",
            checkout.stderr_tail
        );

        let verus_root = temp_dir.join("verus");
        let verus_ref = write_synthetic_verus_checkout(&verus_root);
        let fake_cargo = temp_dir.join("fake-bin/cargo");
        fs::create_dir_all(
            fake_cargo
                .parent()
                .expect("fake cargo should have a parent"),
        )
        .expect("fake cargo bin dir should be created");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
case "$1" in
  fetch|check|test|generate-lockfile)
    exit 0
    ;;
  *)
    echo "unexpected synthetic cargo command: $*" >&2
    exit 64
    ;;
esac
"#,
        );

        rewrite_synthetic_ay_pins(&crate_root, &latest_ay);
        let trust_vc_path = "evals/verus/ported/adts.rs";
        let case_id = "struct_update_copies_omitted_fields";
        let candidate = TrustVcCorpusRunCandidate {
            upstream_path: format!("{VERUS_TEST_ROOT}/synthetic.rs"),
            classification: "ported".to_string(),
            evidence_kind: VerusEvidenceKind::ProofObligation,
            trust_vc_paths: vec![trust_vc_path.to_string()],
            trust_vc_check_args: Vec::new(),
            expected_cases: vec![VerusExpectedCase {
                case_id: case_id.to_string(),
                upstream_case_id: None,
                trust_vc_path: None,
                expected_verdict: VerusExpectedVerdict::Verified,
                min_obligations: 1,
                obligation_fingerprints: Vec::new(),
                expected_error_patterns: Vec::new(),
                expected_rust_diagnostic_pattern_sets: Vec::new(),
                forbidden_diagnostic_patterns: Vec::new(),
                expected_warning_patterns: Vec::new(),
            }],
        };
        let dry_run = run_trust_vc_corpus_direct(&crate_root, &candidate);
        assert_eq!(
            dry_run.status,
            GateStatus::Passed,
            "synthetic direct-source port should produce a passing observed case: {:?}",
            dry_run.failures
        );
        let fingerprints = dry_run.observed_cases[0].obligation_fingerprints.clone();
        assert!(
            !fingerprints.is_empty(),
            "schema v2 synthetic evidence needs pinned obligation fingerprints"
        );
        let source_hash = source_file_sha256_from_head(&crate_root, trust_vc_path)
            .expect("synthetic trust_vc_path should be tracked in HEAD");
        write_synthetic_replacement_manifest(
            &crate_root,
            &verus_ref,
            trust_vc_path,
            case_id,
            &source_hash,
            &fingerprints,
        );
        assume_unchanged_for_synthetic_evidence(
            &crate_root,
            &["Cargo.toml", "Cargo.lock", "evals/verus/verus-tests.json"],
        );
        assert_eq!(
            git_dirty(&crate_root),
            Some(false),
            "synthetic repo must be clean before proven evidence run"
        );

        let child_exe = copy_current_test_binary_under_repo_target(&crate_root);
        let output_dir = temp_dir.join("evidence-output");
        let mut command = std::process::Command::new(&child_exe);
        command
            .arg("replacement_evidence_synthetic_success_child")
            .arg("--nocapture")
            .env(SYNTHETIC_PROVEN_CHILD_ENV, "1")
            .env(SYNTHETIC_PROVEN_CRATE_ROOT_ENV, &crate_root)
            .env(SYNTHETIC_PROVEN_VERUS_ROOT_ENV, &verus_root)
            .env(SYNTHETIC_PROVEN_CARGO_ENV, &fake_cargo)
            .env(SYNTHETIC_PROVEN_OUTPUT_DIR_ENV, &output_dir);
        for key in [
            "RUSTC_WRAPPER",
            "RUSTFLAGS",
            "CARGO_ENCODED_RUSTFLAGS",
            "DYLD_INSERT_LIBRARIES",
            "LD_PRELOAD",
        ] {
            command.env_remove(key);
        }
        let output = command
            .output()
            .expect("synthetic child test process should run");
        let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        fs::remove_dir_all(&temp_dir).ok();
        assert!(
            output.status.success(),
            "synthetic proven child test failed with {:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
            output.status.code()
        );
    }

    #[cfg(unix)]
    #[test]
    fn replacement_evidence_synthetic_success_child() {
        if std::env::var_os(SYNTHETIC_PROVEN_CHILD_ENV).is_none() {
            return;
        }
        let crate_root = env_path(SYNTHETIC_PROVEN_CRATE_ROOT_ENV);
        let verus_root = env_path(SYNTHETIC_PROVEN_VERUS_ROOT_ENV);
        let fake_cargo = env_path(SYNTHETIC_PROVEN_CARGO_ENV);
        let output_dir = env_path(SYNTHETIC_PROVEN_OUTPUT_DIR_ENV);
        let manifest_path = crate_root.join("evals/verus/verus-tests.json");
        let args = EvidenceArgs {
            crate_root: crate_root.clone(),
            output_dir: output_dir.clone(),
            port_output_dir: crate_root.join("evals/verus/ported"),
            verus_path: Some(verus_root),
            verus_rev: None,
            manifest_path: Some(manifest_path.clone()),
            canonical_manifest_path: manifest_path,
            strict: true,
            json: true,
            markdown: false,
            run_trust_vc: true,
            cargo_command: fake_cargo.to_string_lossy().into_owned(),
            cargo_command_overridden: false,
            run_trust_vc_corpus: true,
            trust_vc_corpus_command: None,
            run_verus: true,
            port_manifest_only: false,
            update_verus_tests_manifest: false,
            refresh_trust_vc_corpus_evidence: false,
            corpus_triage_report: false,
            scaffold_verus_port_stubs: false,
            verus_command: None,
        };

        let report = run_evidence(&args).expect("synthetic proven evidence should run");
        let failed_required = report
            .gates
            .iter()
            .filter(|gate| gate.required && gate.status != GateStatus::Passed)
            .map(|gate| {
                format!(
                    "{}: {:?}; command={:?}",
                    gate.name, gate.detail, gate.command
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            report.replacement_verdict,
            ReplacementVerdict::Proven,
            "synthetic evidence should prove replacement; blocking={:?}; failed_required={:?}",
            report.blocking_reasons,
            failed_required
        );
        assert!(
            report.blocking_reasons.is_empty(),
            "proven synthetic evidence must not carry blockers: {:?}",
            report.blocking_reasons
        );
        let json = fs::read_to_string(output_dir.join("replacement-evidence.json"))
            .expect("synthetic evidence JSON should be written");
        let parsed: serde_json::Value =
            serde_json::from_str(&json).expect("synthetic evidence JSON should parse");
        assert_eq!(parsed["replacement_verdict"], "proven");
    }

    #[cfg(unix)]
    fn cargo_trust_vc_repo_root() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("cargo-trust-vc should live under crates/")
            .to_path_buf()
    }

    #[cfg(unix)]
    fn env_path(key: &str) -> PathBuf {
        std::env::var_os(key)
            .map(PathBuf::from)
            .unwrap_or_else(|| panic!("{key} must be set for synthetic proven child test"))
    }

    #[cfg(unix)]
    fn copy_current_test_binary_under_repo_target(crate_root: &Path) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;

        let current = std::env::current_exe().expect("current test binary should be available");
        let file_name = current
            .file_name()
            .expect("current test binary should have a file name");
        let target_dir = crate_root.join("target/debug/deps");
        fs::create_dir_all(&target_dir).expect("synthetic target dir should be created");
        let copied = target_dir.join(file_name);
        fs::copy(&current, &copied).expect("current test binary should copy into synthetic target");
        let mut permissions = fs::metadata(&copied)
            .expect("copied test binary metadata should be readable")
            .permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(&copied, permissions).expect("copied test binary should be runnable");
        copied
    }

    #[cfg(unix)]
    fn write_synthetic_verus_checkout(verus_root: &Path) -> String {
        let upstream_tests = verus_root.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("synthetic upstream test dir should exist");
        fs::create_dir_all(verus_root.join(VERUS_CARGO_VERUS_TEST_ROOT))
            .expect("synthetic cargo-verus test root should exist");
        fs::create_dir_all(verus_root.join("source/tools"))
            .expect("synthetic source tools dir should exist");
        fs::create_dir_all(verus_root.join("tools")).expect("synthetic tools dir should exist");
        fs::create_dir_all(verus_root.join("fake-bin"))
            .expect("synthetic fake bin dir should exist");
        fs::write(
            upstream_tests.join("synthetic.rs"),
            r#"
test_verify_one_file! {
    #[test] struct_update_copies_omitted_fields verus_code! {
        fn struct_update_copies_omitted_fields() {}
    } => Ok(())
}
"#,
        )
        .expect("synthetic upstream test should be written");
        write_executable(
            &verus_root.join("source/tools/get-z3.sh"),
            "#!/bin/sh\nexit 0\n",
        );
        fs::write(
            verus_root.join("tools/activate"),
            r#"activate_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/../fake-bin" && pwd)"
export PATH="$activate_dir:$PATH"
"#,
        )
        .expect("synthetic activate script should be written");
        write_executable(&verus_root.join("fake-bin/vargo"), "#!/bin/sh\nexit 0\n");
        init_git_repo(verus_root);
        git_commit_all(verus_root, "synthetic Verus replacement corpus")
    }

    #[cfg(unix)]
    fn rewrite_synthetic_ay_pins(crate_root: &Path, latest_ay: &str) {
        let cargo_toml = crate_root.join("Cargo.toml");
        let old_pin = common_ay_pin(&parse_ay_pins(&cargo_toml))
            .expect("root Cargo.toml should have a common ay pin");
        let text = fs::read_to_string(&cargo_toml).expect("Cargo.toml should be readable");
        let mut rewritten = text
            .lines()
            .map(|line| {
                let trimmed = line.trim_start();
                if let Some(crate_name) = REQUIRED_AY_CRATES
                    .iter()
                    .find(|crate_name| trimmed.starts_with(&format!("{crate_name} =")))
                {
                    format!("{crate_name} = {{ git = \"{AY_REPO_URL}\", rev = \"{latest_ay}\" }}")
                } else {
                    line.to_string()
                }
            })
            .collect::<Vec<_>>()
            .join("\n");
        rewritten.push('\n');
        fs::write(&cargo_toml, rewritten).expect("synthetic Cargo.toml should be rewritten");

        let cargo_lock = crate_root.join("Cargo.lock");
        let lock_text = fs::read_to_string(&cargo_lock).expect("Cargo.lock should be readable");
        fs::write(&cargo_lock, lock_text.replace(&old_pin, latest_ay))
            .expect("synthetic Cargo.lock should be rewritten");
    }

    #[cfg(unix)]
    fn write_synthetic_replacement_manifest(
        crate_root: &Path,
        verus_ref: &str,
        trust_vc_path: &str,
        case_id: &str,
        source_hash: &str,
        fingerprints: &[String],
    ) {
        let manifest = serde_json::json!({
            "schema_version": 2,
            "manifest_id": "upstream-verus-corpus",
            "description": "Synthetic proven replacement evidence corpus.",
            "upstream": {
                "repo": VERUS_REPO_URL,
                "ref": verus_ref,
                "test_roots": [VERUS_TEST_ROOT, VERUS_CARGO_VERUS_TEST_ROOT],
            },
            "gate": {
                "missing_entry": "fail",
                "failing_classifications": ["unclassified", "unsupported-gap"],
            },
            "entries": [
                {
                    "upstream_path": format!("{VERUS_TEST_ROOT}/synthetic.rs"),
                    "classification": "ported",
                    "owner_issue": "#123",
                    "reason": "Synthetic positive replacement-evidence success path.",
                    "trust_vc_paths": [trust_vc_path],
                    "trust_vc_source_hashes": [
                        {
                            "path": trust_vc_path,
                            "kind": "file",
                            "sha256": source_hash,
                        }
                    ],
                    "expected_cases": [
                        {
                            "case_id": case_id,
                            "expected_verdict": "verified",
                            "min_obligations": fingerprints.len(),
                            "obligation_fingerprints": fingerprints,
                        }
                    ],
                }
            ],
        });
        let manifest_path = crate_root.join("evals/verus/verus-tests.json");
        fs::write(
            &manifest_path,
            format!(
                "{}\n",
                serde_json::to_string_pretty(&manifest)
                    .expect("synthetic manifest should serialize")
            ),
        )
        .expect("synthetic manifest should be written");
    }

    #[cfg(unix)]
    fn assume_unchanged_for_synthetic_evidence(crate_root: &Path, paths: &[&str]) {
        let mut args = vec!["update-index", "--assume-unchanged", "--"];
        args.extend(paths.iter().copied());
        let result = run_command(crate_root, DEFAULT_GIT_COMMAND, &args);
        assert_eq!(
            result.exit_code,
            Some(0),
            "synthetic worktree paths should be hidden from git status: {}",
            result.stderr_tail
        );
    }

    fn write_expected_error_cargo_fixture(temp_dir: &Path, fixture_rel: &str) -> PathBuf {
        let upstream_tests = temp_dir
            .join(VERUS_TEST_ROOT)
            .join("cargo-tests/errors/borrow/src");
        let fixture_root = temp_dir.join(fixture_rel);
        fs::create_dir_all(&upstream_tests).expect("upstream fixture dir should be created");
        fs::create_dir_all(fixture_root.join("src")).expect("ported fixture dir should be created");
        fs::write(upstream_tests.join("lib.rs"), "").expect("upstream test should be written");
        fs::write(
            fixture_root.join("Cargo.toml"),
            r#"[package]
name = "borrow-error-fixture"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("fixture Cargo.toml should be written");
        fs::write(fixture_root.join("Cargo.lock"), "version = 4\n")
            .expect("fixture Cargo.lock should be written");
        fs::write(
            fixture_root.join("src/lib.rs"),
            r#"
pub fn test_regression_70() {
    let mut values = vec![1];
    let first = &values[0];
    values.push(2);
    let _ = *first;
}
"#,
        )
        .expect("fixture source should be written");

        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            format!(
                r##"{{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {{
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  }},
  "gate": {{
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  }},
  "entries": [
    {{
      "upstream_path": "source/rust_verify_test/tests/cargo-tests/errors/borrow/src/lib.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported expected Rust compiler-error case for TrustVc.",
      "trust_vc_paths": ["{fixture_rel}"],
      "expected_cases": [
        {{
          "case_id": "test_regression_70",
          "expected_verdict": "error",
          "min_obligations": 0,
          "expected_error_patterns": ["cannot borrow `values` as mutable"]
        }}
      ]
    }}
  ]
}}"##
            ),
        )
        .expect("manifest should be written");
        manifest_path
    }

    fn write_exact_rust_diagnostic_set_cargo_fixture(
        temp_dir: &Path,
        fixture_rel: &str,
    ) -> PathBuf {
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        let fixture_root = temp_dir.join(fixture_rel);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(fixture_root.join("src")).expect("ported fixture dir should be created");
        fs::write(
            upstream_tests.join("functions.rs"),
            r#"
test_verify_one_file! {
    #[test] test_non_async_opaque_types_disallowed verus_code! {
        type OT = impl Foo;
    } => Err(err) => {
        assert!(err.errors.iter().find(|p| p.message == "`impl Trait` in type aliases is unstable").is_some());
    }
}
"#,
        )
        .expect("upstream functions test should be written");
        fs::write(
            fixture_root.join("Cargo.toml"),
            r#"[package]
name = "opaque-type-error-fixture"
version = "0.1.0"
edition = "2021"

[workspace]
"#,
        )
        .expect("fixture Cargo.toml should be written");
        fs::write(fixture_root.join("Cargo.lock"), "version = 4\n")
            .expect("fixture Cargo.lock should be written");
        fs::write(
            fixture_root.join("src/lib.rs"),
            r#"
trait FunctionsOpaqueFoo {
    fn bar(&self) -> bool;
}

type OT = impl FunctionsOpaqueFoo;
"#,
        )
        .expect("fixture source should be written");

        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            format!(
                r##"{{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {{
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  }},
  "gate": {{
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  }},
  "entries": [
    {{
      "upstream_path": "source/rust_verify_test/tests/functions.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported expected Rust compiler diagnostic set for TrustVc.",
      "trust_vc_paths": ["{fixture_rel}"],
      "expected_cases": [
        {{
          "case_id": "test_non_async_opaque_types_disallowed",
          "expected_verdict": "error",
          "min_obligations": 0,
          "expected_error_patterns": ["`impl Trait` in type aliases is unstable"],
          "expected_rust_diagnostic_pattern_sets": [
            ["`impl Trait` in type aliases is unstable"],
            ["unconstrained opaque type"]
          ]
        }}
      ]
    }}
  ]
}}"##
            ),
        )
        .expect("manifest should be written");
        manifest_path
    }

    fn corpus_for_typecheck(candidate: TrustVcCorpusRunCandidate) -> VerusCorpusReport {
        VerusCorpusReport {
            manifest_path: PathBuf::from("verus-tests.json"),
            manifest_schema_version: 1,
            upstream_repo: None,
            upstream_ref: None,
            upstream_test_roots: Vec::new(),
            upstream_test_count: 1,
            entry_count: 1,
            classification_counts: BTreeMap::new(),
            replacement_summary: VerusReplacementSummary::default(),
            duplicate_entries: Vec::new(),
            invalid_entries: Vec::new(),
            missing_entries: Vec::new(),
            extra_entries: Vec::new(),
            unsupported_entries: Vec::new(),
            failing_entries: Vec::new(),
            port_path_failures: Vec::new(),
            upstream_case_failures: Vec::new(),
            ignored_upstream_cases: Vec::new(),
            upstream_case_extraction_gaps: Vec::new(),
            porting_next_action: None,
            accepted_executable_ports: Vec::new(),
            unsupported_gap_evidence: Vec::new(),
            accepted_trust_vc_source_hashes: Vec::new(),
            run_candidates: vec![candidate],
        }
    }

    #[test]
    fn corpus_manifest_gate_detail_names_actionable_blockers() {
        let mut corpus = corpus_for_typecheck(TrustVcCorpusRunCandidate {
            upstream_path: "source/rust_verify_test/tests/foo.rs".to_string(),
            classification: "ported".to_string(),
            evidence_kind: VerusEvidenceKind::ProofObligation,
            trust_vc_paths: vec!["evals/verus/ported/foo.rs".to_string()],
            trust_vc_check_args: Vec::new(),
            expected_cases: Vec::new(),
        });
        corpus.unsupported_entries = vec![
            "source/rust_verify_test/tests/unsupported.rs: owner=#2780, reason=missing choose tuple lowering"
                .to_string(),
        ];
        corpus.failing_entries = vec![
            "source/rust_verify_test/tests/unclassified.rs: classification=unclassified, owner=TBD, reason=Pending classification"
                .to_string(),
        ];
        corpus.port_path_failures = vec![
            "source/rust_verify_test/tests/ported.rs: accepted executable entry has no expected_cases"
                .to_string(),
        ];

        let detail = verus_corpus_manifest_gate_detail(&corpus);

        assert!(detail.contains("1 unsupported"));
        assert!(detail.contains("blockers:"));
        assert!(
            detail.contains(
                "unsupported: source/rust_verify_test/tests/unsupported.rs: owner=#2780, reason=missing choose tuple lowering"
            ),
            "unsupported blocker should name owner and reason: {detail}"
        );
        assert!(
            detail.contains("failing classifications: source/rust_verify_test/tests/unclassified.rs: classification=unclassified, owner=TBD"),
            "failing classification blocker should include owner: {detail}"
        );
        assert!(
            detail.contains("port path failures: source/rust_verify_test/tests/ported.rs"),
            "port path blocker should be surfaced: {detail}"
        );
    }

    #[test]
    fn canonical_manifest_schema_blocker_rejects_schema_v1_for_replacement() {
        let mut corpus = corpus_for_typecheck(TrustVcCorpusRunCandidate {
            upstream_path: "source/rust_verify_test/tests/foo.rs".to_string(),
            classification: "ported".to_string(),
            evidence_kind: VerusEvidenceKind::ProofObligation,
            trust_vc_paths: vec!["evals/verus/ported/foo.rs".to_string()],
            trust_vc_check_args: Vec::new(),
            expected_cases: Vec::new(),
        });

        let reason = canonical_manifest_schema_blocking_reason(Some(&corpus), true)
            .expect("canonical schema v1 corpus should block replacement");
        assert!(
            reason.contains("schema_version 2") && reason.contains("got 1"),
            "unexpected schema blocker: {reason}"
        );
        assert!(
            canonical_manifest_schema_blocking_reason(Some(&corpus), false).is_none(),
            "non-canonical migration manifests should be handled by the canonical-manifest blocker"
        );

        corpus.manifest_schema_version = 2;
        assert!(
            canonical_manifest_schema_blocking_reason(Some(&corpus), true).is_none(),
            "canonical schema v2 corpus should not add a schema blocker"
        );
    }

    #[test]
    fn direct_source_typecheck_render_erases_trust_vc_proof_surface() {
        let rendered = render_direct_source_typecheck_lib(
            r#"
#[trust_vc::ensures(true)]
fn proof_surface(x: i32) -> i32 {
    trust_vc::assert!(x == x);
    trust_vc::assume_by!(x == x, {});
    trust_vc::assert_by_nonlinear!(x * x >= 0);
    trust_vc::calc! {
        (==)
        x;
        (==) { trust_vc::assume!(false); } x;
    };
    let _witness: i32 = trust_vc::choose!(|candidate: i32| candidate == x);
    x
}

trust_vc::extern_spec! {
    fn external_surface(x: i32) -> i32;
}
"#,
        )
        .expect("known TrustVc proof surface should normalize");

        assert!(
            !rendered.contains("trust_vc :: ensures")
                && !rendered.contains("trust_vc :: assert")
                && !rendered.contains("trust_vc :: calc"),
            "normalizer should erase proof-only TrustVc surface: {rendered}"
        );
        syn::parse_file(&rendered).expect("normalized source should still parse as Rust");

        let cargo_toml = render_direct_source_typecheck_cargo_toml(Path::new("/repo"));
        assert!(
            cargo_toml.contains("[workspace]"),
            "scratch crate must opt out of any parent workspace: {cargo_toml}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn direct_source_rust_typecheck_gate_rejects_uncompiled_executable_rust() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-direct-typecheck-fails");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(temp_dir.join("Cargo.lock"), "version = 4\n")
            .expect("root Cargo.lock should be written");
        fs::write(
            temp_dir.join("ported/foo.rs"),
            r#"
#[trust_vc::ensures(true)]
fn identity() {
    trust_vc::assert!(true);
    let _ = missing_helper();
}
"#,
        )
        .expect("ported source should be written");
        let fake_cargo = temp_dir.join("fake-cargo");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
cmd="$1"
manifest=""
while [ "$#" -gt 0 ]; do
  if [ "$1" = "--manifest-path" ]; then
    shift
    manifest="$1"
  fi
  shift || true
done
if [ -z "$manifest" ]; then
  echo "missing --manifest-path" >&2
  exit 64
fi
if [ "$cmd" = "generate-lockfile" ]; then
  exit 0
fi
src_dir="$(dirname "$manifest")/src"
if grep -R "missing_helper" "$src_dir" >/dev/null; then
  echo '{"reason":"compiler-message","message":{"level":"error","message":"cannot find function `missing_helper` in this scope","spans":[]}}'
  exit 101
fi
exit 0
"#,
        );
        let corpus = corpus_for_typecheck(TrustVcCorpusRunCandidate {
            upstream_path: "source/rust_verify_test/tests/foo.rs".to_string(),
            classification: "ported".to_string(),
            evidence_kind: VerusEvidenceKind::ProofObligation,
            trust_vc_paths: vec!["ported/foo.rs".to_string()],
            trust_vc_check_args: Vec::new(),
            expected_cases: vec![VerusExpectedCase {
                case_id: "identity".to_string(),
                upstream_case_id: None,
                trust_vc_path: None,
                expected_verdict: VerusExpectedVerdict::Verified,
                min_obligations: 1,
                obligation_fingerprints: Vec::new(),
                expected_error_patterns: Vec::new(),
                expected_rust_diagnostic_pattern_sets: Vec::new(),
                forbidden_diagnostic_patterns: Vec::new(),
                expected_warning_patterns: Vec::new(),
            }],
        });
        let env = vec![
            ("CARGO".to_string(), fake_cargo.display().to_string()),
            (
                "CARGO_HOME".to_string(),
                temp_dir.join("isolated-cargo-home").display().to_string(),
            ),
        ];

        let gate =
            direct_source_rust_typecheck_gate(&temp_dir, &temp_dir.join("evidence"), &corpus, &env);

        assert_eq!(gate.status, GateStatus::Failed);
        assert!(
            gate.detail
                .as_deref()
                .is_some_and(|detail| detail.contains("cargo check failed")),
            "uncompiled executable Rust must block direct-source evidence: {:?}",
            gate.detail
        );
        assert!(gate.command.is_some());

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn direct_source_rust_typecheck_gate_does_not_run_for_cargo_fixture_paths() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-direct-typecheck-fixture");
        let fixture_root = temp_dir.join("ported/fixture");
        fs::create_dir_all(fixture_root.join("src")).expect("fixture dir should be created");
        fs::write(
            fixture_root.join("Cargo.toml"),
            r#"[package]
name = "fixture"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("fixture manifest should be written");
        fs::write(fixture_root.join("src/lib.rs"), "pub fn ok() {}\n")
            .expect("fixture source should be written");
        let fake_cargo = temp_dir.join("fake-cargo");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
echo "direct-source typecheck should not run for cargo fixtures" >&2
exit 88
"#,
        );
        let corpus = corpus_for_typecheck(TrustVcCorpusRunCandidate {
            upstream_path: "source/rust_verify_test/tests/foo.rs".to_string(),
            classification: "ported".to_string(),
            evidence_kind: VerusEvidenceKind::ProofObligation,
            trust_vc_paths: vec!["ported/fixture".to_string()],
            trust_vc_check_args: Vec::new(),
            expected_cases: vec![VerusExpectedCase {
                case_id: "ok".to_string(),
                upstream_case_id: None,
                trust_vc_path: None,
                expected_verdict: VerusExpectedVerdict::Verified,
                min_obligations: 1,
                obligation_fingerprints: Vec::new(),
                expected_error_patterns: Vec::new(),
                expected_rust_diagnostic_pattern_sets: Vec::new(),
                forbidden_diagnostic_patterns: Vec::new(),
                expected_warning_patterns: Vec::new(),
            }],
        });
        let env = vec![("CARGO".to_string(), fake_cargo.display().to_string())];

        let gate =
            direct_source_rust_typecheck_gate(&temp_dir, &temp_dir.join("evidence"), &corpus, &env);

        assert_eq!(gate.status, GateStatus::Passed);
        assert!(gate.command.is_none());
        assert!(
            gate.detail
                .as_deref()
                .is_some_and(|detail| detail.contains("0 direct-source")),
            "fixture-only corpus should skip direct-source cargo execution: {:?}",
            gate.detail
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn parse_rev_field_extracts_git_revision() {
        let line = r#"ay-core = { git = "https://github.com/alabsystems/ay", rev = "abc123" }"#;
        assert_eq!(parse_rev_field(line).as_deref(), Some("abc123"));
    }

    #[test]
    fn explicit_main_ref_parser_requires_one_exact_lowercase_sha_row() {
        let revision = "0123456789abcdef0123456789abcdef01234567";
        assert_eq!(
            parse_explicit_main_ref(&format!("{revision}\trefs/heads/main\n")).as_deref(),
            Some(revision)
        );

        for malformed in [
            "",
            "0123456789abcdef0123456789abcdef01234567\tHEAD\n",
            "0123456789abcdef0123456789abcdef01234567\trefs/heads/other\n",
            "0123456789abcdef0123456789abcdef0123456\trefs/heads/main\n",
            "0123456789ABCDEF0123456789ABCDEF01234567\trefs/heads/main\n",
            "ref: refs/heads/main\tHEAD\n",
            "warning: redirected\n0123456789abcdef0123456789abcdef01234567\trefs/heads/main\n",
            "0123456789abcdef0123456789abcdef01234567\trefs/heads/main\n89abcdef0123456789abcdef0123456789abcdef\trefs/heads/main\n",
            "0123456789abcdef0123456789abcdef01234567\trefs/heads/main\textra\n",
        ] {
            assert_eq!(
                parse_explicit_main_ref(malformed),
                None,
                "malformed ls-remote response must fail closed: {malformed:?}"
            );
        }
    }

    #[test]
    fn parse_ay_pins_requires_all_workspace_ay_crates() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-ay-pins");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");
        let cargo_toml = temp_dir.join("Cargo.toml");
        fs::write(
            &cargo_toml,
            r#"
ay-core = { git = "https://github.com/alabsystems/ay", rev = "abc123" }
ay-dpll = { git = "https://github.com/alabsystems/ay", rev = "abc123" }
ay-frontend = { git = "https://github.com/alabsystems/ay", rev = "abc123" }
ay-sys = { git = "https://github.com/alabsystems/ay", rev = "def456" }
"#,
        )
        .expect("Cargo.toml should be written");

        let pins = parse_ay_pins(&cargo_toml);
        let sources = parse_ay_sources(&cargo_toml);
        assert_eq!(pins["ay-core"].as_deref(), Some("abc123"));
        assert_eq!(pins["ay-sys"].as_deref(), Some("def456"));
        assert_eq!(
            sources["ay-core"].as_deref(),
            Some("https://github.com/alabsystems/ay")
        );
        assert_eq!(common_ay_pin(&pins), None);

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn git_rev_ay_model_preserves_common_pin_and_sources() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-ay-git-model");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");
        fs::write(
            temp_dir.join("Cargo.toml"),
            r#"
ay-core = { git = "https://github.com/alabsystems/ay", rev = "abc123" }
ay-dpll = { git = "https://github.com/alabsystems/ay", rev = "abc123" }
ay-frontend = { git = "https://github.com/alabsystems/ay", rev = "abc123" }
ay-sys = { git = "https://github.com/alabsystems/ay", rev = "abc123" }
"#,
        )
        .expect("Cargo.toml should be written");

        let provenance = collect_ay_manifest_provenance(&temp_dir);
        assert_eq!(provenance.source_model, AYSourceModel::GitRev);
        assert_eq!(provenance.pinned_rev.as_deref(), Some("abc123"));
        assert_eq!(
            provenance.pinned_sources["ay-core"].as_deref(),
            Some(AY_REPO_URL)
        );
        assert!(ay_latest_private_main_matches(&provenance, "abc123", false));
        assert!(!ay_latest_private_main_matches(&provenance, "abc123", true));

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn git_rev_with_committed_sibling_patch_preserves_and_agrees_both_authorities() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-ay-composed-model");
        let trust_vc_root = temp_dir.join("trust_vc");
        fs::create_dir_all(&trust_vc_root).expect("trust_vc dir should be created");
        let (ay_root, ay_head) = create_clean_origin_main_ay_sibling(&temp_dir);
        write_ay_git_manifest(&trust_vc_root, &ay_head);
        write_ay_patch_config(&trust_vc_root, "../ay");

        let provenance = collect_ay_manifest_provenance(&trust_vc_root);
        assert_eq!(
            provenance.source_model,
            AYSourceModel::GitRevWithVerifiedSiblingPath,
            "the normal Git-rev + committed-patch topology must not collapse to either authority"
        );
        assert_eq!(provenance.pinned_rev.as_deref(), Some(ay_head.as_str()));
        let identity = provenance
            .sibling_identity
            .as_ref()
            .expect("the active sibling patch must produce an independent identity");
        assert_eq!(identity.head, ay_head);
        assert_eq!(
            identity.repo_root,
            ay_root.canonicalize().expect("ay root should canonicalize")
        );
        assert!(identity.worktree_clean);
        assert!(!active_local_ay_patch_detected(
            &trust_vc_root,
            None,
            Some(&identity.repo_root)
        ));
        assert_eq!(
            ay_latest_private_main_gate_passes(&provenance, Some(&ay_head), false),
            Some(true)
        );
        assert_eq!(
            ay_latest_private_main_gate_passes(&provenance, Some("stale-public-head"), false),
            Some(false),
            "the sibling identity must not make a stale manifest/public pin pass"
        );

        let path_lock_entries = REQUIRED_AY_CRATES
            .iter()
            .map(|crate_name| AYLockSourceEntry {
                package_name: (*crate_name).to_string(),
                source: None,
            })
            .collect::<Vec<_>>();
        assert_eq!(
            ay_lock_provenance_gate(&provenance, &path_lock_entries).status,
            GateStatus::Passed,
            "source-less lock rows are authorized only by the verified sibling identity"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn git_rev_with_sibling_patch_rejects_clean_head_mismatch() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-ay-composed-head-mismatch");
        let trust_vc_root = temp_dir.join("trust_vc");
        fs::create_dir_all(&trust_vc_root).expect("trust_vc dir should be created");
        let (ay_root, manifest_head) = create_clean_origin_main_ay_sibling(&temp_dir);
        write_ay_git_manifest(&trust_vc_root, &manifest_head);
        write_ay_patch_config(&trust_vc_root, "../ay");

        fs::write(ay_root.join("ahead.txt"), "different compiled bytes\n")
            .expect("ahead file should be written");
        let compiled_head = git_commit_all(&ay_root, "different clean ay head");
        assert_ne!(compiled_head, manifest_head);

        let provenance = collect_ay_manifest_provenance(&trust_vc_root);
        assert_eq!(
            provenance.source_model,
            AYSourceModel::GitRevWithVerifiedSiblingPath
        );
        assert_eq!(
            provenance.pinned_rev.as_deref(),
            Some(manifest_head.as_str())
        );
        assert_eq!(
            provenance
                .sibling_identity
                .as_ref()
                .map(|identity| identity.head.as_str()),
            Some(compiled_head.as_str())
        );
        assert_eq!(
            ay_latest_private_main_gate_passes(&provenance, Some(&manifest_head), false),
            Some(false),
            "a clean but different compiled sibling must not inherit the manifest's authority"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn git_rev_with_sibling_patch_rejects_dirty_or_wrong_path() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-ay-composed-patch-tamper");
        let trust_vc_root = temp_dir.join("trust_vc");
        fs::create_dir_all(&trust_vc_root).expect("trust_vc dir should be created");
        let (ay_root, ay_head) = create_clean_origin_main_ay_sibling(&temp_dir);
        write_ay_git_manifest(&trust_vc_root, &ay_head);
        write_ay_patch_config(&trust_vc_root, "../ay");

        fs::write(ay_root.join("dirty.txt"), "uncommitted proof code\n")
            .expect("dirty file should be written");
        let dirty = collect_ay_manifest_provenance(&trust_vc_root);
        assert_eq!(dirty.source_model, AYSourceModel::GitRev);
        assert!(dirty.sibling_identity.is_none());
        assert!(active_local_ay_patch_detected(&trust_vc_root, None, None));
        assert_eq!(
            ay_latest_private_main_gate_passes(&dirty, Some(&ay_head), true),
            Some(false)
        );
        fs::remove_file(ay_root.join("dirty.txt")).expect("dirty file should be removed");

        let (_rogue_root, _rogue_head) =
            create_clean_origin_main_named_ay_sibling(&temp_dir, "rogue-ay");
        write_ay_patch_config(&trust_vc_root, "../rogue-ay");
        let wrong_path = collect_ay_manifest_provenance(&trust_vc_root);
        assert_eq!(wrong_path.source_model, AYSourceModel::GitRev);
        assert!(wrong_path.sibling_identity.is_none());
        assert!(active_local_ay_patch_detected(&trust_vc_root, None, None));
        assert_eq!(
            ay_latest_private_main_gate_passes(&wrong_path, Some(&ay_head), true),
            Some(false)
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn git_rev_with_sibling_patch_rejects_wrong_origin_or_missing_entry() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-ay-composed-incomplete");
        let trust_vc_root = temp_dir.join("trust_vc");
        fs::create_dir_all(&trust_vc_root).expect("trust_vc dir should be created");
        let (ay_root, ay_head) = create_clean_origin_main_ay_sibling(&temp_dir);
        write_ay_git_manifest(&trust_vc_root, &ay_head);
        write_ay_patch_config(&trust_vc_root, "../ay");

        let set_url = run_command(
            &ay_root,
            DEFAULT_GIT_COMMAND,
            &[
                "remote",
                "set-url",
                "origin",
                "https://attacker.invalid/ay.git",
            ],
        );
        assert_eq!(
            set_url.exit_code,
            Some(0),
            "remote tamper should succeed: {}",
            set_url.stderr_tail
        );
        let wrong_origin = collect_ay_manifest_provenance(&trust_vc_root);
        assert_eq!(wrong_origin.source_model, AYSourceModel::GitRev);
        assert!(wrong_origin.sibling_identity.is_none());
        assert!(active_local_ay_patch_detected(&trust_vc_root, None, None));
        assert_eq!(
            ay_latest_private_main_gate_passes(&wrong_origin, Some(&ay_head), true),
            Some(false)
        );

        let restore_url = run_command(
            &ay_root,
            DEFAULT_GIT_COMMAND,
            &["remote", "set-url", "origin", AY_REPO_URL],
        );
        assert_eq!(
            restore_url.exit_code,
            Some(0),
            "remote restore should succeed: {}",
            restore_url.stderr_tail
        );
        let config_path = trust_vc_root.join(".cargo/config.toml");
        let config = fs::read_to_string(&config_path).expect("patch config should be readable");
        let missing = config
            .lines()
            .filter(|line| !line.trim_start().starts_with("ay-sys ="))
            .collect::<Vec<_>>()
            .join("\n");
        fs::write(&config_path, format!("{missing}\n"))
            .expect("incomplete patch config should be written");
        let missing_entry = collect_ay_manifest_provenance(&trust_vc_root);
        assert_eq!(missing_entry.source_model, AYSourceModel::GitRev);
        assert!(missing_entry.sibling_identity.is_none());
        assert!(active_local_ay_patch_detected(&trust_vc_root, None, None));
        assert_eq!(
            ay_latest_private_main_gate_passes(&missing_entry, Some(&ay_head), true),
            Some(false)
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn git_rev_with_sibling_patch_rejects_duplicate_required_entry() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-ay-composed-duplicate");
        let trust_vc_root = temp_dir.join("trust_vc");
        fs::create_dir_all(&trust_vc_root).expect("trust_vc dir should be created");
        let (_ay_root, ay_head) = create_clean_origin_main_ay_sibling(&temp_dir);
        write_ay_git_manifest(&trust_vc_root, &ay_head);
        write_ay_patch_config(&trust_vc_root, "../ay");

        let config_path = trust_vc_root.join(".cargo/config.toml");
        let mut config = fs::read_to_string(&config_path).expect("patch config should be readable");
        config.push_str("ay-core = { path = \"../ay/crates/ay-core\" }\n");
        fs::write(&config_path, config).expect("duplicate patch entry should be written");

        let duplicate = collect_ay_manifest_provenance(&trust_vc_root);
        assert_eq!(duplicate.source_model, AYSourceModel::GitRev);
        assert!(duplicate.sibling_identity.is_none());
        assert!(active_local_ay_patch_detected(&trust_vc_root, None, None));
        assert_eq!(
            ay_latest_private_main_gate_passes(&duplicate, Some(&ay_head), true),
            Some(false)
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn git_rev_with_sibling_patch_rejects_extra_patch_outside_verified_repo() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-ay-composed-extra-patch");
        let trust_vc_root = temp_dir.join("trust_vc");
        fs::create_dir_all(&trust_vc_root).expect("trust_vc dir should be created");
        let (_ay_root, ay_head) = create_clean_origin_main_ay_sibling(&temp_dir);
        let (rogue_root, _) = create_clean_origin_main_named_ay_sibling(&temp_dir, "rogue-ay");
        fs::create_dir_all(rogue_root.join("crates/ay-proof"))
            .expect("rogue transitive crate dir should be created");
        write_ay_git_manifest(&trust_vc_root, &ay_head);
        write_ay_patch_config(&trust_vc_root, "../ay");
        let config_path = trust_vc_root.join(".cargo/config.toml");
        let mut config = fs::read_to_string(&config_path).expect("patch config should be readable");
        config.push_str("ay-proof = { path = \"../rogue-ay/crates/ay-proof\" }\n");
        fs::write(&config_path, config).expect("extra patch entry should be written");

        // The four required entries still produce a valid independent sibling
        // identity. The extra transitive replacement must nevertheless make
        // the local-patch gate fail; otherwise the positive path is vacuous.
        let provenance = collect_ay_manifest_provenance(&trust_vc_root);
        assert_eq!(
            provenance.source_model,
            AYSourceModel::GitRevWithVerifiedSiblingPath
        );
        let identity = provenance
            .sibling_identity
            .as_ref()
            .expect("required patch entries should still identify the canonical sibling");
        assert!(active_local_ay_patch_detected(
            &trust_vc_root,
            None,
            Some(&identity.repo_root)
        ));
        assert_eq!(
            ay_latest_private_main_gate_passes(&provenance, Some(&ay_head), true),
            Some(false)
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn sibling_path_ay_model_reports_clean_origin_main_head_as_pin() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-ay-sibling-model");
        let trust_vc_root = temp_dir.join("trust_vc");
        fs::create_dir_all(&trust_vc_root).expect("trust_vc dir should be created");
        write_ay_path_manifest(&trust_vc_root);
        let (ay_root, ay_head) = create_clean_origin_main_ay_sibling(&temp_dir);
        let canonical_ay_root = ay_root.canonicalize().expect("ay root should canonicalize");

        let provenance = collect_ay_manifest_provenance(&trust_vc_root);
        assert_eq!(provenance.source_model, AYSourceModel::VerifiedSiblingPath);
        assert_eq!(provenance.pinned_rev.as_deref(), Some(ay_head.as_str()));
        for crate_name in REQUIRED_AY_CRATES {
            assert_eq!(
                provenance.pinned_revs[*crate_name].as_deref(),
                Some(ay_head.as_str())
            );
            let source = provenance.pinned_sources[*crate_name]
                .as_deref()
                .expect("path source should be reported");
            assert!(
                source.contains(&format!("path:../ay/crates/{crate_name}")),
                "source should include dependency path: {source}"
            );
            assert!(
                source.contains("local git repo:"),
                "source should label local repo provenance: {source}"
            );
            assert!(
                source.contains(&canonical_ay_root.display().to_string()),
                "source should include local repo path: {source}"
            );
        }
        // The Path model passes the latest-pin gate on IDENTITY: a clean,
        // origin-verified sibling. The published HEAD here is reachable.
        let identity = provenance
            .sibling_identity
            .as_ref()
            .expect("path identity should be recorded");
        assert_eq!(identity.published, AYPublished::Reachable);
        assert!(identity.worktree_clean);
        assert!(ay_remote_url_matches(&identity.origin_url));
        assert_eq!(identity.repo_root, canonical_ay_root);
        // Gate passes on identity regardless of the live remote HEAD value.
        assert_eq!(
            ay_latest_private_main_gate_passes(&provenance, Some(&ay_head), false),
            Some(true)
        );
        assert_eq!(
            ay_latest_private_main_gate_passes(&provenance, Some("def456"), false),
            Some(true)
        );
        // Identity does not require the live remote at all.
        assert_eq!(
            ay_latest_private_main_gate_passes(&provenance, None, false),
            Some(true)
        );
        // An active *unsanctioned* local patch override still fails the gate.
        assert_eq!(
            ay_latest_private_main_gate_passes(&provenance, Some(&ay_head), true),
            Some(false)
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn sibling_path_ay_model_dirty_repo_degrades_to_unverified() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-ay-sibling-dirty");
        let trust_vc_root = temp_dir.join("trust_vc");
        fs::create_dir_all(&trust_vc_root).expect("trust_vc dir should be created");
        write_ay_path_manifest(&trust_vc_root);
        let (ay_root, _) = create_clean_origin_main_ay_sibling(&temp_dir);
        fs::write(ay_root.join("dirty.txt"), "dirty\n").expect("dirty file should be written");

        // A DIRTY sibling ay is not a faithful content commitment to the bytes
        // compiled, so it must still degrade to Unverified (no identity).
        let provenance = collect_ay_manifest_provenance(&trust_vc_root);
        assert_eq!(provenance.source_model, AYSourceModel::Unverified);
        assert_eq!(provenance.pinned_rev, None);
        assert!(provenance.sibling_identity.is_none());
        assert_eq!(
            provenance.pinned_sources["ay-core"].as_deref(),
            Some("path:../ay/crates/ay-core")
        );
        // Unverified never passes the latest-pin gate, on any remote.
        assert_eq!(
            ay_latest_private_main_gate_passes(&provenance, Some("anything"), false),
            Some(false)
        );
        assert_eq!(
            ay_latest_private_main_gate_passes(&provenance, None, false),
            None
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn sibling_path_ay_model_clean_but_ahead_yields_path_identity_local_only() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-ay-sibling-ahead");
        let trust_vc_root = temp_dir.join("trust_vc");
        fs::create_dir_all(&trust_vc_root).expect("trust_vc dir should be created");
        write_ay_path_manifest(&trust_vc_root);
        let (ay_root, origin_main) = create_clean_origin_main_ay_sibling(&temp_dir);
        fs::write(ay_root.join("ahead.txt"), "ahead\n").expect("ahead file should be written");
        let head = git_commit_all(&ay_root, "ay ahead");
        assert_ne!(head, origin_main);
        let canonical_ay_root = ay_root.canonicalize().expect("ay root should canonicalize");

        // A CLEAN sibling ay that is merely ahead of origin/main is a fully
        // knowable identity: the Path model now accepts it and records the HEAD
        // as the pin, classifying it LocalOnly (ahead, not yet published) rather
        // than degrading to Unverified.
        let provenance = collect_ay_manifest_provenance(&trust_vc_root);
        assert_eq!(provenance.source_model, AYSourceModel::VerifiedSiblingPath);
        assert_eq!(provenance.pinned_rev.as_deref(), Some(head.as_str()));
        let identity = provenance
            .sibling_identity
            .as_ref()
            .expect("clean-but-ahead sibling should yield a path identity");
        assert_eq!(identity.published, AYPublished::LocalOnly);
        assert!(identity.worktree_clean);
        assert!(ay_remote_url_matches(&identity.origin_url));
        assert_eq!(identity.repo_root, canonical_ay_root);
        // Identity passes the latest-pin gate without requiring publication.
        assert_eq!(
            ay_latest_private_main_gate_passes(&provenance, None, false),
            Some(true)
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn sibling_path_ay_model_descendant_of_origin_main_is_reachable() {
        // origin/main between the base and HEAD: HEAD is reachable from
        // origin/main only when origin/main *contains* HEAD. Here we advance
        // origin/main to contain a later HEAD to exercise the merge-base path.
        let temp_dir = unique_temp_dir("trust-vc-evidence-ay-sibling-reachable");
        let trust_vc_root = temp_dir.join("trust_vc");
        fs::create_dir_all(&trust_vc_root).expect("trust_vc dir should be created");
        write_ay_path_manifest(&trust_vc_root);
        let (ay_root, base) = create_clean_origin_main_ay_sibling(&temp_dir);
        // HEAD stays at `base`; advance origin/main to a descendant so that
        // origin/main contains HEAD via merge-base (ancestor) — Reachable.
        fs::write(ay_root.join("published.txt"), "published\n")
            .expect("published file should be written");
        let descendant = git_commit_all(&ay_root, "ay published descendant");
        // Move HEAD back to base (clean), leaving origin/main ahead.
        let reset = run_command(&ay_root, DEFAULT_GIT_COMMAND, &["reset", "--hard", &base]);
        assert_eq!(
            reset.exit_code,
            Some(0),
            "reset should succeed: {}",
            reset.stderr_tail
        );
        let update = run_command(
            &ay_root,
            DEFAULT_GIT_COMMAND,
            &["update-ref", "refs/remotes/origin/main", &descendant],
        );
        assert_eq!(
            update.exit_code,
            Some(0),
            "update-ref should succeed: {}",
            update.stderr_tail
        );

        let provenance = collect_ay_manifest_provenance(&trust_vc_root);
        assert_eq!(provenance.source_model, AYSourceModel::VerifiedSiblingPath);
        assert_eq!(provenance.pinned_rev.as_deref(), Some(base.as_str()));
        let identity = provenance
            .sibling_identity
            .as_ref()
            .expect("path identity should be recorded");
        assert_eq!(
            identity.published,
            AYPublished::Reachable,
            "HEAD contained by origin/main must classify Reachable"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn current_git_rev_and_patch_checkout_non_vacuously_agree() {
        // This repository cannot resolve its committed dependency graph without
        // the committed sibling patch, so a passing workspace test necessarily
        // has an available sibling. Assert the REAL checkout composition rather
        // than returning early merely because Cargo.toml carries Git revs (the
        // old test did exactly that and therefore never exercised this lane).
        let repo_root = cargo_trust_vc_repo_root();
        let provenance = collect_ay_manifest_provenance(&repo_root);
        assert_eq!(
            provenance.source_model,
            AYSourceModel::GitRevWithVerifiedSiblingPath,
            "the committed Git rev and active sibling patch must both be represented"
        );
        let identity = provenance
            .sibling_identity
            .as_ref()
            .expect("current checkout must record the compiled sibling identity");
        assert!(identity.worktree_clean);
        assert!(ay_remote_url_matches(&identity.origin_url));
        assert_eq!(
            provenance.pinned_rev.as_deref(),
            Some(identity.head.as_str())
        );

        assert!(!active_local_ay_patch_detected(
            &repo_root,
            None,
            Some(identity.repo_root.as_path())
        ));
        assert_eq!(
            ay_latest_private_main_gate_passes(&provenance, Some(&identity.head), false),
            Some(true),
            "current checkout must pass only because manifest, public expectation, and sibling agree"
        );
    }

    #[test]
    fn ay_lock_provenance_requires_locked_sources_to_match_pin() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-ay-lock");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");
        let cargo_lock = temp_dir.join("Cargo.lock");
        fs::write(
            &cargo_lock,
            r#"
[[package]]
name = "serde"
version = "1.0.0"
source = "registry+https://github.com/rust-lang/crates.io-index"

[[package]]
name = "ay-core"
version = "0.10.0"
source = "git+https://github.com/alabsystems/ay?rev=abc123#abc123"

[[package]]
name = "ay-dpll"
version = "0.10.0"
source = "git+https://github.com/alabsystems/ay?rev=abc123#def456"
"#,
        )
        .expect("Cargo.lock should be written");

        let sources = parse_ay_lock_sources(&cargo_lock);
        assert_eq!(
            sources
                .iter()
                .find(|entry| entry.package_name == "ay-core")
                .and_then(|entry| entry.source.as_deref()),
            Some("git+https://github.com/alabsystems/ay?rev=abc123#abc123")
        );
        let gate = ay_lock_provenance_gate(&test_git_ay_provenance("abc123"), &sources);
        assert_eq!(gate.status, GateStatus::Failed);
        assert!(
            gate.detail
                .as_deref()
                .is_some_and(|detail| detail.contains("ay-dpll source does not match pin")),
            "unexpected detail: {:?}",
            gate.detail
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn ay_lock_provenance_accepts_null_sources_only_for_verified_sibling_path() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-ay-lock-null-source");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");
        let cargo_lock = temp_dir.join("Cargo.lock");
        fs::write(
            &cargo_lock,
            r#"
[[package]]
name = "ay-core"
version = "0.10.0"
source = null

[[package]]
name = "ay-dpll"
version = "0.10.0"

[[package]]
name = "ay-frontend"
version = "0.10.0"
source = null

[[package]]
name = "ay-sys"
version = "0.10.0"
"#,
        )
        .expect("Cargo.lock should be written");

        let sources = parse_ay_lock_sources(&cargo_lock);
        assert!(sources.iter().all(|entry| entry.source.is_none()));

        let sibling_gate = ay_lock_provenance_gate(&test_sibling_ay_provenance("abc123"), &sources);
        assert_eq!(sibling_gate.status, GateStatus::Passed);
        assert!(
            sibling_gate
                .detail
                .as_deref()
                .is_some_and(|detail| detail.contains("verified sibling-path ay repo")),
            "unexpected detail: {:?}",
            sibling_gate.detail
        );

        let git_gate = ay_lock_provenance_gate(&test_git_ay_provenance("abc123"), &sources);
        assert_eq!(git_gate.status, GateStatus::Failed);
        assert!(
            git_gate
                .detail
                .as_deref()
                .is_some_and(|detail| detail.contains("has no Cargo.lock source")),
            "git-rev model must not accept local lock sources: {:?}",
            git_gate.detail
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn ay_lock_provenance_checks_duplicate_package_entries() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-ay-lock-duplicate");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");
        let cargo_lock = temp_dir.join("Cargo.lock");
        fs::write(
            &cargo_lock,
            r#"
[[package]]
name = "ay-core"
version = "0.10.0"
source = "git+https://github.com/alabsystems/ay?rev=abc123#abc123"

[[package]]
name = "ay-core"
version = "0.11.0"
source = "git+https://github.com/alabsystems/ay?rev=abc123#def456"

[[package]]
name = "ay-dpll"
version = "0.10.0"
source = "git+https://github.com/alabsystems/ay?rev=abc123#abc123"

[[package]]
name = "ay-frontend"
version = "0.10.0"
source = "git+https://github.com/alabsystems/ay?rev=abc123#abc123"

[[package]]
name = "ay-sys"
version = "0.10.0"
source = "git+https://github.com/alabsystems/ay?rev=abc123#abc123"
"#,
        )
        .expect("Cargo.lock should be written");

        let sources = parse_ay_lock_sources(&cargo_lock);
        assert_eq!(
            sources
                .iter()
                .filter(|entry| entry.package_name == "ay-core")
                .count(),
            2
        );
        let gate = ay_lock_provenance_gate(&test_git_ay_provenance("abc123"), &sources);
        assert_eq!(gate.status, GateStatus::Failed);
        assert!(
            gate.detail
                .as_deref()
                .is_some_and(|detail| detail.contains("ay-core source does not match pin")),
            "duplicate stale ay package entry should be checked: {:?}",
            gate.detail
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn cargo_lock_gate_requires_git_tracked_lockfile() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-cargo-lock-tracked");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");
        let init = run_command(&temp_dir, DEFAULT_GIT_COMMAND, &["init"]);
        assert_eq!(
            init.exit_code,
            Some(0),
            "git init failed: {}",
            init.stderr_tail
        );

        fs::write(temp_dir.join("Cargo.lock"), "").expect("Cargo.lock should be written");
        let untracked_gate = cargo_lock_tracked_gate(&temp_dir);
        assert_eq!(untracked_gate.status, GateStatus::Failed);

        let add = run_command(&temp_dir, DEFAULT_GIT_COMMAND, &["add", "Cargo.lock"]);
        assert_eq!(
            add.exit_code,
            Some(0),
            "git add failed: {}",
            add.stderr_tail
        );
        let tracked_gate = cargo_lock_tracked_gate(&temp_dir);
        assert_eq!(tracked_gate.status, GateStatus::Passed);

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn cargo_fixture_lockfile_gate_requires_tracked_fresh_locks() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-fixture-lock-tracked");
        let fixture_root = temp_dir.join("ported/fixture");
        fs::create_dir_all(fixture_root.join("src")).expect("fixture dir should be created");
        fs::write(
            fixture_root.join("Cargo.toml"),
            r#"[package]
name = "fixture"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("fixture Cargo.toml should be written");
        fs::write(fixture_root.join("src/lib.rs"), "").expect("fixture source should be written");
        fs::write(
            fixture_root.join("Cargo.lock"),
            r#"
version = 4

[[package]]
name = "ay-core"
version = "0.10.0"
source = "git+https://github.com/alabsystems/ay?rev=abc123#abc123"
"#,
        )
        .expect("fixture Cargo.lock should be written");
        let init = run_command(&temp_dir, DEFAULT_GIT_COMMAND, &["init"]);
        assert_eq!(init.exit_code, Some(0), "git init failed: {init:?}");

        let corpus = corpus_for_typecheck(TrustVcCorpusRunCandidate {
            upstream_path: "source/rust_verify_test/tests/cargo-tests/verified/basic/src/lib.rs"
                .to_string(),
            classification: "ported".to_string(),
            evidence_kind: VerusEvidenceKind::ProofObligation,
            trust_vc_paths: vec!["ported/fixture".to_string()],
            trust_vc_check_args: Vec::new(),
            expected_cases: vec![VerusExpectedCase {
                case_id: "fixture_ok".to_string(),
                upstream_case_id: None,
                trust_vc_path: None,
                expected_verdict: VerusExpectedVerdict::Verified,
                min_obligations: 1,
                obligation_fingerprints: Vec::new(),
                expected_error_patterns: Vec::new(),
                expected_rust_diagnostic_pattern_sets: Vec::new(),
                forbidden_diagnostic_patterns: Vec::new(),
                expected_warning_patterns: Vec::new(),
            }],
        });
        let untracked_gate =
            cargo_fixture_lockfile_gate(&temp_dir, &corpus, &test_git_ay_provenance("abc123"));
        assert_eq!(untracked_gate.status, GateStatus::Failed);
        assert!(
            untracked_gate
                .detail
                .as_deref()
                .is_some_and(|detail| detail.contains("must be tracked by git")),
            "fixture lockfiles must be tracked: {:?}",
            untracked_gate.detail
        );

        let add = run_command(
            &temp_dir,
            DEFAULT_GIT_COMMAND,
            &[
                "add",
                "ported/fixture/Cargo.toml",
                "ported/fixture/Cargo.lock",
            ],
        );
        assert_eq!(add.exit_code, Some(0), "git add failed: {add:?}");
        let tracked_gate =
            cargo_fixture_lockfile_gate(&temp_dir, &corpus, &test_git_ay_provenance("abc123"));
        assert_eq!(tracked_gate.status, GateStatus::Passed);

        let stale_gate =
            cargo_fixture_lockfile_gate(&temp_dir, &corpus, &test_git_ay_provenance("def456"));
        assert_eq!(stale_gate.status, GateStatus::Failed);
        assert!(
            stale_gate
                .detail
                .as_deref()
                .is_some_and(|detail| detail.contains("does not match root ay pin")),
            "fixture ay source must match root pin: {:?}",
            stale_gate.detail
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn cargo_fixture_lockfile_gate_summarizes_stale_ay_revs() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-fixture-lock-stale-summary");
        let fixture_root = temp_dir.join("ported/fixture");
        fs::create_dir_all(fixture_root.join("src")).expect("fixture dir should be created");
        fs::write(
            fixture_root.join("Cargo.toml"),
            r#"[package]
name = "fixture"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("fixture Cargo.toml should be written");
        fs::write(fixture_root.join("src/lib.rs"), "").expect("fixture source should be written");
        fs::write(
            fixture_root.join("Cargo.lock"),
            r#"
version = 4

[[package]]
name = "ay-core"
version = "0.10.0"
source = "git+https://github.com/alabsystems/ay?rev=abc123#abc123"

[[package]]
name = "ay-dpll"
version = "0.10.0"
source = "git+https://github.com/alabsystems/ay?rev=abc123#abc123"
"#,
        )
        .expect("fixture Cargo.lock should be written");
        let init = run_command(&temp_dir, DEFAULT_GIT_COMMAND, &["init"]);
        assert_eq!(init.exit_code, Some(0), "git init failed: {init:?}");
        let add = run_command(
            &temp_dir,
            DEFAULT_GIT_COMMAND,
            &[
                "add",
                "ported/fixture/Cargo.toml",
                "ported/fixture/Cargo.lock",
            ],
        );
        assert_eq!(add.exit_code, Some(0), "git add failed: {add:?}");

        let corpus = corpus_for_typecheck(TrustVcCorpusRunCandidate {
            upstream_path: "source/rust_verify_test/tests/cargo-tests/verified/basic/src/lib.rs"
                .to_string(),
            classification: "ported".to_string(),
            evidence_kind: VerusEvidenceKind::ProofObligation,
            trust_vc_paths: vec!["ported/fixture".to_string()],
            trust_vc_check_args: Vec::new(),
            expected_cases: vec![VerusExpectedCase {
                case_id: "fixture_ok".to_string(),
                upstream_case_id: None,
                trust_vc_path: None,
                expected_verdict: VerusExpectedVerdict::Verified,
                min_obligations: 1,
                obligation_fingerprints: Vec::new(),
                expected_error_patterns: Vec::new(),
                expected_rust_diagnostic_pattern_sets: Vec::new(),
                forbidden_diagnostic_patterns: Vec::new(),
                expected_warning_patterns: Vec::new(),
            }],
        });

        let gate =
            cargo_fixture_lockfile_gate(&temp_dir, &corpus, &test_git_ay_provenance("def456"));
        let detail = gate.detail.as_deref().unwrap_or_default();
        assert_eq!(gate.status, GateStatus::Failed);
        assert!(
            detail.contains("ported/fixture/Cargo.lock"),
            "fixture path should be reported: {detail}"
        );
        assert!(
            detail.contains("observed ay rev(s) abc123"),
            "stale rev should be summarized: {detail}"
        );
        assert!(
            !detail.contains("git+https://github.com/alabsystems/ay"),
            "raw package sources should not be dumped: {detail}"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn cargo_fixture_git_ay_sources_match_sibling_head_pin() {
        let lock_sources = test_ay_lock_source_entries("abc123");
        let lock_rel = Path::new("ported/fixture/Cargo.lock");
        assert_eq!(
            fixture_ay_lock_mismatch_detail(lock_rel, &lock_sources, "abc123", false),
            None
        );

        let mismatch = fixture_ay_lock_mismatch_detail(lock_rel, &lock_sources, "def456", false)
            .expect("stale fixture sources should be reported");
        assert!(
            mismatch.contains("observed ay rev(s) abc123"),
            "fixture git sources should be compared to sibling HEAD pin: {mismatch}"
        );
    }

    #[test]
    fn cargo_fixture_path_ay_sources_match_verified_sibling_path_model() {
        let lock_sources = REQUIRED_AY_CRATES
            .iter()
            .map(|crate_name| AYLockSourceEntry {
                package_name: (*crate_name).to_string(),
                source: None,
            })
            .collect::<Vec<_>>();
        let lock_rel = Path::new("ported/fixture/Cargo.lock");
        assert_eq!(
            fixture_ay_lock_mismatch_detail(lock_rel, &lock_sources, "abc123", true),
            None
        );

        let mismatch = fixture_ay_lock_mismatch_detail(lock_rel, &lock_sources, "abc123", false)
            .expect("git-rev model should reject path lock entries");
        assert!(
            mismatch.contains("missing source for ay-core"),
            "git-rev model should keep rejecting missing fixture sources: {mismatch}"
        );
    }

    #[test]
    fn cargo_fixture_lockfile_path_model_accepts_any_recorded_ay_source() {
        // Under the Path model the root [patch] redirects ay to ../ay regardless
        // of what a fixture's Cargo.lock records, so the fixture's frozen git+rev
        // ay source is irrelevant and must NOT fail the gate.
        let stale_git_sources = test_ay_lock_source_entries("12ff0250stale");
        let lock_rel = Path::new("ported/fixture/Cargo.lock");
        assert_eq!(
            fixture_ay_lock_mismatch_detail(lock_rel, &stale_git_sources, "abc123", true),
            None,
            "Path model must accept a fixture's frozen git+rev ay source"
        );

        // The same stale fixture git+rev source is rejected under the GitRev model.
        let mismatch =
            fixture_ay_lock_mismatch_detail(lock_rel, &stale_git_sources, "abc123", false)
                .expect("git-rev model should reject stale fixture git+rev sources");
        assert!(
            mismatch.contains("observed ay rev(s) 12ff0250stale"),
            "git-rev model should keep reporting stale fixture revs: {mismatch}"
        );

        // Mixed path + null sources are likewise accepted under the Path model.
        let mut mixed = stale_git_sources;
        mixed.push(AYLockSourceEntry {
            package_name: "ay-extra".to_string(),
            source: None,
        });
        assert_eq!(
            fixture_ay_lock_mismatch_detail(lock_rel, &mixed, "abc123", true),
            None
        );
    }

    #[test]
    fn evidence_output_gate_requires_ignored_or_external_output_path() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-output-isolated");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");
        let init = run_command(&temp_dir, DEFAULT_GIT_COMMAND, &["init"]);
        assert_eq!(
            init.exit_code,
            Some(0),
            "git init failed: {}",
            init.stderr_tail
        );

        let unignored_gate = evidence_output_isolated_gate(&temp_dir, &temp_dir.join("reports"));
        assert_eq!(unignored_gate.status, GateStatus::Failed);

        fs::write(temp_dir.join(".gitignore"), ".trust_vc/evidence/\n")
            .expect("gitignore should be written");
        let ignored_gate =
            evidence_output_isolated_gate(&temp_dir, &temp_dir.join(".trust_vc/evidence"));
        assert_eq!(ignored_gate.status, GateStatus::Passed);

        fs::write(
            temp_dir.join(".gitignore"),
            "reports/replacement-evidence.json\n",
        )
        .expect("partial gitignore should be written");
        let partially_ignored_gate =
            evidence_output_isolated_gate(&temp_dir, &temp_dir.join("reports"));
        assert_eq!(partially_ignored_gate.status, GateStatus::Failed);

        let external_gate = evidence_output_isolated_gate(&temp_dir, &std::env::temp_dir());
        assert_eq!(external_gate.status, GateStatus::Passed);

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn local_ay_patch_detection_ignores_comments_and_finds_active_path_patches() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-ay-patch");
        fs::create_dir_all(temp_dir.join(".cargo")).expect("config dir should be created");
        fs::write(
            temp_dir.join(".cargo/config.toml"),
            r#"
# [patch."https://github.com/alabsystems/ay"]
# ay-core = { path = "../ay/crates/ay-core" }
"#,
        )
        .expect("commented config should be written");
        assert!(!active_local_ay_patch_detected(&temp_dir, None, None));

        fs::write(
            temp_dir.join(".cargo/config.toml"),
            r#"
[patch."https://github.com/alabsystems/ay"]
ay-core = { path = "../ay/crates/ay-core" }
"#,
        )
        .expect("active config should be written");
        // With no verified `../ay` root established, an active ay path patch is
        // an unsanctioned override and must be flagged.
        assert!(active_local_ay_patch_detected(&temp_dir, None, None));

        fs::write(temp_dir.join(".cargo/config.toml"), "").expect("repo config should be cleared");
        let cargo_home = temp_dir.join("isolated-cargo-home");
        fs::create_dir_all(&cargo_home).expect("isolated cargo home should be created");
        fs::write(
            cargo_home.join("config.toml"),
            r#"
[patch."https://github.com/alabsystems/ay"]
ay-core = { path = "../ay/crates/ay-core" }
"#,
        )
        .expect("isolated cargo home ay config should be written");
        assert!(active_local_ay_patch_detected(
            &temp_dir,
            Some(&cargo_home),
            None
        ));

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn sanctioned_ay_patch_redirect_to_verified_root_is_not_detected() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-ay-patch-sanctioned");
        let trust_vc_root = temp_dir.join("trust_vc");
        fs::create_dir_all(&trust_vc_root).expect("trust_vc dir should be created");
        // Create the sibling ay repo so `../ay/crates/...` resolves on disk.
        for crate_name in REQUIRED_AY_CRATES {
            fs::create_dir_all(temp_dir.join("ay").join("crates").join(crate_name))
                .expect("ay crate dir should be created");
        }
        let verified_root = temp_dir
            .join("ay")
            .canonicalize()
            .expect("ay root should canonicalize");

        // A `[patch]` whose every ay entry redirects to the verified `../ay`
        // sibling root is the sanctioned dev redirect — NOT a disqualifier.
        fs::write(
            trust_vc_root.join("Cargo.toml"),
            r#"
[patch."https://github.com/alabsystems/ay.git"]
ay-core = { path = "../ay/crates/ay-core" }
ay-dpll = { path = "../ay/crates/ay-dpll" }
ay-frontend = { path = "../ay/crates/ay-frontend" }
ay-sys = { path = "../ay/crates/ay-sys" }
"#,
        )
        .expect("sanctioned patch manifest should be written");
        assert!(
            !active_local_ay_patch_detected(&trust_vc_root, None, Some(&verified_root)),
            "patch redirecting to the verified ../ay root must be sanctioned"
        );

        // The same patch is still flagged when no verified root is established.
        assert!(active_local_ay_patch_detected(&trust_vc_root, None, None));

        // A patch entry pointing OUTSIDE the verified root is never sanctioned,
        // even when a verified root exists.
        fs::create_dir_all(temp_dir.join("rogue-ay").join("crates").join("ay-core"))
            .expect("rogue ay crate dir should be created");
        fs::write(
            trust_vc_root.join("Cargo.toml"),
            r#"
[patch."https://github.com/alabsystems/ay.git"]
ay-core = { path = "../rogue-ay/crates/ay-core" }
"#,
        )
        .expect("rogue patch manifest should be written");
        assert!(
            active_local_ay_patch_detected(&trust_vc_root, None, Some(&verified_root)),
            "patch redirecting outside the verified ../ay root must be flagged"
        );

        // A git/rev-carrying patch entry is never sanctioned (ambiguous ay).
        fs::write(
            trust_vc_root.join("Cargo.toml"),
            r#"
[patch."https://github.com/alabsystems/ay.git"]
ay-core = { path = "../ay/crates/ay-core", git = "https://github.com/alabsystems/ay", rev = "deadbeef" }
"#,
        )
        .expect("mixed patch manifest should be written");
        assert!(active_local_ay_patch_detected(
            &trust_vc_root,
            None,
            Some(&verified_root)
        ));

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn seed_yaml_parser_extracts_manifest_entries() {
        let yaml = r#"
upstream:
  repo: https://github.com/verus-lang/verus
  ref: abc
  test_roots:
    - source/rust_verify_test/tests
gate:
  missing_entry: fail
  failing_classifications:
    - unclassified
entries:
  - upstream_path: source/rust_verify_test/tests/foo.rs
    classification: unclassified # inline comments must not change the class
    owner_issue: TBD
    reason: Pending classification.
"#;
        let manifest = parse_seed_yaml_manifest(yaml).expect("seed yaml should parse");
        assert_eq!(
            manifest.upstream_repo.as_deref(),
            Some("https://github.com/verus-lang/verus")
        );
        assert_eq!(manifest.upstream_ref.as_deref(), Some("abc"));
        assert_eq!(manifest.test_roots, vec!["source/rust_verify_test/tests"]);
        assert!(manifest.failing_classifications.contains("unclassified"));
        assert_eq!(manifest.entries.len(), 1);
        assert_eq!(manifest.entries[0].classification, "unclassified");
    }

    #[test]
    fn json_manifest_requires_schema_header_and_fail_closed_missing_entry() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-json-schema-required");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");
        let manifest_path = temp_dir.join("verus-tests.json");
        let base = minimal_valid_json_manifest();

        for (field, line) in [
            ("schema_version", "  \"schema_version\": 1,\n"),
            (
                "manifest_id",
                "  \"manifest_id\": \"upstream-verus-corpus\",\n",
            ),
            ("description", "  \"description\": \"Test manifest.\",\n"),
        ] {
            fs::write(&manifest_path, base.replace(line, "")).expect("manifest should be written");
            let err = load_manifest(&manifest_path).expect_err("required field should fail");
            assert!(
                err.to_string()
                    .contains(&format!("missing field `{field}`")),
                "unexpected error for missing {field}: {err}"
            );
        }

        fs::write(
            &manifest_path,
            base.replace("    \"missing_entry\": \"fail\",\n", ""),
        )
        .expect("manifest should be written");
        let err = load_manifest(&manifest_path).expect_err("missing_entry should be required");
        assert!(
            err.to_string().contains("missing field `missing_entry`"),
            "unexpected error: {err}"
        );

        fs::write(
            &manifest_path,
            base.replace(
                "    \"missing_entry\": \"fail\",",
                "    \"missing_entry\": \"warn\",",
            ),
        )
        .expect("manifest should be written");
        let err = load_manifest(&manifest_path).expect_err("weakened missing_entry should fail");
        assert!(
            err.to_string()
                .contains("gate.missing_entry must be `fail`"),
            "unexpected error: {err}"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn json_manifest_rejects_unknown_schema_fields_at_each_level() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-json-unknown-fields");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");
        let manifest_path = temp_dir.join("verus-tests.json");
        let base = minimal_valid_json_manifest();
        let cases = [
            (
                "top-level",
                base.replace("  \"entries\": [", "  \"unexpected\": true,\n  \"entries\": ["),
            ),
            (
                "upstream",
                base.replace(
                    "    \"test_roots\": [\"source/rust_verify_test/tests\"]",
                    "    \"test_roots\": [\"source/rust_verify_test/tests\"],\n    \"unexpected\": true",
                ),
            ),
            (
                "gate",
                base.replace(
                    "    \"failing_classifications\":",
                    "    \"unexpected\": true,\n    \"failing_classifications\":",
                ),
            ),
            (
                "entry",
                base.replace(
                    "      \"reason\": \"Ported for TrustVc.\",",
                    "      \"reason\": \"Ported for TrustVc.\",\n      \"unexpected\": true,",
                ),
            ),
            (
                "expected_case",
                base.replace(
                    "          \"min_obligations\": 1",
                    "          \"min_obligations\": 1,\n          \"unexpected\": true",
                ),
            ),
        ];

        for (level, manifest) in cases {
            fs::write(&manifest_path, manifest).expect("manifest should be written");
            let err = match load_manifest(&manifest_path) {
                Ok(_) => panic!("{level} unknown field should fail"),
                Err(err) => err,
            };
            assert!(
                err.to_string().contains("unknown field `unexpected`"),
                "unexpected error for {level}: {err}"
            );
        }

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn json_manifest_validates_owner_issue_format() {
        assert!(valid_owner_issue("TBD"));
        assert!(valid_owner_issue("#123"));
        assert!(valid_owner_issue("alabsystems/trust-vc#123"));
        assert!(valid_owner_issue(
            "https://github.com/alabsystems/trust-vc/issues/123"
        ));
        assert!(!valid_owner_issue(""));
        assert!(!valid_owner_issue("#abc"));
        assert!(!valid_owner_issue("alabsystems/trust-vc#abc"));
        assert!(!valid_owner_issue(
            "https://github.com/alabsystems/trust-vc/pull/123"
        ));
        assert!(!valid_owner_issue(
            "https://github.com/org/team/trust_vc/issues/123"
        ));
        assert!(!valid_owner_issue(
            "https://github.com/alabsystems/trust-vc/issues/not-a-number"
        ));

        let temp_dir = unique_temp_dir("trust-vc-evidence-json-owner-issue");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            minimal_valid_json_manifest().replace(
                "\"owner_issue\": \"#123\"",
                "\"owner_issue\": \"trust_vc#abc\"",
            ),
        )
        .expect("manifest should be written");
        let err = load_manifest(&manifest_path).expect_err("invalid owner_issue should fail");
        assert!(
            err.to_string().contains("owner_issue must be"),
            "unexpected error: {err}"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_triage_report_summarizes_manifest_without_gates() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-triage");
        fs::create_dir_all(temp_dir.join("evals/verus/ported"))
            .expect("ported dir should be created");
        fs::write(temp_dir.join("evals/verus/ported/present.rs"), "")
            .expect("present port should be written");
        let manifest_path = temp_dir.join("evals/verus/verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/root_missing.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported but missing mapped TrustVc path."
    },
    {
      "upstream_path": "source/rust_verify_test/tests/cargo-tests/verified/example/src/lib.rs",
      "classification": "unclassified",
      "owner_issue": "TBD",
      "reason": "Pending classification."
    },
    {
      "upstream_path": "source/rust_verify_test/tests/common/mod.rs",
      "classification": "not-applicable",
      "owner_issue": "#124",
      "reason": "Shared upstream helper."
    },
    {
      "upstream_path": "source/rust_verify_test/tests/cargo-tests/verified/ported/src/lib.rs",
      "classification": "ported",
      "owner_issue": "#125",
      "reason": "Ported for TrustVc.",
      "trust_vc_paths": [
        "evals/verus/ported/present.rs",
        "evals/verus/ported/missing.rs"
      ],
      "expected_cases": [
        {
          "case_id": "ported_case",
          "expected_verdict": "verified",
          "min_obligations": 1,
          "obligation_fingerprints": ["sha256:abc"]
        }
      ]
    },
    {
      "upstream_path": "source/rust_verify_test/tests/partial.rs",
      "classification": "unsupported-gap",
      "owner_issue": "#127",
      "reason": "Partial executable evidence only.",
      "trust_vc_paths": [
        "evals/verus/ported/present.rs"
      ],
      "expected_cases": [
        {
          "case_id": "partial_case",
          "expected_verdict": "verified",
          "min_obligations": 1,
          "obligation_fingerprints": ["sha256:def"]
        }
      ]
    },
    {
      "upstream_path": "source/rust_verify_test/tests/typo.rs",
      "classification": "ported-typo",
      "owner_issue": "#126",
      "reason": "Typo should be reported."
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let report = load_corpus_triage_report(&manifest_path, &temp_dir)
            .expect("triage report should load");

        assert_eq!(report.schema_version, 1);
        assert_eq!(report.manifest_schema_version, 1);
        assert_eq!(report.manifest_path, "evals/verus/verus-tests.json");
        assert_eq!(report.entry_count, 6);
        assert_eq!(report.classification_counts["ported"], 2);
        assert_eq!(report.classification_counts["unclassified"], 1);
        assert_eq!(report.replacement_summary.accepted_executable_entries, 2);
        assert_eq!(report.replacement_summary.accepted_trust_vc_path_count, 2);
        assert_eq!(report.replacement_summary.accepted_expected_case_count, 1);
        assert_eq!(report.replacement_summary.unsupported_gap_entries, 1);
        assert_eq!(report.unsupported_gap_evidence.len(), 1);
        assert_eq!(
            report.unsupported_gap_evidence[0].upstream_path,
            "source/rust_verify_test/tests/partial.rs"
        );
        assert_eq!(report.missing_trust_vc_paths.len(), 1);
        assert_eq!(
            report.missing_trust_vc_paths[0].upstream_path,
            "source/rust_verify_test/tests/root_missing.rs"
        );
        assert_eq!(report.missing_trust_vc_path_files.len(), 1);
        assert_eq!(
            report.missing_trust_vc_path_files[0].trust_vc_path,
            "evals/verus/ported/missing.rs"
        );
        assert_eq!(report.invalid_classification_entries.len(), 1);
        assert_eq!(
            report.invalid_classification_entries[0].classification,
            "ported-typo"
        );

        let bucket_names: Vec<_> = report
            .path_buckets
            .iter()
            .map(|bucket| bucket.bucket.as_str())
            .collect();
        assert_eq!(bucket_names, vec!["cargo-tests", "common", "root"]);
        let root_bucket = report
            .path_buckets
            .iter()
            .find(|bucket| bucket.bucket == "root")
            .expect("root bucket should exist");
        assert_eq!(root_bucket.entry_count, 3);
        assert_eq!(root_bucket.missing_trust_vc_paths, 1);

        let markdown = report.render_markdown();
        assert!(markdown.contains("# Verus Corpus Triage Report"));
        assert!(markdown.contains("| cargo-tests | 2 | 0 | 1 | ported=1, unclassified=1 |"));
        assert!(markdown.contains("source/rust_verify_test/tests/root_missing.rs"));
        assert!(markdown.contains("## Replacement Summary"));
        assert!(markdown.contains("- Accepted executable entries: `2`"));
        assert!(markdown.contains("- Unsupported gaps: `1`"));
        assert!(markdown.contains("### Unsupported Gap Partial Evidence"));
        assert!(markdown.contains("partial_case=>verified"));

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_rejects_accepted_entries_with_known_gaps() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-known-gaps");
        fs::create_dir_all(temp_dir.join(VERUS_TEST_ROOT)).expect("upstream dir should exist");
        fs::create_dir_all(temp_dir.join("evals/verus/ported")).expect("ported dir should exist");
        fs::write(temp_dir.join(VERUS_TEST_ROOT).join("foo.rs"), "")
            .expect("upstream test should be written");
        fs::write(temp_dir.join("evals/verus/ported/foo.rs"), "")
            .expect("ported test should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            minimal_valid_json_manifest().replace(
                "\"trust_vc_paths\": [\"evals/verus/ported/foo.rs\"]",
                "\"known_gaps\": [\"partial syntax coverage\"],\n      \"trust_vc_paths\": [\"evals/verus/ported/foo.rs\"]",
            ),
        )
        .expect("manifest should be written");

        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");

        assert!(
            report
                .failing_entries
                .iter()
                .any(|entry| entry.contains("known replacement gaps")),
            "known gaps should fail accepted entries: {:?}",
            report.failing_entries
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn verus_port_scaffold_creates_fail_closed_stubs_and_preserves_existing() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-port-scaffold");
        let crate_root = temp_dir.join("trust_vc");
        let output_dir = crate_root.join("evals/verus/ported");
        fs::create_dir_all(&output_dir).expect("ported dir should be created");
        fs::write(output_dir.join("existing.rs"), "// keep this real port\n")
            .expect("existing port should be written");
        fs::create_dir_all(crate_root.join("evals/verus")).expect("manifest dir should exist");
        let manifest_path = crate_root.join("evals/verus/verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "unsupported-gap",
      "owner_issue": "#123",
      "reason": "Needs a TrustVc port."
    },
    {
      "upstream_path": "source/rust_verify_test/tests/nested/bar.rs",
      "classification": "unclassified",
      "owner_issue": "TBD",
      "reason": "Pending classification."
    },
    {
      "upstream_path": "source/rust_verify_test/tests/existing.rs",
      "classification": "unsupported-gap",
      "owner_issue": "#124",
      "reason": "Existing scaffold must not be overwritten."
    },
    {
      "upstream_path": "source/rust_verify_test/tests/accepted.rs",
      "classification": "ported",
      "owner_issue": "#125",
      "reason": "Already accepted.",
      "trust_vc_paths": ["evals/verus/ported/accepted.rs"],
      "expected_cases": [
        {
          "case_id": "accepted",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let mut args = test_evidence_args(&crate_root, &temp_dir.join("verus"), Some("abc123"));
        args.update_verus_tests_manifest = false;
        args.port_manifest_only = false;
        args.scaffold_verus_port_stubs = true;
        let report = run_verus_port_scaffold(&args).expect("scaffold report should succeed");

        assert_eq!(report.manifest_path, "evals/verus/verus-tests.json");
        assert_eq!(report.output_dir, "evals/verus/ported");
        assert_eq!(report.created_count, 2);
        assert_eq!(report.existing_count, 1);
        assert_eq!(report.skipped_count, 1);
        assert_eq!(report.created[0].trust_vc_path, "evals/verus/ported/foo.rs");
        assert_eq!(
            report.created[1].trust_vc_path,
            "evals/verus/ported/nested/bar.rs"
        );
        assert_eq!(
            fs::read_to_string(output_dir.join("existing.rs"))
                .expect("existing port should be readable"),
            "// keep this real port\n"
        );

        let stub = fs::read_to_string(output_dir.join("foo.rs"))
            .expect("scaffolded stub should be readable");
        assert!(stub.contains("Auto-scaffolded fail-closed TrustVc port placeholder"));
        assert!(stub.contains("Upstream Verus test: source/rust_verify_test/tests/foo.rs"));
        assert!(stub.contains("intentionally contains no TrustVc-annotated functions"));
        let nested = fs::read_to_string(output_dir.join("nested/bar.rs"))
            .expect("nested scaffold should be readable");
        assert!(nested.contains("Current classification: unclassified"));

        let markdown = report.render_markdown();
        assert!(markdown.contains("# Verus Port Scaffold Report"));
        assert!(markdown.contains("| `source/rust_verify_test/tests/existing.rs` |"));

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn verus_port_scaffold_rejects_paths_that_escape_repo_or_output_dir() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-port-scaffold-rejects");
        let crate_root = temp_dir.join("trust_vc");
        fs::create_dir_all(crate_root.join("evals/verus")).expect("manifest dir should exist");
        let manifest_path = crate_root.join("evals/verus/verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/../escape.rs",
      "classification": "unsupported-gap",
      "owner_issue": "#123",
      "reason": "Malformed upstream path must not escape."
    }
  ]
}"##,
        )
        .expect("manifest should be written");
        let mut args = test_evidence_args(&crate_root, &temp_dir.join("verus"), Some("abc123"));
        args.update_verus_tests_manifest = false;
        args.port_manifest_only = false;
        args.scaffold_verus_port_stubs = true;
        let err = run_verus_port_scaffold(&args)
            .expect_err("parent components in upstream-derived path should fail");
        assert!(
            err.to_string()
                .contains("must stay inside the output directory"),
            "unexpected error: {err}"
        );

        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "unsupported-gap",
      "owner_issue": "#123",
      "reason": "Valid path with invalid output dir."
    }
  ]
}"##,
        )
        .expect("manifest should be rewritten");
        let outside_output = temp_dir.join("outside-ported");
        args.port_output_dir = outside_output.clone();
        let err =
            run_verus_port_scaffold(&args).expect_err("outside output dir should be rejected");
        assert!(
            err.to_string().contains("must stay inside the repo"),
            "unexpected error: {err}"
        );
        assert!(
            !outside_output.exists(),
            "outside output dir must not be created before rejection"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn verus_port_scaffold_rejects_symlinked_output_parent_before_creating_dirs() {
        use std::os::unix::fs as unix_fs;

        let temp_dir = unique_temp_dir("trust-vc-evidence-port-scaffold-symlink");
        let crate_root = temp_dir.join("trust_vc");
        let outside_root = temp_dir.join("outside");
        fs::create_dir_all(crate_root.join("evals/verus")).expect("manifest dir should exist");
        fs::create_dir_all(&outside_root).expect("outside dir should exist");
        let manifest_path = crate_root.join("evals/verus/verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "unsupported-gap",
      "owner_issue": "#123",
      "reason": "Valid path with symlinked output parent."
    }
  ]
}"##,
        )
        .expect("manifest should be written");
        let symlink_parent = crate_root.join("evals/verus/symlinked-ported");
        unix_fs::symlink(&outside_root, &symlink_parent).expect("symlink should be created");

        let mut args = test_evidence_args(&crate_root, &temp_dir.join("verus"), Some("abc123"));
        args.update_verus_tests_manifest = false;
        args.port_manifest_only = false;
        args.scaffold_verus_port_stubs = true;
        args.port_output_dir = symlink_parent.join("nested");
        let err = run_verus_port_scaffold(&args)
            .expect_err("symlinked output parent outside repo should be rejected");
        assert!(
            err.to_string().contains("must stay inside the repo"),
            "unexpected error: {err}"
        );
        assert!(
            !outside_root.join("nested").exists(),
            "scaffold must reject symlinked parents before creating outside dirs"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_fails_weakened_manifest_policy_and_unsupported_gaps() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus");
        let upstream_tests = temp_dir.join("source/rust_verify_test/tests");
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("foo test should be written");
        fs::write(upstream_tests.join("bar.rs"), "").expect("bar test should be written");
        init_git_repo(&temp_dir);
        git_commit_all(&temp_dir, "pin upstream tests");
        git_tag(&temp_dir, "abc123");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "unsupported-gap",
      "owner_issue": "#123",
      "reason": "Known unsupported Verus behavior."
    },
    {
      "upstream_path": "source/rust_verify_test/tests/bar.rs",
      "classification": "ported-typo",
      "owner_issue": "#124",
      "reason": "Typo must not pass as an accepted class."
    }
  ]
}"##,
        )
        .expect("manifest should be written");
        git_commit_all(&temp_dir, "track manifest");

        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        assert_eq!(report.upstream_test_count, 2);
        assert_eq!(report.unsupported_entries.len(), 1);
        assert!(
            report.unsupported_entries[0].contains("owner=#123")
                && report.unsupported_entries[0].contains("Known unsupported Verus behavior"),
            "unsupported entries should carry burn-down owner and reason: {:?}",
            report.unsupported_entries
        );
        let gate_detail = verus_corpus_manifest_gate_detail(&report);
        assert!(
            gate_detail.contains("blockers:")
                && gate_detail.contains("unsupported: source/rust_verify_test/tests/foo.rs"),
            "manifest gate detail should name unsupported blockers: {gate_detail}"
        );
        assert!(
            report
                .invalid_entries
                .iter()
                .any(|entry| entry.contains("unsupported-gap")),
            "weakened failing_classifications gate should be invalid: {:?}",
            report.invalid_entries
        );
        assert!(
            report
                .invalid_entries
                .iter()
                .any(|entry| entry.contains("ported-typo")),
            "classification typos should be invalid: {:?}",
            report.invalid_entries
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_summarizes_accepted_ports_versus_replacement_gaps() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-replacement-summary");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(upstream_tests.join("common"))
            .expect("upstream common dir should be created");
        fs::create_dir_all(temp_dir.join("evals/verus/ported"))
            .expect("ported dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("foo test should be written");
        fs::write(upstream_tests.join("gap.rs"), "").expect("gap test should be written");
        fs::write(upstream_tests.join("gap_partial.rs"), "")
            .expect("partial gap test should be written");
        fs::write(upstream_tests.join("pending.rs"), "").expect("pending test should be written");
        fs::write(upstream_tests.join("common/mod.rs"), "")
            .expect("common helper should be written");
        fs::write(temp_dir.join("evals/verus/ported/foo.rs"), "")
            .expect("ported foo should be written");
        fs::write(temp_dir.join("evals/verus/ported/foo_extra.rs"), "")
            .expect("ported foo extra should be written");
        fs::write(temp_dir.join("evals/verus/ported/gap_partial.rs"), "")
            .expect("partial gap port should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported for TrustVc.",
      "trust_vc_paths": [
        "evals/verus/ported/foo.rs",
        "evals/verus/ported/foo_extra.rs"
      ],
      "expected_cases": [
        {
          "case_id": "foo",
          "trust_vc_path": "evals/verus/ported/foo.rs",
          "expected_verdict": "verified",
          "min_obligations": 1
        },
        {
          "case_id": "foo_extra",
          "trust_vc_path": "evals/verus/ported/foo_extra.rs",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    },
    {
      "upstream_path": "source/rust_verify_test/tests/gap.rs",
      "classification": "unsupported-gap",
      "owner_issue": "#124",
      "reason": "Known unsupported replacement gap."
    },
    {
      "upstream_path": "source/rust_verify_test/tests/gap_partial.rs",
      "classification": "unsupported-gap",
      "owner_issue": "#126",
      "reason": "Known unsupported replacement gap with partial executable evidence.",
      "trust_vc_paths": ["evals/verus/ported/gap_partial.rs"],
      "expected_cases": [
        {
          "case_id": "gap_partial_smoke",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ],
      "known_gaps": ["remaining upstream behavior"]
    },
    {
      "upstream_path": "source/rust_verify_test/tests/pending.rs",
      "classification": "unclassified",
      "owner_issue": "TBD",
      "reason": "Pending triage."
    },
    {
      "upstream_path": "source/rust_verify_test/tests/common/mod.rs",
      "classification": "not-applicable",
      "owner_issue": "#125",
      "reason": "Shared upstream helper."
    }
  ]
}"##,
        )
        .expect("manifest should be written");
        init_git_repo(&temp_dir);
        git_commit_all(&temp_dir, "pin replacement summary fixture");
        git_tag(&temp_dir, "abc123");

        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");

        assert_eq!(report.replacement_summary.total_entries, 5);
        assert_eq!(report.replacement_summary.accepted_executable_entries, 1);
        assert_eq!(report.replacement_summary.accepted_trust_vc_path_count, 2);
        assert_eq!(report.replacement_summary.accepted_expected_case_count, 2);
        assert_eq!(report.replacement_summary.unsupported_gap_entries, 2);
        assert_eq!(report.replacement_summary.unclassified_entries, 1);
        assert_eq!(report.replacement_summary.not_applicable_entries, 1);
        assert_eq!(report.accepted_executable_ports.len(), 1);
        assert_eq!(
            report.accepted_executable_ports[0].owner_issue, "#123",
            "accepted ports should expose their owning issue"
        );
        assert_eq!(
            report.accepted_executable_ports[0]
                .owner_issue_url
                .as_deref(),
            Some("https://github.com/alabsystems/trust-vc/issues/123")
        );
        assert_eq!(report.accepted_executable_ports[0].expected_cases.len(), 2);
        assert_eq!(
            report.accepted_executable_ports[0].expected_cases[0]
                .trust_vc_path
                .as_deref(),
            Some("evals/verus/ported/foo.rs")
        );
        assert_eq!(report.unsupported_gap_evidence.len(), 1);
        assert_eq!(report.unsupported_gap_evidence[0].owner_issue, "#126");
        assert_eq!(
            report.unsupported_gap_evidence[0].reason,
            "Known unsupported replacement gap with partial executable evidence."
        );
        let action = report.porting_next_action.as_ref().expect(
            "unsupported/unclassified entries should produce an actionable porting command",
        );
        assert_eq!(action.blocking_entries, 3);
        assert_eq!(
            action.classifications,
            vec!["unclassified".to_string(), "unsupported-gap".to_string()]
        );
        assert_eq!(action.manifest_path, "verus-tests.json");
        assert!(
            action.command.contains("--scaffold-verus-port-stubs"),
            "porting action should point at scaffold mode: {action:?}"
        );
        assert!(
            action.command.contains("--manifest 'verus-tests.json'"),
            "porting action should name the manifest to burn down: {action:?}"
        );

        let gate_detail = verus_corpus_manifest_gate_detail(&report);
        assert!(
            gate_detail.contains("replacement summary: 1 accepted executable entries"),
            "gate detail should expose accepted executable coverage: {gate_detail}"
        );
        assert!(
            gate_detail.contains("2 accepted TrustVc path bindings"),
            "gate detail should expose accepted path coverage: {gate_detail}"
        );
        assert!(
            gate_detail.contains("2 unsupported gaps, 1 unclassified gaps"),
            "gate detail should expose blocking replacement gaps: {gate_detail}"
        );

        let evidence = test_evidence_report_with_corpus(report);
        let markdown = evidence.render_markdown();
        assert!(markdown.contains("### Replacement Summary"));
        assert!(markdown.contains("- Accepted executable entries: `1`"));
        assert!(markdown.contains("- Accepted TrustVc path bindings: `2`"));
        assert!(markdown.contains("- Unsupported gaps: `2`"));
        assert!(markdown.contains("### Accepted Executable Ports"));
        assert!(markdown.contains("[#123](https://github.com/alabsystems/trust-vc/issues/123)"));
        assert!(markdown.contains("foo=>verified (min_obligations=1"));
        assert!(markdown.contains("### Unsupported Gap Partial Evidence"));
        assert!(markdown
            .contains("Known unsupported replacement gap with partial executable evidence."));
        assert!(markdown.contains("### Verus Porting Next Action"));
        assert!(markdown.contains("--scaffold-verus-port-stubs"));
        assert!(markdown.contains("not replacement evidence"));

        let json = serde_json::to_value(&evidence).expect("evidence should serialize to JSON");
        assert_eq!(
            json["corpus"]["replacement_summary"]["accepted_executable_entries"],
            1
        );
        assert_eq!(
            json["corpus"]["replacement_summary"]["unsupported_gap_entries"],
            2
        );
        assert_eq!(
            json["corpus"]["accepted_executable_ports"][0]["owner_issue"],
            "#123"
        );
        assert_eq!(
            json["corpus"]["accepted_executable_ports"][0]["owner_issue_url"],
            "https://github.com/alabsystems/trust-vc/issues/123"
        );
        assert_eq!(
            json["corpus"]["accepted_executable_ports"][0]["expected_cases"][0]["trust_vc_path"],
            "evals/verus/ported/foo.rs"
        );
        assert_eq!(
            json["corpus"]["unsupported_gap_evidence"][0]["owner_issue"],
            "#126"
        );
        assert_eq!(json["corpus"]["porting_next_action"]["blocking_entries"], 3);
        assert_eq!(
            json["corpus"]["porting_next_action"]["command"],
            "cargo trust_vc evidence . --manifest 'verus-tests.json' --scaffold-verus-port-stubs"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_requires_canonical_repo_root_and_exact_inventory() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-inventory");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("foo test should be written");
        init_git_repo(&temp_dir);
        git_commit_all(&temp_dir, "pin upstream tests");
        git_tag(&temp_dir, "abc123");
        fs::write(temp_dir.join("ported/foo.rs"), "").expect("ported foo should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://example.invalid/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported for TrustVc.",
      "trust_vc_paths": ["ported/foo.rs"],
      "expected_cases": [
        {
          "case_id": "identity",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    },
    {
      "upstream_path": "source/rust_verify_test/tests/stale.rs",
      "classification": "not-applicable",
      "owner_issue": "#124",
      "reason": "Stale entry should fail exact inventory."
    }
  ]
}"##,
        )
        .expect("manifest should be written");
        git_commit_all(&temp_dir, "track manifest and port");

        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        assert_eq!(report.missing_entries.len(), 0);
        assert_eq!(
            report.extra_entries,
            vec!["source/rust_verify_test/tests/stale.rs"]
        );
        assert!(
            report
                .invalid_entries
                .iter()
                .any(|entry| entry.contains("upstream.repo")),
            "wrong upstream repo must be invalid: {:?}",
            report.invalid_entries
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_denominator_uses_manifest_ref_not_verus_worktree() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-pinned-denominator");
        let crate_root = temp_dir.join("trust_vc");
        let verus_root = temp_dir.join("verus");
        let upstream_tests = verus_root.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("foo test should be written");
        init_git_repo(&verus_root);
        let pinned_ref = git_commit_all(&verus_root, "pin upstream foo");
        fs::write(upstream_tests.join("bar.rs"), "")
            .expect("dirty worktree test should be written");

        fs::create_dir_all(crate_root.join("evals/verus/ported"))
            .expect("ported dir should be created");
        fs::write(crate_root.join("evals/verus/ported/foo.rs"), "")
            .expect("ported foo should be written");
        let manifest_path = crate_root.join("evals/verus/verus-tests.json");
        fs::write(
            &manifest_path,
            minimal_valid_json_manifest().replace("\"abc123\"", &format!("\"{pinned_ref}\"")),
        )
        .expect("manifest should be written");

        let report = load_corpus_report(&manifest_path, &crate_root, Some(&verus_root))
            .expect("corpus report should load");
        assert_eq!(report.upstream_test_count, 1);
        assert!(report.missing_entries.is_empty());
        assert!(report.extra_entries.is_empty());
        assert!(
            !report
                .invalid_entries
                .iter()
                .any(|entry| entry.contains("upstream inventory")),
            "pinned git inventory should be valid: {:?}",
            report.invalid_entries
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_fails_closed_when_upstream_ref_unresolvable() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-missing-upstream-ref");
        let crate_root = temp_dir.join("trust_vc");
        let verus_root = temp_dir.join("verus");
        fs::create_dir_all(crate_root.join("evals/verus/ported"))
            .expect("ported dir should be created");
        fs::write(crate_root.join("evals/verus/ported/foo.rs"), "")
            .expect("ported foo should be written");
        fs::create_dir_all(verus_root.join(VERUS_TEST_ROOT))
            .expect("upstream test dir should be created");
        init_git_repo(&verus_root);
        let manifest_path = crate_root.join("evals/verus/verus-tests.json");
        fs::write(&manifest_path, minimal_valid_json_manifest())
            .expect("manifest should be written");

        let report = load_corpus_report(&manifest_path, &crate_root, Some(&verus_root))
            .expect("corpus report should load");
        assert_eq!(report.upstream_test_count, 0);
        assert!(
            report
                .invalid_entries
                .iter()
                .any(|entry| entry.contains("upstream inventory") && entry.contains("abc123")),
            "unresolvable upstream ref must fail closed: {:?}",
            report.invalid_entries
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_schema_v2_requires_evidence_pins_for_accepted_entries() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-schema-v2-pins");
        let crate_root = temp_dir.join("trust_vc");
        let verus_root = temp_dir.join("verus");
        let upstream_tests = verus_root.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("foo test should be written");
        init_git_repo(&verus_root);
        let upstream_ref = git_commit_all(&verus_root, "pin upstream tests");

        fs::create_dir_all(crate_root.join("evals/verus/ported"))
            .expect("ported dir should be created");
        fs::write(crate_root.join("evals/verus/ported/foo.rs"), "alpha\n")
            .expect("ported foo should be written");
        let manifest_path = crate_root.join("evals/verus/verus-tests.json");
        fs::write(
            &manifest_path,
            minimal_valid_json_manifest()
                .replace("\"schema_version\": 1", "\"schema_version\": 2")
                .replace("\"abc123\"", &format!("\"{upstream_ref}\"")),
        )
        .expect("manifest should be written");

        let report = load_corpus_report(&manifest_path, &crate_root, Some(&verus_root))
            .expect("corpus report should load");
        assert!(
            report
                .port_path_failures
                .iter()
                .any(|failure| failure.contains("must pin trust_vc_source_hashes")),
            "schema v2 accepted entries must pin TrustVc source hashes: {:?}",
            report.port_path_failures
        );
        assert!(
            report
                .port_path_failures
                .iter()
                .any(|failure| failure.contains("must pin obligation_fingerprints")),
            "schema v2 accepted entries must pin obligation fingerprints: {:?}",
            report.port_path_failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_manifest_rejects_duplicate_expected_obligation_fingerprints() {
        let fingerprint =
            "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".to_string();
        let expected_case = VerusExpectedCase {
            case_id: "same_name".to_string(),
            upstream_case_id: None,
            trust_vc_path: Some("ported/right.rs".to_string()),
            expected_verdict: VerusExpectedVerdict::Verified,
            min_obligations: 2,
            obligation_fingerprints: vec![fingerprint.clone(), fingerprint],
            expected_error_patterns: Vec::new(),
            expected_rust_diagnostic_pattern_sets: Vec::new(),
            forbidden_diagnostic_patterns: Vec::new(),
            expected_warning_patterns: Vec::new(),
        };
        let entry = manifest_entry_for_expected_case(
            VerusEvidenceKind::ProofObligation,
            expected_case.clone(),
        );
        let mut failures = Vec::new();

        append_expected_case_obligation_pin_failures(
            &entry,
            &expected_case,
            true,
            false,
            &mut failures,
        );

        assert!(
            failures
                .iter()
                .any(|failure| failure.contains("duplicate obligation_fingerprints")),
            "duplicate manifest fingerprints must fail: {:?}",
            failures
        );
    }

    #[test]
    fn corpus_manifest_requires_pins_for_positive_error_obligations() {
        let expected_case = VerusExpectedCase {
            case_id: "same_name".to_string(),
            upstream_case_id: None,
            trust_vc_path: Some("ported/right.rs".to_string()),
            expected_verdict: VerusExpectedVerdict::Error,
            min_obligations: 1,
            obligation_fingerprints: Vec::new(),
            expected_error_patterns: Vec::new(),
            expected_rust_diagnostic_pattern_sets: Vec::new(),
            forbidden_diagnostic_patterns: Vec::new(),
            expected_warning_patterns: Vec::new(),
        };
        let entry = manifest_entry_for_expected_case(
            VerusEvidenceKind::ProofObligation,
            expected_case.clone(),
        );
        let mut failures = Vec::new();

        append_expected_case_obligation_pin_failures(
            &entry,
            &expected_case,
            true,
            false,
            &mut failures,
        );

        assert!(
            failures
                .iter()
                .any(|failure| failure.contains("must pin obligation_fingerprints")),
            "positive error obligations must still be pinned: {:?}",
            failures
        );
    }

    #[test]
    fn corpus_report_records_source_hashes_for_accepted_trust_vc_paths() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-source-hashes");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported/fixture/src"))
            .expect("ported fixture dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("foo test should be written");
        fs::write(upstream_tests.join("bar.rs"), "").expect("bar test should be written");
        fs::write(temp_dir.join("ported/foo.rs"), "alpha\n").expect("ported foo should be written");
        fs::write(temp_dir.join("ported/bar.rs"), "beta\n").expect("ported bar should be written");
        fs::write(temp_dir.join("ported/fixture/Cargo.toml"), "[package]\n")
            .expect("fixture manifest should be written");
        fs::write(temp_dir.join("ported/fixture/src/lib.rs"), "gamma\n")
            .expect("fixture source should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported for TrustVc.",
      "trust_vc_paths": ["ported/foo.rs", "ported/fixture"],
      "expected_cases": [
        {
          "case_id": "identity",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    },
    {
      "upstream_path": "source/rust_verify_test/tests/bar.rs",
      "classification": "unchanged",
      "owner_issue": "#124",
      "reason": "Runs unchanged under TrustVc.",
      "trust_vc_paths": ["ported/bar.rs"],
      "expected_cases": [
        {
          "case_id": "preserved",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let corpus = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");

        assert_eq!(corpus.accepted_trust_vc_source_hashes.len(), 2);
        let ported = &corpus.accepted_trust_vc_source_hashes[0];
        assert_eq!(ported.upstream_path, "source/rust_verify_test/tests/foo.rs");
        assert_eq!(ported.classification, "ported");
        assert_eq!(ported.trust_vc_paths.len(), 2);
        assert_eq!(ported.trust_vc_paths[0].path, "ported/foo.rs");
        assert_eq!(ported.trust_vc_paths[0].kind, TrustVcSourceHashKind::File);
        assert_eq!(
            ported.trust_vc_paths[0].sha256,
            "sha256:b6a98d9ce9a2d9149288fa3df42d377c3e42737afdcdaf714e33c0a100b51060"
        );
        assert_eq!(ported.trust_vc_paths[1].path, "ported/fixture");
        assert_eq!(
            ported.trust_vc_paths[1].kind,
            TrustVcSourceHashKind::Directory
        );
        assert!(is_sha256_digest(&ported.trust_vc_paths[1].sha256));

        let unchanged = &corpus.accepted_trust_vc_source_hashes[1];
        assert_eq!(unchanged.classification, "unchanged");
        assert_eq!(unchanged.trust_vc_paths[0].path, "ported/bar.rs");
        assert_eq!(
            unchanged.trust_vc_paths[0].sha256,
            "sha256:f2c82decdd7181cf98945929a62598db7e6b477e11f6e0eb0ae97020eff151ad"
        );

        let evidence = test_evidence_report_with_corpus(corpus);
        let json = serde_json::to_value(&evidence).expect("report should serialize");
        assert_eq!(
            json["corpus"]["accepted_trust_vc_source_hashes"][0]["trust_vc_paths"][0]["path"],
            "ported/foo.rs"
        );
        assert_eq!(
            json["corpus"]["accepted_trust_vc_source_hashes"][0]["trust_vc_paths"][0]["sha256"],
            "sha256:b6a98d9ce9a2d9149288fa3df42d377c3e42737afdcdaf714e33c0a100b51060"
        );

        let markdown = evidence.render_markdown();
        assert!(markdown.contains("### Accepted TrustVc Source Hashes"));
        assert!(markdown.contains("ported/foo.rs"));
        assert!(markdown
            .contains("sha256:b6a98d9ce9a2d9149288fa3df42d377c3e42737afdcdaf714e33c0a100b51060"));

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn source_tree_hash_ignores_generated_build_and_evidence_dirs() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-source-hash-generated-dirs");
        let source_root = temp_dir.join("ported/fixture");
        fs::create_dir_all(source_root.join("src")).expect("fixture source dir should be created");
        fs::write(source_root.join("Cargo.toml"), "[package]\n")
            .expect("fixture manifest should be written");
        fs::write(source_root.join("src/lib.rs"), "pub fn f() {}\n")
            .expect("fixture source should be written");
        let baseline = source_tree_sha256(&source_root).expect("source tree should hash");

        fs::write(source_root.join("Cargo.lock"), "version = 4\n# old lock\n")
            .expect("fixture lock should be written");
        let with_lock = source_tree_sha256(&source_root).expect("source tree should hash");
        fs::write(source_root.join("Cargo.lock"), "version = 4\n# new lock\n")
            .expect("fixture lock should be rewritten");
        let with_rewritten_lock =
            source_tree_sha256(&source_root).expect("source tree should hash");
        assert_eq!(
            baseline, with_lock,
            "source tree hashing must ignore root Cargo.lock"
        );
        assert_eq!(
            baseline, with_rewritten_lock,
            "root Cargo.lock revisions are checked by the lock provenance gate, not the source hash"
        );

        fs::create_dir_all(source_root.join("target/debug")).expect("target dir should be created");
        fs::write(
            source_root.join("target/debug/generated.txt"),
            "generated\n",
        )
        .expect("target artifact should be written");
        fs::create_dir_all(source_root.join(".trust_vc")).expect("trust_vc dir should be created");
        fs::write(source_root.join(".trust_vc/proof-certificate.json"), "{}\n")
            .expect("trust_vc artifact should be written");
        let with_generated =
            source_tree_sha256(&source_root).expect("generated dirs should be skipped");

        assert_eq!(
            baseline, with_generated,
            "source tree hashing must ignore generated target/ and .trust_vc/ directories"
        );

        fs::create_dir_all(source_root.join("src/target"))
            .expect("source target dir should be created");
        fs::write(source_root.join("src/target/mod.rs"), "pub fn g() {}\n")
            .expect("source target module should be written");
        let with_source_target =
            source_tree_sha256(&source_root).expect("source target dir should be hashed");
        assert_ne!(
            baseline, with_source_target,
            "only root-level generated target/ should be skipped"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn source_tree_hash_from_head_uses_same_generated_dir_skips() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-source-hash-head-generated-dirs");
        let source_root = temp_dir.join("ported/fixture");
        fs::create_dir_all(source_root.join("src")).expect("fixture source dir should be created");
        fs::write(source_root.join("Cargo.toml"), "[package]\n")
            .expect("fixture manifest should be written");
        fs::write(source_root.join("Cargo.lock"), "version = 4\n")
            .expect("fixture lock should be written");
        fs::write(source_root.join("src/lib.rs"), "pub fn f() {}\n")
            .expect("fixture source should be written");
        fs::create_dir_all(source_root.join("target/debug")).expect("target dir should be created");
        fs::write(
            source_root.join("target/debug/generated.txt"),
            "generated\n",
        )
        .expect("target artifact should be written");
        fs::create_dir_all(source_root.join(".trust_vc")).expect("trust_vc dir should be created");
        fs::write(source_root.join(".trust_vc/proof-certificate.json"), "{}\n")
            .expect("trust_vc artifact should be written");

        init_git_repo(&temp_dir);
        git_commit_all(&temp_dir, "track fixture with generated dirs");

        let from_filesystem = source_tree_sha256(&source_root).expect("source tree should hash");
        let from_head = source_tree_sha256_from_head(&temp_dir, "ported/fixture")
            .expect("HEAD source tree should hash");
        assert_eq!(
            from_filesystem, from_head,
            "filesystem and HEAD tree hashing must skip generated dirs consistently"
        );

        fs::write(
            source_root.join("Cargo.lock"),
            "version = 4\n# worktree-only\n",
        )
        .expect("fixture lock should be rewritten");
        let worktree_with_changed_lock =
            source_tree_sha256(&source_root).expect("source tree should hash");
        assert_eq!(
            from_head, worktree_with_changed_lock,
            "filesystem and HEAD source hashes must both ignore root Cargo.lock"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn refresh_trust_vc_corpus_evidence_updates_hashes_and_fingerprints_from_passing_run() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-refresh-pins");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("upstream test should be written");
        let trust_vc_path = temp_dir.join("ported/foo.rs");
        fs::write(
            &trust_vc_path,
            r#"
#[ensures(result == x)]
fn identity(x: i32) -> i32 {
    x
}
"#,
        )
        .expect("ported source should be written");
        let stale_hash = "sha256:0000000000000000000000000000000000000000000000000000000000000000";
        let stale_fingerprint =
            "sha256:1111111111111111111111111111111111111111111111111111111111111111";
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            format!(
                r##"{{
  "schema_version": 2,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {{
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  }},
  "gate": {{
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  }},
  "entries": [
    {{
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported for TrustVc.",
      "trust_vc_paths": ["ported/foo.rs"],
      "trust_vc_source_hashes": [
        {{
          "path": "ported/foo.rs",
          "kind": "file",
          "sha256": "{stale_hash}"
        }}
      ],
      "expected_cases": [
        {{
          "case_id": "identity",
          "expected_verdict": "verified",
          "min_obligations": 9,
          "obligation_fingerprints": ["{stale_fingerprint}"]
        }}
      ]
    }}
  ]
}}"##
            ),
        )
        .expect("manifest should be written");

        let corpus = load_corpus_report_with_options(
            &manifest_path,
            &temp_dir,
            Some(&temp_dir),
            CorpusLoadOptions {
                refresh_evidence_pins: true,
            },
        )
        .expect("corpus report should load in refresh mode");
        let run_report = run_trust_vc_corpus(&temp_dir, &corpus, None);
        assert_eq!(run_report.passed_paths, 1);
        assert_eq!(run_report.failed_paths, 0);

        let summary =
            refresh_trust_vc_corpus_evidence_manifest(&manifest_path, &corpus, Some(&run_report))
                .expect("refresh should write manifest evidence pins");

        assert_eq!(summary.accepted_entries, 1);
        assert_eq!(summary.source_hash_paths, 1);
        assert_eq!(summary.obligation_cases, 1);
        assert!(summary.obligation_fingerprints >= 1);
        let json: serde_json::Value = serde_json::from_str(
            &fs::read_to_string(&manifest_path).expect("manifest should be readable"),
        )
        .expect("refreshed manifest should parse");
        assert_eq!(
            json["entries"][0]["trust_vc_source_hashes"][0]["sha256"],
            source_file_sha256(&trust_vc_path).expect("source hash should be computed")
        );
        let fingerprints = json["entries"][0]["expected_cases"][0]["obligation_fingerprints"]
            .as_array()
            .expect("obligation fingerprints should be an array");
        assert!(!fingerprints.is_empty());
        assert!(fingerprints
            .iter()
            .all(|fingerprint| { fingerprint.as_str().is_some_and(is_sha256_digest) }));
        assert!(fingerprints
            .iter()
            .all(|fingerprint| { fingerprint.as_str() != Some(stale_fingerprint) }));
        assert_eq!(
            json["entries"][0]["expected_cases"][0]["min_obligations"]
                .as_u64()
                .expect("min_obligations should be numeric") as usize,
            fingerprints.len()
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn refresh_trust_vc_corpus_evidence_refuses_proof_entry_executed_as_integration_test() {
        // Integrity cross-check: a PROOF entry (evidence_kind = proof_obligation, the
        // default) whose corpus run executed as a cargo-trust-vc INTEGRATION TEST must
        // be REFUSED. Wrapper execution can never be minted as proof-obligation
        // fingerprint evidence, and the witness skip-path (which omits fingerprinting)
        // must be unreachable for a genuine proof entry. This replaces the prior blanket
        // refusal: integration-WITNESS entries (evidence_kind = integration) are now
        // refreshed source-hash-only, but a proof/witness MISMATCH is still rejected.
        let temp_dir = unique_temp_dir("trust-vc-evidence-refresh-crosscheck");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("upstream test should be written");
        let trust_vc_path = temp_dir.join("ported/foo.rs");
        fs::write(
            &trust_vc_path,
            "#[ensures(result == x)]\nfn identity(x: i32) -> i32 {\n    x\n}\n",
        )
        .expect("ported source should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 2,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported for TrustVc.",
      "trust_vc_paths": ["ported/foo.rs"],
      "trust_vc_source_hashes": [
        { "path": "ported/foo.rs", "kind": "file", "sha256": "sha256:0000000000000000000000000000000000000000000000000000000000000000" }
      ],
      "expected_cases": [
        { "case_id": "identity", "expected_verdict": "verified", "min_obligations": 1, "obligation_fingerprints": ["sha256:1111111111111111111111111111111111111111111111111111111111111111"] }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let corpus = load_corpus_report_with_options(
            &manifest_path,
            &temp_dir,
            Some(&temp_dir),
            CorpusLoadOptions {
                refresh_evidence_pins: true,
            },
        )
        .expect("corpus report should load in refresh mode");

        // Synthetic passing run where the proof entry executed as an integration test
        // (the integrity violation the cross-check must catch).
        let mut run_report = corpus_run_report(1, 1, 0, 0);
        run_report.results.push(TrustVcCorpusRunResult {
            upstream_path: "source/rust_verify_test/tests/foo.rs".to_string(),
            trust_vc_path: "ported/foo.rs".to_string(),
            trust_vc_paths: vec!["ported/foo.rs".to_string()],
            execution_mode: TrustVcCorpusExecutionMode::CargoTrustVcIntegrationTest,
            status: GateStatus::Passed,
            detail: None,
            function_count: 1,
            expected_case_count: 1,
            observed_case_count: 1,
            expected_obligation_count: 0,
            observed_obligation_count: 0,
            expected_case_ids: vec!["identity".to_string()],
            observed_case_ids: vec!["identity".to_string()],
            observed_cases: vec![TrustVcCorpusObservedCase {
                case_id: "identity".to_string(),
                trust_vc_path: "ported/foo.rs".to_string(),
                verdict: "verified".to_string(),
                obligation_count: 0,
                obligation_fingerprints: Vec::new(),
                diagnostic_context: Vec::new(),
                warnings: Vec::new(),
            }],
            failures: Vec::new(),
            command: None,
            commands: Vec::new(),
        });

        let err =
            refresh_trust_vc_corpus_evidence_manifest(&manifest_path, &corpus, Some(&run_report))
                .expect_err("a proof entry executed as an integration test must be refused");

        assert!(
            err.to_string().contains("disagrees with execution"),
            "expected evidence_kind/execution cross-check failure, got: {err}"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn refresh_trust_vc_corpus_evidence_uses_worktree_hashes_for_new_ports() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-refresh-new-port");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        let manifest_dir = temp_dir.join("evals/verus");
        let ported_dir = manifest_dir.join("ported");
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(&ported_dir).expect("ported dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("upstream test should be written");
        fs::write(ported_dir.join("foo.rs"), "new worktree port\n")
            .expect("ported source should be written");
        let manifest_path = manifest_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Newly ported for TrustVc.",
      "trust_vc_paths": ["evals/verus/ported/foo.rs"],
      "expected_cases": [
        {
          "case_id": "identity",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        assert_eq!(
            run_command(&temp_dir, DEFAULT_GIT_COMMAND, &["init"]).exit_code,
            Some(0)
        );
        assert_eq!(
            run_command(
                &temp_dir,
                DEFAULT_GIT_COMMAND,
                &["add", "evals/verus/verus-tests.json"],
            )
            .exit_code,
            Some(0)
        );
        assert_eq!(
            run_command(
                &temp_dir,
                DEFAULT_GIT_COMMAND,
                &[
                    "-c",
                    "user.name=TrustVc Test",
                    "-c",
                    "user.email=trust_vc@example.invalid",
                    "commit",
                    "-m",
                    "manifest",
                ],
            )
            .exit_code,
            Some(0)
        );

        let corpus = load_corpus_report_with_options(
            &manifest_path,
            &temp_dir,
            Some(&temp_dir),
            CorpusLoadOptions {
                refresh_evidence_pins: true,
            },
        )
        .expect("refresh mode should hash untracked new ports from the worktree");

        assert!(
            corpus.port_path_failures.is_empty(),
            "refresh mode should not require new accepted ports to already be in HEAD: {:?}",
            corpus.port_path_failures
        );
        let source_hash = &corpus.accepted_trust_vc_source_hashes[0].trust_vc_paths[0];
        assert_eq!(source_hash.path, "evals/verus/ported/foo.rs");
        assert_eq!(source_hash.kind, TrustVcSourceHashKind::File);
        assert_eq!(
            source_hash.sha256,
            sha256_digest_bytes(b"new worktree port\n")
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn refresh_trust_vc_corpus_evidence_does_not_write_after_failed_run() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-refresh-failed-run");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("upstream test should be written");
        fs::write(
            temp_dir.join("ported/foo.rs"),
            r#"
#[ensures(result == x)]
fn identity(x: i32) -> i32 {
    x
}
"#,
        )
        .expect("ported source should be written");
        let original = r##"{
  "schema_version": 2,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported for TrustVc.",
      "trust_vc_paths": ["ported/foo.rs"],
      "expected_cases": [
        {
          "case_id": "missing_case",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}
"##;
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(&manifest_path, original).expect("manifest should be written");
        let corpus = load_corpus_report_with_options(
            &manifest_path,
            &temp_dir,
            Some(&temp_dir),
            CorpusLoadOptions {
                refresh_evidence_pins: true,
            },
        )
        .expect("corpus report should load in refresh mode");
        let run_report = run_trust_vc_corpus(&temp_dir, &corpus, None);
        assert_eq!(run_report.failed_paths, 1);

        let err =
            refresh_trust_vc_corpus_evidence_manifest(&manifest_path, &corpus, Some(&run_report))
                .expect_err("refresh must fail before writing after failed run");

        assert!(err
            .to_string()
            .contains("requires a passing TrustVc corpus run"));
        assert_eq!(
            fs::read_to_string(&manifest_path).expect("manifest should remain readable"),
            original
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_hashes_accepted_sources_from_head_when_git_is_available() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-head-source-hashes");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        let manifest_dir = temp_dir.join("evals/verus");
        let ported_dir = manifest_dir.join("ported");
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(&ported_dir).expect("ported dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("foo test should be written");
        fs::write(upstream_tests.join("untracked.rs"), "")
            .expect("untracked test should be written");
        fs::write(ported_dir.join("tracked.rs"), "head version\n")
            .expect("tracked port should be written");
        let manifest_path = manifest_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported for TrustVc.",
      "trust_vc_paths": ["evals/verus/ported/tracked.rs"],
      "expected_cases": [
        {
          "case_id": "identity",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    },
    {
      "upstream_path": "source/rust_verify_test/tests/untracked.rs",
      "classification": "ported",
      "owner_issue": "#124",
      "reason": "Ported for TrustVc.",
      "trust_vc_paths": ["evals/verus/ported/untracked.rs"],
      "expected_cases": [
        {
          "case_id": "untracked",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        assert_eq!(
            run_command(&temp_dir, DEFAULT_GIT_COMMAND, &["init"]).exit_code,
            Some(0)
        );
        assert_eq!(
            run_command(
                &temp_dir,
                DEFAULT_GIT_COMMAND,
                &[
                    "add",
                    "evals/verus/verus-tests.json",
                    "evals/verus/ported/tracked.rs",
                ],
            )
            .exit_code,
            Some(0)
        );
        assert_eq!(
            run_command(
                &temp_dir,
                DEFAULT_GIT_COMMAND,
                &[
                    "-c",
                    "user.name=TrustVc Test",
                    "-c",
                    "user.email=trust_vc@example.invalid",
                    "commit",
                    "-m",
                    "initial",
                ],
            )
            .exit_code,
            Some(0)
        );

        fs::write(ported_dir.join("tracked.rs"), "working tree version\n")
            .expect("tracked port should be modified after commit");
        fs::write(ported_dir.join("untracked.rs"), "untracked\n")
            .expect("untracked port should exist in the working tree");

        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");

        assert!(
            report
                .port_path_failures
                .iter()
                .any(|failure| failure.contains("TrustVc source path must be tracked in HEAD")),
            "untracked port must fail HEAD provenance: {:?}",
            report.port_path_failures
        );
        assert_eq!(report.accepted_trust_vc_source_hashes.len(), 1);
        let source_hash = &report.accepted_trust_vc_source_hashes[0].trust_vc_paths[0];
        assert_eq!(source_hash.path, "evals/verus/ported/tracked.rs");
        assert_eq!(source_hash.kind, TrustVcSourceHashKind::File);
        assert_eq!(source_hash.sha256, sha256_digest_bytes(b"head version\n"));
        assert_ne!(
            source_hash.sha256,
            sha256_digest_bytes(b"working tree version\n"),
            "source hash must be computed from HEAD, not dirty working-tree bytes"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_rejects_overbroad_not_applicable_classification() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-not-applicable");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(upstream_tests.join("common")).expect("upstream dirs should exist");
        fs::write(upstream_tests.join("foo.rs"), "").expect("foo test should be written");
        fs::write(upstream_tests.join("common/mod.rs"), "").expect("helper should be written");
        fs::write(
            upstream_tests.join("ignored_only.rs"),
            r#"
test_verify_one_file! {
    #[ignore] #[test] ignored_only verus_code! {
        fn intentionally_not_run() {}
    } => Ok(())
}
"#,
        )
        .expect("ignored-only test should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "not-applicable",
      "owner_issue": "#123",
      "reason": "This semantic test must not be hidden."
    },
    {
      "upstream_path": "source/rust_verify_test/tests/common/mod.rs",
      "classification": "not-applicable",
      "owner_issue": "#124",
      "reason": "Shared helper module."
    },
    {
      "upstream_path": "source/rust_verify_test/tests/ignored_only.rs",
      "classification": "not-applicable",
      "owner_issue": "#125",
      "reason": "Upstream harness case is #[ignore], so it is not part of the runnable Verus test gate."
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        assert!(
            report
                .failing_entries
                .iter()
                .any(|entry| entry.contains("foo.rs: not-applicable is reserved")),
            "semantic not-applicable entry should fail: {:?}",
            report.failing_entries
        );
        assert!(
            !report
                .failing_entries
                .iter()
                .any(|entry| entry.contains("common/mod.rs")),
            "approved helper not-applicable entry should not fail: {:?}",
            report.failing_entries
        );
        assert!(
            !report
                .failing_entries
                .iter()
                .any(|entry| entry.contains("ignored_only.rs")),
            "ignored-only upstream files may be not-applicable: {:?}",
            report.failing_entries
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn upstream_harness_case_extraction_records_ignored_cases() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-upstream-cases");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::write(
            upstream_tests.join("foo.rs"),
            r#"
test_verify_one_file! {
    #[test] test_ok verus_code! {
        fn f() {}
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[ignore] #[test] ignored_case ["--compile"] => verus_code! {
        fn g() {}
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_with_options ["--compile"] => verus_code! {
        fn h() {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_fails verus_code! {
        fn i() { assert(false); }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_no_cheating_gate ["--no-cheating"] => verus_code! {
        proof fn i() { assume(false); }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_rust_error verus_code! {
        fn j() { let x = 1; x = 2; }
    } => Err(err) => assert_rust_error_msg(err, "cannot assign twice")
}

test_verify_one_file! {
    #[test] test_rust_error_plural verus_code! {
        fn m() { let x = 1; x = 2; }
    } => Err(err) => assert_rust_error_msgs(err, &["cannot assign twice"])
}

test_verify_one_file! {
    #[test] test_rust_error_skip verus_code! {
        fn k() { let x = 1; x = 2; }
    } => Err(err) => assert_rust_error_msg_skip_spec_msgs(err, "cannot assign twice")
}

test_verify_one_file! {
    #[test] test_rust_error_any verus_code! {
        fn l() { let x = 1; x = 2; }
    } => Err(err) => assert_rust_error_msg_any(err, "cannot assign twice")
}

test_verify_one_file! {
    #[test] test_direct_error_message verus_code! {
        type OT = impl Foo;
    } => Err(err) => {
        assert!(err.errors.iter().find(|p| p.message == "`impl Trait` in type aliases is unstable").is_some());
    }
}
"#,
        )
        .expect("upstream test should be written");

        let cases_with_verdicts =
            upstream_verus_harness_cases(Some(&temp_dir), "source/rust_verify_test/tests/foo.rs")
                .expect("case extraction should succeed")
                .expect("verus path was supplied");
        assert_eq!(
            cases_with_verdicts
                .iter()
                .map(|case| case.case_id.as_str())
                .collect::<Vec<_>>(),
            vec![
                "ignored_case",
                "test_direct_error_message",
                "test_fails",
                "test_no_cheating_gate",
                "test_ok",
                "test_rust_error",
                "test_rust_error_any",
                "test_rust_error_plural",
                "test_rust_error_skip",
                "test_with_options"
            ]
        );
        assert_eq!(
            cases_with_verdicts
                .iter()
                .map(|case| (case.case_id.as_str(), case.expected_verdict, case.ignored))
                .collect::<Vec<_>>(),
            vec![
                ("ignored_case", VerusExpectedVerdict::Verified, true),
                (
                    "test_direct_error_message",
                    VerusExpectedVerdict::Error,
                    false
                ),
                ("test_fails", VerusExpectedVerdict::Counterexample, false),
                ("test_no_cheating_gate", VerusExpectedVerdict::Error, false),
                ("test_ok", VerusExpectedVerdict::Verified, false),
                ("test_rust_error", VerusExpectedVerdict::Error, false),
                ("test_rust_error_any", VerusExpectedVerdict::Error, false),
                ("test_rust_error_plural", VerusExpectedVerdict::Error, false),
                ("test_rust_error_skip", VerusExpectedVerdict::Error, false),
                ("test_with_options", VerusExpectedVerdict::Verified, false),
            ]
        );
        let rust_patterns = cases_with_verdicts
            .iter()
            .filter(|case| case.rust_error)
            .map(|case| (case.case_id.as_str(), case.error_patterns.clone()))
            .collect::<Vec<_>>();
        assert_eq!(
            rust_patterns,
            vec![
                (
                    "test_direct_error_message",
                    vec!["`impl Trait` in type aliases is unstable".to_string()]
                ),
                ("test_rust_error", vec!["cannot assign twice".to_string()]),
                (
                    "test_rust_error_any",
                    vec!["cannot assign twice".to_string()]
                ),
                (
                    "test_rust_error_plural",
                    vec!["cannot assign twice".to_string()]
                ),
                (
                    "test_rust_error_skip",
                    vec!["cannot assign twice".to_string()]
                ),
            ]
        );
        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn upstream_harness_case_extraction_records_manual_verify_one_file_tests() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-upstream-manual-cases");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::write(
            upstream_tests.join("manual.rs"),
            r#"
#[test]
fn manual_ok() {
    assert!(verify_one_file("manual_ok", verus_code! { fn f() {} }, &[]).is_ok());
}

#[test]
fn manual_counterexample() {
    let err = verify_one_file(
        "manual_counterexample",
        verus_code! { fn f() { assert(false); } },
        &[],
    ).unwrap_err();
    assert_eq!(err.errors.len(), 1);
}

#[test]
fn manual_rust_error() {
    let err = verify_one_file(
        "manual_rust_error",
        verus_code! { fn f() { invalid(true); } },
        &[],
    ).unwrap_err();
    assert_rust_error_msg(err, "cannot find function");
}

#[test]
fn manual_vir_error() {
    let err = verify_one_file(
        "manual_vir_error",
        verus_code! { proof fn f() { assert(false); } },
        &[],
    ).unwrap_err();
    assert_vir_error_msg(err, "assertion failed");
}

#[test]
fn manual_any_vir_error() {
    let err = verify_one_file(
        "manual_any_vir_error",
        verus_code! { proof fn f() { assert(false); } },
        &[],
    ).unwrap_err();
    assert_any_vir_error_msg(err, "assertion failed");
}

#[test]
fn manual_help_error() {
    let err = verify_one_file(
        "manual_help_error",
        verus_code! { proof fn f() { assert(false); } },
        &[],
    ).unwrap_err();
    assert_help_error_msg(err, "try adding");
}
"#,
        )
        .expect("upstream test should be written");

        let cases = upstream_verus_harness_cases(
            Some(&temp_dir),
            "source/rust_verify_test/tests/manual.rs",
        )
        .expect("manual case extraction should succeed")
        .expect("verus path was supplied");
        assert_eq!(
            cases
                .iter()
                .map(|case| (case.case_id.as_str(), case.expected_verdict))
                .collect::<Vec<_>>(),
            vec![
                ("manual_any_vir_error", VerusExpectedVerdict::Error),
                (
                    "manual_counterexample",
                    VerusExpectedVerdict::Counterexample
                ),
                ("manual_help_error", VerusExpectedVerdict::Error),
                ("manual_ok", VerusExpectedVerdict::Verified),
                ("manual_rust_error", VerusExpectedVerdict::Error),
                ("manual_vir_error", VerusExpectedVerdict::Error),
            ]
        );
        let error_patterns = cases
            .iter()
            .filter(|case| case.expected_verdict == VerusExpectedVerdict::Error)
            .map(|case| (case.case_id.as_str(), case.error_patterns.clone()))
            .collect::<BTreeMap<_, _>>();
        assert_eq!(
            error_patterns,
            BTreeMap::from([
                ("manual_any_vir_error", vec!["assertion failed".to_string()]),
                ("manual_help_error", vec!["try adding".to_string()]),
                (
                    "manual_rust_error",
                    vec!["cannot find function".to_string()]
                ),
                ("manual_vir_error", vec!["assertion failed".to_string()]),
            ])
        );
        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn upstream_harness_case_extraction_fails_closed_for_negated_manual_is_ok() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-upstream-negated-is-ok");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::write(
            upstream_tests.join("manual_negated.rs"),
            r#"
#[test]
fn manual_negated_ok() {
    assert!(!verify_one_file("manual_negated_ok", verus_code! { fn f() {} }, &[]).is_ok());
}
"#,
        )
        .expect("upstream test should be written");

        let err = upstream_verus_harness_cases(
            Some(&temp_dir),
            "source/rust_verify_test/tests/manual_negated.rs",
        )
        .expect_err("negated manual is_ok harness must fail closed");
        assert!(
            err.contains("cannot infer its expected verdict"),
            "unexpected negated is_ok extraction error: {err}"
        );
        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn upstream_harness_case_extraction_fails_closed_for_unknown_err_helpers() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-upstream-unknown-err");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::write(
            upstream_tests.join("unknown_err.rs"),
            r#"
test_verify_one_file! {
    #[test] test_unknown_err verus_code! {
        fn f() { assert(false); }
    } => Err(err) => assert_custom_error_helper(err)
}
"#,
        )
        .expect("upstream test should be written");

        let err = upstream_verus_harness_cases(
            Some(&temp_dir),
            "source/rust_verify_test/tests/unknown_err.rs",
        )
        .expect_err("unknown Err helper must fail closed");
        assert!(
            err.contains("unknown Err harness helper `assert_custom_error_helper`"),
            "unexpected unknown Err helper extraction error: {err}"
        );
        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn upstream_harness_case_extraction_records_diagnostic_context_filters() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-upstream-diagnostic-context");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::write(
            upstream_tests.join("ui.rs"),
            r#"
test_verify_one_file! {
    #[test] regression_114_unrelated_precondition verus_code! {
        fn require_false() -> bool
            requires false // INCORRECT CONTEXT
        {
            false
        }

        fn test() {
            if false {
                require_false();
            }
            assert(false); // FAILS
        }
    } => Err(e) => {
        assert!(e.errors.len() == 1);
        assert!(!e.errors[0].spans.iter().any(|x| x.text[0].text.contains("INCORRECT CONTEXT")));
    }
}
"#,
        )
        .expect("upstream ui test should be written");

        let cases =
            upstream_verus_harness_cases(Some(&temp_dir), "source/rust_verify_test/tests/ui.rs")
                .expect("diagnostic-context extraction should succeed")
                .expect("verus path was supplied");
        assert_eq!(cases.len(), 1);
        let case = &cases[0];
        assert_eq!(case.case_id, "regression_114_unrelated_precondition");
        assert_eq!(case.expected_verdict, VerusExpectedVerdict::Counterexample);
        assert_eq!(
            case.forbidden_diagnostic_patterns,
            vec!["INCORRECT CONTEXT".to_string()]
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn upstream_harness_case_extraction_records_assert_fails_counts() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-upstream-assert-fails-count");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::write(
            upstream_tests.join("results.rs"),
            r#"
test_verify_one_file! {
    #[test] test_result_fails verus_code! {
        fn test() {
            assert(false); // FAILS
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}
"#,
        )
        .expect("upstream results test should be written");

        let cases = upstream_verus_harness_cases(
            Some(&temp_dir),
            "source/rust_verify_test/tests/results.rs",
        )
        .expect("assert_fails extraction should succeed")
        .expect("verus path was supplied");
        assert_eq!(cases.len(), 1);
        assert_eq!(cases[0].case_id, "test_result_fails");
        assert_eq!(
            cases[0].expected_verdict,
            VerusExpectedVerdict::Counterexample
        );
        assert_eq!(cases[0].expected_occurrences, 2);

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn upstream_harness_case_extraction_records_braced_err_helpers() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-upstream-braced-err-helper");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::write(
            upstream_tests.join("recommends.rs"),
            r#"
test_verify_one_file! {
    #[test] ensures_type_substitutes_issue1566 verus_code! {
        fn test() {
            assert(false); // FAILS
        }
    } => Err(e) => {
        assert_one_fails(e);
    }
}
"#,
        )
        .expect("upstream recommends test should be written");

        let cases = upstream_verus_harness_cases(
            Some(&temp_dir),
            "source/rust_verify_test/tests/recommends.rs",
        )
        .expect("braced Err helper extraction should succeed")
        .expect("verus path was supplied");
        assert_eq!(cases.len(), 1);
        assert_eq!(cases[0].case_id, "ensures_type_substitutes_issue1566");
        assert_eq!(
            cases[0].expected_verdict,
            VerusExpectedVerdict::Counterexample
        );
        assert_eq!(cases[0].expected_occurrences, 1);

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn upstream_harness_case_extraction_fails_closed_for_duplicate_case_ids() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-upstream-duplicate-cases");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::write(
            upstream_tests.join("duplicates.rs"),
            r#"
mod a {
    test_verify_one_file! {
        #[test] duplicate_name verus_code! {
            fn f() {}
        } => Ok(())
    }
}

mod b {
    test_verify_one_file! {
        #[test] duplicate_name verus_code! {
            fn g() {}
        } => Ok(())
    }
}
"#,
        )
        .expect("upstream test should be written");

        let err = upstream_verus_harness_cases(
            Some(&temp_dir),
            "source/rust_verify_test/tests/duplicates.rs",
        )
        .expect_err("duplicate upstream case ids must fail closed");
        assert!(
            err.contains("duplicate harness case id") && err.contains("duplicate_name"),
            "unexpected duplicate case extraction error: {err}"
        );
        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn upstream_harness_case_extraction_fails_closed_for_macro_generated_cases() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-upstream-macro-cases");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::write(
            upstream_tests.join("macro_cases.rs"),
            r#"
macro_rules! generated_case {
    ($name:ident) => {
        test_verify_one_file! {
            #[test] $name verus_code! {
                fn f() {}
            } => Ok(())
        }
    };
}

generated_case!(test_generated);
"#,
        )
        .expect("upstream test should be written");

        let err = upstream_verus_harness_cases(
            Some(&temp_dir),
            "source/rust_verify_test/tests/macro_cases.rs",
        )
        .expect_err("macro-generated harness cases must fail closed");
        assert!(
            err.contains("unexpanded item macro invocation")
                && err.contains("generated_case")
                && err.contains("macro_rules"),
            "unexpected macro-generated case extraction error: {err}"
        );
        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn upstream_harness_case_extraction_fails_closed_for_unknown_item_macros() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-upstream-unknown-macro-cases");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::write(
            upstream_tests.join("unknown_macro_cases.rs"),
            r#"
generated_case!(test_generated);
"#,
        )
        .expect("upstream test should be written");

        let err = upstream_verus_harness_cases(
            Some(&temp_dir),
            "source/rust_verify_test/tests/unknown_macro_cases.rs",
        )
        .expect_err("unknown item macros must fail closed");
        assert!(
            err.contains("unexpanded item macro invocation") && err.contains("generated_case"),
            "unexpected unknown item macro extraction error: {err}"
        );
        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn upstream_harness_case_extraction_allows_macros_inside_harness_bodies() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-upstream-body-macros");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::write(
            upstream_tests.join("body_macros.rs"),
            r#"
test_verify_one_file! {
    #[test] test_macro_item verus_code! {
        fn f() {
            let mut x = 1;
            macro_rules! add_1 {
                () => { x = x + 1; }
            }
            add_1!();
            assert(x == 2);
        }
    } => Ok(())
}
"#,
        )
        .expect("upstream test should be written");

        let cases = upstream_verus_harness_cases(
            Some(&temp_dir),
            "source/rust_verify_test/tests/body_macros.rs",
        )
        .expect("body macros inside harness tokens should not fail extraction")
        .expect("verus path was supplied");
        assert_eq!(
            cases
                .iter()
                .map(|case| (case.case_id.as_str(), case.expected_verdict))
                .collect::<Vec<_>>(),
            vec![("test_macro_item", VerusExpectedVerdict::Verified)]
        );
        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn upstream_harness_case_extraction_records_cargo_examples_cases() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-upstream-cargo-examples");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        for fixture in [
            "cargo-tests/verified/basic-fixture",
            "cargo-tests/verified/spec_use",
            "cargo-tests/unverified/structural",
        ] {
            let fixture_root = upstream_tests.join(fixture);
            fs::create_dir_all(&fixture_root).expect("fixture dir should be created");
            fs::write(
                fixture_root.join("Cargo.toml"),
                r#"
[package]
name = "fixture"
version = "0.1.0"
edition = "2021"
"#,
            )
            .expect("fixture manifest should be written");
        }
        fs::write(
            upstream_tests.join("cargo.rs"),
            r#"
#[test]
fn cargo_new_verifies() {
    let run = run_cargo_verus(&[], std::path::Path::new("."));
    assert!(run.status.success());
}

#[test]
fn cargo_new_builds() {
    let run = run_cargo_verus(&[], std::path::Path::new("."));
    assert!(run.status.success());
}

cargo_examples!(true);
cargo_examples!(false);
"#,
        )
        .expect("upstream cargo wrapper test should be written");

        let cases = upstream_verus_harness_cases(Some(&temp_dir), VERUS_CARGO_WRAPPER_TEST_PATH)
            .expect("cargo wrapper extraction should succeed")
            .expect("verus path was supplied");
        assert_eq!(
            cases
                .iter()
                .map(|case| (case.case_id.as_str(), case.expected_verdict))
                .collect::<Vec<_>>(),
            vec![
                ("cargo_new_builds", VerusExpectedVerdict::Verified),
                ("cargo_new_verifies", VerusExpectedVerdict::Verified),
                ("unverified_structural", VerusExpectedVerdict::Verified),
                ("verified_basic_fixture", VerusExpectedVerdict::Verified),
                ("verified_spec_use", VerusExpectedVerdict::Verified),
            ]
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn upstream_harness_case_extraction_records_cargo_verus_integration_tests() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-upstream-cargo-verus-integration");
        let upstream_tests = temp_dir.join(VERUS_CARGO_VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("cargo-verus test dir should be created");
        fs::write(
            upstream_tests.join("test_late_args.rs"),
            r#"
fn helper() {}

#[test]
fn late_package_arg_after_release() {
    helper();
}

#[ignore]
#[test]
fn ignored_cargo_verus_case() {}

#[test]
fn z_flag_with_space_is_accepted() {}
"#,
        )
        .expect("cargo-verus integration test should be written");

        let cases = upstream_verus_harness_cases(
            Some(&temp_dir),
            "source/cargo-verus/tests/test_late_args.rs",
        )
        .expect("cargo-verus integration extraction should succeed")
        .expect("verus path was supplied");

        assert_eq!(
            cases
                .iter()
                .map(|case| (case.case_id.as_str(), case.expected_verdict, case.ignored))
                .collect::<Vec<_>>(),
            vec![
                (
                    "ignored_cargo_verus_case",
                    VerusExpectedVerdict::Verified,
                    true
                ),
                (
                    "late_package_arg_after_release",
                    VerusExpectedVerdict::Verified,
                    false
                ),
                (
                    "z_flag_with_space_is_accepted",
                    VerusExpectedVerdict::Verified,
                    false
                ),
            ]
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_requires_expected_cases_to_cover_upstream_harness_cases() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-upstream-case-coverage");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(
            upstream_tests.join("foo.rs"),
            r#"
test_verify_one_file! {
    #[test] test_ok verus_code! {
        fn f() {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_fails verus_code! {
        fn g() { assert(false); }
    } => Err(err) => assert_one_fails(err)
}
"#,
        )
        .expect("upstream test should be written");
        fs::write(
            temp_dir.join("ported/foo.rs"),
            r#"
#[ensures(result == x)]
fn test_ok(x: i32) -> i32 {
    x
}
"#,
        )
        .expect("ported foo should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Partial port should not prove the full upstream file.",
      "trust_vc_paths": ["ported/foo.rs"],
      "expected_cases": [
        {
          "case_id": "test_ok",
          "expected_verdict": "verified",
          "min_obligations": 1
        },
        {
          "case_id": "extra_case",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        assert!(
            report
                .upstream_case_failures
                .iter()
                .any(|entry| entry.contains("missing upstream Verus case `test_fails`")),
            "missing upstream harness cases must fail: {:?}",
            report.upstream_case_failures
        );
        assert!(
            report
                .upstream_case_failures
                .iter()
                .any(|entry| entry.contains("`extra_case` does not match")),
            "extra expected cases must fail: {:?}",
            report.upstream_case_failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_records_ignored_upstream_harness_cases_without_requiring_ports() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-upstream-ignored-case-coverage");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(
            upstream_tests.join("foo.rs"),
            r#"
test_verify_one_file! {
    #[test] test_ok verus_code! {
        fn f() {}
    } => Ok(())
}

test_verify_one_file! {
    #[ignore] #[test] ignored_case verus_code! {
        fn g() {}
    } => Ok(())
}
"#,
        )
        .expect("upstream test should be written");
        fs::write(
            temp_dir.join("ported/foo.rs"),
            r#"
#[ensures(result == x)]
fn test_ok(x: i32) -> i32 {
    x
}

#[ensures(result == x)]
fn ignored_case(x: i32) -> i32 {
    x
}
"#,
        )
        .expect("ported foo should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ignored upstream cases must remain visible to evidence.",
      "trust_vc_paths": ["ported/foo.rs"],
      "expected_cases": [
        {
          "case_id": "test_ok",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        assert_eq!(report.ignored_upstream_cases.len(), 1);
        assert_eq!(report.ignored_upstream_cases[0].case_id, "ignored_case");
        assert!(
            report.ignored_upstream_cases[0]
                .expected_case_ids
                .is_empty(),
            "uncovered ignored case should still be represented: {:?}",
            report.ignored_upstream_cases
        );
        assert!(
            report.upstream_case_failures.is_empty(),
            "ignored upstream cases are not run by the upstream test gate and should not require ports: {:?}",
            report.upstream_case_failures
        );
        let markdown = test_evidence_report_with_corpus(report).render_markdown();
        assert!(markdown.contains("### Ignored Upstream Cases"));
        assert!(markdown.contains("ignored_case"));

        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ignored upstream cases must remain visible to evidence.",
      "trust_vc_paths": ["ported/foo.rs"],
      "expected_cases": [
        {
          "case_id": "test_ok",
          "expected_verdict": "verified",
          "min_obligations": 1
        },
        {
          "case_id": "ignored_case",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be rewritten");
        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        assert!(
            report.upstream_case_failures.is_empty(),
            "covered ignored upstream cases should not fail: {:?}",
            report.upstream_case_failures
        );
        assert_eq!(
            report.ignored_upstream_cases[0].expected_case_ids,
            vec!["ignored_case"]
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_counts_cargo_tests_extraction_bypass_as_gap_for_accepted_entries() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-cargo-tests-extraction-gap");
        let accepted_upstream = temp_dir
            .join(VERUS_TEST_ROOT)
            .join("cargo-tests/verified/accepted/src");
        let unsupported_upstream = temp_dir
            .join(VERUS_TEST_ROOT)
            .join("cargo-tests/verified/unsupported/src");
        fs::create_dir_all(&accepted_upstream).expect("accepted upstream dir should be created");
        fs::create_dir_all(&unsupported_upstream)
            .expect("unsupported upstream dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(accepted_upstream.join("main.rs"), "").expect("accepted upstream should exist");
        fs::write(unsupported_upstream.join("lib.rs"), "")
            .expect("unsupported upstream should exist");
        fs::write(
            temp_dir.join("ported/accepted.rs"),
            r#"
#[ensures(result == x)]
fn main(x: i32) -> i32 {
    x
}
"#,
        )
        .expect("ported accepted file should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/cargo-tests/verified/accepted/src/main.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Accepted cargo fixtures must not bypass upstream inventory accounting.",
      "trust_vc_paths": ["ported/accepted.rs"],
      "expected_cases": [
        {
          "case_id": "main",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    },
    {
      "upstream_path": "source/rust_verify_test/tests/cargo-tests/verified/unsupported/src/lib.rs",
      "classification": "unsupported-gap",
      "owner_issue": "#124",
      "reason": "Explicit gap classification accounts for bypassed cargo fixture extraction."
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        assert_eq!(report.upstream_case_extraction_gaps.len(), 1);
        assert!(
            report.upstream_case_extraction_gaps[0].contains(
                "source/rust_verify_test/tests/cargo-tests/verified/accepted/src/main.rs"
            ) && report.upstream_case_extraction_gaps[0].contains("coverage gap"),
            "accepted cargo-tests bypass should be a coverage gap: {:?}",
            report.upstream_case_extraction_gaps
        );
        assert_eq!(report.unsupported_entries.len(), 1);
        assert!(
            !report.upstream_case_extraction_gaps[0].contains("unsupported/src/lib.rs"),
            "unsupported-gap entry should be accounted by classification, not extraction gap: {:?}",
            report.upstream_case_extraction_gaps
        );
        let markdown = test_evidence_report_with_corpus(report).render_markdown();
        assert!(markdown.contains("### Upstream Case Extraction Gaps"));
        assert!(markdown.contains("coverage gap"));

        fs::write(
            temp_dir
                .join(VERUS_TEST_ROOT)
                .join("cargo-tests/verified/accepted/Cargo.toml"),
            r#"
[package]
name = "accepted"
version = "0.1.0"
edition = "2021"

[workspace]
"#,
        )
        .expect("accepted cargo fixture manifest should be written");
        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        assert!(
            report.upstream_case_extraction_gaps.is_empty(),
            "Cargo fixture with Cargo.toml and src/main.rs should have concrete inventory: {:?}",
            report.upstream_case_extraction_gaps
        );
        assert!(
            report.upstream_case_failures.is_empty(),
            "Cargo fixture case id should match synthesized upstream case: {:?}",
            report.upstream_case_failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_requires_multi_failure_upstream_case_coverage() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-multi-failure-coverage");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(
            upstream_tests.join("results.rs"),
            r#"
test_verify_one_file! {
    #[test] test_result_fails verus_code! {
        fn test() {
            assert(false); // FAILS
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}
"#,
        )
        .expect("upstream results test should be written");
        fs::write(
            temp_dir.join("ported/results.rs"),
            r#"
#[ensures(false)]
fn only_one_result_failure() {
}
"#,
        )
        .expect("ported results source should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/results.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "One TrustVc counterexample is not enough for assert_fails(err, 2).",
      "trust_vc_paths": ["ported/results.rs"],
      "expected_cases": [
        {
          "case_id": "only_one_result_failure",
          "upstream_case_id": "test_result_fails",
          "expected_verdict": "counterexample",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        assert!(
            report
                .upstream_case_failures
                .iter()
                .any(|failure| failure.contains("requires at least 2 mapped TrustVc expected case")),
            "multi-failure upstream case must require enough TrustVc mappings: {:?}",
            report.upstream_case_failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_rejects_cargo_fixture_package_shape_mismatch() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-cargo-shape-mismatch");
        let upstream_src = temp_dir
            .join(VERUS_TEST_ROOT)
            .join("cargo-tests/verified/shape/src");
        let trust_vc_fixture = temp_dir.join("ported/shape_fixture");
        fs::create_dir_all(&upstream_src).expect("upstream src should be created");
        fs::create_dir_all(trust_vc_fixture.join("src")).expect("trust_vc src should be created");
        fs::write(upstream_src.join("lib.rs"), "").expect("upstream lib should be written");
        fs::write(
            temp_dir
                .join(VERUS_TEST_ROOT)
                .join("cargo-tests/verified/shape/Cargo.toml"),
            r#"
[package]
name = "shape"
version = "0.1.0"
edition = "2021"

[dependencies]
vstd = { path = "../../../../../vstd" }
upstream_dep = { path = "../upstream_dep" }

[workspace]
"#,
        )
        .expect("upstream cargo manifest should be written");
        fs::write(
            trust_vc_fixture.join("Cargo.toml"),
            r#"
[package]
name = "wrong_shape"
version = "0.1.0"
edition = "2021"

[dependencies]
trust_vc = { path = "../../../../crates/trust_vc" }

[workspace]
"#,
        )
        .expect("trust_vc cargo manifest should be written");
        fs::write(trust_vc_fixture.join("src/lib.rs"), "").expect("trust_vc lib should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/cargo-tests/verified/shape/src/lib.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Cargo fixture must mirror package and dependency shape.",
      "trust_vc_paths": ["ported/shape_fixture"],
      "expected_cases": [
        {
          "case_id": "lib",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        assert!(
            report
                .port_path_failures
                .iter()
                .any(|failure| failure.contains("package name `wrong_shape`")),
            "package mismatch should be rejected: {:?}",
            report.port_path_failures
        );
        assert!(
            report
                .port_path_failures
                .iter()
                .any(|failure| failure.contains("missing upstream dependency `upstream_dep`")),
            "dependency mismatch should be rejected: {:?}",
            report.port_path_failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_requires_expected_verdicts_to_match_upstream_harness() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-upstream-case-verdicts");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(
            upstream_tests.join("foo.rs"),
            r#"
test_verify_one_file! {
    #[test] test_ok verus_code! {
        fn f() {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_fails verus_code! {
        fn g() { assert(false); }
    } => Err(err) => assert_one_fails(err)
}
"#,
        )
        .expect("upstream test should be written");
        fs::write(
            temp_dir.join("ported/foo.rs"),
            r#"
#[ensures(result == x)]
fn test_ok(x: i32) -> i32 {
    x
}

#[ensures(false)]
fn test_fails() {}
"#,
        )
        .expect("ported foo should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Manifest polarity must match upstream.",
      "trust_vc_paths": ["ported/foo.rs"],
      "expected_cases": [
        {
          "case_id": "test_ok",
          "expected_verdict": "counterexample",
          "min_obligations": 1
        },
        {
          "case_id": "test_fails",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        assert!(
            report.upstream_case_failures.iter().any(|entry| entry
                .contains("`test_ok` declares `counterexample`")
                && entry.contains("expects `verified`")),
            "Ok upstream cases must not be marked counterexample: {:?}",
            report.upstream_case_failures
        );
        assert!(
            report
                .upstream_case_failures
                .iter()
                .any(|entry| entry.contains("`test_fails` declares `verified`")
                    && entry.contains("expects `counterexample`")),
            "Err upstream cases must not be marked verified: {:?}",
            report.upstream_case_failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_allows_split_cases_to_map_to_one_upstream_case() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-upstream-split-cases");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(
            upstream_tests.join("nested.rs"),
            r#"
test_verify_one_file! {
    #[test] test_ignorable_items verus_code! {
        fn test_use_item() { assert(true); }
        fn test_macro_item() { assert(true); }
    } => Ok(())
}
"#,
        )
        .expect("upstream test should be written");
        fs::write(
            temp_dir.join("ported/nested.rs"),
            r#"
#[ensures(result)]
fn test_use_item() -> bool { true }

#[ensures(result)]
fn test_macro_item() -> bool { true }
"#,
        )
        .expect("ported nested file should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/nested.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Split one upstream harness case into concrete TrustVc cases.",
      "trust_vc_paths": ["ported/nested.rs"],
      "expected_cases": [
        {
          "case_id": "test_use_item",
          "upstream_case_id": "test_ignorable_items",
          "expected_verdict": "verified",
          "min_obligations": 1
        },
        {
          "case_id": "test_macro_item",
          "upstream_case_id": "test_ignorable_items",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");

        assert!(
            report.upstream_case_failures.is_empty(),
            "split TrustVc cases mapped by upstream_case_id should cover the upstream harness case: {:?}",
            report.upstream_case_failures
        );

        let invalid_manifest = fs::read_to_string(&manifest_path)
            .expect("manifest should be readable")
            .replace(
                "\"upstream_case_id\": \"test_ignorable_items\"",
                "\"upstream_case_id\": \"\"",
            );
        fs::write(&manifest_path, invalid_manifest).expect("manifest should be written");
        let invalid_report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        assert!(
            invalid_report
                .port_path_failures
                .iter()
                .any(|failure| failure.contains("expected_cases.upstream_case_id")),
            "explicit empty upstream_case_id must fail runtime validation: {:?}",
            invalid_report.port_path_failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_requires_upstream_case_id_for_multi_case_accepted_entries() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-missing-upstream-case-id");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(upstream_tests.join("multi.rs"), "").expect("upstream test should be written");
        fs::write(
            temp_dir.join("ported/multi.rs"),
            r#"
#[ensures(result)]
fn alpha() -> bool { true }

#[ensures(result)]
fn beta() -> bool { true }
"#,
        )
        .expect("ported multi file should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/multi.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Multi-case accepted entries must map to upstream harness cases explicitly.",
      "trust_vc_paths": ["ported/multi.rs"],
      "expected_cases": [
        {
          "case_id": "alpha",
          "expected_verdict": "verified",
          "min_obligations": 1
        },
        {
          "case_id": "beta",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");

        assert!(
            report
                .port_path_failures
                .iter()
                .any(|failure| failure.contains("must declare upstream_case_id")),
            "multi-case accepted entries must require explicit upstream_case_id: {:?}",
            report.port_path_failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_rejects_case_level_trust_vc_path_not_declared_by_entry() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-case-trust-vc-path-validation");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("upstream test should be written");
        fs::write(
            temp_dir.join("ported/foo.rs"),
            r#"
#[ensures(result == x)]
fn identity(x: i32) -> i32 {
    x
}
"#,
        )
        .expect("ported foo should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Case-level paths must bind to entry-level paths.",
      "trust_vc_paths": ["ported/foo.rs"],
      "expected_cases": [
        {
          "case_id": "identity",
          "trust_vc_path": "ported/bar.rs",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        assert!(
            report
                .port_path_failures
                .iter()
                .any(|failure| failure.contains(
                    "expected_cases entry `identity` trust_vc_path `ported/bar.rs` must match"
                )),
            "case-level trust_vc_path must be entry-scoped: {:?}",
            report.port_path_failures
        );
        assert!(
            report.run_candidates.is_empty(),
            "invalid case-level paths must not be scheduled: {:?}",
            report.run_candidates
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_rejects_unassigned_entry_trust_vc_path_when_cases_are_split() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-unassigned-case-trust-vc-path");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("upstream test should be written");
        fs::write(
            temp_dir.join("ported/foo.rs"),
            r#"
#[ensures(result == x)]
fn identity(x: i32) -> i32 {
    x
}
"#,
        )
        .expect("ported foo should be written");
        fs::write(
            temp_dir.join("ported/unused.rs"),
            r#"
#[ensures(result == x)]
fn unused(x: i32) -> i32 {
    x
}
"#,
        )
        .expect("unused port should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Case-level paths must assign every entry-level path.",
      "trust_vc_paths": ["ported/foo.rs", "ported/unused.rs"],
      "expected_cases": [
        {
          "case_id": "identity",
          "trust_vc_path": "ported/foo.rs",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        assert!(
            report.port_path_failures.iter().any(|failure| failure
                .contains("entry-level trust_vc_paths value `ported/unused.rs` is not assigned")),
            "case-level splits must execute every declared entry-level path: {:?}",
            report.port_path_failures
        );
        assert!(
            report.run_candidates.is_empty(),
            "unassigned case-level paths must not be scheduled: {:?}",
            report.run_candidates
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_requires_upstream_rust_error_cases_to_map_to_cargo_fixtures() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-rust-error-fixture-required");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(
            upstream_tests.join("erase.rs"),
            r#"
test_verify_one_file! {
    #[test] test_regression_70 verus_code! {
        fn m(v: &mut u64) { }
        fn main() {
            let v = 6;
            m(&mut v);
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot borrow")
}
"#,
        )
        .expect("upstream test should be written");
        fs::write(
            temp_dir.join("ported/erase.rs"),
            r#"
fn test_regression_70() {
    let _ = 6;
}
"#,
        )
        .expect("ported direct file should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/erase.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Upstream Rust errors need cargo fixture evidence.",
      "trust_vc_paths": ["ported/erase.rs"],
      "expected_cases": [
        {
          "case_id": "test_regression_70",
          "expected_verdict": "error",
          "min_obligations": 0,
          "expected_error_patterns": ["cannot borrow"]
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        assert!(
            report.port_path_failures.iter().any(|failure| failure.contains(
                "upstream Rust-error expected_cases entry `test_regression_70` must map to a cargo fixture"
            )),
            "upstream Rust-error cases must require fixture evidence: {:?}",
            report.port_path_failures
        );
        assert!(
            report.run_candidates.is_empty(),
            "upstream Rust-error path failures must not be scheduled: {:?}",
            report.run_candidates
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_rejects_absolute_and_parent_trust_vc_paths() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-paths");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("foo test should be written");
        fs::write(upstream_tests.join("bar.rs"), "").expect("bar test should be written");
        let absolute = temp_dir.join("outside.rs");
        fs::write(&absolute, "").expect("absolute fixture should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            format!(
                r##"{{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {{
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  }},
  "gate": {{
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  }},
  "entries": [
    {{
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Bad absolute path.",
      "trust_vc_paths": ["{}"],
      "expected_cases": [
        {{
          "case_id": "identity",
          "expected_verdict": "verified",
          "min_obligations": 1
        }}
      ]
    }},
    {{
      "upstream_path": "source/rust_verify_test/tests/bar.rs",
      "classification": "ported",
      "owner_issue": "#124",
      "reason": "Bad parent path.",
      "trust_vc_paths": ["../outside.rs"],
      "expected_cases": [
        {{
          "case_id": "identity",
          "expected_verdict": "verified",
          "min_obligations": 1
        }}
      ]
    }}
  ]
}}"##,
                absolute.display()
            ),
        )
        .expect("manifest should be written");

        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        assert_eq!(report.port_path_failures.len(), 2);
        assert!(report
            .port_path_failures
            .iter()
            .any(|entry| entry.contains("repo-relative")));
        assert!(report
            .port_path_failures
            .iter()
            .any(|entry| entry.contains("inside the repo")));

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_rejects_empty_current_dir_and_symlink_trust_vc_paths() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-path-shapes");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(upstream_tests.join("empty.rs"), "").expect("empty upstream should be written");
        fs::write(upstream_tests.join("dot.rs"), "").expect("dot upstream should be written");
        fs::write(upstream_tests.join("cur.rs"), "").expect("cur upstream should be written");
        fs::write(upstream_tests.join("link.rs"), "").expect("link upstream should be written");
        fs::write(temp_dir.join("ported/real.rs"), "").expect("real port should be written");
        #[cfg(unix)]
        {
            use std::os::unix::fs as unix_fs;
            unix_fs::symlink(
                temp_dir.join("ported/real.rs"),
                temp_dir.join("ported/link.rs"),
            )
            .expect("symlink should be created");
        }
        #[cfg(not(unix))]
        fs::write(temp_dir.join("ported/link.rs"), "").expect("link fallback should be written");

        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/empty.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Empty path must not hash the repo root.",
      "trust_vc_paths": [""],
      "expected_cases": [{"case_id": "identity", "expected_verdict": "verified", "min_obligations": 1}]
    },
    {
      "upstream_path": "source/rust_verify_test/tests/dot.rs",
      "classification": "ported",
      "owner_issue": "#124",
      "reason": "Current dir path must not hash the repo root.",
      "trust_vc_paths": ["."],
      "expected_cases": [{"case_id": "identity", "expected_verdict": "verified", "min_obligations": 1}]
    },
    {
      "upstream_path": "source/rust_verify_test/tests/cur.rs",
      "classification": "ported",
      "owner_issue": "#125",
      "reason": "CurDir components are rejected for stable path binding.",
      "trust_vc_paths": ["./ported/real.rs"],
      "expected_cases": [{"case_id": "identity", "expected_verdict": "verified", "min_obligations": 1}]
    },
    {
      "upstream_path": "source/rust_verify_test/tests/link.rs",
      "classification": "ported",
      "owner_issue": "#126",
      "reason": "Top-level symlink paths are rejected for stable path binding.",
      "trust_vc_paths": ["ported/link.rs"],
      "expected_cases": [{"case_id": "identity", "expected_verdict": "verified", "min_obligations": 1}]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        #[cfg(unix)]
        assert_eq!(report.port_path_failures.len(), 4);
        #[cfg(not(unix))]
        assert_eq!(report.port_path_failures.len(), 3);
        assert!(report
            .port_path_failures
            .iter()
            .any(|entry| entry.contains("must not be empty")));
        assert!(report
            .port_path_failures
            .iter()
            .any(|entry| entry.contains("must stay inside the repo: .")));
        assert!(report
            .port_path_failures
            .iter()
            .any(|entry| entry.contains("must stay inside the repo: ./ported/real.rs")));
        #[cfg(unix)]
        assert!(report
            .port_path_failures
            .iter()
            .any(|entry| entry.contains("must not be a symlink")));
        assert!(
            report.accepted_trust_vc_source_hashes.is_empty(),
            "hash evidence must not be partial when accepted paths fail: {:?}",
            report.accepted_trust_vc_source_hashes
        );
        #[cfg(unix)]
        assert!(
            report.run_candidates.is_empty(),
            "accepted entries with path failures must not be scheduled for execution: {:?}",
            report.run_candidates
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_requires_expected_cases_for_accepted_entries() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-expected-cases");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("foo test should be written");
        fs::write(
            temp_dir.join("ported/foo.rs"),
            r#"
#[ensures(result == x)]
fn identity(x: i32) -> i32 {
    x
}
"#,
        )
        .expect("ported foo should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported for TrustVc.",
      "trust_vc_paths": ["ported/foo.rs"]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        assert!(
            report
                .port_path_failures
                .iter()
                .any(|entry| entry.contains("no expected_cases")),
            "accepted entries must declare expected cases: {:?}",
            report.port_path_failures
        );

        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported for TrustVc.",
      "trust_vc_paths": ["ported/foo.rs"],
      "expected_cases": [
        {
          "case_id": "bad-case-id",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be rewritten");
        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        assert!(
            report
                .port_path_failures
                .iter()
                .any(|entry| entry.contains("Rust function identifier")),
            "invalid expected case IDs must fail: {:?}",
            report.port_path_failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn trust_vc_corpus_execution_requires_expected_cases() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-expectations");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("foo test should be written");
        fs::write(
            temp_dir.join("ported/foo.rs"),
            r#"
#[ensures(result == x)]
fn identity(x: i32) -> i32 {
    x
}
"#,
        )
        .expect("ported foo should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported for TrustVc.",
      "trust_vc_paths": ["ported/foo.rs"],
      "expected_cases": [
        {
          "case_id": "identity",
          "upstream_case_id": "identity",
          "expected_verdict": "verified",
          "min_obligations": 1
        },
        {
          "case_id": "missing_case",
          "upstream_case_id": "missing_case",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");
        let corpus = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        assert!(
            corpus.port_path_failures.is_empty(),
            "valid expectations should not fail manifest validation: {:?}",
            corpus.port_path_failures
        );

        let run_report = run_trust_vc_corpus(&temp_dir, &corpus, None);

        assert_eq!(run_report.attempted_paths, 1);
        assert_eq!(run_report.passed_paths, 0);
        assert_eq!(run_report.failed_paths, 1);
        assert_eq!(run_report.results.len(), 1);
        let result = &run_report.results[0];
        assert_eq!(result.status, GateStatus::Failed);
        assert_eq!(
            result.expected_case_ids,
            vec!["identity".to_string(), "missing_case".to_string()]
        );
        assert_eq!(result.observed_case_ids, vec!["identity".to_string()]);
        assert_eq!(result.expected_case_count, 2);
        assert_eq!(result.observed_case_count, 1);
        assert_eq!(result.expected_obligation_count, 2);
        assert!(
            result.observed_obligation_count >= 1,
            "identity should capture at least one obligation: {:?}",
            result.observed_cases
        );
        assert!(
            result
                .failures
                .iter()
                .any(|failure| failure.contains("missing expected case missing_case")),
            "missing expected case should fail the run: {:?}",
            result.failures
        );

        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported for TrustVc.",
      "trust_vc_paths": ["ported/foo.rs"],
      "expected_cases": [
        {
          "case_id": "identity",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be rewritten");
        let corpus = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        let run_report = run_trust_vc_corpus(&temp_dir, &corpus, None);
        assert_eq!(run_report.passed_paths, 1);
        assert_eq!(run_report.failed_paths, 0);
        assert_eq!(run_report.results[0].status, GateStatus::Passed);
        assert_eq!(run_report.results[0].observed_case_ids, vec!["identity"]);
        let observed_case = &run_report.results[0].observed_cases[0];
        assert_eq!(observed_case.verdict, "verified");
        assert_sha256_obligation_fingerprints(observed_case);

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn trust_vc_corpus_execution_rejects_too_few_captured_obligations() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-min-obligations");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("foo test should be written");
        fs::write(
            temp_dir.join("ported/foo.rs"),
            r#"
#[ensures(result == x)]
fn identity(x: i32) -> i32 {
    x
}
"#,
        )
        .expect("ported foo should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported for TrustVc.",
      "trust_vc_paths": ["ported/foo.rs"],
      "expected_cases": [
        {
          "case_id": "identity",
          "expected_verdict": "verified",
          "min_obligations": 2
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let corpus = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        let run_report = run_trust_vc_corpus(&temp_dir, &corpus, None);

        assert_eq!(run_report.failed_paths, 1);
        assert!(
            run_report.results[0]
                .failures
                .iter()
                .any(|failure| failure.contains("expected at least 2 captured obligation")),
            "under-observed cases must fail: {:?}",
            run_report.results[0].failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn trust_vc_corpus_execution_accepts_expected_counterexample_cases() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-counterexample");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("foo test should be written");
        fs::write(
            temp_dir.join("ported/foo.rs"),
            r#"
#[ensures(result == x + 1)]
fn identity_counterexample(x: i32) -> i32 {
    x
}
"#,
        )
        .expect("ported foo should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported expected-fail Verus case for TrustVc.",
      "trust_vc_paths": ["ported/foo.rs"],
      "expected_cases": [
        {
          "case_id": "identity_counterexample",
          "expected_verdict": "counterexample",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let corpus = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        let run_report = run_trust_vc_corpus(&temp_dir, &corpus, None);

        assert_eq!(run_report.passed_paths, 1);
        assert_eq!(run_report.failed_paths, 0);
        let observed_case = &run_report.results[0].observed_cases[0];
        assert_eq!(observed_case.verdict, "counterexample");
        assert_sha256_obligation_fingerprints(observed_case);

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_execution_treats_cargo_trust_vc_integration_tests_as_diagnostic_only() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-cargo-trust-vc-integration");
        let upstream_tests = temp_dir.join(VERUS_CARGO_VERUS_TEST_ROOT);
        let trust_vc_tests = temp_dir.join("crates/cargo-trust-vc/tests");
        fs::create_dir_all(temp_dir.join(VERUS_TEST_ROOT))
            .expect("rust_verify_test root should be created");
        fs::create_dir_all(&upstream_tests).expect("cargo-verus test dir should be created");
        fs::create_dir_all(&trust_vc_tests).expect("cargo-trust-vc test dir should be created");
        fs::write(
            upstream_tests.join("test_late_args.rs"),
            r#"
#[test]
fn late_package_arg_after_release() {}

#[test]
fn z_flag_with_space_is_accepted() {}
"#,
        )
        .expect("upstream cargo-verus test should be written");
        fs::write(
            trust_vc_tests.join("late_args_integration.rs"),
            r#"
fn helper() {}

#[test]
fn late_package_arg_after_release() {
    helper();
}

#[test]
fn z_flag_with_space_is_accepted() {}

#[test]
fn extra_local_regression() {}
"#,
        )
        .expect("cargo-trust-vc integration test should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests", "source/cargo-verus/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/cargo-verus/tests/test_late_args.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Cargo wrapper integration-test evidence.",
      "trust_vc_paths": ["crates/cargo-trust-vc/tests/late_args_integration.rs"],
      "expected_cases": [
        {
          "case_id": "late_package_arg_after_release",
          "expected_verdict": "verified",
          "min_obligations": 1
        },
        {
          "case_id": "z_flag_with_space_is_accepted",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");
        let fake_cargo = temp_dir.join("fake-cargo");
        let record_path = temp_dir.join("cargo-test-cases.txt");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
if [ "$1" != "test" ] || [ "$2" != "--locked" ] || [ "$3" != "--offline" ] || [ "$4" != "-p" ] || [ "$5" != "cargo-trust-vc" ] || [ "$6" != "--test" ] || [ "$7" != "late_args_integration" ] || [ "$8" != "--" ] || [ "$9" != "--exact" ]; then
  echo "unexpected cargo args: $*" >&2
  exit 64
fi
case_name="${10}"
case "$case_name" in
  late_package_arg_after_release|z_flag_with_space_is_accepted) ;;
  *)
    echo "unexpected exact test case: $case_name" >&2
    exit 65
    ;;
esac
printf '%s\n' "$case_name" >> "$TRUST_VC_FAKE_CARGO_CASE_RECORD"
printf 'running 1 test\n'
printf 'test %s ... ok\n\n' "$case_name"
printf 'test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s\n'
"#,
        );
        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = load_corpus_report(&manifest_path, &crate_root, Some(&crate_root))
            .expect("corpus report should load");
        assert!(
            corpus
                .port_path_failures
                .iter()
                .any(|failure| failure.contains("wrapper execution witnesses")),
            "accepted integration test trust_vc_path should not be accepted evidence: {:?}",
            corpus.port_path_failures
        );
        let (direct_inputs, direct_failures) = direct_source_typecheck_inputs(&crate_root, &corpus);
        assert!(
            direct_inputs.is_empty() && direct_failures.is_empty(),
            "cargo-trust-vc integration tests must not be treated as direct TrustVc source: inputs={direct_inputs:?} failures={direct_failures:?}"
        );
        let candidate = TrustVcCorpusRunCandidate {
            upstream_path: "source/cargo-verus/tests/test_late_args.rs".to_string(),
            classification: "ported".to_string(),
            evidence_kind: VerusEvidenceKind::CargoTrustVcIntegrationTest,
            trust_vc_paths: vec!["crates/cargo-trust-vc/tests/late_args_integration.rs".to_string()],
            trust_vc_check_args: Vec::new(),
            expected_cases: vec![
                VerusExpectedCase {
                    case_id: "late_package_arg_after_release".to_string(),
                    upstream_case_id: None,
                    trust_vc_path: None,
                    expected_verdict: VerusExpectedVerdict::Verified,
                    min_obligations: 0,
                    obligation_fingerprints: Vec::new(),
                    expected_error_patterns: Vec::new(),
                    expected_rust_diagnostic_pattern_sets: Vec::new(),
                    forbidden_diagnostic_patterns: Vec::new(),
                    expected_warning_patterns: Vec::new(),
                },
                VerusExpectedCase {
                    case_id: "z_flag_with_space_is_accepted".to_string(),
                    upstream_case_id: None,
                    trust_vc_path: None,
                    expected_verdict: VerusExpectedVerdict::Verified,
                    min_obligations: 0,
                    obligation_fingerprints: Vec::new(),
                    expected_error_patterns: Vec::new(),
                    expected_rust_diagnostic_pattern_sets: Vec::new(),
                    forbidden_diagnostic_patterns: Vec::new(),
                    expected_warning_patterns: Vec::new(),
                },
            ],
        };
        let env = vec![
            ("CARGO".to_string(), fake_cargo.display().to_string()),
            (
                "TRUST_VC_FAKE_CARGO_CASE_RECORD".to_string(),
                record_path.display().to_string(),
            ),
        ];

        let result =
            run_trust_vc_corpus_cargo_trust_vc_integration_test(&crate_root, &candidate, &env);

        assert_eq!(result.status, GateStatus::Passed);
        assert_eq!(
            result.execution_mode,
            TrustVcCorpusExecutionMode::CargoTrustVcIntegrationTest
        );
        assert_eq!(
            result.observed_case_ids,
            vec![
                "late_package_arg_after_release".to_string(),
                "z_flag_with_space_is_accepted".to_string()
            ]
        );
        assert_eq!(result.observed_obligation_count, 0);
        assert_eq!(result.commands.len(), 2);
        for observed_case in &result.observed_cases {
            assert_eq!(
                observed_case.trust_vc_path,
                "crates/cargo-trust-vc/tests/late_args_integration.rs"
            );
            assert_eq!(observed_case.obligation_count, 0);
            assert!(
                observed_case.obligation_fingerprints.is_empty(),
                "cargo-trust-vc integration tests must not emit proof-obligation fingerprints: {observed_case:?}"
            );
        }
        assert_eq!(
            fs::read_to_string(&record_path).expect("case record should be written"),
            "late_package_arg_after_release\nz_flag_with_space_is_accepted\n"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_execution_accepts_explicit_cargo_trust_vc_integration_evidence_kind() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-cargo-trust-vc-evidence-kind");
        let upstream_tests = temp_dir.join(VERUS_CARGO_VERUS_TEST_ROOT);
        let trust_vc_tests = temp_dir.join("crates/cargo-trust-vc/tests");
        fs::create_dir_all(temp_dir.join(VERUS_TEST_ROOT))
            .expect("rust_verify_test root should be created");
        fs::create_dir_all(&upstream_tests).expect("cargo-verus test dir should be created");
        fs::create_dir_all(&trust_vc_tests).expect("cargo-trust-vc test dir should be created");
        fs::write(
            upstream_tests.join("test_late_args.rs"),
            r#"
#[test]
fn late_package_arg_after_release() {}

#[test]
fn z_flag_with_space_is_accepted() {}
"#,
        )
        .expect("upstream cargo-verus test should be written");
        fs::write(
            trust_vc_tests.join("late_args_integration.rs"),
            r#"
#[test]
fn late_package_arg_after_release() {}

#[test]
fn z_flag_with_space_is_accepted() {}
"#,
        )
        .expect("cargo-trust-vc integration test should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests", "source/cargo-verus/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/cargo-verus/tests/test_late_args.rs",
      "classification": "ported",
      "evidence_kind": "cargo_trust_vc_integration_test",
      "owner_issue": "#123",
      "reason": "Cargo wrapper integration-test evidence.",
      "trust_vc_paths": ["crates/cargo-trust-vc/tests/late_args_integration.rs"],
      "expected_cases": [
        {
          "case_id": "late_package_arg_after_release",
          "upstream_case_id": "late_package_arg_after_release",
          "expected_verdict": "verified",
          "min_obligations": 0
        },
        {
          "case_id": "z_flag_with_space_is_accepted",
          "upstream_case_id": "z_flag_with_space_is_accepted",
          "expected_verdict": "verified",
          "min_obligations": 0
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");
        let fake_cargo = temp_dir.join("fake-cargo");
        let record_path = temp_dir.join("cargo-test-cases.txt");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
if [ "$1" != "test" ] || [ "$2" != "--locked" ] || [ "$3" != "--offline" ] || [ "$4" != "-p" ] || [ "$5" != "cargo-trust-vc" ] || [ "$6" != "--test" ] || [ "$7" != "late_args_integration" ] || [ "$8" != "--" ] || [ "$9" != "--exact" ]; then
  echo "unexpected cargo args: $*" >&2
  exit 64
fi
case_name="${10}"
case "$case_name" in
  late_package_arg_after_release|z_flag_with_space_is_accepted) ;;
  *)
    echo "unexpected exact test case: $case_name" >&2
    exit 65
    ;;
esac
printf '%s\n' "$case_name" >> "$TRUST_VC_FAKE_CARGO_CASE_RECORD"
printf 'running 1 test\n'
printf 'test %s ... ok\n\n' "$case_name"
printf 'test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s\n'
"#,
        );
        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = load_corpus_report(&manifest_path, &crate_root, Some(&crate_root))
            .expect("corpus report should load");
        assert!(
            corpus.port_path_failures.is_empty(),
            "explicit cargo-trust-vc integration evidence should be accepted: {:?}",
            corpus.port_path_failures
        );
        assert_eq!(corpus.run_candidates.len(), 1);
        assert_eq!(
            corpus.run_candidates[0].evidence_kind,
            VerusEvidenceKind::CargoTrustVcIntegrationTest
        );
        let env = vec![
            ("CARGO".to_string(), fake_cargo.display().to_string()),
            (
                "TRUST_VC_FAKE_CARGO_CASE_RECORD".to_string(),
                record_path.display().to_string(),
            ),
        ];

        let run_report =
            run_trust_vc_corpus_with_env(&crate_root, &corpus, None, &env, &BTreeMap::new());

        assert_eq!(run_report.failed_paths, 0, "{run_report:?}");
        assert_eq!(trust_vc_corpus_gate(&run_report).status, GateStatus::Passed);
        assert_eq!(
            fs::read_to_string(&record_path).expect("case record should be written"),
            "late_package_arg_after_release\nz_flag_with_space_is_accepted\n"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn trust_vc_corpus_execution_rejects_missing_cargo_trust_vc_integration_test_case() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-cargo-trust-vc-missing-test");
        let trust_vc_tests = temp_dir.join("crates/cargo-trust-vc/tests");
        fs::create_dir_all(&trust_vc_tests).expect("cargo-trust-vc test dir should be created");
        fs::write(
            trust_vc_tests.join("late_args_integration.rs"),
            r#"
#[test]
fn late_package_arg_after_release() {}
"#,
        )
        .expect("cargo-trust-vc integration test should be written");
        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let candidate = TrustVcCorpusRunCandidate {
            upstream_path: "source/cargo-verus/tests/test_late_args.rs".to_string(),
            classification: "ported".to_string(),
            evidence_kind: VerusEvidenceKind::CargoTrustVcIntegrationTest,
            trust_vc_paths: vec!["crates/cargo-trust-vc/tests/late_args_integration.rs".to_string()],
            trust_vc_check_args: Vec::new(),
            expected_cases: vec![VerusExpectedCase {
                case_id: "missing_case".to_string(),
                upstream_case_id: None,
                trust_vc_path: None,
                expected_verdict: VerusExpectedVerdict::Verified,
                min_obligations: 0,
                obligation_fingerprints: Vec::new(),
                expected_error_patterns: Vec::new(),
                expected_rust_diagnostic_pattern_sets: Vec::new(),
                forbidden_diagnostic_patterns: Vec::new(),
                expected_warning_patterns: Vec::new(),
            }],
        };

        let result =
            run_trust_vc_corpus_cargo_trust_vc_integration_test(&crate_root, &candidate, &[]);

        assert_eq!(result.status, GateStatus::Failed);
        assert!(
            result.commands.is_empty(),
            "missing declared tests should fail before cargo test runs: {:?}",
            result.commands
        );
        assert!(
            result
                .failures
                .iter()
                .any(|failure| failure.contains("does not declare #[test] `missing_case`")),
            "missing integration test cases must fail closed: {:?}",
            result.failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn trust_vc_corpus_execution_rejects_observed_case_from_wrong_declared_path() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-case-path-mismatch");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(temp_dir.join("ported/right.rs"), "").expect("right path should be written");
        fs::write(temp_dir.join("ported/wrong.rs"), "").expect("wrong path should be written");
        let candidate = TrustVcCorpusRunCandidate {
            upstream_path: "source/rust_verify_test/tests/foo.rs".to_string(),
            classification: "ported".to_string(),
            evidence_kind: VerusEvidenceKind::ProofObligation,
            trust_vc_paths: vec!["ported/right.rs".to_string()],
            trust_vc_check_args: Vec::new(),
            expected_cases: vec![VerusExpectedCase {
                case_id: "same_name".to_string(),
                upstream_case_id: None,
                trust_vc_path: Some("ported/right.rs".to_string()),
                expected_verdict: VerusExpectedVerdict::Verified,
                min_obligations: 1,
                obligation_fingerprints: Vec::new(),
                expected_error_patterns: Vec::new(),
                expected_rust_diagnostic_pattern_sets: Vec::new(),
                forbidden_diagnostic_patterns: Vec::new(),
                expected_warning_patterns: Vec::new(),
            }],
        };
        let observed_cases = vec![TrustVcCorpusObservedCase {
            case_id: "same_name".to_string(),
            trust_vc_path: "ported/wrong.rs".to_string(),
            verdict: "verified".to_string(),
            obligation_count: 1,
            obligation_fingerprints: vec![
                "sha256:1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef"
                    .to_string(),
            ],
            diagnostic_context: Vec::new(),
            warnings: Vec::new(),
        }];
        let mut failures = Vec::new();

        append_trust_vc_corpus_case_failures(&temp_dir, &candidate, &observed_cases, &mut failures);

        assert!(
            failures.iter().any(|failure| failure.contains(
                "same_name observed in `ported/wrong.rs`, expected source under declared trust_vc_path `ported/right.rs`"
            )),
            "same-name observations from the wrong path must fail: {:?}",
            failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn trust_vc_corpus_execution_rejects_obligation_fingerprint_mismatch() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-fingerprint-mismatch");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(temp_dir.join("ported/right.rs"), "").expect("right path should be written");
        let expected_fingerprint =
            "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".to_string();
        let observed_fingerprint =
            "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".to_string();
        let candidate = TrustVcCorpusRunCandidate {
            upstream_path: "source/rust_verify_test/tests/foo.rs".to_string(),
            classification: "ported".to_string(),
            evidence_kind: VerusEvidenceKind::ProofObligation,
            trust_vc_paths: vec!["ported/right.rs".to_string()],
            trust_vc_check_args: Vec::new(),
            expected_cases: vec![VerusExpectedCase {
                case_id: "same_name".to_string(),
                upstream_case_id: None,
                trust_vc_path: Some("ported/right.rs".to_string()),
                expected_verdict: VerusExpectedVerdict::Verified,
                min_obligations: 1,
                obligation_fingerprints: vec![expected_fingerprint.clone()],
                expected_error_patterns: Vec::new(),
                expected_rust_diagnostic_pattern_sets: Vec::new(),
                forbidden_diagnostic_patterns: Vec::new(),
                expected_warning_patterns: Vec::new(),
            }],
        };
        let observed_cases = vec![TrustVcCorpusObservedCase {
            case_id: "same_name".to_string(),
            trust_vc_path: "ported/right.rs".to_string(),
            verdict: "verified".to_string(),
            obligation_count: 1,
            obligation_fingerprints: vec![observed_fingerprint.clone()],
            diagnostic_context: Vec::new(),
            warnings: Vec::new(),
        }];
        let mut failures = Vec::new();

        append_trust_vc_corpus_case_failures(&temp_dir, &candidate, &observed_cases, &mut failures);

        assert!(
            failures.iter().any(|failure| {
                failure.contains("expected obligation fingerprints")
                    && failure.contains(&expected_fingerprint)
                    && failure.contains(&observed_fingerprint)
            }),
            "fingerprint mismatches must fail corpus execution: {:?}",
            failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn trust_vc_corpus_execution_rejects_invalid_observed_obligation_fingerprint() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-invalid-fingerprint");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(temp_dir.join("ported/right.rs"), "").expect("right path should be written");
        let candidate = TrustVcCorpusRunCandidate {
            upstream_path: "source/rust_verify_test/tests/foo.rs".to_string(),
            classification: "ported".to_string(),
            evidence_kind: VerusEvidenceKind::ProofObligation,
            trust_vc_paths: vec!["ported/right.rs".to_string()],
            trust_vc_check_args: Vec::new(),
            expected_cases: vec![VerusExpectedCase {
                case_id: "same_name".to_string(),
                upstream_case_id: None,
                trust_vc_path: Some("ported/right.rs".to_string()),
                expected_verdict: VerusExpectedVerdict::Verified,
                min_obligations: 1,
                obligation_fingerprints: Vec::new(),
                expected_error_patterns: Vec::new(),
                expected_rust_diagnostic_pattern_sets: Vec::new(),
                forbidden_diagnostic_patterns: Vec::new(),
                expected_warning_patterns: Vec::new(),
            }],
        };
        let observed_cases = vec![TrustVcCorpusObservedCase {
            case_id: "same_name".to_string(),
            trust_vc_path: "ported/right.rs".to_string(),
            verdict: "verified".to_string(),
            obligation_count: 1,
            obligation_fingerprints: vec!["not-a-sha256".to_string()],
            diagnostic_context: Vec::new(),
            warnings: Vec::new(),
        }];
        let mut failures = Vec::new();

        append_trust_vc_corpus_case_failures(&temp_dir, &candidate, &observed_cases, &mut failures);

        assert!(
            failures
                .iter()
                .any(|failure| failure.contains("invalid observed obligation_fingerprints")),
            "invalid observed fingerprints must fail corpus execution: {:?}",
            failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn trust_vc_corpus_execution_rejects_obligation_count_without_fingerprint() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-count-without-fingerprint");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(temp_dir.join("ported/right.rs"), "").expect("right path should be written");
        let candidate = TrustVcCorpusRunCandidate {
            upstream_path: "source/rust_verify_test/tests/foo.rs".to_string(),
            classification: "ported".to_string(),
            evidence_kind: VerusEvidenceKind::ProofObligation,
            trust_vc_paths: vec!["ported/right.rs".to_string()],
            trust_vc_check_args: Vec::new(),
            expected_cases: vec![VerusExpectedCase {
                case_id: "same_name".to_string(),
                upstream_case_id: None,
                trust_vc_path: Some("ported/right.rs".to_string()),
                expected_verdict: VerusExpectedVerdict::Verified,
                min_obligations: 1,
                obligation_fingerprints: Vec::new(),
                expected_error_patterns: Vec::new(),
                expected_rust_diagnostic_pattern_sets: Vec::new(),
                forbidden_diagnostic_patterns: Vec::new(),
                expected_warning_patterns: Vec::new(),
            }],
        };
        let observed_cases = vec![TrustVcCorpusObservedCase {
            case_id: "same_name".to_string(),
            trust_vc_path: "ported/right.rs".to_string(),
            verdict: "verified".to_string(),
            obligation_count: 1,
            obligation_fingerprints: Vec::new(),
            diagnostic_context: Vec::new(),
            warnings: Vec::new(),
        }];
        let mut failures = Vec::new();

        append_trust_vc_corpus_case_failures(&temp_dir, &candidate, &observed_cases, &mut failures);

        assert!(
            failures.iter().any(|failure| failure
                .contains("observed obligation_count 1 but reported no obligation_fingerprints")),
            "positive obligation counts without fingerprints must fail: {:?}",
            failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn trust_vc_corpus_execution_counts_duplicate_observed_obligation_fingerprints_once() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-duplicate-fingerprint");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(temp_dir.join("ported/right.rs"), "").expect("right path should be written");
        let fingerprint =
            "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".to_string();
        let candidate = TrustVcCorpusRunCandidate {
            upstream_path: "source/rust_verify_test/tests/foo.rs".to_string(),
            classification: "ported".to_string(),
            evidence_kind: VerusEvidenceKind::ProofObligation,
            trust_vc_paths: vec!["ported/right.rs".to_string()],
            trust_vc_check_args: Vec::new(),
            expected_cases: vec![VerusExpectedCase {
                case_id: "same_name".to_string(),
                upstream_case_id: None,
                trust_vc_path: Some("ported/right.rs".to_string()),
                expected_verdict: VerusExpectedVerdict::Verified,
                min_obligations: 2,
                obligation_fingerprints: vec![
                    fingerprint.clone(),
                    "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
                        .to_string(),
                ],
                expected_error_patterns: Vec::new(),
                expected_rust_diagnostic_pattern_sets: Vec::new(),
                forbidden_diagnostic_patterns: Vec::new(),
                expected_warning_patterns: Vec::new(),
            }],
        };
        let observed_cases = vec![TrustVcCorpusObservedCase {
            case_id: "same_name".to_string(),
            trust_vc_path: "ported/right.rs".to_string(),
            verdict: "verified".to_string(),
            obligation_count: 2,
            obligation_fingerprints: vec![fingerprint.clone(), fingerprint],
            diagnostic_context: Vec::new(),
            warnings: Vec::new(),
        }];
        let mut failures = Vec::new();

        append_trust_vc_corpus_case_failures(&temp_dir, &candidate, &observed_cases, &mut failures);

        assert!(
            failures
                .iter()
                .any(|failure| failure
                    .contains("expected at least 2 unique obligation_fingerprints")),
            "duplicate observed fingerprints must not inflate obligation evidence: {:?}",
            failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn trust_vc_corpus_execution_checks_forbidden_diagnostic_context() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-diagnostic-context");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(upstream_tests.join("ui.rs"), "").expect("ui test should be written");
        fs::write(
            temp_dir.join("ported/ui.rs"),
            r#"
#[ensures(true)]
fn ui_context_counterexample() {
    if false {
        let _ = 0i32; // INCORRECT CONTEXT
    }

    trust_vc::assert!(1i32 == 2i32);
}
"#,
        )
        .expect("ported ui should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/ui.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported diagnostic-context Verus case for TrustVc.",
      "trust_vc_paths": ["ported/ui.rs"],
      "expected_cases": [
        {
          "case_id": "ui_context_counterexample",
          "expected_verdict": "counterexample",
          "min_obligations": 1,
          "forbidden_diagnostic_patterns": ["INCORRECT CONTEXT"]
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let corpus = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        let run_report = run_trust_vc_corpus(&temp_dir, &corpus, None);

        assert_eq!(run_report.passed_paths, 1);
        assert_eq!(run_report.failed_paths, 0);
        let observed_case = &run_report.results[0].observed_cases[0];
        assert!(
            observed_case
                .diagnostic_context
                .iter()
                .any(|entry| entry.contains("trust_vc::assert!(1i32 == 2i32)")),
            "assertion source line should be captured as diagnostic context: {:?}",
            observed_case.diagnostic_context
        );
        assert!(
            observed_case
                .diagnostic_context
                .iter()
                .all(|entry| !entry.contains("INCORRECT CONTEXT")),
            "dead branch marker must not appear in diagnostic context: {:?}",
            observed_case.diagnostic_context
        );

        fs::write(
            temp_dir.join("ported/ui.rs"),
            r#"
#[ensures(true)]
fn ui_context_counterexample() {
    trust_vc::assert!(1i32 == 2i32); // INCORRECT CONTEXT
}
"#,
        )
        .expect("ported ui should be rewritten");
        let corpus = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should reload");
        let run_report = run_trust_vc_corpus(&temp_dir, &corpus, None);
        assert_eq!(run_report.failed_paths, 1);
        assert!(
            run_report.results[0].failures.iter().any(|failure| {
                failure.contains("diagnostic context unexpectedly contained forbidden pattern")
            }),
            "forbidden diagnostic context must fail the run: {:?}",
            run_report.results[0].failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn trust_vc_corpus_execution_accepts_expected_extraction_error_cases() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-extraction-error");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("foo test should be written");
        fs::write(
            temp_dir.join("ported/foo.rs"),
            r#"
#[requires(!!!)]
fn bad_requires(x: i32) -> i32 {
    x
}
"#,
        )
        .expect("ported foo should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported expected-error Verus case for TrustVc.",
      "trust_vc_paths": ["ported/foo.rs"],
      "expected_cases": [
        {
          "case_id": "bad_requires",
          "expected_verdict": "error",
          "min_obligations": 0,
          "expected_error_patterns": ["Failed to parse"]
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let corpus = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        assert!(
            corpus.port_path_failures.is_empty(),
            "expected error cases may declare zero obligations: {:?}",
            corpus.port_path_failures
        );
        let run_report = run_trust_vc_corpus(&temp_dir, &corpus, None);

        assert_eq!(run_report.passed_paths, 1);
        assert_eq!(run_report.failed_paths, 0);
        assert_eq!(
            run_report.results[0].observed_case_ids,
            vec!["bad_requires"]
        );
        assert_eq!(run_report.results[0].observed_cases[0].verdict, "error");
        assert_eq!(run_report.results[0].observed_cases[0].obligation_count, 0);

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn trust_vc_corpus_scan_ignores_pure_spec_helpers() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-spec-helper");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");
        let source_path = temp_dir.join("ported.rs");
        fs::write(
            &source_path,
            r#"
#[trust_vc::decreases(n)]
#[trust_vc::spec]
fn fib_compute(n: u64) -> u64 {
    if n <= 1 {
        n
    } else {
        fib_compute(n - 1) + fib_compute(n - 2)
    }
}

#[trust_vc::ensures(true)]
fn target() {}
"#,
        )
        .expect("ported source should be written");

        let mut functions = Vec::new();
        let mut source_errors = Vec::new();
        scan_trust_vc_corpus_file(&source_path, &mut functions, &mut source_errors);

        assert!(
            source_errors.is_empty(),
            "spec helper fixture should not produce source errors: {source_errors:?}"
        );
        let names = functions
            .iter()
            .map(|function| function.name.as_str())
            .collect::<Vec<_>>();
        assert_eq!(
            names,
            vec!["target"],
            "pure spec helpers support verified cases but are not evidence cases themselves"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn trust_vc_corpus_execution_rejects_uncased_direct_source_errors() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-source-error");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("foo test should be written");
        fs::write(
            temp_dir.join("ported/foo.rs"),
            r#"
#[ensures(result == x)]
fn compiler_error_case(x: i32) -> i32 {
    x
"#,
        )
        .expect("ported foo should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported expected compiler-error Verus case for TrustVc.",
      "trust_vc_paths": ["ported/foo.rs"],
      "expected_cases": [
        {
          "case_id": "compiler_error_case",
          "expected_verdict": "error",
          "min_obligations": 0,
          "expected_error_patterns": ["compiler_error_case"]
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let corpus = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        let run_report = run_trust_vc_corpus(&temp_dir, &corpus, None);

        assert_eq!(run_report.passed_paths, 0);
        assert_eq!(run_report.failed_paths, 1);
        let result = &run_report.results[0];
        assert_eq!(result.function_count, 0);
        assert!(result.observed_case_ids.is_empty());
        assert!(
            result
                .failures
                .iter()
                .any(|failure| failure.contains("failed to parse TrustVc source")),
            "uncased source parse errors must fail instead of satisfying an expected case: {:?}",
            result.failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn trust_vc_corpus_execution_records_unsafe_proof_mode_errors_as_expected_cases() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-unsafe-proof-error");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("foo test should be written");
        fs::write(
            temp_dir.join("ported/foo.rs"),
            r#"
#[trust_vc::proof]
unsafe fn unsafe_proof_fn_fail() {
}
"#,
        )
        .expect("ported foo should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported expected unsafe proof diagnostic for TrustVc.",
      "trust_vc_paths": ["ported/foo.rs"],
      "expected_cases": [
        {
          "case_id": "unsafe_proof_fn_fail",
          "expected_verdict": "error",
          "min_obligations": 0,
          "expected_error_patterns": ["'unsafe' only makes sense on exec-mode functions"]
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let corpus = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        let run_report = run_trust_vc_corpus(&temp_dir, &corpus, None);

        assert_eq!(run_report.passed_paths, 1);
        assert_eq!(run_report.failed_paths, 0);
        let result = &run_report.results[0];
        assert_eq!(result.function_count, 0);
        assert_eq!(result.observed_case_ids, vec!["unsafe_proof_fn_fail"]);
        assert_eq!(result.observed_cases[0].verdict, "error");
        assert_eq!(result.observed_cases[0].obligation_count, 0);

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_still_requires_obligations_for_non_error_expected_cases() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-non-error-min-obligations");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("foo test should be written");
        fs::write(
            temp_dir.join("ported/foo.rs"),
            r#"
#[ensures(result == x)]
fn identity(x: i32) -> i32 {
    x
}
"#,
        )
        .expect("ported foo should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Verified cases still need captured obligations.",
      "trust_vc_paths": ["ported/foo.rs"],
      "expected_cases": [
        {
          "case_id": "identity",
          "expected_verdict": "verified",
          "min_obligations": 0
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let corpus = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        assert!(
            corpus
                .port_path_failures
                .iter()
                .any(|failure| failure.contains("min_obligations >= 1")),
            "non-error expected cases must still require captured obligations: {:?}",
            corpus.port_path_failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn trust_vc_corpus_execution_rejects_split_paths_without_case_bindings() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-aggregate-fixture");
        let upstream_tests = temp_dir
            .join(VERUS_TEST_ROOT)
            .join("cargo-tests/verified/basic/src");
        fs::create_dir_all(&upstream_tests).expect("upstream fixture dir should be created");
        fs::create_dir_all(temp_dir.join("ported/basic_fixture/src"))
            .expect("ported fixture dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(upstream_tests.join("lib.rs"), "").expect("upstream test should be written");
        fs::write(
            temp_dir.join("ported/alpha.rs"),
            r#"
#[ensures(result == x)]
fn alpha(x: i32) -> i32 {
    x
}
"#,
        )
        .expect("ported alpha should be written");
        fs::write(
            temp_dir.join("ported/basic_fixture/src/lib.rs"),
            r#"
#[ensures(result == x)]
fn beta(x: i32) -> i32 {
    x
}
"#,
        )
        .expect("ported fixture lib should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/cargo-tests/verified/basic/src/lib.rs",
      "classification": "ported",
      "owner_issue": "#2780",
      "reason": "Cargo fixture port split across a direct file and fixture crate.",
      "trust_vc_paths": ["ported/alpha.rs", "ported/basic_fixture"],
      "expected_cases": [
        {
          "case_id": "alpha",
          "expected_verdict": "verified",
          "min_obligations": 1
        },
        {
          "case_id": "beta",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let corpus = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        assert!(
            corpus.port_path_failures.iter().any(|failure| failure
                .contains("expected_cases entry `alpha` must declare trust_vc_path")),
            "split trust_vc_paths must bind each expected case to a path: {:?}",
            corpus.port_path_failures
        );
        assert!(
            corpus.port_path_failures.iter().any(|failure| failure
                .contains("accepted directory ports must be cargo fixtures with Cargo.toml")),
            "plain directory trust_vc_paths must fail closed: {:?}",
            corpus.port_path_failures
        );
        assert!(
            corpus.run_candidates.is_empty(),
            "unsafe split path entries must not be scheduled for corpus execution: {:?}",
            corpus.run_candidates
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn trust_vc_corpus_cargo_fixture_rejects_mixed_error_and_non_error_cases() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-cargo-mixed-cases");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT).join("cargo-tests/mixed/src");
        let fixture_root = temp_dir.join("ported/mixed_fixture");
        fs::create_dir_all(&upstream_tests).expect("upstream fixture dir should be created");
        fs::create_dir_all(fixture_root.join("src")).expect("ported fixture dir should be created");
        fs::write(upstream_tests.join("lib.rs"), "").expect("upstream test should be written");
        fs::write(
            fixture_root.join("Cargo.toml"),
            r#"[package]
name = "mixed-fixture"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("fixture Cargo.toml should be written");
        fs::write(fixture_root.join("src/lib.rs"), "").expect("fixture lib should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/cargo-tests/mixed/src/lib.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "One cargo fixture cannot prove both Rust-error and non-error cases.",
      "trust_vc_paths": ["ported/mixed_fixture"],
      "expected_cases": [
        {
          "case_id": "fixture_ok",
          "upstream_case_id": "fixture_ok",
          "expected_verdict": "verified",
          "min_obligations": 1
        },
        {
          "case_id": "fixture_rust_error",
          "upstream_case_id": "fixture_rust_error",
          "expected_verdict": "error",
          "min_obligations": 0,
          "expected_error_patterns": ["fixture_rust_error"]
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let corpus = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        let run_report = run_trust_vc_corpus(&temp_dir, &corpus, None);

        assert_eq!(run_report.attempted_paths, 1);
        assert_eq!(run_report.passed_paths, 0);
        assert_eq!(run_report.failed_paths, 1);
        let result = &run_report.results[0];
        assert_eq!(
            result.execution_mode,
            TrustVcCorpusExecutionMode::CargoFixture
        );
        assert!(
            result.failures.iter().any(|failure| failure
                .contains("cannot mix expected Rust-error cases with non-error cases")),
            "mixed cargo fixture cases must fail closed: {:?}",
            result.failures
        );
        assert!(
            result.command.is_none() && result.commands.is_empty(),
            "mixed fixture cases should fail before running commands: {:?}",
            result
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_execution_splits_case_level_paths_for_mixed_upstream_file() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-mixed-split");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        let fixture_root = temp_dir.join("ported/erase_error");
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::create_dir_all(fixture_root.join("src")).expect("ported fixture dir should be created");
        fs::write(
            upstream_tests.join("erase.rs"),
            r#"
test_verify_one_file! {
    #[test] test_regression_78 verus_code! {
        proof fn f1() { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_regression_70 verus_code! {
        fn m(v: &mut u64) { }
        fn main() {
            let v = 6;
            m(&mut v);
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot borrow")
}
"#,
        )
        .expect("upstream test should be written");
        fs::write(
            temp_dir.join("ported/erase_ok.rs"),
            r#"
#[ensures(result == x)]
fn test_regression_78(x: i32) -> i32 {
    x
}
"#,
        )
        .expect("ported direct case should be written");
        fs::write(
            fixture_root.join("Cargo.toml"),
            r#"[package]
name = "erase-error-fixture"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("fixture Cargo.toml should be written");
        fs::write(fixture_root.join("Cargo.lock"), "version = 4\n")
            .expect("fixture Cargo.lock should be written");
        fs::write(
            fixture_root.join("src/lib.rs"),
            r#"
pub fn test_regression_70() {
    let mut values = vec![1];
    let first = &values[0];
    values.push(2);
    let _ = *first;
}
"#,
        )
        .expect("fixture source should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/erase.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Mixed upstream file split by expected case path.",
      "trust_vc_paths": ["ported/erase_ok.rs", "ported/erase_error"],
      "expected_cases": [
        {
          "case_id": "test_regression_78",
          "upstream_case_id": "test_regression_78",
          "trust_vc_path": "ported/erase_ok.rs",
          "expected_verdict": "verified",
          "min_obligations": 1
        },
        {
          "case_id": "test_regression_70",
          "upstream_case_id": "test_regression_70",
          "trust_vc_path": "ported/erase_error",
          "expected_verdict": "error",
          "min_obligations": 0,
          "expected_error_patterns": ["cannot borrow"]
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");
        let fake_cargo = temp_dir.join("fake-cargo");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
if [ "$1" != "check" ] || [ "$2" != "--message-format=json" ] || [ "$3" != "--all-targets" ] || [ "$4" != "--locked" ] || [ "$5" != "--offline" ]; then
  echo "unexpected cargo args: $*" >&2
  exit 64
fi
cat <<'JSON'
{"reason":"compiler-message","message":{"level":"error","message":"cannot borrow `values` as mutable because it is also borrowed as immutable","code":{"code":"E0502"},"spans":[{"file_name":"src/lib.rs","is_primary":true}],"rendered":"error[E0502]: cannot borrow `values` as mutable because it is also borrowed as immutable\n"}}
JSON
exit 101
"#,
        );
        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = load_corpus_report(&manifest_path, &crate_root, Some(&crate_root))
            .expect("corpus report should load");
        assert!(
            corpus.port_path_failures.is_empty(),
            "valid split paths should not fail path validation: {:?}",
            corpus.port_path_failures
        );
        assert!(
            corpus.upstream_case_failures.is_empty(),
            "case-level split should still cover upstream cases: {:?}",
            corpus.upstream_case_failures
        );
        assert_eq!(
            corpus
                .run_candidates
                .iter()
                .map(|candidate| candidate.trust_vc_paths.clone())
                .collect::<Vec<_>>(),
            vec![
                vec!["ported/erase_error".to_string()],
                vec!["ported/erase_ok.rs".to_string()]
            ]
        );
        let env = vec![
            ("CARGO".to_string(), fake_cargo.display().to_string()),
            (
                "CARGO_HOME".to_string(),
                temp_dir.join("isolated-cargo-home").display().to_string(),
            ),
        ];

        let run_report =
            run_trust_vc_corpus_with_env(&crate_root, &corpus, None, &env, &BTreeMap::new());

        assert_eq!(run_report.attempted_paths, 2);
        assert_eq!(run_report.passed_paths, 2);
        assert_eq!(run_report.failed_paths, 0);
        assert_eq!(run_report.results.len(), 2);
        let rust_error_result = run_report
            .results
            .iter()
            .find(|result| result.expected_case_ids == ["test_regression_70"])
            .expect("Rust-error fixture result should be present");
        assert_eq!(
            rust_error_result.execution_mode,
            TrustVcCorpusExecutionMode::CargoFixture
        );
        assert_eq!(
            rust_error_result.observed_case_ids,
            vec!["test_regression_70"]
        );
        assert_eq!(rust_error_result.observed_cases[0].verdict, "error");
        assert_eq!(
            rust_error_result.observed_cases[0].trust_vc_path,
            "ported/erase_error/src/lib.rs"
        );
        let verified_result = run_report
            .results
            .iter()
            .find(|result| result.expected_case_ids == ["test_regression_78"])
            .expect("direct verified result should be present");
        assert_eq!(
            verified_result.execution_mode,
            TrustVcCorpusExecutionMode::DirectSource
        );
        assert_eq!(
            verified_result.observed_case_ids,
            vec!["test_regression_78"]
        );
        assert_sha256_obligation_fingerprints(&verified_result.observed_cases[0]);

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_execution_dispatches_cargo_fixture_to_current_binary() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-cargo-fixture");
        let upstream_tests = temp_dir
            .join(VERUS_TEST_ROOT)
            .join("cargo-tests/verified/basic/src");
        let fixture_root = temp_dir.join("ported/basic_fixture");
        fs::create_dir_all(&upstream_tests).expect("upstream fixture dir should be created");
        fs::create_dir_all(fixture_root.join("src")).expect("ported fixture dir should be created");
        fs::write(upstream_tests.join("lib.rs"), "").expect("upstream test should be written");
        fs::write(
            fixture_root.join("Cargo.toml"),
            r#"[package]
name = "basic-fixture"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("fixture Cargo.toml should be written");
        fs::write(fixture_root.join("Cargo.lock"), "version = 4\n")
            .expect("fixture Cargo.lock should be written");
        fs::write(
            fixture_root.join("src/lib.rs"),
            r#"
#[ensures(result == x)]
fn fixture_ok(x: i32) -> i32 {
    x
}
"#,
        )
        .expect("fixture source should be written");
        let fake_cargo = temp_dir.join("fake-cargo");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
if [ "$1" != "check" ] || [ "$2" != "--message-format=json" ] || [ "$3" != "--all-targets" ] || [ "$4" != "--locked" ] || [ "$5" != "--offline" ]; then
  echo "unexpected cargo args: $*" >&2
  exit 64
fi
mkdir -p "$CARGO_TARGET_DIR/debug/deps"
printf '%s: %s\n' "$CARGO_TARGET_DIR/debug/deps/libbasic_fixture.rmeta" "$(pwd)/src/lib.rs" > "$CARGO_TARGET_DIR/debug/deps/basic_fixture.d"
cat <<'JSON'
{"reason":"compiler-artifact"}
JSON
exit 0
"#,
        );
        let fake_binary = temp_dir.join("fake-cargo-trust-vc");
        write_executable(
            &fake_binary,
            r#"#!/usr/bin/env bash
if [ "$1" != "check" ] || [ "$2" != "--json" ] || [ "$3" != "--emit-certificate" ] || [ "$4" != "." ]; then
  echo "unexpected args: $*" >&2
  exit 64
fi
if [ -z "$CARGO_HOME" ] || [ ! -x "$CARGO" ]; then
  echo "missing isolated cargo environment" >&2
  exit 65
fi
mkdir -p .trust_vc
cat > .trust_vc/proof-certificate.json <<'JSON'
{
  "schema_version": 1,
  "trust_vc_version": "test",
  "generated_at_unix_secs": 0,
  "crate_name": "basic-fixture",
  "functions": [
    {
      "name": "helper_spec",
      "file": "src/lib.rs",
      "line": 1,
      "status": "skipped",
      "obligations": []
    },
    {
      "name": "fixture_ok",
      "file": "src/lib.rs",
      "line": 3,
      "status": "verified",
      "obligations": [
        {
          "name": "postcondition",
          "kind": "assert",
          "condition_hash": "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
          "status": "verified"
        },
        {
          "name": "assumption",
          "kind": "assume",
          "condition_hash": "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
          "status": "assumed"
        }
      ]
    }
  ]
}
JSON
cat <<'JSON'
{
  "crate": "basic-fixture",
  "functions": [
    {
      "file": "src/lib.rs",
      "line": 3,
      "name": "fixture_ok",
      "result": "verified",
      "duration_ms": 0
    }
  ],
  "summary": {
    "verified": 1,
    "counterexample": 0,
    "unknown": 0,
    "error": 0,
    "skipped": 1
  }
}
JSON
"#,
        );

        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/cargo-tests/verified/basic/src/lib.rs",
      "classification": "ported",
      "owner_issue": "#2780",
      "reason": "Cargo fixture port.",
      "trust_vc_paths": ["ported/basic_fixture"],
      "expected_cases": [
        {
          "case_id": "fixture_ok",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = load_corpus_report(&manifest_path, &crate_root, Some(&crate_root))
            .expect("corpus report should load");
        let env = vec![
            (
                "CARGO_HOME".to_string(),
                temp_dir.join("isolated-cargo-home").display().to_string(),
            ),
            ("CARGO".to_string(), fake_cargo.display().to_string()),
        ];
        let run_report = run_trust_vc_corpus_with_trust_vc_binary_and_env(
            &crate_root,
            &corpus,
            None,
            &env,
            Some(&fake_binary),
            &BTreeMap::new(),
        );

        assert_eq!(run_report.attempted_paths, 1);
        assert_eq!(run_report.passed_paths, 1);
        assert_eq!(run_report.failed_paths, 0);
        assert_eq!(run_report.results.len(), 1);
        let result = &run_report.results[0];
        assert_eq!(
            result.execution_mode,
            TrustVcCorpusExecutionMode::CargoFixture
        );
        assert_eq!(
            result
                .command
                .as_ref()
                .and_then(|command| command.cwd.canonicalize().ok()),
            Some(
                fixture_root
                    .canonicalize()
                    .expect("fixture root should canonicalize")
            )
        );
        assert_eq!(
            result
                .command
                .as_ref()
                .map(|command| command.args.as_slice()),
            Some(
                &[
                    "check".to_string(),
                    "--json".to_string(),
                    "--emit-certificate".to_string(),
                    ".".to_string()
                ][..]
            )
        );
        assert_eq!(result.observed_case_ids, vec!["fixture_ok".to_string()]);
        assert!(
            !result
                .observed_case_ids
                .iter()
                .any(|case| case == "helper_spec"),
            "skipped helper functions from cargo-trust-vc certificates are not accepted corpus cases"
        );
        assert_eq!(result.observed_cases[0].obligation_count, 1);
        assert_eq!(
            result.observed_cases[0].trust_vc_path,
            "ported/basic_fixture/src/lib.rs"
        );
        assert!(
            !fixture_root
                .join(certificate::CERTIFICATE_DIR)
                .join(certificate::CERTIFICATE_FILENAME)
                .exists(),
            "cargo fixture execution should not leave generated proof certificates behind"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn trust_vc_corpus_certificate_rejects_invalid_condition_hash() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-invalid-certificate-hash");
        let fixture_root = temp_dir.join("ported/basic_fixture");
        fs::create_dir_all(fixture_root.join("src")).expect("fixture src should be created");
        fs::write(fixture_root.join("src/lib.rs"), "fn fixture_ok() {}\n")
            .expect("fixture source should be written");
        let certificate_path = fixture_root.join("proof-certificate.json");
        fs::write(
            &certificate_path,
            r#"{
  "schema_version": 1,
  "trust_vc_version": "test",
  "generated_at_unix_secs": 0,
  "crate_name": "basic-fixture",
  "functions": [
    {
      "name": "fixture_ok",
      "file": "src/lib.rs",
      "line": 1,
      "status": "verified",
      "obligations": [
        {
          "name": "postcondition",
          "kind": "assert",
          "condition_hash": "not-a-sha256",
          "status": "verified"
        }
      ]
    }
  ]
}"#,
        )
        .expect("certificate should be written");

        let error =
            observed_cases_from_trust_vc_certificate(&temp_dir, &fixture_root, &certificate_path)
                .expect_err("invalid certificate condition_hash should fail");

        assert!(
            error.contains("invalid obligation condition_hash") && error.contains("not-a-sha256"),
            "unexpected certificate validation error: {error}"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    fn write_spec_use_sidecar_fixture(temp_dir: &Path) -> PathBuf {
        let fixture_root = temp_dir.join("ported/cargo_spec_use");
        let dep1_root = temp_dir.join("ported/cargo_spec_def");
        let dep2_root = temp_dir.join("ported/cargo_spec_def2");
        for root in [&fixture_root, &dep1_root, &dep2_root] {
            fs::create_dir_all(root.join("src")).expect("fixture src dir should be created");
            fs::write(root.join("Cargo.lock"), "version = 4\n")
                .expect("fixture lockfile should be written");
        }
        fs::write(
            fixture_root.join("Cargo.toml"),
            r#"[package]
name = "spec_use"
version = "0.1.0"
edition = "2021"

[dependencies]
spec_def = { path = "../cargo_spec_def" }
spec_def2 = { path = "../cargo_spec_def2", package = "spec_def" }
"#,
        )
        .expect("spec_use manifest should be written");
        fs::write(
            fixture_root.join("src/lib.rs"),
            r#"
pub fn concrete_b(x: u16) -> u16 { x }
pub fn concrete_caller(x: u16) -> u16 { spec_def::concrete_a(x) }
pub fn test(x: u16) -> bool { spec_def::double(x) == spec_def2::double(x) - 1 }
pub fn lib(x: u16) -> u16 { concrete_caller(x) }
"#,
        )
        .expect("spec_use source should be written");
        for (root, version) in [(&dep1_root, "0.1.0"), (&dep2_root, "0.2.0")] {
            fs::write(
                root.join("Cargo.toml"),
                format!(
                    r#"[package]
name = "spec_def"
version = "{version}"
edition = "2021"
"#
                ),
            )
            .expect("producer manifest should be written");
            fs::write(
                root.join("src/lib.rs"),
                r#"
pub fn concrete_a(x: u16) -> u16 { x }
pub fn double(x: u16) -> i128 { x as i128 + x as i128 }
"#,
            )
            .expect("producer source should be written");
        }
        fixture_root
    }

    #[cfg(unix)]
    fn write_spec_use_sidecar_fake_cargo(path: &Path, log_path: &Path, missing_sidecar: bool) {
        let missing_sidecar = if missing_sidecar { "1" } else { "0" };
        write_executable(
            path,
            &format!(
                r#"#!/usr/bin/env bash
printf '%s|%s\n' "$(basename "$PWD")" "$*" >> "{}"
if [ "$1" = "check" ] && [ "$2" = "--message-format=json" ] && [ "$3" = "--all-targets" ] && [ "$4" = "--locked" ] && [ "$5" = "--offline" ]; then
  mkdir -p "$CARGO_TARGET_DIR/debug/deps"
  printf '%s: %s\n' "$CARGO_TARGET_DIR/debug/deps/libspec_use.rmeta" "$(pwd)/src/lib.rs" > "$CARGO_TARGET_DIR/debug/deps/spec_use.d"
  echo '{{"reason":"compiler-artifact"}}'
  exit 0
fi
if [ "$(basename "$PWD")" = "cargo_spec_use" ] && [ "$1" = "check" ] && [ "$2" = "--lib" ] && [ "$3" = "--locked" ] && [ "$4" = "--offline" ]; then
  mkdir -p "$CARGO_TARGET_DIR/debug/deps"
  driver_args="$(env | grep '^ __VERUS_DRIVER_ARGS_FOR_' || true)"
  case "$driver_args" in
    *"import-dep-if-present=spec_def__VERUS_DRIVER_ARGS_SEP__"*|*"import-dep-if-present=spec_def") ;;
    *)
      echo "missing spec_def import arg for spec_use sidecar build" >&2
      exit 66
      ;;
  esac
  case "$driver_args" in
    *"import-dep-if-present=spec_def2"*) ;;
    *)
      echo "missing spec_def2 import arg for spec_use sidecar build" >&2
      exit 67
      ;;
  esac
  if [ "$(env | grep -c '^__VERUS_DRIVER_VERIFY_')" -lt 3 ]; then
    echo "spec_use sidecar build should verify spec_use, spec_def, and spec_def2" >&2
    exit 68
  fi
  for dep in spec_def spec_def2; do
    metadata="$CARGO_TARGET_DIR/debug/deps/lib$dep.rmeta"
    printf 'fake metadata' > "$metadata"
    cat > "$CARGO_TARGET_DIR/debug/deps/lib$dep.vir" <<JSON
trust-vc-rustc-wrapper-artifact-v1
{{
  "schema_version": 1,
  "artifact_kind": "cargo-trust-vc-rustc-wrapper-dependency-metadata",
  "crate_name": "spec_def",
  "package_name": "spec_def",
  "package_version": "0.1.0",
  "package_env_id": "test-package-id",
  "manifest_path": "$(pwd)/../cargo_spec_def/Cargo.toml",
  "metadata_path": "$metadata",
  "metadata_len": 13,
  "metadata_sha256": "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
  "source_path": "$(pwd)/../cargo_spec_def/src/lib.rs",
  "source_len": 1,
  "source_sha256": "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
  "semantic_payload": {{
    "kind": "trust-vc-semantic-facts-v1",
    "proof_facts_exported": true,
    "concrete_functions": [
      {{
        "name": "concrete_a",
        "return_type": "u16",
        "params": [{{"name": "x", "ty": "u16"}}],
        "return_binding": "result",
        "requires": [],
        "ensures": ["result == x"]
      }}
    ]
  }}
}}
JSON
  done
  metadata="$CARGO_TARGET_DIR/debug/deps/libspec_use.rmeta"
  printf 'fake metadata' > "$metadata"
  cat > "$CARGO_TARGET_DIR/debug/deps/libspec_use.vir" <<JSON
trust-vc-rustc-wrapper-artifact-v1
{{
  "schema_version": 1,
  "artifact_kind": "cargo-trust-vc-rustc-wrapper-dependency-metadata",
  "crate_name": "spec_use",
  "package_name": "spec_use",
  "package_version": "0.1.0",
  "package_env_id": "test-package-id",
  "manifest_path": "$(pwd)/Cargo.toml",
  "metadata_path": "$metadata",
  "metadata_len": 13,
  "metadata_sha256": "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
  "source_path": "$(pwd)/src/lib.rs",
  "source_len": 1,
  "source_sha256": "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
  "semantic_payload": {{
    "kind": "trust-vc-semantic-facts-v1",
    "proof_facts_exported": true,
    "concrete_functions": [
      {{
        "name": "concrete_b",
        "return_type": "u16",
        "params": [{{"name": "x", "ty": "u16"}}],
        "return_binding": "result",
        "requires": [],
        "ensures": ["result == x"]
      }},
      {{
        "name": "concrete_caller",
        "return_type": "u16",
        "params": [{{"name": "x", "ty": "u16"}}],
        "return_binding": "result",
        "requires": [],
        "ensures": ["result == x"]
      }}
    ]
  }}
}}
JSON
  echo '{{"reason":"compiler-artifact"}}'
  exit 0
fi
if [ "$1" = "check" ] && [ "$2" = "--lib" ] && [ "$3" = "--locked" ] && [ "$4" = "--offline" ]; then
  mkdir -p "$CARGO_TARGET_DIR/debug/deps"
  metadata="$CARGO_TARGET_DIR/debug/deps/libspec_def.rmeta"
  printf 'fake metadata' > "$metadata"
  if [ "{missing_sidecar}" = "1" ]; then
    echo '{{"reason":"compiler-artifact"}}'
    exit 0
  fi
  package_version="0.1.0"
  if [ "$(basename "$PWD")" = "cargo_spec_def2" ]; then
    package_version="0.2.0"
  fi
  sidecar="$CARGO_TARGET_DIR/debug/deps/libspec_def.vir"
  cat > "$sidecar" <<JSON
trust-vc-rustc-wrapper-artifact-v1
{{
  "schema_version": 1,
  "artifact_kind": "cargo-trust-vc-rustc-wrapper-dependency-metadata",
  "crate_name": "spec_def",
  "package_name": "spec_def",
  "package_version": "$package_version",
  "package_env_id": "test-package-id",
  "manifest_path": "$(pwd)/Cargo.toml",
  "metadata_path": "$metadata",
  "metadata_len": 13,
  "metadata_sha256": "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
  "source_path": "$(pwd)/src/lib.rs",
  "source_len": 1,
  "source_sha256": "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
  "semantic_payload": {{
    "kind": "trust-vc-semantic-facts-v1",
    "proof_facts_exported": true,
    "concrete_functions": [
      {{
        "name": "concrete_a",
        "return_type": "u16",
        "params": [{{"name": "x", "ty": "u16"}}],
        "return_binding": "result",
        "requires": [],
        "ensures": ["result == x"]
      }}
    ]
  }}
}}
JSON
  echo '{{"reason":"compiler-artifact"}}'
  exit 0
fi
echo "unexpected cargo args: $*" >&2
exit 64
"#,
                log_path.display()
            ),
        );
    }

    #[cfg(unix)]
    fn write_spec_use_sidecar_fake_trust_vc(path: &Path, facts_record: &Path, marker: &Path) {
        write_executable(
            path,
            &format!(
                r#"#!/usr/bin/env bash
touch "{}"
if [ "$1" != "check" ] || [ "$2" != "--json" ] || [ "$3" != "--emit-certificate" ] || [ "$4" != "." ]; then
  echo "unexpected cargo-trust-vc args: $*" >&2
  exit 64
fi
if [ -z "$__TRUST_VC_DEPENDENCY_FACTS__" ]; then
  echo "missing dependency facts" >&2
  exit 65
fi
printf '%s' "$__TRUST_VC_DEPENDENCY_FACTS__" > "{}"
mkdir -p .trust_vc
cat > .trust_vc/proof-certificate.json <<'JSON'
{{
  "functions": [
    {{"name": "concrete_b", "file": "src/lib.rs", "status": "verified", "obligations": [{{"condition_hash": "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "status": "verified"}}]}},
    {{"name": "concrete_caller", "file": "src/lib.rs", "status": "verified", "obligations": [{{"condition_hash": "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb", "status": "verified"}}]}},
    {{"name": "test", "file": "src/lib.rs", "status": "verified", "obligations": [{{"condition_hash": "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc", "status": "verified"}}]}},
    {{"name": "lib", "file": "src/lib.rs", "status": "verified", "obligations": [{{"condition_hash": "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd", "status": "verified"}}]}}
  ]
}}
JSON
cat <<'JSON'
{{
  "functions": [
    {{"name": "concrete_b"}},
    {{"name": "concrete_caller"}},
    {{"name": "test"}},
    {{"name": "lib"}}
  ]
}}
JSON
exit 0
"#,
                marker.display(),
                facts_record.display()
            ),
        );
    }

    #[cfg(unix)]
    fn spec_use_sidecar_candidate() -> TrustVcCorpusRunCandidate {
        TrustVcCorpusRunCandidate {
            upstream_path: "source/rust_verify_test/tests/cargo-tests/verified/spec_use/src/lib.rs"
                .to_string(),
            classification: "ported".to_string(),
            evidence_kind: VerusEvidenceKind::ProofObligation,
            trust_vc_paths: vec!["ported/cargo_spec_use".to_string()],
            trust_vc_check_args: Vec::new(),
            expected_cases: ["concrete_b", "concrete_caller", "test", "lib"]
                .into_iter()
                .map(|case_id| VerusExpectedCase {
                    case_id: case_id.to_string(),
                    upstream_case_id: None,
                    trust_vc_path: None,
                    expected_verdict: VerusExpectedVerdict::Verified,
                    min_obligations: 1,
                    obligation_fingerprints: Vec::new(),
                    expected_error_patterns: Vec::new(),
                    expected_rust_diagnostic_pattern_sets: Vec::new(),
                    forbidden_diagnostic_patterns: Vec::new(),
                    expected_warning_patterns: Vec::new(),
                })
                .collect(),
        }
    }

    #[cfg(unix)]
    fn write_unverified_spec_use_sidecar_fixture(temp_dir: &Path) -> PathBuf {
        write_spec_use_sidecar_fixture(temp_dir);
        let fixture_root = temp_dir.join("ported/cargo_unverified_spec_use");
        fs::create_dir_all(fixture_root.join("src")).expect("fixture src dir should be created");
        fs::write(fixture_root.join("Cargo.lock"), "version = 4\n")
            .expect("fixture lockfile should be written");
        fs::write(
            fixture_root.join("Cargo.toml"),
            r#"[package]
name = "spec_use_unverified"
version = "0.1.0"
edition = "2021"

[dependencies]
spec_use = { path = "../cargo_spec_use" }
"#,
        )
        .expect("unverified spec_use manifest should be written");
        fs::write(
            fixture_root.join("src/lib.rs"),
            r#"
pub fn test_calling(x: u16) {
    use spec_use::*;

    let y = concrete_b(x);
    let z = concrete_caller(y);
    println!("{}", z);
}

#[trust_vc::contract(
    requires(x < 50u16),
    ensures(result == x),
    returns(result),
)]
pub fn direct_body_call(x: u16) -> u16 {
    let y = spec_use::concrete_b(x);
    spec_use::concrete_caller(y)
}
"#,
        )
        .expect("unverified spec_use source should be written");
        fixture_root
    }

    #[cfg(unix)]
    fn write_unverified_spec_use_sidecar_fake_trust_vc(
        path: &Path,
        facts_record: &Path,
        marker: &Path,
    ) {
        write_executable(
            path,
            &format!(
                r#"#!/usr/bin/env bash
touch "{}"
if [ "$1" != "check" ] || [ "$2" != "--json" ] || [ "$3" != "--emit-certificate" ] || [ "$4" != "." ]; then
  echo "unexpected cargo-trust-vc args: $*" >&2
  exit 64
fi
if [ -z "$__TRUST_VC_DEPENDENCY_FACTS__" ]; then
  echo "missing dependency facts" >&2
  exit 65
fi
printf '%s' "$__TRUST_VC_DEPENDENCY_FACTS__" > "{}"
mkdir -p .trust_vc
cat > .trust_vc/proof-certificate.json <<'JSON'
{{
  "functions": [
    {{"name": "direct_body_call", "file": "src/lib.rs", "status": "verified", "obligations": [{{"condition_hash": "sha256:eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee", "status": "verified"}}]}}
  ]
}}
JSON
cat <<'JSON'
{{
  "functions": [
    {{"name": "direct_body_call"}}
  ]
}}
JSON
exit 0
"#,
                marker.display(),
                facts_record.display()
            ),
        );
    }

    #[cfg(unix)]
    fn unverified_spec_use_sidecar_candidate() -> TrustVcCorpusRunCandidate {
        TrustVcCorpusRunCandidate {
            upstream_path:
                "source/rust_verify_test/tests/cargo-tests/unverified/spec_use/src/lib.rs"
                    .to_string(),
            classification: "ported".to_string(),
            evidence_kind: VerusEvidenceKind::ProofObligation,
            trust_vc_paths: vec!["ported/cargo_unverified_spec_use".to_string()],
            trust_vc_check_args: Vec::new(),
            expected_cases: vec![VerusExpectedCase {
                case_id: "direct_body_call".to_string(),
                upstream_case_id: None,
                trust_vc_path: None,
                expected_verdict: VerusExpectedVerdict::Verified,
                min_obligations: 1,
                obligation_fingerprints: Vec::new(),
                expected_error_patterns: Vec::new(),
                expected_rust_diagnostic_pattern_sets: Vec::new(),
                forbidden_diagnostic_patterns: Vec::new(),
                expected_warning_patterns: Vec::new(),
            }],
        }
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_cargo_spec_use_builds_dependency_sidecars_for_direct_check() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-cargo-spec-use-sidecars");
        let fixture_root = write_spec_use_sidecar_fixture(&temp_dir);
        let upstream_tests = temp_dir
            .join(VERUS_TEST_ROOT)
            .join("cargo-tests/verified/spec_use/src");
        fs::create_dir_all(&upstream_tests).expect("upstream fixture dir should be created");
        fs::write(upstream_tests.join("lib.rs"), "").expect("upstream fixture should be written");
        let fake_cargo = temp_dir.join("fake-cargo");
        let fake_binary = temp_dir.join("fake-cargo-trust-vc");
        let cargo_log = temp_dir.join("cargo-log");
        let facts_record = temp_dir.join("dependency-facts.json");
        let binary_marker = temp_dir.join("trust-vc-ran");
        write_spec_use_sidecar_fake_cargo(&fake_cargo, &cargo_log, false);
        write_spec_use_sidecar_fake_trust_vc(&fake_binary, &facts_record, &binary_marker);

        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = corpus_for_typecheck(spec_use_sidecar_candidate());
        let env = vec![("CARGO".to_string(), fake_cargo.display().to_string())];
        let run_report = run_trust_vc_corpus_with_trust_vc_binary_and_env(
            &crate_root,
            &corpus,
            None,
            &env,
            Some(&fake_binary),
            &BTreeMap::new(),
        );

        assert_eq!(run_report.passed_paths, 1);
        assert_eq!(run_report.failed_paths, 0);
        let result = &run_report.results[0];
        assert_eq!(result.status, GateStatus::Passed);
        assert_eq!(
            result.observed_case_ids,
            vec!["concrete_b", "concrete_caller", "test", "lib"]
        );
        assert!(
            binary_marker.exists(),
            "direct cargo-trust-vc check should run after sidecar setup"
        );
        let facts = fs::read_to_string(&facts_record).expect("dependency facts should be recorded");
        assert!(
            facts.contains("\"package_version\":\"0.1.0\"")
                && facts.contains("\"package_version\":\"0.2.0\""),
            "direct check should receive both producer sidecars: {facts}"
        );
        let cargo_log = fs::read_to_string(&cargo_log).expect("cargo log should be readable");
        assert!(
            cargo_log.contains(
                "cargo_spec_use|check --message-format=json --all-targets --locked --offline"
            ),
            "consumer typecheck should still run first: {cargo_log}"
        );
        assert!(
            cargo_log.contains("cargo_spec_def|check --lib --locked --offline")
                && cargo_log.contains("cargo_spec_def2|check --lib --locked --offline"),
            "producer sidecar builds should be orchestrated: {cargo_log}"
        );
        assert_eq!(
            result
                .command
                .as_ref()
                .and_then(|command| command.cwd.canonicalize().ok()),
            Some(
                fixture_root
                    .canonicalize()
                    .expect("fixture root should canonicalize")
            )
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_cargo_unverified_spec_use_builds_transitive_sidecar_for_direct_body_call() {
        let temp_dir =
            unique_temp_dir("trust-vc-evidence-corpus-cargo-unverified-spec-use-sidecars");
        let fixture_root = write_unverified_spec_use_sidecar_fixture(&temp_dir);
        let upstream_tests = temp_dir
            .join(VERUS_TEST_ROOT)
            .join("cargo-tests/unverified/spec_use/src");
        fs::create_dir_all(&upstream_tests).expect("upstream fixture dir should be created");
        fs::write(upstream_tests.join("lib.rs"), "").expect("upstream fixture should be written");
        let fake_cargo = temp_dir.join("fake-cargo");
        let fake_binary = temp_dir.join("fake-cargo-trust-vc");
        let cargo_log = temp_dir.join("cargo-log");
        let facts_record = temp_dir.join("dependency-facts.json");
        let binary_marker = temp_dir.join("trust-vc-ran");
        write_spec_use_sidecar_fake_cargo(&fake_cargo, &cargo_log, false);
        write_unverified_spec_use_sidecar_fake_trust_vc(
            &fake_binary,
            &facts_record,
            &binary_marker,
        );

        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = corpus_for_typecheck(unverified_spec_use_sidecar_candidate());
        let env = vec![("CARGO".to_string(), fake_cargo.display().to_string())];
        let run_report = run_trust_vc_corpus_with_trust_vc_binary_and_env(
            &crate_root,
            &corpus,
            None,
            &env,
            Some(&fake_binary),
            &BTreeMap::new(),
        );

        assert_eq!(run_report.passed_paths, 1);
        assert_eq!(run_report.failed_paths, 0);
        let result = &run_report.results[0];
        assert_eq!(result.status, GateStatus::Passed);
        assert_eq!(result.observed_case_ids, vec!["direct_body_call"]);
        assert!(
            binary_marker.exists(),
            "direct cargo-trust-vc check should run after transitive sidecar setup"
        );
        let facts = fs::read_to_string(&facts_record).expect("dependency facts should be recorded");
        assert!(
            facts.contains("\"package_name\":\"spec_use\"")
                && facts.contains("\"name\":\"concrete_b\"")
                && facts.contains("\"name\":\"concrete_caller\""),
            "direct unverified consumer should receive the verified spec_use sidecar: {facts}"
        );
        assert!(
            !facts.contains("\"package_name\":\"spec_def\""),
            "direct unverified consumer should not receive transitive spec_def sidecars: {facts}"
        );
        let cargo_log = fs::read_to_string(&cargo_log).expect("cargo log should be readable");
        assert!(
            cargo_log.contains(
                "cargo_unverified_spec_use|check --message-format=json --all-targets --locked --offline"
            ),
            "unverified consumer typecheck should still run first: {cargo_log}"
        );
        assert!(
            cargo_log.contains("cargo_spec_use|check --lib --locked --offline"),
            "spec_use sidecar should be built for the unverified consumer: {cargo_log}"
        );
        assert_eq!(
            result
                .command
                .as_ref()
                .and_then(|command| command.cwd.canonicalize().ok()),
            Some(
                fixture_root
                    .canonicalize()
                    .expect("fixture root should canonicalize")
            )
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_cargo_spec_use_fails_closed_without_dependency_sidecars() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-cargo-spec-use-sidecars-missing");
        write_spec_use_sidecar_fixture(&temp_dir);
        let fake_cargo = temp_dir.join("fake-cargo");
        let fake_binary = temp_dir.join("fake-cargo-trust-vc");
        let cargo_log = temp_dir.join("cargo-log");
        let facts_record = temp_dir.join("dependency-facts.json");
        let binary_marker = temp_dir.join("trust-vc-ran");
        write_spec_use_sidecar_fake_cargo(&fake_cargo, &cargo_log, true);
        write_spec_use_sidecar_fake_trust_vc(&fake_binary, &facts_record, &binary_marker);

        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = corpus_for_typecheck(spec_use_sidecar_candidate());
        let env = vec![("CARGO".to_string(), fake_cargo.display().to_string())];
        let run_report = run_trust_vc_corpus_with_trust_vc_binary_and_env(
            &crate_root,
            &corpus,
            None,
            &env,
            Some(&fake_binary),
            &BTreeMap::new(),
        );

        assert_eq!(run_report.passed_paths, 0);
        assert_eq!(run_report.failed_paths, 1);
        let result = &run_report.results[0];
        assert_eq!(result.status, GateStatus::Failed);
        assert!(
            result
                .failures
                .iter()
                .any(|failure| failure.contains("produced 0 cargo-trust-vc sidecar artifact(s)")),
            "missing dependency sidecars must fail closed: {:?}",
            result.failures
        );
        assert!(
            !result
                .failures
                .iter()
                .any(|failure| failure.contains("missing expected case")),
            "sidecar prerequisite failure should suppress missing-case noise: {:?}",
            result.failures
        );
        assert!(
            !binary_marker.exists(),
            "direct cargo-trust-vc check must not run after sidecar setup failure"
        );
        assert!(
            !facts_record.exists(),
            "dependency facts should not be passed when sidecar setup fails"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_cargo_fixture_rejects_uncompiled_observed_source() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-cargo-fixture-uncompiled-source");
        let upstream_tests = temp_dir
            .join(VERUS_TEST_ROOT)
            .join("cargo-tests/verified/basic/src");
        let fixture_root = temp_dir.join("ported/basic_fixture");
        fs::create_dir_all(&upstream_tests).expect("upstream fixture dir should be created");
        fs::create_dir_all(fixture_root.join("src")).expect("ported fixture dir should be created");
        fs::write(upstream_tests.join("lib.rs"), "").expect("upstream test should be written");
        fs::write(
            fixture_root.join("Cargo.toml"),
            r#"[package]
name = "basic-fixture"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("fixture Cargo.toml should be written");
        fs::write(fixture_root.join("Cargo.lock"), "version = 4\n")
            .expect("fixture Cargo.lock should be written");
        fs::write(fixture_root.join("src/lib.rs"), "pub fn compiled() {}\n")
            .expect("fixture compiled source should be written");
        fs::write(
            fixture_root.join("src/hidden.rs"),
            r#"
#[ensures(result == x)]
fn fixture_hidden(x: i32) -> i32 {
    x
}
"#,
        )
        .expect("fixture hidden source should be written");
        let fake_cargo = temp_dir.join("fake-cargo");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
if [ "$1" != "check" ] || [ "$2" != "--message-format=json" ] || [ "$3" != "--all-targets" ] || [ "$4" != "--locked" ] || [ "$5" != "--offline" ]; then
  echo "unexpected cargo args: $*" >&2
  exit 64
fi
mkdir -p "$CARGO_TARGET_DIR/debug/deps"
printf '%s: %s\n' "$CARGO_TARGET_DIR/debug/deps/libbasic_fixture.rmeta" "$(pwd)/src/lib.rs" > "$CARGO_TARGET_DIR/debug/deps/basic_fixture.d"
cat <<'JSON'
{"reason":"compiler-artifact"}
JSON
exit 0
"#,
        );
        let fake_binary = temp_dir.join("fake-cargo-trust-vc");
        write_executable(
            &fake_binary,
            r#"#!/usr/bin/env bash
mkdir -p .trust_vc
cat > .trust_vc/proof-certificate.json <<'JSON'
{
  "schema_version": 1,
  "trust_vc_version": "test",
  "generated_at_unix_secs": 0,
  "crate_name": "basic-fixture",
  "functions": [
    {
      "name": "fixture_hidden",
      "file": "src/hidden.rs",
      "line": 3,
      "status": "verified",
      "obligations": [
        {
          "name": "postcondition",
          "kind": "assert",
          "condition_hash": "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
          "status": "verified"
        }
      ]
    }
  ]
}
JSON
cat <<'JSON'
{
  "crate": "basic-fixture",
  "functions": [
    {
      "file": "src/hidden.rs",
      "line": 3,
      "name": "fixture_hidden",
      "result": "verified",
      "duration_ms": 0
    }
  ],
  "summary": {
    "verified": 1,
    "counterexample": 0,
    "unknown": 0,
    "error": 0,
    "skipped": 0
  }
}
JSON
exit 0
"#,
        );

        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/cargo-tests/verified/basic/src/lib.rs",
      "classification": "ported",
      "owner_issue": "#2780",
      "reason": "Cargo fixture port.",
      "trust_vc_paths": ["ported/basic_fixture"],
      "expected_cases": [
        {
          "case_id": "fixture_hidden",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = load_corpus_report(&manifest_path, &crate_root, Some(&crate_root))
            .expect("corpus report should load");
        let env = vec![
            (
                "CARGO_HOME".to_string(),
                temp_dir.join("isolated-cargo-home").display().to_string(),
            ),
            ("CARGO".to_string(), fake_cargo.display().to_string()),
        ];
        let run_report = run_trust_vc_corpus_with_trust_vc_binary_and_env(
            &crate_root,
            &corpus,
            None,
            &env,
            Some(&fake_binary),
            &BTreeMap::new(),
        );

        assert_eq!(run_report.attempted_paths, 1);
        assert_eq!(run_report.passed_paths, 0);
        assert_eq!(run_report.failed_paths, 1);
        let result = &run_report.results[0];
        assert!(
            result
                .failures
                .iter()
                .any(|failure| failure.contains("was not present in cargo check dep-info")),
            "uncompiled observed sources must fail replacement evidence: {:?}",
            result.failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn cargo_fixture_rust_typecheck_uses_locked_offline_and_restores_lockfile() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-cargo-fixture-lock-restore");
        let fixture_root = temp_dir.join("ported/basic_fixture");
        fs::create_dir_all(fixture_root.join("src")).expect("fixture source dir should be created");
        fs::write(
            fixture_root.join("Cargo.toml"),
            r#"[package]
name = "basic-fixture"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("fixture Cargo.toml should be written");
        fs::write(fixture_root.join("src/lib.rs"), "pub fn ok() {}\n")
            .expect("fixture source should be written");
        fs::write(fixture_root.join("Cargo.lock"), "version = 4\n# original\n")
            .expect("fixture lockfile should be written");
        let fake_cargo = temp_dir.join("fake-cargo");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
if [ "$1" != "check" ] || [ "$2" != "--message-format=json" ] || [ "$3" != "--all-targets" ] || [ "$4" != "--locked" ] || [ "$5" != "--offline" ]; then
  echo "unexpected cargo args: $*" >&2
  exit 64
fi
cat > Cargo.lock <<'LOCK'
version = 4
# mutated by cargo
LOCK
cat <<'JSON'
{"reason":"compiler-artifact"}
JSON
exit 0
"#,
        );
        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let env = vec![("CARGO".to_string(), fake_cargo.display().to_string())];

        let output = run_cargo_check_for_fixture(&crate_root, &fixture_root, &env);

        assert_eq!(output.command.exit_code, Some(0));
        assert_eq!(
            output.command.args,
            vec![
                "check".to_string(),
                "--message-format=json".to_string(),
                "--all-targets".to_string(),
                "--locked".to_string(),
                "--offline".to_string()
            ]
        );
        assert_eq!(
            fs::read_to_string(fixture_root.join("Cargo.lock"))
                .expect("fixture lockfile should remain readable"),
            "version = 4\n# original\n"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn root_workspace_fetch_is_required_for_workspace_or_cargo_trust_vc_corpus_gates() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-root-fetch-policy");
        fs::create_dir_all(temp_dir.join("crates/cargo-trust-vc/tests"))
            .expect("cargo-trust-vc test dir should be created");
        fs::create_dir_all(temp_dir.join("ported/basic_fixture/src"))
            .expect("fixture dir should be created");
        fs::write(
            temp_dir.join("crates/cargo-trust-vc/tests/late_args_integration.rs"),
            "#[test]\nfn late_package_arg_after_release() {}\n",
        )
        .expect("cargo-trust-vc integration test should be written");
        fs::write(
            temp_dir.join("ported/basic_fixture/Cargo.toml"),
            "[package]\nname = \"basic-fixture\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
        )
        .expect("fixture Cargo.toml should be written");
        let mut args = test_evidence_args(&temp_dir, &temp_dir, None);
        args.run_trust_vc = false;
        args.run_trust_vc_corpus = true;
        args.port_manifest_only = true;
        let direct_corpus = corpus_for_typecheck(TrustVcCorpusRunCandidate {
            upstream_path: "source/rust_verify_test/tests/direct.rs".to_string(),
            classification: "ported".to_string(),
            evidence_kind: VerusEvidenceKind::ProofObligation,
            trust_vc_paths: vec!["ported/direct.rs".to_string()],
            trust_vc_check_args: Vec::new(),
            expected_cases: Vec::new(),
        });
        let fixture_corpus = corpus_for_typecheck(TrustVcCorpusRunCandidate {
            upstream_path: "source/rust_verify_test/tests/cargo-tests/verified/basic/src/lib.rs"
                .to_string(),
            classification: "ported".to_string(),
            evidence_kind: VerusEvidenceKind::ProofObligation,
            trust_vc_paths: vec!["ported/basic_fixture".to_string()],
            trust_vc_check_args: Vec::new(),
            expected_cases: Vec::new(),
        });
        let integration_corpus = corpus_for_typecheck(TrustVcCorpusRunCandidate {
            upstream_path: "source/cargo-verus/tests/test_late_args.rs".to_string(),
            classification: "ported".to_string(),
            evidence_kind: VerusEvidenceKind::CargoTrustVcIntegrationTest,
            trust_vc_paths: vec!["crates/cargo-trust-vc/tests/late_args_integration.rs".to_string()],
            trust_vc_check_args: Vec::new(),
            expected_cases: Vec::new(),
        });

        assert!(
            !root_workspace_fetch_required(&args, None),
            "corpus-only evidence without a manifest must not fetch the full workspace"
        );
        assert!(
            !root_workspace_fetch_required(&args, Some(&direct_corpus)),
            "direct-source corpus-only evidence must not fetch the full workspace"
        );
        assert!(
            !root_workspace_fetch_required(&args, Some(&fixture_corpus)),
            "cargo fixture corpus evidence has per-fixture locked fetch gates"
        );
        assert!(
            root_workspace_fetch_required(&args, Some(&integration_corpus)),
            "cargo-trust-vc integration-test corpus evidence needs root dependencies fetched before offline cargo test"
        );

        args.trust_vc_corpus_command = Some("custom-check {trust_vc_path}".to_string());
        assert!(
            !root_workspace_fetch_required(&args, Some(&integration_corpus)),
            "custom corpus commands own their dependency preflight"
        );
        args.trust_vc_corpus_command = None;

        args.run_trust_vc = true;
        assert!(
            root_workspace_fetch_required(&args, Some(&direct_corpus)),
            "workspace TrustVc gates still need a root locked fetch"
        );
        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_fixture_fetch_gates_prefetch_unique_fixture_locks() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-fixture-fetch");
        let fixture_root = temp_dir.join("ported/basic_fixture");
        fs::create_dir_all(fixture_root.join("src")).expect("fixture source dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(
            fixture_root.join("Cargo.toml"),
            r#"[package]
name = "basic-fixture"
version = "0.1.0"
edition = "2021"

[workspace]
"#,
        )
        .expect("fixture Cargo.toml should be written");
        fs::write(fixture_root.join("Cargo.lock"), "version = 4\n# original\n")
            .expect("fixture lockfile should be written");
        fs::write(fixture_root.join("src/lib.rs"), "pub fn ok() {}\n")
            .expect("fixture source should be written");
        fs::write(temp_dir.join("ported/direct.rs"), "fn direct() {}\n")
            .expect("direct source should be written");
        let fetch_log = temp_dir.join("fetch-log");
        let fake_cargo = temp_dir.join("fake-cargo");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
printf '%s|%s\n' "$(pwd)" "$*" >> "$FETCH_LOG"
if [ "$1" != "fetch" ] || [ "$2" != "--locked" ]; then
  echo "unexpected cargo args: $*" >&2
  exit 64
fi
cat > Cargo.lock <<'LOCK'
version = 4
# mutated by cargo fetch
LOCK
exit 0
"#,
        );
        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = corpus_for_typecheck(TrustVcCorpusRunCandidate {
            upstream_path: "source/rust_verify_test/tests/cargo-tests/verified/basic/src/lib.rs"
                .to_string(),
            classification: "ported".to_string(),
            evidence_kind: VerusEvidenceKind::ProofObligation,
            trust_vc_paths: vec![
                "ported/basic_fixture".to_string(),
                "ported/basic_fixture".to_string(),
                "ported/direct.rs".to_string(),
            ],
            trust_vc_check_args: Vec::new(),
            expected_cases: vec![VerusExpectedCase {
                case_id: "fixture_ok".to_string(),
                upstream_case_id: None,
                trust_vc_path: None,
                expected_verdict: VerusExpectedVerdict::Verified,
                min_obligations: 1,
                obligation_fingerprints: Vec::new(),
                expected_error_patterns: Vec::new(),
                expected_rust_diagnostic_pattern_sets: Vec::new(),
                forbidden_diagnostic_patterns: Vec::new(),
                expected_warning_patterns: Vec::new(),
            }],
        });
        let env = vec![
            ("CARGO".to_string(), fake_cargo.display().to_string()),
            (
                "CARGO_HOME".to_string(),
                temp_dir.join("isolated-cargo-home").display().to_string(),
            ),
            ("FETCH_LOG".to_string(), fetch_log.display().to_string()),
        ];

        let gates = trust_vc_corpus_fixture_fetch_gates(&crate_root, &corpus, &env);

        assert_eq!(gates.len(), 1);
        assert_eq!(gates[0].status, GateStatus::Passed);
        let command = gates[0]
            .command
            .as_ref()
            .expect("fixture fetch gate should record cargo command");
        assert_eq!(
            command.args,
            vec!["fetch".to_string(), "--locked".to_string()]
        );
        assert!(
            same_path(&command.cwd, &fixture_root, &crate_root),
            "fixture fetch must run in the fixture root, not the workspace root: {:?}",
            command
        );
        assert_eq!(
            fs::read_to_string(fixture_root.join("Cargo.lock"))
                .expect("fixture lockfile should remain readable"),
            "version = 4\n# original\n"
        );
        let log = fs::read_to_string(&fetch_log).expect("fetch log should be readable");
        let log_lines = log.lines().collect::<Vec<_>>();
        assert_eq!(log_lines.len(), 1);
        assert!(
            log_lines[0].ends_with("|fetch --locked"),
            "fixture fetch should run exactly once with locked cargo args: {log}"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn cargo_fixture_target_dirs_are_process_scoped() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-target-scope");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");
        let crate_root = temp_dir.join("repo");
        let fixture_root = crate_root.join("ported/basic_fixture");
        let producer_root = crate_root.join("ported/basic_dependency");
        let run_id = evidence_process_run_id();

        let fixture_target = cargo_fixture_target_dir(&crate_root, &fixture_root);
        let sidecar_target =
            cargo_fixture_dependency_sidecar_target_dir(&crate_root, &fixture_root, &producer_root);

        assert!(
            fixture_target.starts_with(
                crate_root
                    .join("target")
                    .join("trust-vc-corpus-fixtures")
                    .join("runs")
                    .join(&run_id)
            ),
            "fixture target dirs must be process-scoped: {}",
            fixture_target.display()
        );
        assert!(
            sidecar_target.starts_with(
                crate_root
                    .join("target")
                    .join("trust-vc-corpus-fixtures")
                    .join("runs")
                    .join(&run_id)
            ),
            "sidecar target dirs must be process-scoped: {}",
            sidecar_target.display()
        );
        assert!(
            fixture_target
                .file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.starts_with("fixture-")),
            "fixture target dir should keep fixture digest leaf: {}",
            fixture_target.display()
        );
        assert!(
            sidecar_target
                .file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.starts_with("dependency-sidecars-")),
            "sidecar target dir should keep dependency digest leaf: {}",
            sidecar_target.display()
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn evidence_command_runner_reports_timeout() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-command-timeout");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");

        let output = run_command_with_env_capture_timeout(
            &temp_dir,
            "/bin/sh",
            &["-c", "printf started; sleep 2; printf finished"],
            &[],
            Some(Duration::from_millis(100)),
        );

        assert_eq!(output.command.exit_code, Some(124));
        assert!(
            output.stdout.contains("started"),
            "timeout output should retain stdout prefix: {:?}",
            output.command
        );
        assert!(
            !output.stdout.contains("finished"),
            "timed out command should not complete: {:?}",
            output.command
        );
        assert!(
            output.command.stderr_tail.contains("command timed out"),
            "timeout should be reported in stderr_tail: {:?}",
            output.command
        );
        assert!(
            output.command.duration_ms < 2_000,
            "timeout should stop before the shell sleep completes: {:?}",
            output.command
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn evidence_command_runner_drains_large_output() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-command-large-output");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");

        let output = run_command_with_env_capture_timeout(
            &temp_dir,
            "/bin/sh",
            &[
                "-c",
                "i=0; while [ $i -lt 5000 ]; do printf '0123456789abcdef0123456789abcdef\\n'; i=$((i + 1)); done",
            ],
            &[],
            Some(Duration::from_secs(5)),
        );

        assert_eq!(output.command.exit_code, Some(0), "{:?}", output.command);
        assert!(
            output.stdout.len() > 100_000,
            "large stdout should be captured without blocking: {:?}",
            output.command
        );
        assert!(
            !output.command.stderr_tail.contains("command timed out"),
            "large stdout command should not time out: {:?}",
            output.command
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn evidence_command_runner_kills_descendants_on_timeout() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-command-timeout-descendant");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");
        let survivor_file = temp_dir.join("descendant-survived");
        let command = format!(
            "(sleep 1; touch {}) & wait",
            shell_quote(&survivor_file.to_string_lossy())
        );

        let output = run_command_with_env_capture_timeout(
            &temp_dir,
            "/bin/sh",
            &["-c", &command],
            &[],
            Some(Duration::from_millis(100)),
        );

        assert_eq!(output.command.exit_code, Some(124), "{:?}", output.command);
        std::thread::sleep(Duration::from_millis(1_200));
        assert!(
            !survivor_file.exists(),
            "timeout should terminate descendants, but {} was created: {:?}",
            survivor_file.display(),
            output.command
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn command_result_detail_mentions_timeout() {
        let command = CommandResult {
            program: "cargo".to_string(),
            args: vec!["check".to_string()],
            cwd: PathBuf::from("."),
            exit_code: Some(124),
            duration_ms: 30_000,
            stdout_tail: String::new(),
            stderr_tail: "prior line\ncommand timed out after 30.000s".to_string(),
        };

        assert_eq!(
            command_result_detail(&command).as_deref(),
            Some("exit code 124; command timed out after 30.000s")
        );
    }

    #[cfg(unix)]
    #[test]
    fn cargo_fixture_fetch_preflight_failure_suppresses_missing_case_noise() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-fixture-fetch-prereq");
        let fixture_root = temp_dir.join("ported/basic_fixture");
        fs::create_dir_all(fixture_root.join("src")).expect("fixture source dir should be created");
        fs::write(
            fixture_root.join("Cargo.toml"),
            r#"[package]
name = "basic-fixture"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("fixture Cargo.toml should be written");
        fs::write(fixture_root.join("Cargo.lock"), "version = 4\n")
            .expect("fixture lockfile should be written");
        fs::write(fixture_root.join("src/lib.rs"), "pub fn ok() {}\n")
            .expect("fixture source should be written");
        let fake_binary = temp_dir.join("cargo-trust-vc");
        write_executable(
            &fake_binary,
            "#!/bin/sh\necho should-not-run >&2\nexit 99\n",
        );

        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let fixture_root = fixture_root
            .canonicalize()
            .expect("fixture root should canonicalize");
        let corpus = corpus_for_typecheck(TrustVcCorpusRunCandidate {
            upstream_path: "source/rust_verify_test/tests/cargo-tests/verified/basic/src/lib.rs"
                .to_string(),
            classification: "ported".to_string(),
            evidence_kind: VerusEvidenceKind::ProofObligation,
            trust_vc_paths: vec!["ported/basic_fixture".to_string()],
            trust_vc_check_args: Vec::new(),
            expected_cases: vec![VerusExpectedCase {
                case_id: "fixture_ok".to_string(),
                upstream_case_id: None,
                trust_vc_path: None,
                expected_verdict: VerusExpectedVerdict::Verified,
                min_obligations: 1,
                obligation_fingerprints: Vec::new(),
                expected_error_patterns: Vec::new(),
                expected_rust_diagnostic_pattern_sets: Vec::new(),
                forbidden_diagnostic_patterns: Vec::new(),
                expected_warning_patterns: Vec::new(),
            }],
        });
        let mut preflight_failures = BTreeMap::new();
        preflight_failures.insert(
            fixture_root,
            vec![
                "ported/basic_fixture: cargo fetch failed for locked fixture dependencies with exit code 101".to_string(),
            ],
        );

        let run_report = run_trust_vc_corpus_with_trust_vc_binary_and_env(
            &crate_root,
            &corpus,
            None,
            &[],
            Some(&fake_binary),
            &preflight_failures,
        );
        let result = &run_report.results[0];
        assert_eq!(result.status, GateStatus::Failed);
        assert!(
            result
                .failures
                .iter()
                .any(|failure| failure.contains("cargo fetch failed")),
            "preflight fetch failure should be primary: {:?}",
            result.failures
        );
        assert!(
            !result
                .failures
                .iter()
                .any(|failure| failure.contains("missing expected case")),
            "preflight failure should suppress missing-case noise: {:?}",
            result.failures
        );
        assert!(
            result.commands.is_empty(),
            "fixture commands should not run after preflight failure: {:?}",
            result.commands
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn cargo_fixture_rust_typecheck_requires_committed_lockfile() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-cargo-fixture-missing-lock");
        let fixture_root = temp_dir.join("ported/basic_fixture");
        fs::create_dir_all(fixture_root.join("src")).expect("fixture source dir should be created");
        fs::write(
            fixture_root.join("Cargo.toml"),
            r#"[package]
name = "basic-fixture"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("fixture Cargo.toml should be written");
        fs::write(fixture_root.join("src/lib.rs"), "pub fn ok() {}\n")
            .expect("fixture source should be written");
        let fake_cargo = temp_dir.join("fake-cargo");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
echo "cargo should not run without a fixture lockfile" >&2
exit 70
"#,
        );
        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let env = vec![("CARGO".to_string(), fake_cargo.display().to_string())];

        let output = run_cargo_check_for_fixture(&crate_root, &fixture_root, &env);

        assert_eq!(output.command.exit_code, Some(127));
        assert!(
            output
                .command
                .stderr_tail
                .contains("must include Cargo.lock"),
            "missing lockfile should fail before cargo runs: {:?}",
            output.command
        );
        assert!(
            !fixture_root.join("Cargo.lock").exists(),
            "missing lockfile should not be generated by the evidence gate"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_cargo_fixture_rejects_accepted_fixture_that_fails_rust_typecheck() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-cargo-fixture-rust-fail");
        let upstream_tests = temp_dir
            .join(VERUS_TEST_ROOT)
            .join("cargo-tests/verified/basic/src");
        let fixture_root = temp_dir.join("ported/bad_fixture");
        fs::create_dir_all(&upstream_tests).expect("upstream fixture dir should be created");
        fs::create_dir_all(fixture_root.join("src")).expect("ported fixture dir should be created");
        fs::write(upstream_tests.join("lib.rs"), "").expect("upstream test should be written");
        fs::write(
            fixture_root.join("Cargo.toml"),
            r#"[package]
name = "bad-fixture"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("fixture Cargo.toml should be written");
        fs::write(fixture_root.join("Cargo.lock"), "version = 4\n")
            .expect("fixture Cargo.lock should be written");
        fs::write(
            fixture_root.join("src/lib.rs"),
            r#"
fn fixture_ok() {
    missing_helper();
}
"#,
        )
        .expect("fixture source should be written");
        let fake_cargo = temp_dir.join("fake-cargo");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
if [ "$1" != "check" ] || [ "$2" != "--message-format=json" ] || [ "$3" != "--all-targets" ] || [ "$4" != "--locked" ] || [ "$5" != "--offline" ]; then
  echo "unexpected cargo args: $*" >&2
  exit 64
fi
cat <<'JSON'
{"reason":"compiler-message","message":{"level":"error","message":"cannot find function `missing_helper` in this scope","code":{"code":"E0425"},"spans":[{"file_name":"src/lib.rs","is_primary":true}],"rendered":"error[E0425]: cannot find function `missing_helper` in this scope\n"}}
JSON
exit 101
"#,
        );
        let marker = temp_dir.join("trust-vc-ran");
        let fake_binary = temp_dir.join("fake-cargo-trust-vc");
        write_executable(
            &fake_binary,
            r#"#!/usr/bin/env bash
touch ../../trust-vc-ran
echo "cargo-trust-vc should not run after rustc rejection" >&2
exit 70
"#,
        );
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/cargo-tests/verified/basic/src/lib.rs",
      "classification": "ported",
      "owner_issue": "#2780",
      "reason": "Cargo fixture port.",
      "trust_vc_paths": ["ported/bad_fixture"],
      "expected_cases": [
        {
          "case_id": "fixture_ok",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");
        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = load_corpus_report(&manifest_path, &crate_root, Some(&crate_root))
            .expect("corpus report should load");
        let env = vec![
            (
                "CARGO_HOME".to_string(),
                temp_dir.join("isolated-cargo-home").display().to_string(),
            ),
            ("CARGO".to_string(), fake_cargo.display().to_string()),
        ];

        let run_report = run_trust_vc_corpus_with_trust_vc_binary_and_env(
            &crate_root,
            &corpus,
            None,
            &env,
            Some(&fake_binary),
            &BTreeMap::new(),
        );

        assert_eq!(run_report.passed_paths, 0);
        assert_eq!(run_report.failed_paths, 1);
        let result = &run_report.results[0];
        assert_eq!(result.observed_case_count, 0);
        assert!(result.command.is_none());
        assert_eq!(result.commands.len(), 1);
        assert!(
            result
                .failures
                .iter()
                .any(|failure| failure.contains("cargo check failed for accepted cargo fixture")),
            "accepted cargo fixtures must pass rustc first: {:?}",
            result.failures
        );
        assert!(
            result
                .failures
                .iter()
                .any(|failure| failure.contains("missing_helper")),
            "rustc diagnostics should explain the failed fixture: {:?}",
            result.failures
        );
        assert!(
            !marker.exists(),
            "cargo-trust-vc must not run after fixture rustc typecheck failure"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_cargo_fixture_accepts_no_cheating_expected_errors() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-no-cheating");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        let fixture_root = temp_dir.join("ported/no_cheating");
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(fixture_root.join("src")).expect("ported fixture dir should be created");
        fs::write(
            upstream_tests.join("no_cheating.rs"),
            r#"
test_verify_one_file_with_options! {
    #[test] test_no_cheating_assume ["--no-cheating"] => verus_code! {
        proof fn test() { assume(false); }
    } => Err(err) => assert_one_fails(err)
}
"#,
        )
        .expect("upstream no_cheating test should be written");
        fs::write(
            fixture_root.join("Cargo.toml"),
            r#"[package]
name = "no-cheating-fixture"
version = "0.1.0"
edition = "2021"

[workspace]
"#,
        )
        .expect("fixture Cargo.toml should be written");
        fs::write(fixture_root.join("Cargo.lock"), "version = 4\n")
            .expect("fixture lockfile should be written");
        fs::write(
            fixture_root.join("src/lib.rs"),
            r#"
fn test_no_cheating_assume() {
    assume(false);
}
"#,
        )
        .expect("fixture source should be written");
        let fake_binary = temp_dir.join("fake-cargo-trust-vc");
        write_executable(
            &fake_binary,
            r#"#!/usr/bin/env bash
if [ "$1" != "check" ] || [ "$2" != "--json" ] || [ "$3" != "--emit-certificate" ] || [ "$4" != "--no-cheating" ] || [ "$5" != "." ]; then
  echo "unexpected cargo-trust-vc args: $*" >&2
  exit 64
fi
cat <<'JSON'
{"result":"no_cheating_failed","trusted_constructs":1,"findings":[{"file":"src/lib.rs","line":3,"construct":"assume","detail":"source assumption: `assume(...)`"}]}
JSON
exit 1
"#,
        );
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/no_cheating.rs",
      "classification": "ported",
      "owner_issue": "#2777",
      "reason": "Ported no-cheating CLI gate rejection.",
      "trust_vc_paths": ["ported/no_cheating"],
      "trust_vc_check_args": ["--no-cheating"],
      "expected_cases": [
        {
          "case_id": "test_no_cheating_assume",
          "expected_verdict": "error",
          "min_obligations": 0,
          "expected_error_patterns": ["src/lib.rs", "assume", "source assumption"]
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");
        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = load_corpus_report(&manifest_path, &crate_root, Some(&crate_root))
            .expect("corpus report should load");

        let run_report = run_trust_vc_corpus_with_trust_vc_binary_and_env(
            &crate_root,
            &corpus,
            None,
            &[],
            Some(&fake_binary),
            &BTreeMap::new(),
        );

        assert_eq!(run_report.passed_paths, 1);
        assert_eq!(run_report.failed_paths, 0);
        let result = &run_report.results[0];
        assert_eq!(result.observed_case_ids, vec!["test_no_cheating_assume"]);
        assert_eq!(result.observed_cases[0].verdict, "error");
        assert_eq!(result.observed_cases[0].obligation_count, 0);
        assert_eq!(
            result
                .command
                .as_ref()
                .map(|command| command.args.as_slice()),
            Some(
                &[
                    "check".to_string(),
                    "--json".to_string(),
                    "--emit-certificate".to_string(),
                    "--no-cheating".to_string(),
                    ".".to_string()
                ][..]
            )
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn no_cheating_expected_cases_must_bind_to_observed_source_file() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-no-cheating-source-binding");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        let fixture_root = temp_dir.join("ported/no_cheating");
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(fixture_root.join("src")).expect("ported fixture dir should be created");
        fs::write(upstream_tests.join("no_cheating.rs"), "").expect("upstream test should exist");
        fs::write(
            fixture_root.join("Cargo.toml"),
            r#"[package]
name = "no-cheating-fixture"
version = "0.1.0"
edition = "2021"

[workspace]
"#,
        )
        .expect("fixture Cargo.toml should be written");
        fs::write(fixture_root.join("src/lib.rs"), "fn f() {}\n")
            .expect("fixture source should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/no_cheating.rs",
      "classification": "ported",
      "owner_issue": "#2777",
      "reason": "Ported no-cheating CLI gate rejection.",
      "trust_vc_paths": ["ported/no_cheating"],
      "trust_vc_check_args": ["--no-cheating"],
      "expected_cases": [
        {
          "case_id": "test_no_cheating_assume",
          "expected_verdict": "error",
          "min_obligations": 0,
          "expected_error_patterns": ["assume", "source assumption"]
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let corpus = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");

        assert!(
            corpus.port_path_failures.iter().any(|failure| {
                failure.contains("--no-cheating expected case `test_no_cheating_assume`")
                    && failure.contains("source file pattern")
            }),
            "no-cheating expected cases must be pinned to a source file: {:?}",
            corpus.port_path_failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_cargo_fixture_rejects_certificate_paths_outside_fixture() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-cargo-fixture-outside");
        let upstream_tests = temp_dir
            .join(VERUS_TEST_ROOT)
            .join("cargo-tests/verified/basic/src");
        let fixture_root = temp_dir.join("ported/basic_fixture");
        let outside_source = temp_dir.join("outside/src/lib.rs");
        fs::create_dir_all(&upstream_tests).expect("upstream fixture dir should be created");
        fs::create_dir_all(fixture_root.join("src")).expect("ported fixture dir should be created");
        fs::create_dir_all(outside_source.parent().expect("outside source has parent"))
            .expect("outside source dir should be created");
        fs::write(upstream_tests.join("lib.rs"), "").expect("upstream test should be written");
        fs::write(
            fixture_root.join("Cargo.toml"),
            r#"[package]
name = "basic-fixture"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("fixture Cargo.toml should be written");
        fs::write(fixture_root.join("src/lib.rs"), "").expect("fixture source should be written");
        fs::write(fixture_root.join("Cargo.lock"), "version = 4\n")
            .expect("fixture lockfile should be written");
        fs::write(&outside_source, "").expect("outside source should be written");
        let fake_cargo = temp_dir.join("fake-cargo");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
if [ "$1" != "check" ] || [ "$2" != "--message-format=json" ] || [ "$3" != "--all-targets" ] || [ "$4" != "--locked" ] || [ "$5" != "--offline" ]; then
  echo "unexpected cargo args: $*" >&2
  exit 64
fi
mkdir -p "$CARGO_TARGET_DIR/debug/deps"
printf '%s: %s\n' "$CARGO_TARGET_DIR/debug/deps/liboutside_fixture.rmeta" "$(pwd)/src/lib.rs" > "$CARGO_TARGET_DIR/debug/deps/outside_fixture.d"
cat <<'JSON'
{"reason":"compiler-artifact"}
JSON
exit 0
"#,
        );
        let fake_binary = temp_dir.join("fake-cargo-trust-vc");
        write_executable(
            &fake_binary,
            r#"#!/usr/bin/env bash
if [ "$1" != "check" ] || [ "$2" != "--json" ] || [ "$3" != "--emit-certificate" ] || [ "$4" != "." ]; then
  echo "unexpected args: $*" >&2
  exit 64
fi
mkdir -p .trust_vc
cat > .trust_vc/proof-certificate.json <<'JSON'
{
  "schema_version": 1,
  "trust_vc_version": "test",
  "generated_at_unix_secs": 0,
  "crate_name": "basic-fixture",
  "functions": [
    {
      "name": "fixture_ok",
      "file": "../../outside/src/lib.rs",
      "line": 1,
      "status": "verified",
      "obligations": [
        {
          "name": "postcondition",
          "kind": "assert",
          "condition_hash": "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
          "status": "verified"
        }
      ]
    }
  ]
}
JSON
cat <<'JSON'
{
  "crate": "basic-fixture",
  "functions": [
    {
      "file": "../../outside/src/lib.rs",
      "line": 1,
      "name": "fixture_ok",
      "result": "verified",
      "duration_ms": 0
    }
  ],
  "summary": {
    "verified": 1,
    "counterexample": 0,
    "unknown": 0,
    "error": 0,
    "skipped": 0
  }
}
JSON
"#,
        );

        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/cargo-tests/verified/basic/src/lib.rs",
      "classification": "ported",
      "owner_issue": "#2780",
      "reason": "Cargo fixture port.",
      "trust_vc_paths": ["ported/basic_fixture"],
      "expected_cases": [
        {
          "case_id": "fixture_ok",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = load_corpus_report(&manifest_path, &crate_root, Some(&crate_root))
            .expect("corpus report should load");
        let env = vec![
            (
                "CARGO_HOME".to_string(),
                temp_dir.join("isolated-cargo-home").display().to_string(),
            ),
            ("CARGO".to_string(), fake_cargo.display().to_string()),
        ];
        let run_report = run_trust_vc_corpus_with_trust_vc_binary_and_env(
            &crate_root,
            &corpus,
            None,
            &env,
            Some(&fake_binary),
            &BTreeMap::new(),
        );

        assert_eq!(run_report.passed_paths, 0);
        assert_eq!(run_report.failed_paths, 1);
        let result = &run_report.results[0];
        assert!(
            result
                .failures
                .iter()
                .any(|failure| failure.contains("outside cargo fixture")),
            "proof certificates must not satisfy fixture evidence with outside files: {:?}",
            result.failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_cargo_fixture_accepts_expected_rust_diagnostics() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-cargo-rust-error");
        let manifest_path = write_expected_error_cargo_fixture(&temp_dir, "ported/borrow_error");
        let fake_cargo = temp_dir.join("fake-cargo");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
if [ "$1" != "check" ] || [ "$2" != "--message-format=json" ] || [ "$3" != "--all-targets" ] || [ "$4" != "--locked" ] || [ "$5" != "--offline" ]; then
  echo "unexpected cargo args: $*" >&2
  exit 64
fi
cat <<'JSON'
{"reason":"compiler-message","message":{"level":"error","message":"cannot borrow `values` as mutable because it is also borrowed as immutable","code":{"code":"E0502"},"spans":[{"file_name":"src/lib.rs","is_primary":true}],"rendered":"error[E0502]: cannot borrow `values` as mutable because it is also borrowed as immutable\n"}}
JSON
exit 101
"#,
        );
        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = load_corpus_report(&manifest_path, &crate_root, Some(&crate_root))
            .expect("corpus report should load");
        let env = vec![
            ("CARGO".to_string(), fake_cargo.display().to_string()),
            (
                "CARGO_HOME".to_string(),
                temp_dir.join("isolated-cargo-home").display().to_string(),
            ),
        ];

        let run_report =
            run_trust_vc_corpus_with_env(&crate_root, &corpus, None, &env, &BTreeMap::new());

        assert_eq!(run_report.passed_paths, 1);
        assert_eq!(run_report.failed_paths, 0);
        let result = &run_report.results[0];
        assert_eq!(
            result.execution_mode,
            TrustVcCorpusExecutionMode::CargoFixture
        );
        assert_eq!(result.observed_case_ids, vec!["test_regression_70"]);
        assert_eq!(result.observed_cases[0].verdict, "error");
        assert_eq!(result.observed_cases[0].obligation_count, 0);
        assert_eq!(
            result.observed_cases[0].trust_vc_path,
            "ported/borrow_error/src/lib.rs"
        );
        assert_eq!(
            result
                .command
                .as_ref()
                .map(|command| command.args.as_slice()),
            Some(
                &[
                    "check".to_string(),
                    "--message-format=json".to_string(),
                    "--all-targets".to_string(),
                    "--locked".to_string(),
                    "--offline".to_string()
                ][..]
            )
        );
        assert!(
            result.failures.is_empty(),
            "expected rust diagnostics should satisfy explicit error cases: {:?}",
            result.failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_cargo_fixture_accepts_exact_rust_diagnostic_sets() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-cargo-rust-error-set");
        let manifest_path =
            write_exact_rust_diagnostic_set_cargo_fixture(&temp_dir, "ported/opaque_error");
        let fake_cargo = temp_dir.join("fake-cargo");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
if [ "$1" != "check" ] || [ "$2" != "--message-format=json" ] || [ "$3" != "--all-targets" ] || [ "$4" != "--locked" ] || [ "$5" != "--offline" ]; then
  echo "unexpected cargo args: $*" >&2
  exit 64
fi
cat <<'JSON'
{"reason":"compiler-message","message":{"level":"error","message":"`impl Trait` in type aliases is unstable","code":{"code":"E0658"},"spans":[{"file_name":"src/lib.rs","is_primary":true,"line_start":6,"column_start":11}],"rendered":"error[E0658]: `impl Trait` in type aliases is unstable\n"}}
{"reason":"compiler-message","message":{"level":"error","message":"unconstrained opaque type","code":{"code":"E0207"},"spans":[{"file_name":"src/lib.rs","is_primary":true,"line_start":6,"column_start":6}],"rendered":"error[E0207]: unconstrained opaque type\n"}}
JSON
exit 101
"#,
        );
        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = load_corpus_report(&manifest_path, &crate_root, Some(&crate_root))
            .expect("corpus report should load");
        let env = vec![
            ("CARGO".to_string(), fake_cargo.display().to_string()),
            (
                "CARGO_HOME".to_string(),
                temp_dir.join("isolated-cargo-home").display().to_string(),
            ),
        ];

        let run_report =
            run_trust_vc_corpus_with_env(&crate_root, &corpus, None, &env, &BTreeMap::new());

        assert_eq!(run_report.passed_paths, 1);
        assert_eq!(run_report.failed_paths, 0);
        let result = &run_report.results[0];
        assert_eq!(
            result.observed_case_ids,
            vec!["test_non_async_opaque_types_disallowed"]
        );
        assert_eq!(result.observed_cases.len(), 1);
        assert_eq!(result.observed_cases[0].diagnostic_context.len(), 2);
        assert!(
            result.failures.is_empty(),
            "exact Rust diagnostic set should satisfy one expected error case: {:?}",
            result.failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_cargo_fixture_rejects_wrong_exact_rust_diagnostic_sets() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-cargo-wrong-rust-error-set");
        let manifest_path =
            write_exact_rust_diagnostic_set_cargo_fixture(&temp_dir, "ported/opaque_error");
        let fake_cargo = temp_dir.join("fake-cargo");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
if [ "$1" != "check" ] || [ "$2" != "--message-format=json" ] || [ "$3" != "--all-targets" ] || [ "$4" != "--locked" ] || [ "$5" != "--offline" ]; then
  echo "unexpected cargo args: $*" >&2
  exit 64
fi
cat <<'JSON'
{"reason":"compiler-message","message":{"level":"error","message":"`impl Trait` in type aliases is unstable","code":{"code":"E0658"},"spans":[{"file_name":"src/lib.rs","is_primary":true,"line_start":6,"column_start":11}],"rendered":"error[E0658]: `impl Trait` in type aliases is unstable\n"}}
{"reason":"compiler-message","message":{"level":"error","message":"different opaque type diagnostic","code":{"code":"E0207"},"spans":[{"file_name":"src/lib.rs","is_primary":true,"line_start":6,"column_start":6}],"rendered":"error[E0207]: different opaque type diagnostic\n"}}
JSON
exit 101
"#,
        );
        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = load_corpus_report(&manifest_path, &crate_root, Some(&crate_root))
            .expect("corpus report should load");
        let env = vec![
            ("CARGO".to_string(), fake_cargo.display().to_string()),
            (
                "CARGO_HOME".to_string(),
                temp_dir.join("isolated-cargo-home").display().to_string(),
            ),
        ];

        let run_report =
            run_trust_vc_corpus_with_env(&crate_root, &corpus, None, &env, &BTreeMap::new());

        assert_eq!(run_report.passed_paths, 0);
        assert_eq!(run_report.failed_paths, 1);
        let result = &run_report.results[0];
        assert!(
            result.failures.iter().any(|failure| failure.contains(
                "no Rust compiler diagnostic set matched expected_rust_diagnostic_pattern_sets"
            )),
            "wrong exact diagnostic set must fail closed: {:?}",
            result.failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_cargo_fixture_deduplicates_repeated_rust_diagnostics() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-cargo-duplicate-rust-error");
        let manifest_path = write_expected_error_cargo_fixture(&temp_dir, "ported/borrow_error");
        let fake_cargo = temp_dir.join("fake-cargo");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
if [ "$1" != "check" ] || [ "$2" != "--message-format=json" ] || [ "$3" != "--all-targets" ] || [ "$4" != "--locked" ] || [ "$5" != "--offline" ]; then
  echo "unexpected cargo args: $*" >&2
  exit 64
fi
cat <<'JSON'
{"reason":"compiler-message","message":{"level":"error","message":"cannot borrow `values` as mutable because it is also borrowed as immutable","code":{"code":"E0502"},"spans":[{"file_name":"src/lib.rs","is_primary":true,"line_start":3,"column_start":5}],"rendered":"error[E0502]: cannot borrow `values` as mutable because it is also borrowed as immutable\n"}}
{"reason":"compiler-message","message":{"level":"failure-note","message":"For more information about this error, try `rustc --explain E0502`.","spans":[],"rendered":"For more information about this error, try `rustc --explain E0502`.\n"}}
{"reason":"compiler-message","message":{"level":"error","message":"cannot borrow `values` as mutable because it is also borrowed as immutable","code":{"code":"E0502"},"spans":[{"file_name":"src/lib.rs","is_primary":true,"line_start":3,"column_start":5}],"rendered":"error[E0502]: cannot borrow `values` as mutable because it is also borrowed as immutable\n"}}
JSON
exit 101
"#,
        );
        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = load_corpus_report(&manifest_path, &crate_root, Some(&crate_root))
            .expect("corpus report should load");
        let env = vec![
            ("CARGO".to_string(), fake_cargo.display().to_string()),
            (
                "CARGO_HOME".to_string(),
                temp_dir.join("isolated-cargo-home").display().to_string(),
            ),
        ];

        let run_report =
            run_trust_vc_corpus_with_env(&crate_root, &corpus, None, &env, &BTreeMap::new());

        assert_eq!(run_report.passed_paths, 1);
        assert_eq!(run_report.failed_paths, 0);
        let result = &run_report.results[0];
        assert_eq!(result.observed_case_ids, vec!["test_regression_70"]);
        assert_eq!(result.observed_cases.len(), 1);
        assert!(
            result.failures.is_empty(),
            "duplicate cargo target diagnostics should collapse to one expected error: {:?}",
            result.failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_cargo_fixture_rejects_wrong_source_for_expected_rust_diagnostics() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-cargo-wrong-error-source");
        let manifest_path = write_expected_error_cargo_fixture(&temp_dir, "ported/borrow_error");
        let build_script = temp_dir.join("ported/borrow_error/build.rs");
        fs::write(&build_script, "").expect("fixture build script should be written");
        let fake_cargo = temp_dir.join("fake-cargo");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
if [ "$1" != "check" ] || [ "$2" != "--message-format=json" ] || [ "$3" != "--all-targets" ] || [ "$4" != "--locked" ] || [ "$5" != "--offline" ]; then
  echo "unexpected cargo args: $*" >&2
  exit 64
fi
cat <<'JSON'
{"reason":"compiler-message","message":{"level":"error","message":"cannot borrow `values` as mutable because it is also borrowed as immutable","code":{"code":"E0502"},"spans":[{"file_name":"build.rs","is_primary":true}],"rendered":"error[E0502]: cannot borrow `values` as mutable because it is also borrowed as immutable\n"}}
JSON
exit 101
"#,
        );
        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = load_corpus_report(&manifest_path, &crate_root, Some(&crate_root))
            .expect("corpus report should load");
        let env = vec![
            ("CARGO".to_string(), fake_cargo.display().to_string()),
            (
                "CARGO_HOME".to_string(),
                temp_dir.join("isolated-cargo-home").display().to_string(),
            ),
        ];

        let run_report =
            run_trust_vc_corpus_with_env(&crate_root, &corpus, None, &env, &BTreeMap::new());

        assert_eq!(run_report.passed_paths, 0);
        assert_eq!(run_report.failed_paths, 1);
        let result = &run_report.results[0];
        assert!(
            result.failures.iter().any(|failure| failure.contains(
                "Rust compiler diagnostic source does not match mirrored upstream cargo fixture source"
            )),
            "wrong fixture-local source must not satisfy expected Rust diagnostics: {:?}",
            result.failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_cargo_fixture_accepts_non_cargo_upstream_rust_diagnostics() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-noncargo-rust-error");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT);
        let fixture_root = temp_dir.join("ported/harness_invalid_rust");
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(fixture_root.join("src")).expect("ported fixture dir should be created");
        fs::write(upstream_tests.join("harness.rs"), "").expect("upstream test should be written");
        fs::write(
            fixture_root.join("Cargo.toml"),
            r#"[package]
name = "harness-invalid-rust"
version = "0.1.0"
edition = "2021"

[workspace]
"#,
        )
        .expect("fixture Cargo.toml should be written");
        fs::write(fixture_root.join("Cargo.lock"), "version = 4\n")
            .expect("fixture Cargo.lock should be written");
        fs::write(
            fixture_root.join("src/lib.rs"),
            r#"
pub fn harness_invalid_rust() {
    invalid(true);
}
"#,
        )
        .expect("fixture source should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/harness.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported rustc diagnostic fixture for a non-cargo upstream harness.",
      "trust_vc_paths": ["ported/harness_invalid_rust"],
      "expected_cases": [
        {
          "case_id": "harness_invalid_rust",
          "trust_vc_path": "ported/harness_invalid_rust",
          "expected_verdict": "error",
          "min_obligations": 0,
          "expected_error_patterns": ["cannot find function `invalid` in this scope"]
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");
        let fake_cargo = temp_dir.join("fake-cargo");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
if [ "$1" != "check" ] || [ "$2" != "--message-format=json" ] || [ "$3" != "--all-targets" ] || [ "$4" != "--locked" ] || [ "$5" != "--offline" ]; then
  echo "unexpected cargo args: $*" >&2
  exit 64
fi
cat <<'JSON'
{"reason":"compiler-message","message":{"level":"error","message":"cannot find function `invalid` in this scope","code":{"code":"E0425"},"spans":[{"file_name":"src/lib.rs","is_primary":true}],"rendered":"error[E0425]: cannot find function `invalid` in this scope\n"}}
JSON
exit 101
"#,
        );
        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = load_corpus_report(&manifest_path, &crate_root, Some(&crate_root))
            .expect("corpus report should load");
        let env = vec![
            ("CARGO".to_string(), fake_cargo.display().to_string()),
            (
                "CARGO_HOME".to_string(),
                temp_dir.join("isolated-cargo-home").display().to_string(),
            ),
        ];

        let run_report =
            run_trust_vc_corpus_with_env(&crate_root, &corpus, None, &env, &BTreeMap::new());

        assert_eq!(run_report.passed_paths, 1);
        assert_eq!(run_report.failed_paths, 0);
        let result = &run_report.results[0];
        assert!(result.failures.is_empty(), "{:?}", result.failures);
        assert_eq!(result.observed_case_ids, vec!["harness_invalid_rust"]);
        assert_eq!(
            result.observed_cases[0].trust_vc_path,
            "ported/harness_invalid_rust/src/lib.rs"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_cargo_fixture_rejects_expected_error_when_cargo_check_succeeds() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-cargo-error-success");
        let manifest_path = write_expected_error_cargo_fixture(&temp_dir, "ported/assert_false");
        let fake_cargo = temp_dir.join("fake-cargo");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
if [ "$1" != "check" ] || [ "$2" != "--message-format=json" ] || [ "$3" != "--all-targets" ] || [ "$4" != "--locked" ] || [ "$5" != "--offline" ]; then
  echo "unexpected cargo args: $*" >&2
  exit 64
fi
exit 0
"#,
        );
        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = load_corpus_report(&manifest_path, &crate_root, Some(&crate_root))
            .expect("corpus report should load");
        let env = vec![
            ("CARGO".to_string(), fake_cargo.display().to_string()),
            (
                "CARGO_HOME".to_string(),
                temp_dir.join("isolated-cargo-home").display().to_string(),
            ),
        ];

        let run_report =
            run_trust_vc_corpus_with_env(&crate_root, &corpus, None, &env, &BTreeMap::new());

        assert_eq!(run_report.passed_paths, 0);
        assert_eq!(run_report.failed_paths, 1);
        let result = &run_report.results[0];
        assert!(
            result
                .failures
                .iter()
                .any(|failure| failure.contains("cargo check succeeded")),
            "successful cargo check must not satisfy an expected Rust error: {:?}",
            result.failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_cargo_fixture_rejects_generic_command_failures_as_errors() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-cargo-generic-failure");
        let manifest_path = write_expected_error_cargo_fixture(&temp_dir, "ported/generic_failure");
        let fake_cargo = temp_dir.join("fake-cargo");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
if [ "$1" != "check" ] || [ "$2" != "--message-format=json" ] || [ "$3" != "--all-targets" ] || [ "$4" != "--locked" ] || [ "$5" != "--offline" ]; then
  echo "unexpected cargo args: $*" >&2
  exit 64
fi
echo "simulated dependency resolution failure" >&2
exit 101
"#,
        );
        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = load_corpus_report(&manifest_path, &crate_root, Some(&crate_root))
            .expect("corpus report should load");
        let env = vec![
            ("CARGO".to_string(), fake_cargo.display().to_string()),
            (
                "CARGO_HOME".to_string(),
                temp_dir.join("isolated-cargo-home").display().to_string(),
            ),
        ];

        let run_report =
            run_trust_vc_corpus_with_env(&crate_root, &corpus, None, &env, &BTreeMap::new());

        assert_eq!(run_report.passed_paths, 0);
        assert_eq!(run_report.failed_paths, 1);
        let result = &run_report.results[0];
        assert!(
            result.failures.iter().any(|failure| failure.contains(
                "cargo check failed without Rust compiler error diagnostics with primary source spans"
            )),
            "generic command failures must remain blocking: {:?}",
            result.failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_cargo_fixture_rejects_extra_source_error_diagnostics() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-cargo-extra-errors");
        let manifest_path = write_expected_error_cargo_fixture(&temp_dir, "ported/extra_errors");
        let fake_cargo = temp_dir.join("fake-cargo");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
if [ "$1" != "check" ] || [ "$2" != "--message-format=json" ] || [ "$3" != "--all-targets" ] || [ "$4" != "--locked" ] || [ "$5" != "--offline" ]; then
  echo "unexpected cargo args: $*" >&2
  exit 64
fi
cat <<'JSON'
{"reason":"compiler-message","message":{"level":"error","message":"first Rust compiler error","code":{"code":"E0502"},"spans":[{"file_name":"src/lib.rs","is_primary":true}],"rendered":"error[E0502]: first Rust compiler error\n"}}
{"reason":"compiler-message","message":{"level":"error","message":"second Rust compiler error","code":{"code":"E0503"},"spans":[{"file_name":"src/lib.rs","is_primary":true}],"rendered":"error[E0503]: second Rust compiler error\n"}}
JSON
exit 101
"#,
        );
        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = load_corpus_report(&manifest_path, &crate_root, Some(&crate_root))
            .expect("corpus report should load");
        let env = vec![
            ("CARGO".to_string(), fake_cargo.display().to_string()),
            (
                "CARGO_HOME".to_string(),
                temp_dir.join("isolated-cargo-home").display().to_string(),
            ),
        ];

        let run_report =
            run_trust_vc_corpus_with_env(&crate_root, &corpus, None, &env, &BTreeMap::new());

        assert_eq!(run_report.passed_paths, 0);
        assert_eq!(run_report.failed_paths, 1);
        let result = &run_report.results[0];
        assert!(
            result.failures.iter().any(|failure| failure
                .contains("expected exactly 1 Rust compiler error diagnostic(s), observed 2")),
            "extra Rust compiler diagnostics must fail closed: {:?}",
            result.failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_cargo_fixture_rejects_external_source_error_diagnostics() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-cargo-external-errors");
        let manifest_path = write_expected_error_cargo_fixture(&temp_dir, "ported/external_errors");
        let external_source = temp_dir.join("external_dep/src/lib.rs");
        fs::create_dir_all(
            external_source
                .parent()
                .expect("external source has parent"),
        )
        .expect("external source dir should be created");
        fs::write(&external_source, "").expect("external source should be written");
        let fake_cargo = temp_dir.join("fake-cargo");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
if [ "$1" != "check" ] || [ "$2" != "--message-format=json" ] || [ "$3" != "--all-targets" ] || [ "$4" != "--locked" ] || [ "$5" != "--offline" ]; then
  echo "unexpected cargo args: $*" >&2
  exit 64
fi
cat <<'JSON'
{"reason":"compiler-message","message":{"level":"error","message":"cannot borrow `values` as mutable because it is also borrowed as immutable","code":{"code":"E0502"},"spans":[{"file_name":"src/lib.rs","is_primary":true}],"rendered":"error[E0502]: cannot borrow `values` as mutable because it is also borrowed as immutable\n"}}
{"reason":"compiler-message","message":{"level":"error","message":"dependency failed to compile","code":{"code":"E9999"},"spans":[{"file_name":"../../external_dep/src/lib.rs","is_primary":true}],"rendered":"error[E9999]: dependency failed to compile\n"}}
JSON
exit 101
"#,
        );
        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = load_corpus_report(&manifest_path, &crate_root, Some(&crate_root))
            .expect("corpus report should load");
        let env = vec![
            ("CARGO".to_string(), fake_cargo.display().to_string()),
            (
                "CARGO_HOME".to_string(),
                temp_dir.join("isolated-cargo-home").display().to_string(),
            ),
        ];

        let run_report =
            run_trust_vc_corpus_with_env(&crate_root, &corpus, None, &env, &BTreeMap::new());

        assert_eq!(run_report.passed_paths, 0);
        assert_eq!(run_report.failed_paths, 1);
        let result = &run_report.results[0];
        assert!(
            result.failures.iter().any(|failure| failure
                .contains("Rust compiler diagnostic source is outside cargo fixture")),
            "external cargo diagnostics must fail closed: {:?}",
            result.failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_cargo_fixture_rejects_source_errors_with_wrong_exit_code() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-cargo-wrong-error-exit");
        let manifest_path = write_expected_error_cargo_fixture(&temp_dir, "ported/wrong_exit");
        let fake_cargo = temp_dir.join("fake-cargo");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
if [ "$1" != "check" ] || [ "$2" != "--message-format=json" ] || [ "$3" != "--all-targets" ] || [ "$4" != "--locked" ] || [ "$5" != "--offline" ]; then
  echo "unexpected cargo args: $*" >&2
  exit 64
fi
cat <<'JSON'
{"reason":"compiler-message","message":{"level":"error","message":"Rust compiler error","code":{"code":"E0502"},"spans":[{"file_name":"src/lib.rs","is_primary":true}],"rendered":"error[E0502]: Rust compiler error\n"}}
JSON
exit 64
"#,
        );
        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = load_corpus_report(&manifest_path, &crate_root, Some(&crate_root))
            .expect("corpus report should load");
        let env = vec![
            ("CARGO".to_string(), fake_cargo.display().to_string()),
            (
                "CARGO_HOME".to_string(),
                temp_dir.join("isolated-cargo-home").display().to_string(),
            ),
        ];

        let run_report =
            run_trust_vc_corpus_with_env(&crate_root, &corpus, None, &env, &BTreeMap::new());

        assert_eq!(run_report.passed_paths, 0);
        assert_eq!(run_report.failed_paths, 1);
        let result = &run_report.results[0];
        assert!(
            result.failures.iter().any(|failure| failure
                .contains("expected cargo check source-error exit code 101, got 64")),
            "unexpected cargo exit code must fail closed: {:?}",
            result.failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_corpus_cargo_fixture_rejects_malformed_json_diagnostics() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-cargo-malformed-json");
        let manifest_path = write_expected_error_cargo_fixture(&temp_dir, "ported/malformed_json");
        let fake_cargo = temp_dir.join("fake-cargo");
        write_executable(
            &fake_cargo,
            r#"#!/usr/bin/env bash
if [ "$1" != "check" ] || [ "$2" != "--message-format=json" ] || [ "$3" != "--all-targets" ] || [ "$4" != "--locked" ] || [ "$5" != "--offline" ]; then
  echo "unexpected cargo args: $*" >&2
  exit 64
fi
cat <<'JSON'
{"reason":"compiler-message","message":{"level":"error","message":"Rust compiler error","code":{"code":"E0502"},"spans":[{"file_name":"src/lib.rs","is_primary":true}],"rendered":"error[E0502]: Rust compiler error\n"}}
not-json
JSON
exit 101
"#,
        );
        let crate_root = temp_dir
            .canonicalize()
            .expect("temp dir should canonicalize");
        let corpus = load_corpus_report(&manifest_path, &crate_root, Some(&crate_root))
            .expect("corpus report should load");
        let env = vec![
            ("CARGO".to_string(), fake_cargo.display().to_string()),
            (
                "CARGO_HOME".to_string(),
                temp_dir.join("isolated-cargo-home").display().to_string(),
            ),
        ];

        let run_report =
            run_trust_vc_corpus_with_env(&crate_root, &corpus, None, &env, &BTreeMap::new());

        assert_eq!(run_report.passed_paths, 0);
        assert_eq!(run_report.failed_paths, 1);
        let result = &run_report.results[0];
        assert!(
            result
                .failures
                .iter()
                .any(|failure| failure.contains("cargo check emitted malformed JSON message line")),
            "malformed cargo JSON must fail closed: {:?}",
            result.failures
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn corpus_report_rejects_narrowed_manifest_roots() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-corpus-root");
        let upstream_tests = temp_dir.join(VERUS_TEST_ROOT).join("narrow");
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(temp_dir.join("ported")).expect("ported dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("foo test should be written");
        fs::write(temp_dir.join("ported/foo.rs"), "").expect("ported foo should be written");
        let manifest_path = temp_dir.join("verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests/narrow"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/narrow/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported for TrustVc.",
      "trust_vc_paths": ["ported/foo.rs"],
      "expected_cases": [
        {
          "case_id": "identity",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("manifest should be written");

        let report = load_corpus_report(&manifest_path, &temp_dir, Some(&temp_dir))
            .expect("corpus report should load");
        assert!(
            report
                .invalid_entries
                .iter()
                .any(|entry| entry.contains("upstream.test_roots")),
            "narrowed test roots must be invalid: {:?}",
            report.invalid_entries
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn verus_corpus_root_coverage_gate_rejects_legacy_single_root_manifest() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-legacy-root-coverage");
        let crate_root = temp_dir.join("trust_vc");
        let verus_root = temp_dir.join("verus");
        let upstream_tests = verus_root.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("foo test should be written");
        init_git_repo(&verus_root);
        let upstream_ref = git_commit_all(&verus_root, "pin legacy single-root tests");

        fs::create_dir_all(crate_root.join("evals/verus")).expect("manifest dir should be created");
        let manifest_path = crate_root.join("evals/verus/verus-tests.json");
        let manifest = serde_json::json!({
            "schema_version": 1,
            "manifest_id": "upstream-verus-corpus",
            "description": "Legacy single-root manifest.",
            "upstream": {
                "repo": VERUS_REPO_URL,
                "ref": upstream_ref,
                "test_roots": [VERUS_TEST_ROOT]
            },
            "gate": {
                "missing_entry": "fail",
                "failing_classifications": ["unclassified", "unsupported-gap"]
            },
            "entries": [
                {
                    "upstream_path": "source/rust_verify_test/tests/foo.rs",
                    "classification": "unsupported-gap",
                    "owner_issue": "#123",
                    "reason": "Legacy manifest root coverage regression test."
                }
            ]
        });
        fs::write(
            &manifest_path,
            format!(
                "{}\n",
                serde_json::to_string_pretty(&manifest).expect("manifest JSON should serialize")
            ),
        )
        .expect("manifest should be written");

        let report = load_corpus_report(&manifest_path, &crate_root, Some(&verus_root))
            .expect("corpus report should load");
        assert_eq!(
            report.upstream_test_roots,
            vec![VERUS_TEST_ROOT.to_string()]
        );
        assert_eq!(report.upstream_test_count, 1);

        let gate = verus_corpus_root_coverage_gate(&report);
        assert!(gate.required);
        assert_eq!(gate.status, GateStatus::Failed);
        assert!(
            gate.detail
                .as_deref()
                .is_some_and(|detail| detail.contains(VERUS_CARGO_VERUS_TEST_ROOT)),
            "legacy single-root manifests must fail the two-root coverage gate: {:?}",
            gate.detail
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn update_verus_tests_manifest_preserves_classifications_and_fails_closed() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-update");
        let crate_root = temp_dir.join("trust_vc");
        let verus_root = temp_dir.join("verus");
        let upstream_tests = verus_root.join(VERUS_TEST_ROOT);
        fs::create_dir_all(upstream_tests.join("nested"))
            .expect("upstream test dirs should be created");
        fs::create_dir_all(crate_root.join("evals/verus/ported"))
            .expect("ported dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("foo test should be written");
        fs::write(upstream_tests.join("nested/bar.rs"), "").expect("bar test should be written");
        fs::write(upstream_tests.join("ignored.txt"), "").expect("non-rs file should be written");
        init_git_repo(&verus_root);
        git_commit_all(&verus_root, "pin upstream tests");
        git_tag(&verus_root, "abc123");
        fs::write(crate_root.join("evals/verus/ported/foo.rs"), "")
            .expect("ported foo should be written");
        let manifest_path = crate_root.join("evals/verus/verus-tests.json");
        fs::write(
            &manifest_path,
            r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Existing manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "old",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported for TrustVc.",
      "trust_vc_paths": ["evals/verus/ported/foo.rs"],
      "expected_cases": [
        {
          "case_id": "identity",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    },
    {
      "upstream_path": "source/rust_verify_test/tests/stale.rs",
      "classification": "unchanged",
      "owner_issue": "#124",
      "reason": "No longer present upstream.",
      "trust_vc_paths": ["evals/verus/ported/stale.rs"],
      "expected_cases": [
        {
          "case_id": "stale",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##,
        )
        .expect("existing manifest should be written");

        let args = test_evidence_args(&crate_root, &verus_root, Some("abc123"));
        update_verus_tests_manifest(&args, Some("abc123")).expect("manifest update should succeed");

        let text = fs::read_to_string(&manifest_path).expect("manifest should be readable");
        let json: serde_json::Value =
            serde_json::from_str(&text).expect("generated manifest should parse as JSON");
        assert_eq!(json["upstream"]["ref"], "abc123");
        let entries = json["entries"]
            .as_array()
            .expect("entries should be an array");
        assert_eq!(entries.len(), 2);
        assert_eq!(
            entries[0]["upstream_path"],
            "source/rust_verify_test/tests/foo.rs"
        );
        assert_eq!(entries[0]["classification"], "ported");
        assert_eq!(entries[0]["trust_vc_paths"][0], "evals/verus/ported/foo.rs");
        assert_eq!(entries[0]["expected_cases"][0]["case_id"], "identity");
        assert_eq!(
            entries[1]["upstream_path"],
            "source/rust_verify_test/tests/nested/bar.rs"
        );
        assert_eq!(entries[1]["classification"], "unclassified");
        assert_eq!(entries[1]["owner_issue"], "TBD");

        let report = load_corpus_report(&manifest_path, &crate_root, Some(&verus_root))
            .expect("generated manifest should load");
        assert_eq!(report.upstream_test_count, 2);
        assert_eq!(report.missing_entries.len(), 0);
        assert!(
            report
                .failing_entries
                .iter()
                .any(|entry| entry.contains("nested/bar.rs: classification=unclassified")),
            "new unclassified entries must remain blocking: {:?}",
            report.failing_entries
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn update_verus_tests_manifest_includes_cargo_verus_test_root_entries() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-update-cargo-verus-root");
        let crate_root = temp_dir.join("trust_vc");
        let verus_root = temp_dir.join("verus");
        let upstream_tests = verus_root.join(VERUS_TEST_ROOT);
        let cargo_verus_tests = verus_root.join(VERUS_CARGO_VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(&cargo_verus_tests).expect("cargo-verus test dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("foo test should be written");
        fs::write(cargo_verus_tests.join("integration.rs"), "")
            .expect("cargo-verus integration test should be written");
        fs::write(cargo_verus_tests.join("README.md"), "")
            .expect("non-rs cargo-verus file should be written");
        init_git_repo(&verus_root);
        let upstream_ref = git_commit_all(&verus_root, "pin two-root upstream tests");

        let args = test_evidence_args(&crate_root, &verus_root, Some(&upstream_ref));
        update_verus_tests_manifest(&args, Some(&upstream_ref))
            .expect("manifest update should succeed");

        let text = fs::read_to_string(crate_root.join("evals/verus/verus-tests.json"))
            .expect("manifest should be readable");
        let json: serde_json::Value =
            serde_json::from_str(&text).expect("generated manifest should parse as JSON");
        assert_eq!(json["upstream"]["ref"], upstream_ref);
        assert_eq!(
            json["upstream"]["test_roots"],
            serde_json::json!([VERUS_TEST_ROOT, VERUS_CARGO_VERUS_TEST_ROOT])
        );
        let entries = json["entries"]
            .as_array()
            .expect("entries should be an array");
        let upstream_paths = entries
            .iter()
            .map(|entry| {
                entry["upstream_path"]
                    .as_str()
                    .expect("entry should have upstream_path")
                    .to_string()
            })
            .collect::<Vec<_>>();
        assert_eq!(
            upstream_paths,
            vec![
                format!("{VERUS_CARGO_VERUS_TEST_ROOT}/integration.rs"),
                format!("{VERUS_TEST_ROOT}/foo.rs"),
            ]
        );
        let cargo_verus_entry = entries
            .iter()
            .find(|entry| {
                entry["upstream_path"] == format!("{VERUS_CARGO_VERUS_TEST_ROOT}/integration.rs")
            })
            .expect("manifest should include the cargo-verus test entry");
        assert_eq!(cargo_verus_entry["classification"], "unclassified");
        assert_eq!(cargo_verus_entry["owner_issue"], "TBD");

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn update_verus_tests_manifest_uses_git_ls_tree_ref_not_worktree() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-update-pinned");
        let crate_root = temp_dir.join("trust_vc");
        let verus_root = temp_dir.join("verus");
        let upstream_tests = verus_root.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dirs should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("foo test should be written");
        init_git_repo(&verus_root);
        let pinned_ref = git_commit_all(&verus_root, "pin upstream foo");
        fs::write(upstream_tests.join("bar.rs"), "")
            .expect("dirty worktree test should be written");

        let args = test_evidence_args(&crate_root, &verus_root, Some(&pinned_ref));
        update_verus_tests_manifest(&args, Some(&pinned_ref))
            .expect("manifest update should succeed");

        let text = fs::read_to_string(crate_root.join("evals/verus/verus-tests.json"))
            .expect("manifest should be readable");
        let json: serde_json::Value =
            serde_json::from_str(&text).expect("generated manifest should parse as JSON");
        assert_eq!(json["upstream"]["ref"], pinned_ref);
        let entries = json["entries"]
            .as_array()
            .expect("entries should be an array");
        assert_eq!(entries.len(), 1);
        assert_eq!(
            entries[0]["upstream_path"],
            "source/rust_verify_test/tests/foo.rs"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn update_verus_tests_manifest_rejects_duplicate_existing_entries() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-duplicates");
        let crate_root = temp_dir.join("trust_vc");
        let verus_root = temp_dir.join("verus");
        let upstream_tests = verus_root.join(VERUS_TEST_ROOT);
        fs::create_dir_all(&upstream_tests).expect("upstream test dir should be created");
        fs::create_dir_all(crate_root.join("evals/verus")).expect("manifest dir should be created");
        fs::write(upstream_tests.join("foo.rs"), "").expect("foo test should be written");
        let manifest_path = crate_root.join("evals/verus/verus-tests.json");
        let original = r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "unchanged",
      "owner_issue": "#123",
      "reason": "Runs unchanged."
    },
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#124",
      "reason": "Duplicate that makes preservation ambiguous.",
      "trust_vc_paths": ["evals/verus/ported/foo.rs"]
    }
  ]
}"##;
        fs::write(&manifest_path, original).expect("duplicate manifest should be written");

        let args = test_evidence_args(&crate_root, &verus_root, Some("abc123"));
        let err = update_verus_tests_manifest(&args, Some("abc123"))
            .expect_err("duplicates should make the update fail");
        assert!(
            err.to_string().contains("duplicate upstream_path"),
            "unexpected error: {err}"
        );
        assert_eq!(
            fs::read_to_string(&manifest_path).expect("manifest should remain readable"),
            original,
            "duplicate manifests must be preserved for manual repair"
        );

        let report = load_corpus_report(&manifest_path, &crate_root, Some(&verus_root))
            .expect("duplicate manifest should still load for reporting");
        assert_eq!(
            report.duplicate_entries,
            vec!["source/rust_verify_test/tests/foo.rs"]
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn git_url_rewrite_detection_finds_local_lowercase_and_include_risks() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-git-rewrite");
        fs::create_dir_all(temp_dir.join(".git")).expect("git config dir should be created");

        fs::write(
            temp_dir.join(".git/config"),
            r#"
[url "ssh://attacker.invalid/"]
    insteadof = https://github.com/alabsystems/
"#,
        )
        .expect("git config should be written");
        assert!(active_git_url_rewrite_detected(&temp_dir));

        fs::write(
            temp_dir.join(".git/config"),
            r#"
[include]
    path = ../external-git-config
"#,
        )
        .expect("git include config should be written");
        assert!(active_git_url_rewrite_detected(&temp_dir));

        fs::write(
            temp_dir.join(".git/config"),
            r#"
[remote "origin"]
    url = git@github.com:alabsystems/trust-vc.git
"#,
        )
        .expect("safe git config should be written");
        assert!(!git_config_url_rewrite_in_file(
            &temp_dir.join(".git/config")
        ));

        let worktree_root = temp_dir.join("linked-worktree");
        let linked_git_dir = temp_dir.join("linked-git-dir");
        fs::create_dir_all(&worktree_root).expect("linked worktree should be created");
        fs::create_dir_all(&linked_git_dir).expect("linked gitdir should be created");
        fs::write(
            worktree_root.join(".git"),
            format!("gitdir: {}\n", linked_git_dir.display()),
        )
        .expect("linked worktree git pointer should be written");
        fs::write(
            linked_git_dir.join("config.worktree"),
            r#"
[url "ssh://attacker.invalid/"]
    insteadOf = https://github.com/alabsystems/
"#,
        )
        .expect("linked worktree config should be written");
        assert!(active_git_url_rewrite_detected(&worktree_root));

        fs::write(linked_git_dir.join("config.worktree"), "")
            .expect("linked worktree config should be cleared");
        let common_git_dir = temp_dir.join("common-git-dir");
        fs::create_dir_all(&common_git_dir).expect("common gitdir should be created");
        fs::write(linked_git_dir.join("commondir"), "../common-git-dir\n")
            .expect("commondir pointer should be written");
        fs::write(
            common_git_dir.join("config"),
            r#"
[include]
    path = ../external-git-config
"#,
        )
        .expect("common git config should be written");
        assert!(active_git_url_rewrite_detected(&worktree_root));

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn cargo_config_override_detection_finds_paths_and_source_replacements() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-cargo-override");
        fs::create_dir_all(temp_dir.join(".cargo")).expect("cargo config dir should be created");

        fs::write(
            temp_dir.join(".cargo/config.toml"),
            r#"
[build]
jobs = 4
"#,
        )
        .expect("safe cargo config should be written");
        assert!(!cargo_config_override_in_file(
            &temp_dir.join(".cargo/config.toml")
        ));

        fs::write(
            temp_dir.join(".cargo/config.toml"),
            r#"
paths = ["../ay"]
"#,
        )
        .expect("paths override config should be written");
        assert!(active_cargo_config_override_detected(&temp_dir, None));

        fs::write(
            temp_dir.join(".cargo/config.toml"),
            r#"
[source.crates-io]
replace-with = "mirror"
"#,
        )
        .expect("source replacement config should be written");
        assert!(active_cargo_config_override_detected(&temp_dir, None));

        fs::write(
            temp_dir.join(".cargo/config.toml"),
            r#"
[patch."https://github.com/example/upstream"]
example = { path = "../example" }
"#,
        )
        .expect("patch override config should be written");
        assert!(active_cargo_config_override_detected(&temp_dir, None));

        fs::write(
            temp_dir.join(".cargo/config.toml"),
            r#"
[build]
rustc-wrapper = "sccache"
"#,
        )
        .expect("rustc-wrapper config should be written");
        assert!(active_cargo_config_override_detected(&temp_dir, None));

        fs::write(
            temp_dir.join(".cargo/config.toml"),
            r#"
[target.aarch64-apple-darwin]
rustflags = ["--cfg", "evidence_side_effect"]
"#,
        )
        .expect("target rustflags config should be written");
        assert!(active_cargo_config_override_detected(&temp_dir, None));

        fs::write(temp_dir.join(".cargo/config.toml"), "").expect("cargo config should be cleared");
        let isolated_cargo_home = temp_dir.join("evidence-cargo-home");
        fs::create_dir_all(&isolated_cargo_home).expect("isolated cargo home should be created");
        fs::write(
            isolated_cargo_home.join("config.toml"),
            r#"
paths = ["../ay"]
"#,
        )
        .expect("isolated cargo home config should be written");
        assert!(active_cargo_config_override_detected(
            &temp_dir,
            Some(&isolated_cargo_home)
        ));
        fs::write(isolated_cargo_home.join("config.toml"), "")
            .expect("isolated cargo home config should be cleared");

        fs::write(
            temp_dir.join("Cargo.toml"),
            r#"
[workspace.dependencies]
local-helper = { path = "crates/local-helper" }
"#,
        )
        .expect("workspace Cargo.toml path dependency should be written");
        assert!(
            !active_cargo_config_override_detected(&temp_dir, None),
            "ordinary manifest path dependencies are not Cargo replacement overrides"
        );

        fs::write(
            temp_dir.join("Cargo.toml"),
            r#"
[patch."https://github.com/example/upstream"]
example = { path = "../example" }
"#,
        )
        .expect("workspace Cargo.toml patch should be written");
        assert!(active_cargo_config_override_detected(&temp_dir, None));

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn cargo_config_override_detection_scans_parent_and_nested_fixture_configs() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-cargo-override-effective");
        let parent = temp_dir.join("parent");
        let repo = parent.join("repo");
        fs::create_dir_all(parent.join(".cargo")).expect("parent cargo config dir should exist");
        fs::create_dir_all(&repo).expect("repo dir should exist");

        fs::write(
            parent.join(".cargo/config.toml"),
            r#"
[build]
rustflags = ["--cfg", "parent_override"]
"#,
        )
        .expect("parent cargo config should be written");
        assert!(
            active_cargo_config_override_detected(&repo, None),
            "Cargo config overrides in parent directories affect cargo runs from the repo"
        );

        fs::write(parent.join(".cargo/config.toml"), "")
            .expect("parent cargo config should be cleared");
        fs::create_dir_all(repo.join("evals/verus/ported/fixture/.cargo"))
            .expect("nested fixture cargo config dir should exist");
        fs::write(
            repo.join("evals/verus/ported/fixture/.cargo/config.toml"),
            r#"
paths = ["../../../../fake-ay"]
"#,
        )
        .expect("nested cargo config should be written");
        assert!(
            active_cargo_config_override_detected(&repo, None),
            "Cargo config overrides below the repo can affect cargo fixture runs"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn default_verus_command_uses_non_login_shell() {
        assert!(
            !DEFAULT_VERUS_TEST_COMMAND.contains("bash -lc"),
            "default Verus command must not use a login shell"
        );
        assert!(
            DEFAULT_VERUS_TEST_COMMAND.contains("--noprofile --norc"),
            "default Verus command must disable bash startup files"
        );
        assert!(
            DEFAULT_VERUS_TEST_COMMAND.contains("$(dirname \"$CARGO\")"),
            "default Verus command must expose the proven cargo binary to Verus activation"
        );
        assert!(
            DEFAULT_VERUS_TEST_COMMAND.contains("git sparse-checkout disable;"),
            "default Verus command must materialize sparse Verus checkouts and fail visibly"
        );
        assert!(
            !DEFAULT_VERUS_TEST_COMMAND.contains("sparse-checkout disable >/dev/null"),
            "default Verus command must not hide sparse checkout materialization failures"
        );
        assert!(
            !DEFAULT_VERUS_TEST_COMMAND.contains("--test-threads"),
            "vargo test rejects libtest --test-threads arguments for the pinned Verus checkout"
        );
        assert!(
            DEFAULT_VERUS_TEST_COMMAND
                .contains("cargo test -p cargo-verus --features integration-tests"),
            "default Verus command must include cargo-verus integration tests"
        );
    }

    #[cfg(unix)]
    #[test]
    fn rustup_cargo_detection_requires_default_shim_symlink() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-rustup-shim");
        let home = temp_dir.join("home");
        let bin = home.join(".cargo/bin");
        fs::create_dir_all(&bin).expect("cargo bin dir should be created");
        fs::write(bin.join("rustup"), "").expect("rustup placeholder should be written");
        std::os::unix::fs::symlink("rustup", bin.join("cargo"))
            .expect("cargo shim symlink should be created");

        assert!(is_symlink_to_rustup(&bin.join("cargo"), &home));

        fs::remove_file(bin.join("cargo")).expect("cargo shim should be removed");
        fs::write(bin.join("cargo"), "").expect("regular cargo should be written");
        assert!(!is_symlink_to_rustup(&bin.join("cargo"), &home));

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn cargo_command_provenance_gate_requires_verified_command() {
        let mut evidence = test_cargo_evidence();
        evidence.default_rustup_cargo = true;
        evidence.command = "/home/user/.cargo/bin/cargo".to_string();
        evidence.rustup_active_toolchain = Some("stable-aarch64-apple-darwin".to_string());
        evidence.cargo_proxy_sha256 = Some(
            "sha256:0000000000000000000000000000000000000000000000000000000000000000".to_string(),
        );
        evidence.toolchain_cargo_sha256 = Some(
            "sha256:1111111111111111111111111111111111111111111111111111111111111111".to_string(),
        );

        let passed = cargo_command_provenance_gate(true, &evidence);
        assert_eq!(passed.status, GateStatus::Passed);

        evidence
            .failures
            .push("default HOME cargo must be the rustup shim symlink".to_string());
        let failed = cargo_command_provenance_gate(true, &evidence);
        assert_eq!(failed.status, GateStatus::Failed);
        assert!(
            failed
                .detail
                .as_deref()
                .is_some_and(|detail| detail.contains("rustup shim")),
            "unexpected detail: {:?}",
            failed.detail
        );
    }

    #[test]
    fn cargo_environment_reasons_allow_verified_default_rustup_cargo_only() {
        let Some(home) = std::env::var_os("HOME").map(PathBuf::from) else {
            return;
        };
        let temp_dir = unique_temp_dir("trust-vc-evidence-cargo-env");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");

        let mut args = test_evidence_args(&temp_dir, &temp_dir, None);
        args.port_manifest_only = false;
        args.update_verus_tests_manifest = false;
        args.run_trust_vc = true;
        args.cargo_command = standard_home_cargo_path(&home).display().to_string();
        let mut evidence = test_cargo_evidence();
        evidence.default_rustup_cargo = true;
        evidence.failures.clear();
        let verified_reasons = evidence_environment_blocking_reasons(&args, &evidence);
        assert!(
            !verified_reasons
                .iter()
                .any(|reason| reason.contains("cannot trust a cargo binary under HOME")),
            "verified rustup cargo should not get the generic HOME cargo blocker: {verified_reasons:?}"
        );

        args.cargo_command = home.join("bin/cargo").display().to_string();
        evidence.default_rustup_cargo = false;
        let unverified_reasons = evidence_environment_blocking_reasons(&args, &evidence);
        assert!(
            unverified_reasons
                .iter()
                .any(|reason| reason.contains("cannot trust a cargo binary under HOME")),
            "arbitrary HOME cargo should be blocked: {unverified_reasons:?}"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn cargo_trust_vc_executable_provenance_accepts_repo_target_binary() {
        let crate_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("cargo-trust-vc should live under crates/")
            .to_path_buf();

        let gate = cargo_trust_vc_executable_provenance_gate(&crate_root);

        assert_eq!(
            gate.status,
            GateStatus::Passed,
            "test binary should be under the repo target dir: {:?}",
            gate.detail
        );
        assert!(
            gate.detail
                .as_deref()
                .is_some_and(|detail| detail.contains("executable_hash=sha256:")
                    && detail.contains("build_git_head=")),
            "executable hash and build git HEAD should be recorded: {:?}",
            gate.detail
        );
    }

    #[test]
    fn cargo_trust_vc_executable_provenance_rejects_stale_build_head() {
        let crate_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("cargo-trust-vc should live under crates/")
            .to_path_buf();

        let gate = cargo_trust_vc_executable_provenance_gate_with_build_head(
            &crate_root,
            "0000000000000000000000000000000000000000",
        );

        assert_eq!(gate.status, GateStatus::Failed);
        assert!(
            gate.detail
                .as_deref()
                .is_some_and(|detail| detail.contains("was built from")),
            "stale build git HEAD should be rejected: {:?}",
            gate.detail
        );
    }

    #[test]
    fn cargo_gate_env_prepends_cargo_proxy_dir_to_path() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-cargo-gate-path");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");
        let mut args = test_evidence_args(&temp_dir, &temp_dir, None);
        args.cargo_command = "/tmp/trust-vc-rustup/bin/cargo".to_string();

        let env = cargo_gate_env(&args);
        let path = env
            .iter()
            .find_map(|(key, value)| (key == "PATH").then_some(value.as_str()))
            .expect("cargo gate env should set PATH");

        // The cargo/rustc proxy dir must precede the sanitized system PATH so a
        // rustup `cargo` can execute its sibling `rustc`. (A detected rustup
        // shim dir may be prepended AHEAD of it; we assert the ordering
        // invariant rather than an absolute prefix so the check is robust to
        // toolchain detection, which is a process-global.)
        let proxy = path
            .find("/tmp/trust-vc-rustup/bin")
            .expect("cargo gate PATH must contain the cargo proxy dir");
        let sanitized = path
            .find(SANITIZED_PATH)
            .expect("cargo gate PATH should retain the sanitized system PATH");
        assert!(
            proxy < sanitized,
            "cargo/rustc proxy dir must come before the sanitized system PATH: {path}"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn cargo_gate_path_prepends_detected_rustup_shim_dir_ahead_of_non_rustup_cargo() {
        // Regression: when the resolved default cargo lives outside the rustup
        // shim dir (e.g. Homebrew's `/opt/homebrew/bin/cargo`), the detected
        // rustup shim dir must be prepended AHEAD of it so the trust shim
        // `rustc` (which accepts `-Ztrust-verify=off`) wins over the non-rustup
        // stable `rustc` sitting on the sanitized system PATH.
        let path = cargo_gate_path_with("/opt/homebrew/bin/cargo", Some("/home/user/.cargo/bin"));
        assert_eq!(
            path,
            format!("/home/user/.cargo/bin:/opt/homebrew/bin:{SANITIZED_PATH}")
        );

        // Without a detected shim dir the behaviour is exactly the pre-existing
        // one (cargo proxy dir prepended to the sanitized system PATH).
        assert_eq!(
            cargo_gate_path_with("/opt/homebrew/bin/cargo", None),
            format!("/opt/homebrew/bin:{SANITIZED_PATH}")
        );

        // When the cargo already lives in the shim dir, no duplicate leading
        // component is produced.
        assert_eq!(
            cargo_gate_path_with("/home/user/.cargo/bin/cargo", Some("/home/user/.cargo/bin")),
            format!("/home/user/.cargo/bin:{SANITIZED_PATH}")
        );
    }

    #[test]
    fn sanitized_command_env_injects_detected_active_toolchain() {
        // With a detected toolchain, the shim dir leads PATH and RUSTUP_TOOLCHAIN
        // is exported so the shims resolve to that toolchain in cwds without a
        // rust-toolchain.toml (corpus fixtures run in isolated directories).
        let toolchain = SanitizedToolchainEnv {
            rustup_bin_dir: Some("/home/user/.cargo/bin".to_string()),
            active_toolchain: Some("trust".to_string()),
        };
        let env = sanitized_command_env_with(Some(&toolchain));
        assert_eq!(
            env.get("PATH").map(String::as_str),
            Some(format!("/home/user/.cargo/bin:{SANITIZED_PATH}").as_str()),
            "detected rustup shim dir must lead the sanitized PATH"
        );
        assert_eq!(
            env.get("RUSTUP_TOOLCHAIN").map(String::as_str),
            Some("trust"),
            "the active toolchain must be exported so shims resolve to it"
        );
        assert_eq!(
            env.get("RUSTC").map(String::as_str),
            Some("/home/user/.cargo/bin/rustc"),
            "RUSTC must be pinned at the active toolchain's rustup shim so tooling \
             that resolves rustc from the $CARGO sibling (not PATH) still gets Trust"
        );

        // A detected toolchain name without a shim dir still exports
        // RUSTUP_TOOLCHAIN but cannot pin RUSTC (no shim path to point at).
        let named_only = SanitizedToolchainEnv {
            rustup_bin_dir: None,
            active_toolchain: Some("trust".to_string()),
        };
        let named_only_env = sanitized_command_env_with(Some(&named_only));
        assert_eq!(
            named_only_env.get("RUSTUP_TOOLCHAIN").map(String::as_str),
            Some("trust")
        );
        assert!(
            !named_only_env.contains_key("RUSTC"),
            "RUSTC needs the rustup shim dir; without it the pre-existing behaviour is kept"
        );

        // With no detected toolchain the env is exactly the pre-existing
        // hermetic one: bare sanitized PATH and no RUSTUP_TOOLCHAIN/RUSTC.
        let bare = sanitized_command_env_with(None);
        assert_eq!(bare.get("PATH").map(String::as_str), Some(SANITIZED_PATH));
        assert!(
            !bare.contains_key("RUSTUP_TOOLCHAIN"),
            "un-detected toolchain must not inject RUSTUP_TOOLCHAIN"
        );
        assert!(
            !bare.contains_key("RUSTC"),
            "un-detected toolchain must not inject RUSTC"
        );
        assert_eq!(
            sanitized_command_env_with(Some(&SanitizedToolchainEnv::default())),
            bare,
            "an empty detected toolchain must not perturb the hermetic env"
        );
    }

    #[test]
    fn active_toolchain_name_parses_rustup_show_active_toolchain() {
        assert_eq!(
            active_toolchain_name("trust (overridden by '/repo/rust-toolchain.toml')\n").as_deref(),
            Some("trust")
        );
        assert_eq!(
            active_toolchain_name("stable-aarch64-apple-darwin\n").as_deref(),
            Some("stable-aarch64-apple-darwin")
        );
        assert_eq!(active_toolchain_name("   \n\n").as_deref(), None);
        assert_eq!(active_toolchain_name("").as_deref(), None);
    }

    #[test]
    fn sanitized_command_env_disables_git_terminal_prompts() {
        let env = sanitized_command_env();
        assert_eq!(
            env.get("GIT_TERMINAL_PROMPT").map(String::as_str),
            Some("0"),
            "evidence commands must fail fast instead of prompting for git credentials"
        );
    }

    #[test]
    fn command_runner_closes_stdin() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-command-stdin");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");

        let command = run_command_with_env(
            &temp_dir,
            "sh",
            &[
                "-c",
                "if read line; then printf 'open:%s' \"$line\"; else printf closed; fi",
            ],
            &[],
        );

        assert_eq!(command.exit_code, Some(0));
        assert_eq!(
            command.stdout_tail, "closed",
            "evidence commands must not inherit an interactive stdin"
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn seed_yaml_parser_extracts_trust_vc_paths_without_extra_entries() {
        let yaml = r##"
upstream:
  repo: https://github.com/verus-lang/verus
  ref: abc
  test_roots:
    - source/rust_verify_test/tests
gate:
  missing_entry: fail
  failing_classifications:
    - unclassified
entries:
  - upstream_path: source/rust_verify_test/tests/foo.rs
    classification: ported
    owner_issue: "#123"
    reason: Ported for TrustVc.
    trust_vc_paths:
      - evals/verus/ported/foo.rs
  - upstream_path: source/rust_verify_test/tests/bar.rs
    classification: unchanged
    owner_issue: "#124"
    reason: Runs unchanged.
"##;
        let manifest = parse_seed_yaml_manifest(yaml).expect("seed yaml should parse");
        assert_eq!(manifest.entries.len(), 2);
        assert_eq!(
            manifest.entries[0].trust_vc_paths,
            vec!["evals/verus/ported/foo.rs"]
        );
        assert_eq!(
            manifest.entries[1].upstream_path,
            "source/rust_verify_test/tests/bar.rs"
        );
    }

    #[test]
    fn command_runner_respects_cwd_env_and_computes_status() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-command");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");
        fs::write(temp_dir.join("marker.txt"), "present").expect("marker should be written");

        let command = run_command_with_env(
            &temp_dir,
            "sh",
            &[
                "-c",
                "printf '%s:%s' \"$TRUST_VC_EVIDENCE_TEST\" \"$(cat marker.txt)\"",
            ],
            &[("TRUST_VC_EVIDENCE_TEST", "ok")],
        );

        assert_eq!(command.exit_code, Some(0));
        assert_eq!(gate_status_from_exit(command.exit_code), GateStatus::Passed);
        assert_eq!(command.stdout_tail, "ok:present");

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn verus_revision_gate_rejects_cli_manifest_mismatch() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-verus-rev");
        let args = test_evidence_args(&temp_dir, &temp_dir, Some("cli123"));
        let corpus = VerusCorpusReport {
            manifest_path: temp_dir.join("verus-tests.json"),
            manifest_schema_version: 1,
            upstream_repo: Some(VERUS_REPO_URL.to_string()),
            upstream_ref: Some("manifest456".to_string()),
            upstream_test_roots: vec![VERUS_TEST_ROOT.to_string()],
            upstream_test_count: 1,
            entry_count: 1,
            classification_counts: BTreeMap::new(),
            replacement_summary: VerusReplacementSummary::default(),
            duplicate_entries: Vec::new(),
            invalid_entries: Vec::new(),
            missing_entries: Vec::new(),
            extra_entries: Vec::new(),
            unsupported_entries: Vec::new(),
            failing_entries: Vec::new(),
            port_path_failures: Vec::new(),
            upstream_case_failures: Vec::new(),
            ignored_upstream_cases: Vec::new(),
            upstream_case_extraction_gaps: Vec::new(),
            porting_next_action: None,
            accepted_executable_ports: Vec::new(),
            unsupported_gap_evidence: Vec::new(),
            accepted_trust_vc_source_hashes: Vec::new(),
            run_candidates: Vec::new(),
        };

        let gate = verus_revision_gate(&args, Some("cli123"), Some(&corpus));
        assert_eq!(gate.status, GateStatus::Failed);
        assert!(
            gate.detail
                .as_deref()
                .is_some_and(|detail| detail.contains("does not match manifest")),
            "unexpected detail: {:?}",
            gate.detail
        );

        fs::remove_dir_all(temp_dir).ok();
    }

    #[test]
    fn verus_worktree_gate_fails_closed_for_missing_checkout() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-verus-worktree-missing");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");

        let no_path_gate = verus_worktree_gate(None, None);
        assert!(no_path_gate.required);
        assert_eq!(no_path_gate.status, GateStatus::Failed);
        assert!(
            no_path_gate
                .detail
                .as_deref()
                .is_some_and(|detail| detail.contains("--verus-path is required")),
            "unexpected detail: {:?}",
            no_path_gate.detail
        );

        let missing_path = temp_dir.join("missing-verus");
        let missing_path_gate = verus_worktree_gate(Some(&missing_path), git_dirty(&missing_path));
        assert!(missing_path_gate.required);
        assert_eq!(missing_path_gate.status, GateStatus::Failed);
        assert!(
            missing_path_gate
                .detail
                .as_deref()
                .is_some_and(|detail| detail.contains("could not verify clean Verus git worktree")),
            "unexpected detail: {:?}",
            missing_path_gate.detail
        );

        let plain_dir = temp_dir.join("plain-verus");
        fs::create_dir_all(&plain_dir).expect("plain dir should be created");
        let plain_dir_gate = verus_worktree_gate(Some(&plain_dir), git_dirty(&plain_dir));
        assert!(plain_dir_gate.required);
        assert_eq!(plain_dir_gate.status, GateStatus::Failed);
        assert!(
            plain_dir_gate
                .detail
                .as_deref()
                .is_some_and(|detail| detail.contains("could not verify clean Verus git worktree")),
            "unexpected detail: {:?}",
            plain_dir_gate.detail
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn verus_worktree_gate_rejects_dirty_git_checkout() {
        let temp_dir = unique_temp_dir("trust-vc-evidence-verus-worktree-dirty");
        fs::create_dir_all(&temp_dir).expect("temp dir should be created");
        let init = run_command(&temp_dir, DEFAULT_GIT_COMMAND, &["init"]);
        assert_eq!(
            init.exit_code,
            Some(0),
            "git init failed: {}",
            init.stderr_tail
        );

        let clean_gate = verus_worktree_gate(Some(&temp_dir), git_dirty(&temp_dir));
        assert_eq!(clean_gate.status, GateStatus::Passed);

        let hide_untracked = run_command(
            &temp_dir,
            DEFAULT_GIT_COMMAND,
            &["config", "status.showUntrackedFiles", "no"],
        );
        assert_eq!(
            hide_untracked.exit_code,
            Some(0),
            "git config failed: {}",
            hide_untracked.stderr_tail
        );
        fs::write(temp_dir.join("untracked.rs"), "").expect("dirty file should be written");
        let dirty_gate = verus_worktree_gate(Some(&temp_dir), git_dirty(&temp_dir));
        assert!(dirty_gate.required);
        assert_eq!(dirty_gate.status, GateStatus::Failed);
        assert!(
            dirty_gate
                .detail
                .as_deref()
                .is_some_and(|detail| detail.contains("dirty=true")),
            "unexpected detail: {:?}",
            dirty_gate.detail
        );

        fs::remove_dir_all(temp_dir).expect("temp dir should be removed");
    }

    #[test]
    fn report_serializes_and_renders_markdown() {
        let report = EvidenceReport {
            schema_version: 1,
            generated_unix_seconds: 123,
            strict: true,
            replacement_verdict: ReplacementVerdict::Proven,
            repository: RepositoryEvidence {
                trust_vc_head: Some("abc1234".to_string()),
                dirty: false,
                crate_root: PathBuf::from("/repo"),
            },
            ay: AYEvidence {
                pinned_rev: Some("def5678".to_string()),
                pinned_revs: test_ay_pins("def5678"),
                pinned_sources: test_ay_sources(),
                lock_sources: test_ay_lock_sources("def5678"),
                lock_source_entries: test_ay_lock_source_entries("def5678"),
                latest_private_main: Some("def5678".to_string()),
                is_latest_private_main: Some(true),
                local_patch_detected: false,
                ay_identity_rev: None,
                ay_repo_root: None,
                ay_origin_url: None,
                ay_worktree_clean: None,
                ay_published: None,
            },
            cargo: test_cargo_evidence(),
            verus: VerusEvidence {
                path: Some(PathBuf::from("/verus")),
                requested_rev: Some("main".to_string()),
                head: Some("fedcba9".to_string()),
            },
            gates: vec![GateResult {
                name: "unit".to_string(),
                required: true,
                status: GateStatus::Passed,
                detail: Some("exit code 0".to_string()),
                command: None,
            }],
            corpus: None,
            trust_vc_corpus: None,
            blocking_reasons: Vec::new(),
        };

        let json = serde_json::to_string_pretty(&report).expect("report should serialize");
        let parsed: serde_json::Value =
            serde_json::from_str(&json).expect("report JSON should parse");
        assert_eq!(parsed["replacement_verdict"], "proven");

        let markdown = report.render_markdown();
        assert!(markdown.contains("# TrustVc Verus-Replacement Evidence"));
        assert!(markdown.contains("unit"));
        assert!(!report.has_blocking_failures());
    }

    fn unique_temp_dir(name: &str) -> PathBuf {
        let mut path = std::env::temp_dir();
        path.push(format!(
            "{name}-{}-{}",
            std::process::id(),
            now_unix_seconds()
        ));
        path
    }

    fn init_git_repo(path: &Path) {
        fs::create_dir_all(path).expect("git repo dir should be created");
        let result = run_command(path, DEFAULT_GIT_COMMAND, &["init"]);
        assert_eq!(
            result.exit_code,
            Some(0),
            "git init should succeed: {}",
            result.stderr_tail
        );
    }

    fn git_commit_all(path: &Path, message: &str) -> String {
        let add = run_command(path, DEFAULT_GIT_COMMAND, &["add", "."]);
        assert_eq!(
            add.exit_code,
            Some(0),
            "git add should succeed: {}",
            add.stderr_tail
        );
        let commit = run_command(
            path,
            DEFAULT_GIT_COMMAND,
            &[
                "-c",
                "user.name=TrustVc Test",
                "-c",
                "user.email=trust_vc@example.invalid",
                "commit",
                "-m",
                message,
            ],
        );
        assert_eq!(
            commit.exit_code,
            Some(0),
            "git commit should succeed: {}",
            commit.stderr_tail
        );
        let rev = run_command(path, DEFAULT_GIT_COMMAND, &["rev-parse", "HEAD"]);
        assert_eq!(
            rev.exit_code,
            Some(0),
            "git rev-parse should succeed: {}",
            rev.stderr_tail
        );
        rev.stdout_tail.trim().to_string()
    }

    fn git_tag(path: &Path, tag: &str) {
        let result = run_command(path, DEFAULT_GIT_COMMAND, &["tag", "-f", tag]);
        assert_eq!(
            result.exit_code,
            Some(0),
            "git tag should succeed: {}",
            result.stderr_tail
        );
    }

    fn minimal_valid_json_manifest() -> String {
        r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": [
    {
      "upstream_path": "source/rust_verify_test/tests/foo.rs",
      "classification": "ported",
      "owner_issue": "#123",
      "reason": "Ported for TrustVc.",
      "trust_vc_paths": ["evals/verus/ported/foo.rs"],
      "expected_cases": [
        {
          "case_id": "identity",
          "expected_verdict": "verified",
          "min_obligations": 1
        }
      ]
    }
  ]
}"##
        .to_string()
    }

    fn is_sha256_digest(value: &str) -> bool {
        value
            .strip_prefix("sha256:")
            .is_some_and(|hex| hex.len() == 64 && hex.chars().all(|ch| ch.is_ascii_hexdigit()))
    }

    fn test_evidence_report_with_corpus(corpus: VerusCorpusReport) -> EvidenceReport {
        EvidenceReport {
            schema_version: 1,
            generated_unix_seconds: 123,
            strict: false,
            replacement_verdict: ReplacementVerdict::NotProven,
            repository: RepositoryEvidence {
                trust_vc_head: Some("abc1234".to_string()),
                dirty: true,
                crate_root: PathBuf::from("/repo"),
            },
            ay: AYEvidence {
                pinned_rev: Some("def5678".to_string()),
                pinned_revs: test_ay_pins("def5678"),
                pinned_sources: test_ay_sources(),
                lock_sources: test_ay_lock_sources("def5678"),
                lock_source_entries: test_ay_lock_source_entries("def5678"),
                latest_private_main: Some("def5678".to_string()),
                is_latest_private_main: Some(true),
                local_patch_detected: false,
                ay_identity_rev: None,
                ay_repo_root: None,
                ay_origin_url: None,
                ay_worktree_clean: None,
                ay_published: None,
            },
            cargo: test_cargo_evidence(),
            verus: VerusEvidence {
                path: Some(PathBuf::from("/verus")),
                requested_rev: Some("abc123".to_string()),
                head: Some("abc123".to_string()),
            },
            gates: Vec::new(),
            corpus: Some(corpus),
            trust_vc_corpus: None,
            blocking_reasons: vec!["test report is not replacement evidence".to_string()],
        }
    }

    fn test_evidence_args(
        crate_root: &Path,
        verus_root: &Path,
        verus_rev: Option<&str>,
    ) -> EvidenceArgs {
        let crate_root = crate_root
            .canonicalize()
            .unwrap_or_else(|_| crate_root.to_path_buf());
        EvidenceArgs {
            crate_root: crate_root.clone(),
            output_dir: crate_root.join(".trust_vc/evidence"),
            port_output_dir: crate_root.join("evals/verus/ported"),
            verus_path: Some(verus_root.to_path_buf()),
            verus_rev: verus_rev.map(str::to_string),
            manifest_path: Some(crate_root.join("evals/verus/verus-tests.json")),
            canonical_manifest_path: crate_root.join("evals/verus/verus-tests.json"),
            strict: false,
            json: false,
            markdown: false,
            run_trust_vc: false,
            cargo_command: "cargo".to_string(),
            cargo_command_overridden: false,
            run_trust_vc_corpus: false,
            trust_vc_corpus_command: None,
            run_verus: false,
            port_manifest_only: true,
            update_verus_tests_manifest: true,
            refresh_trust_vc_corpus_evidence: false,
            corpus_triage_report: false,
            scaffold_verus_port_stubs: false,
            verus_command: None,
        }
    }

    fn test_ay_pins(rev: &str) -> BTreeMap<String, Option<String>> {
        REQUIRED_AY_CRATES
            .iter()
            .map(|crate_name| ((*crate_name).to_string(), Some(rev.to_string())))
            .collect()
    }

    fn test_git_ay_provenance(rev: &str) -> AYManifestProvenance {
        AYManifestProvenance {
            pinned_rev: Some(rev.to_string()),
            pinned_revs: test_ay_pins(rev),
            pinned_sources: test_ay_sources(),
            source_model: AYSourceModel::GitRev,
            sibling_identity: None,
        }
    }

    fn test_sibling_ay_provenance(rev: &str) -> AYManifestProvenance {
        AYManifestProvenance {
            pinned_rev: Some(rev.to_string()),
            pinned_revs: test_ay_pins(rev),
            pinned_sources: REQUIRED_AY_CRATES
                .iter()
                .map(|crate_name| {
                    (
                        (*crate_name).to_string(),
                        Some(format!(
                            "path:../ay/crates/{crate_name} (local git repo: /tmp/ay)"
                        )),
                    )
                })
                .collect(),
            source_model: AYSourceModel::VerifiedSiblingPath,
            sibling_identity: Some(AYSiblingIdentity {
                head: rev.to_string(),
                repo_root: PathBuf::from("/tmp/ay"),
                origin_url: AY_REPO_URL.to_string(),
                worktree_clean: true,
                published: AYPublished::Reachable,
            }),
        }
    }

    fn write_ay_path_manifest(crate_root: &Path) {
        fs::write(
            crate_root.join("Cargo.toml"),
            r#"
ay-core = { path = "../ay/crates/ay-core" }
ay-dpll = { path = "../ay/crates/ay-dpll" }
ay-frontend = { path = "../ay/crates/ay-frontend" }
ay-sys = { path = "../ay/crates/ay-sys" }
"#,
        )
        .expect("Cargo.toml should be written");
    }

    fn write_ay_git_manifest(crate_root: &Path, rev: &str) {
        fs::write(
            crate_root.join("Cargo.toml"),
            format!(
                r#"
ay-core = {{ git = "{AY_REPO_URL}", rev = "{rev}" }}
ay-dpll = {{ git = "{AY_REPO_URL}", rev = "{rev}" }}
ay-frontend = {{ git = "{AY_REPO_URL}", rev = "{rev}" }}
ay-sys = {{ git = "{AY_REPO_URL}", rev = "{rev}" }}
"#
            ),
        )
        .expect("Cargo.toml should be written");
    }

    fn write_ay_patch_config(crate_root: &Path, ay_relative_root: &str) {
        let cargo_dir = crate_root.join(".cargo");
        fs::create_dir_all(&cargo_dir).expect(".cargo dir should be created");
        fs::write(
            cargo_dir.join("config.toml"),
            format!(
                r#"
[patch."{AY_REPO_URL}"]
ay-core = {{ path = "{ay_relative_root}/crates/ay-core" }}
ay-dpll = {{ path = "{ay_relative_root}/crates/ay-dpll" }}
ay-frontend = {{ path = "{ay_relative_root}/crates/ay-frontend" }}
ay-sys = {{ path = "{ay_relative_root}/crates/ay-sys" }}
"#
            ),
        )
        .expect(".cargo/config.toml should be written");
    }

    fn create_clean_origin_main_ay_sibling(parent: &Path) -> (PathBuf, String) {
        create_clean_origin_main_named_ay_sibling(parent, "ay")
    }

    fn create_clean_origin_main_named_ay_sibling(
        parent: &Path,
        directory_name: &str,
    ) -> (PathBuf, String) {
        let ay_root = parent.join(directory_name);
        init_git_repo(&ay_root);
        for crate_name in REQUIRED_AY_CRATES {
            let crate_dir = ay_root.join("crates").join(crate_name);
            fs::create_dir_all(&crate_dir).expect("ay crate dir should be created");
            fs::write(crate_dir.join("README.md"), format!("# {crate_name}\n"))
                .expect("ay crate file should be written");
        }
        let remote = run_command(
            &ay_root,
            DEFAULT_GIT_COMMAND,
            &[
                "remote",
                "add",
                "origin",
                "git@github.com:alabsystems/ay.git",
            ],
        );
        assert_eq!(
            remote.exit_code,
            Some(0),
            "git remote add should succeed: {}",
            remote.stderr_tail
        );
        let head = git_commit_all(&ay_root, "ay initial");
        let origin_main = run_command(
            &ay_root,
            DEFAULT_GIT_COMMAND,
            &["update-ref", "refs/remotes/origin/main", &head],
        );
        assert_eq!(
            origin_main.exit_code,
            Some(0),
            "git update-ref should succeed: {}",
            origin_main.stderr_tail
        );
        (ay_root, head)
    }

    fn test_cargo_evidence() -> CargoEvidence {
        CargoEvidence {
            command: "/usr/bin/cargo".to_string(),
            command_overridden: false,
            canonical_command: Some(PathBuf::from("/usr/bin/cargo")),
            default_rustup_cargo: false,
            rustup_command: None,
            rustup_active_toolchain: None,
            rustup_which_cargo: None,
            cargo_proxy_sha256: None,
            rustup_sha256: None,
            toolchain_cargo_sha256: None,
            failures: Vec::new(),
            rustup_show_active_toolchain: None,
            rustup_which_cargo_command: None,
        }
    }

    fn test_ay_sources() -> BTreeMap<String, Option<String>> {
        REQUIRED_AY_CRATES
            .iter()
            .map(|crate_name| ((*crate_name).to_string(), Some(AY_REPO_URL.to_string())))
            .collect()
    }

    fn test_ay_lock_sources(rev: &str) -> BTreeMap<String, Option<String>> {
        ay_lock_sources_by_package(&test_ay_lock_source_entries(rev))
    }

    fn test_ay_lock_source_entries(rev: &str) -> Vec<AYLockSourceEntry> {
        REQUIRED_AY_CRATES
            .iter()
            .map(|crate_name| AYLockSourceEntry {
                package_name: (*crate_name).to_string(),
                source: Some(format!("git+{AY_REPO_URL}?rev={rev}#{rev}")),
            })
            .collect()
    }
}
