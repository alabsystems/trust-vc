// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

mod collect;
mod format;

#[cfg(test)]
mod tests;

use collect::ApiSurfaceCollector;
use rustdoc_types::Id;
use std::collections::BTreeSet;
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use thiserror::Error;

pub const API_SURFACE_FIXTURE_DIR_REL_PATH: &str = "fixtures/api_surface";

/// The Trust toolchain's Cargo frontend: `$CARGO` (targo exports itself to test
/// processes and to `targo run`), else `targo` from PATH. There is no stock
/// fallback: the generator always names the unverified lane, which a cargo that
/// is not targo rejects.
fn cargo_program() -> OsString {
    std::env::var_os("CARGO")
        .filter(|value| !value.is_empty())
        .unwrap_or_else(|| OsString::from("targo"))
}

/// Emit rustdoc JSON for the lib target of `manifest_path` with trustdoc.
///
/// This spawns `targo --unverified rustdoc --lib … -- -Z unstable-options
/// --output-format json` directly. The `rustdoc-json-stable` builder it
/// replaces hard-coded `Command::new("cargo")` (or `rustup run <toolchain>
/// cargo`) and needed a process-global `RUSTC_BOOTSTRAP=1` to unlock the JSON
/// backend on a stable toolchain; the Trust toolchain is a dev channel, so the
/// unstable flag needs no bootstrap escape hatch, and the build carries no proof
/// claim, hence the unverified lane.
fn build_rustdoc_json(
    package_name: &str,
    manifest_path: &Path,
    target_dir: &Path,
) -> Result<PathBuf, ApiSurfaceError> {
    let json_path = target_dir
        .join("doc")
        .join(format!("{}.json", package_name.replace('-', "_")));
    // A JSON file left by an earlier run must not stand in for this one.
    if let Err(source) = fs::remove_file(&json_path) {
        if source.kind() != std::io::ErrorKind::NotFound {
            return Err(ApiSurfaceError::WriteFile {
                path: json_path,
                source,
            });
        }
    }
    let mut command = Command::new(cargo_program());
    command
        .arg("--unverified")
        .arg("rustdoc")
        .arg("--lib")
        .arg("--color")
        .arg("never")
        .arg("--manifest-path")
        .arg(manifest_path)
        .arg("--target-dir")
        .arg(target_dir)
        .args(["--", "-Z", "unstable-options", "--output-format", "json"]);
    let rendered = format!("{command:?}");
    let output = command
        .output()
        .map_err(|source| ApiSurfaceError::RustdocLaunch {
            command: rendered.clone(),
            source,
        })?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let tail: Vec<&str> = stderr.lines().rev().take(20).collect();
        return Err(ApiSurfaceError::RustdocFailed {
            command: rendered,
            status: output.status.to_string(),
            stderr_tail: tail.into_iter().rev().collect::<Vec<_>>().join("\n"),
        });
    }
    if !json_path.is_file() {
        return Err(ApiSurfaceError::MissingRustdocJson {
            command: rendered,
            path: json_path,
        });
    }
    Ok(json_path)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProtectedCrate {
    package_name: &'static str,
    manifest_rel_path: &'static str,
    fixture_file_name: &'static str,
}

impl ProtectedCrate {
    #[must_use]
    pub const fn new(
        package_name: &'static str,
        manifest_rel_path: &'static str,
        fixture_file_name: &'static str,
    ) -> Self {
        Self {
            package_name,
            manifest_rel_path,
            fixture_file_name,
        }
    }

    #[must_use]
    pub const fn package_name(self) -> &'static str {
        self.package_name
    }

    #[must_use]
    pub fn manifest_path(self) -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(self.manifest_rel_path)
    }

    #[must_use]
    pub fn fixture_path(self) -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join(API_SURFACE_FIXTURE_DIR_REL_PATH)
            .join(self.fixture_file_name)
    }

    #[must_use]
    pub fn target_dir(self) -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../target/api_surface")
            .join(self.package_name)
    }
}

pub const PROTECTED_CRATES: [ProtectedCrate; 6] = [
    ProtectedCrate::new("trust-vc", "../trust-vc/Cargo.toml", "trust-vc.txt"),
    ProtectedCrate::new(
        "trust-vc-core",
        "../trust-vc-core/Cargo.toml",
        "trust-vc-core.txt",
    ),
    ProtectedCrate::new(
        "trust-vc-types",
        "../trust-vc-types/Cargo.toml",
        "trust-vc-types.txt",
    ),
    ProtectedCrate::new(
        "trust-vc-merge-contract",
        "Cargo.toml",
        "trust-vc-merge-contract.txt",
    ),
    ProtectedCrate::new(
        "trust-vc-merge-runner",
        "../trust-vc-merge-runner/Cargo.toml",
        "trust-vc-merge-runner.txt",
    ),
    ProtectedCrate::new(
        "trust-vc-trust-engine",
        "../trust-vc-trust-engine/Cargo.toml",
        "trust-vc-trust-engine.txt",
    ),
];

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ApiSurfaceSnapshot {
    package_name: String,
    crate_root: String,
    lines: Vec<String>,
}

impl ApiSurfaceSnapshot {
    #[must_use]
    pub fn package_name(&self) -> &str {
        &self.package_name
    }

    #[must_use]
    pub fn crate_root(&self) -> &str {
        &self.crate_root
    }

    #[must_use]
    pub fn lines(&self) -> &[String] {
        &self.lines
    }

    #[must_use]
    pub fn to_text(&self) -> String {
        if self.lines.is_empty() {
            String::new()
        } else {
            format!("{}\n", self.lines.join("\n"))
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SnapshotDiff {
    removed: Vec<String>,
    added: Vec<String>,
}

impl SnapshotDiff {
    #[must_use]
    pub fn removed(&self) -> &[String] {
        &self.removed
    }

    #[must_use]
    pub fn added(&self) -> &[String] {
        &self.added
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.removed.is_empty() && self.added.is_empty()
    }

    #[must_use]
    pub fn render(&self, package_name: &str) -> String {
        let mut sections = Vec::new();
        if !self.removed.is_empty() {
            sections.push(format!(
                "removed public API lines for {package_name}:\n{}",
                self.removed
                    .iter()
                    .map(|line| format!("- {line}"))
                    .collect::<Vec<_>>()
                    .join("\n")
            ));
        }
        if !self.added.is_empty() {
            sections.push(format!(
                "added public API lines for {package_name}:\n{}",
                self.added
                    .iter()
                    .map(|line| format!("+ {line}"))
                    .collect::<Vec<_>>()
                    .join("\n")
            ));
        }
        sections.join("\n")
    }
}

#[derive(Debug, Error)]
#[non_exhaustive]
pub enum ApiSurfaceError {
    #[error("failed to launch `{command}`: {source}")]
    RustdocLaunch {
        command: String,
        #[source]
        source: std::io::Error,
    },
    #[error("`{command}` failed ({status}):\n{stderr_tail}")]
    RustdocFailed {
        command: String,
        status: String,
        stderr_tail: String,
    },
    #[error("`{command}` succeeded but wrote no rustdoc JSON at {path}")]
    MissingRustdocJson { command: String, path: PathBuf },
    #[error("failed to deserialize rustdoc JSON {path}: {source}")]
    Deserialize {
        path: PathBuf,
        #[source]
        source: serde_json::Error,
    },
    #[error("missing rustdoc item {id:?}")]
    MissingItem { id: Id },
    #[error("expected {context} for rustdoc item {id:?}")]
    UnexpectedItemKind { context: &'static str, id: Id },
    #[error("missing name for {context} item {id:?}")]
    MissingItemName { context: &'static str, id: Id },
    #[error("failed to create API surface directory {path}: {source}")]
    CreateDir {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("failed to read API surface fixture {path}: {source}")]
    ReadFile {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("failed to write API surface fixture {path}: {source}")]
    WriteFile {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
}

pub fn generate_api_surface_snapshot(
    protected: ProtectedCrate,
) -> Result<ApiSurfaceSnapshot, ApiSurfaceError> {
    generate_api_surface_snapshot_from_manifest(
        protected.package_name(),
        &protected.manifest_path(),
        &protected.target_dir(),
    )
}

pub fn read_checked_in_api_surface_snapshot(
    protected: ProtectedCrate,
) -> Result<ApiSurfaceSnapshot, ApiSurfaceError> {
    let path = protected.fixture_path();
    let text = fs::read_to_string(&path).map_err(|source| ApiSurfaceError::ReadFile {
        path: path.clone(),
        source,
    })?;
    let lines = text
        .lines()
        .filter(|line| !line.is_empty())
        .map(str::to_owned)
        .collect();
    Ok(ApiSurfaceSnapshot {
        package_name: protected.package_name().to_owned(),
        crate_root: protected.package_name().replace('-', "_"),
        lines,
    })
}

pub fn checked_in_snapshot_diff(
    protected: ProtectedCrate,
) -> Result<SnapshotDiff, ApiSurfaceError> {
    let checked_in = read_checked_in_api_surface_snapshot(protected)?;
    let generated = generate_api_surface_snapshot(protected)?;
    Ok(diff_snapshots(&checked_in.lines, &generated.lines))
}

pub fn write_default_api_surface_fixtures() -> Result<Vec<PathBuf>, ApiSurfaceError> {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(API_SURFACE_FIXTURE_DIR_REL_PATH);
    fs::create_dir_all(&dir).map_err(|source| ApiSurfaceError::CreateDir {
        path: dir.clone(),
        source,
    })?;

    let mut written = Vec::new();
    for protected in PROTECTED_CRATES {
        let snapshot = generate_api_surface_snapshot(protected)?;
        let path = protected.fixture_path();
        fs::write(&path, snapshot.to_text()).map_err(|source| ApiSurfaceError::WriteFile {
            path: path.clone(),
            source,
        })?;
        written.push(path);
    }
    Ok(written)
}

#[must_use]
pub fn diff_snapshots(expected: &[String], actual: &[String]) -> SnapshotDiff {
    let expected = expected.iter().cloned().collect::<BTreeSet<_>>();
    let actual = actual.iter().cloned().collect::<BTreeSet<_>>();

    SnapshotDiff {
        removed: expected.difference(&actual).cloned().collect(),
        added: actual.difference(&expected).cloned().collect(),
    }
}

fn generate_api_surface_snapshot_from_manifest(
    package_name: &str,
    manifest_path: &Path,
    target_dir: &Path,
) -> Result<ApiSurfaceSnapshot, ApiSurfaceError> {
    let json_path = build_rustdoc_json(package_name, manifest_path, target_dir)?;
    let payload = fs::read_to_string(&json_path).map_err(|source| ApiSurfaceError::ReadFile {
        path: json_path.clone(),
        source,
    })?;
    let krate = serde_json::from_str::<rustdoc_types::Crate>(&payload).map_err(|source| {
        ApiSurfaceError::Deserialize {
            path: json_path,
            source,
        }
    })?;
    let root_item = krate
        .index
        .get(&krate.root)
        .ok_or(ApiSurfaceError::MissingItem { id: krate.root })?;
    let crate_root = root_item
        .name
        .clone()
        .unwrap_or_else(|| package_name.replace('-', "_"));
    let lines = ApiSurfaceCollector::new(&krate).collect(&crate_root)?;
    Ok(ApiSurfaceSnapshot {
        package_name: package_name.to_owned(),
        crate_root,
        lines,
    })
}
