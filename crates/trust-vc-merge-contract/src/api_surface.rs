// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

mod collect;
mod format;

#[cfg(test)]
mod tests;

use collect::ApiSurfaceCollector;
use rustdoc_json_stable::{BuildError, Builder, Color};
use rustdoc_types::Id;
use std::collections::BTreeSet;
use std::ffi::{OsStr, OsString};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use thiserror::Error;

pub const API_SURFACE_FIXTURE_DIR_REL_PATH: &str = "fixtures/api_surface";

// `rustdoc-json-stable` does not expose per-command environment overrides when
// it uses the active toolchain, so generating stable rustdoc JSON currently
// requires a short, process-global RUSTC_BOOTSTRAP override. Keep the mutation
// and restoration in one serialized, panic-safe scope. This also prevents two
// concurrent snapshot requests from restoring each other's values.
static RUSTC_BOOTSTRAP_ENV_LOCK: Mutex<()> = Mutex::new(());

struct RustcBootstrapEnvRestore(Option<OsString>);

impl RustcBootstrapEnvRestore {
    fn install() -> Self {
        let previous = std::env::var_os("RUSTC_BOOTSTRAP");
        write_rustc_bootstrap(Some(OsStr::new("1")));
        Self(previous)
    }
}

impl Drop for RustcBootstrapEnvRestore {
    fn drop(&mut self) {
        write_rustc_bootstrap(self.0.take().as_deref());
    }
}

/// THE single raw environment write for this crate: set (`Some`) or remove
/// (`None`) `RUSTC_BOOTSTRAP`. Every mutation routes through here, serialized
/// by the `RUSTC_BOOTSTRAP_ENV_LOCK` that `with_rustc_bootstrap` holds, and
/// restored by `RustcBootstrapEnvRestore`'s `Drop`. This crate is a dependency
/// leaf below `trust-vc-core` and cannot import its env choke point, so it
/// keeps this one equivalent blessed primitive — the ONLY `env_mutation` site
/// in the crate.
///
/// `env_mutation` is the Trust toolchain's deny-by-default env wall; stock
/// rustc does not know the lint name, hence `unknown_lints`.
#[allow(unknown_lints, env_mutation)]
fn write_rustc_bootstrap(value: Option<&OsStr>) {
    match value {
        Some(value) => std::env::set_var("RUSTC_BOOTSTRAP", value),
        None => std::env::remove_var("RUSTC_BOOTSTRAP"),
    }
}

fn with_rustc_bootstrap<T>(operation: impl FnOnce() -> T) -> T {
    let _lock = RUSTC_BOOTSTRAP_ENV_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _restore = RustcBootstrapEnvRestore::install();
    operation()
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
    #[error(transparent)]
    Build(#[from] BuildError),
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
    let json_path = with_rustc_bootstrap(|| {
        Builder::stable()
            .manifest_path(manifest_path)
            .target_dir(target_dir)
            .color(Color::Never)
            .build()
    })?;
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
