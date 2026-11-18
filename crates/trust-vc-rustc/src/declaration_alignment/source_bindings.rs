//! Byte bindings for staging-owned source and metadata inputs.
//!
//! These values authenticate bytes against the caller's pinned input cohort.
//! They do not prove a compiler invocation ran, authenticate a JSON producer,
//! or grant declaration, mode, header, body, ownership or proof authority.
//! The native staging owner must supply those separate facts before import.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Component, Path, PathBuf};

use serde_json::Value;
use sha2::{Digest as _, Sha256};

use super::observation::ObservedAnchor;
use super::{AuthoredSpan, Digest};

/// One file explicitly selected by the staging owner, including its expected
/// hash. Checking this pin says nothing about who produced the file.
#[derive(Clone, Debug)]
pub struct PinnedFile {
    pub path: PathBuf,
    pub sha256: Digest,
}

impl PinnedFile {
    /// Read the actual file and reject changed bytes or a non-regular input.
    pub fn read(&self) -> Result<Vec<u8>, String> {
        if !self.path.is_absolute() {
            return Err("a pinned input path must be absolute".into());
        }
        let metadata = fs::metadata(&self.path).map_err(|e| e.to_string())?;
        if !metadata.is_file() {
            return Err("a pinned input is not a regular file".into());
        }
        let bytes = fs::read(&self.path).map_err(|e| e.to_string())?;
        if digest(&bytes) != self.sha256 {
            return Err("pinned input bytes changed".into());
        }
        Ok(bytes)
    }

    fn json(&self) -> Result<Value, String> {
        serde_json::from_slice(&self.read()?).map_err(|e| e.to_string())
    }
}

/// An explicitly reviewed source compatibility view. The recipe and patch
/// themselves are pinned; an unmentioned file can never take replacement
/// bytes. The source identity remains the original manifest plus this patch.
pub struct CompatibilityInput {
    pub recipe: PinnedFile,
    pub patch: PinnedFile,
}

struct SourceFile {
    bytes: Vec<u8>,
    sha256: Digest,
}

/// An owned snapshot of the entire approved source graph. Files are read once
/// into owned bytes; span binding cannot observe later, unpinned edits. Call
/// `revalidate` at the staging boundary to check the on-disk graph again.
pub struct Sources {
    requested_root: PathBuf,
    canonical_root: PathBuf,
    manifest: PinnedFile,
    compatibility: Option<CompatibilityInput>,
    files: BTreeMap<String, SourceFile>,
}

/// Identities of the inputs checked by `Sources`, without claiming who
/// selected them or which compiler invocation consumed them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceIdentity {
    pub manifest_sha256: Digest,
    pub compatibility: SourceCompatibility,
}

/// The checked source graph is either the original manifest or the explicit
/// reviewed replacement. Unmodified is a known state, not missing evidence.
/// An applied patch always retains both its recipe and its bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceCompatibility {
    Unmodified,
    Applied {
        recipe_sha256: Digest,
        patch_sha256: Digest,
    },
}

impl SourceCompatibility {
    /// Diagnostic projection; an unmodified graph has no compatibility file.
    #[must_use]
    pub const fn recipe_sha256(self) -> Option<Digest> {
        match self {
            Self::Unmodified => None,
            Self::Applied { recipe_sha256, .. } => Some(recipe_sha256),
        }
    }

    /// Diagnostic projection; an unmodified graph has no patch file.
    #[must_use]
    pub const fn patch_sha256(self) -> Option<Digest> {
        match self {
            Self::Unmodified => None,
            Self::Applied { patch_sha256, .. } => Some(patch_sha256),
        }
    }
}

impl Sources {
    /// Bind every manifest file, reject extra/missing files and symlinks, and
    /// check the exact original/patched hashes for an explicit compatibility
    /// recipe. Symlink-bearing manifests need an explicit resolution policy;
    /// they are refused here, never silently omitted from the graph.
    pub fn load(
        root: &Path,
        manifest: PinnedFile,
        compatibility: Option<CompatibilityInput>,
    ) -> Result<Self, String> {
        if !root.is_absolute() {
            return Err("the approved source root must be absolute".into());
        }
        let canonical_root = root.canonicalize().map_err(|e| e.to_string())?;
        let value = manifest.json()?;
        let hashes = value["files_sha256"]
            .as_object()
            .ok_or("missing source file manifest")?;
        if hashes.is_empty()
            || !value["symlink_targets"]
                .as_object()
                .is_some_and(|s| s.is_empty())
        {
            return Err("empty or symlink-bearing source manifests are not represented".into());
        }
        let mut expected = BTreeMap::new();
        for (name, hash) in hashes {
            relative(name)?;
            expected.insert(name.clone(), parse_digest(hash)?);
        }
        if let Some(input) = &compatibility {
            let recipe = input.recipe.json()?;
            let base = recipe["base_upstream_commit"]
                .as_str()
                .filter(|s| !s.is_empty())
                .ok_or("missing compatibility base source identity")?;
            let original_base = value["git_commit"]
                .as_str()
                .filter(|s| !s.is_empty())
                .ok_or("missing original source identity")?;
            let filename = input
                .patch
                .path
                .file_name()
                .and_then(|s| s.to_str())
                .ok_or("compatibility patch filename is not UTF-8")?;
            let named_patch = recipe["patch"]
                .as_str()
                .filter(|s| !s.is_empty())
                .ok_or("missing compatibility patch filename")?;
            input.patch.read()?;
            if recipe["schema"] != "trust-vc.vstd-source-compat@1"
                || base != original_base
                || parse_digest(&recipe["patch_sha256"])? != input.patch.sha256
                || named_patch != filename
            {
                return Err("source compatibility inputs do not match the manifest".into());
            }
            let name = recipe["affected_file"]
                .as_str()
                .ok_or("missing affected file")?;
            relative(name)?;
            let original = parse_digest(&recipe["original_file_sha256"])?;
            if expected.get(name) != Some(&original) {
                return Err("compatibility recipe changes an unbound original source".into());
            }
            expected.insert(name.into(), parse_digest(&recipe["patched_file_sha256"])?);
        }
        let actual = inventory(&canonical_root)?;
        if actual != expected.keys().cloned().collect() {
            return Err("source graph has missing, extra or unsupported entries".into());
        }
        let mut files = BTreeMap::new();
        for (name, expected) in expected {
            let path = canonical_root.join(&name);
            let bytes = fs::read(&path).map_err(|e| e.to_string())?;
            if u32::try_from(bytes.len()).is_err() || digest(&bytes) != expected {
                return Err(format!(
                    "source bytes differ from the approved manifest: {name}"
                ));
            }
            files.insert(
                name,
                SourceFile {
                    bytes,
                    sha256: expected,
                },
            );
        }
        Ok(Self {
            requested_root: root.into(),
            canonical_root,
            manifest,
            compatibility,
            files,
        })
    }

    /// Number of files in the complete checked source graph.
    #[must_use]
    pub fn file_count(&self) -> usize {
        self.files.len()
    }

    #[must_use]
    pub fn identity(&self) -> SourceIdentity {
        SourceIdentity {
            manifest_sha256: self.manifest.sha256,
            compatibility: match &self.compatibility {
                None => SourceCompatibility::Unmodified,
                Some(input) => SourceCompatibility::Applied {
                    recipe_sha256: input.recipe.sha256,
                    patch_sha256: input.patch.sha256,
                },
            },
        }
    }

    /// Canonical root of the complete checked graph, not an approval of its
    /// content or of a compiler recipe which reads it.
    pub fn root(&self) -> &Path {
        &self.canonical_root
    }

    /// Exact byte pins for configuring a native source reader. These remain
    /// byte facts; the staging owner must establish the producing recipe.
    pub fn source_files(&self) -> Vec<PinnedFile> {
        self.files
            .iter()
            .map(|(name, file)| PinnedFile {
                path: self.canonical_root.join(name),
                sha256: file.sha256,
            })
            .collect()
    }

    /// Check an already structured anchor against this owned byte snapshot.
    /// This does not establish that a compiler actually reported the anchor.
    pub fn validate_anchor(&self, anchor: &AuthoredSpan) -> Result<(), String> {
        relative(&anchor.relative_file)?;
        let file = self
            .files
            .get(&anchor.relative_file)
            .ok_or("authored anchor is absent from the approved source graph")?;
        let (lo, hi) = anchor.bytes;
        let text = std::str::from_utf8(&file.bytes)
            .map_err(|_| "authored anchor is not in UTF-8 source")?;
        if anchor.file_sha256 != file.sha256
            || usize::try_from(anchor.original_file_len).ok() != Some(file.bytes.len())
            || lo >= hi
            || usize::try_from(hi)
                .ok()
                .is_none_or(|n| n > file.bytes.len())
            || !text.is_char_boundary(lo as usize)
            || !text.is_char_boundary(hi as usize)
        {
            return Err("authored anchor does not match the approved source bytes".into());
        }
        Ok(())
    }

    /// Borrow a bounded, exact range of the already-owned source snapshot.
    /// The caller separately establishes native span/owner provenance. This
    /// cannot read a new path or grant any source-language permission.
    #[cfg(feature = "rustc")]
    pub(crate) fn text_for(&self, anchor: &AuthoredSpan, max_bytes: usize) -> Result<&str, String> {
        relative(&anchor.relative_file)?;
        let file = self
            .files
            .get(&anchor.relative_file)
            .ok_or("source slice is absent from the approved graph")?;
        let (lo, hi) = (anchor.bytes.0 as usize, anchor.bytes.1 as usize);
        if lo >= hi
            || hi - lo > max_bytes
            || anchor.file_sha256 != file.sha256
            || usize::try_from(anchor.original_file_len).ok() != Some(file.bytes.len())
        {
            return Err("source slice differs from the bounded approved snapshot".into());
        }
        let bytes = file
            .bytes
            .get(lo..hi)
            .ok_or("source slice is outside the approved snapshot")?;
        std::str::from_utf8(bytes).map_err(|_| "source slice is not complete UTF-8 text".into())
    }

    /// Match original compiler coordinates to exact manifest bytes. The
    /// compiler's source hash is checked for consistency, not used instead of
    /// the SHA256 identity. Debug file IDs and normalized offsets play no role.
    pub fn anchor(&self, observed: &ObservedAnchor) -> Result<AuthoredSpan, String> {
        let path = Path::new(&observed.local_path);
        let name = path
            .strip_prefix(&self.requested_root)
            .or_else(|_| path.strip_prefix(&self.canonical_root))
            .map_err(|_| "source anchor is outside the approved root")?;
        let name = name.to_str().ok_or("source path is not UTF-8")?;
        relative(name)?;
        let file = self
            .files
            .get(name)
            .ok_or("source anchor is absent from the manifest")?;
        let (lo, hi) = observed.bytes;
        let text =
            std::str::from_utf8(&file.bytes).map_err(|_| "source anchor is not in UTF-8 text")?;
        if usize::try_from(observed.original_file_len).ok() != Some(file.bytes.len())
            || lo >= hi
            || usize::try_from(hi)
                .ok()
                .is_none_or(|n| n > file.bytes.len())
            || !text.is_char_boundary(lo as usize)
            || !text.is_char_boundary(hi as usize)
            || !compiler_hash_matches(&observed.compiler_source_hash, &file.bytes)?
        {
            return Err("source anchor hash, length or original byte range differs".into());
        }
        Ok(AuthoredSpan {
            relative_file: name.into(),
            file_sha256: file.sha256,
            original_file_len: observed.original_file_len,
            bytes: observed.bytes,
        })
    }

    /// Reject graph/input changes before a later staging consumer uses this
    /// snapshot. This is an input check, not a claim of race-free execution.
    pub fn revalidate(&self) -> Result<(), String> {
        if self
            .requested_root
            .canonicalize()
            .map_err(|e| e.to_string())?
            != self.canonical_root
        {
            return Err("approved source root changed its canonical identity".into());
        }
        self.manifest.read()?;
        if let Some(input) = &self.compatibility {
            input.recipe.read()?;
            input.patch.read()?;
        }
        if inventory(&self.canonical_root)? != self.files.keys().cloned().collect() {
            return Err("source graph changed after its snapshot".into());
        }
        for (name, file) in &self.files {
            if digest(&fs::read(self.canonical_root.join(name)).map_err(|e| e.to_string())?)
                != file.sha256
            {
                return Err("source bytes changed after their snapshot".into());
            }
        }
        Ok(())
    }
}

/// Actual metadata selection from the native staging owner. Stable IDs/SVH
/// are observations supplied by that owner; a file hash alone does not prove
/// that these native identities belong to the metadata bytes.
pub struct MetadataInput {
    pub stable_crate_id: u64,
    pub svh: u128,
    pub file: PinnedFile,
}

struct MetadataFile {
    svh: u128,
    file: PinnedFile,
    canonical_path: PathBuf,
}

/// Exact byte/path bindings for the selected native metadata cohort. Keep the
/// target Erase artifact separate from the common Keep/Erase dependency set.
pub struct Metadata {
    files: BTreeMap<u64, MetadataFile>,
}

impl Metadata {
    pub fn load(inputs: impl IntoIterator<Item = MetadataInput>) -> Result<Self, String> {
        Self::load_bound(inputs.into_iter().map(|input| (input, None)))
    }

    /// Bind raw paths captured from an actual native selection to the exact
    /// canonical files already admitted by the caller's input inventory. This
    /// records byte/path correspondence only; it supplies no native-context,
    /// image-owner, declaration, mode, body or verification authority.
    #[cfg(any(feature = "rustc", test))]
    pub(crate) fn load_native_selections(
        inputs: impl IntoIterator<Item = (MetadataInput, PathBuf)>,
    ) -> Result<Self, String> {
        Self::load_bound(
            inputs
                .into_iter()
                .map(|(input, canonical)| (input, Some(canonical))),
        )
    }

    fn load_bound(
        inputs: impl IntoIterator<Item = (MetadataInput, Option<PathBuf>)>,
    ) -> Result<Self, String> {
        let mut files = BTreeMap::new();
        let mut paths = BTreeSet::new();
        for (input, approved_canonical) in inputs {
            if !input.file.path.is_absolute() {
                return Err("a selected metadata path must be absolute".into());
            }
            let canonical_path = input.file.path.canonicalize().map_err(|e| e.to_string())?;
            if approved_canonical
                .as_ref()
                .is_some_and(|approved| *approved != canonical_path)
            {
                return Err("the native selection changed its approved canonical artifact".into());
            }
            PinnedFile {
                path: canonical_path.clone(),
                sha256: input.file.sha256,
            }
            .read()?;
            if input.file.path.canonicalize().map_err(|e| e.to_string())? != canonical_path {
                return Err("selected metadata path changed while binding its bytes".into());
            }
            if files.contains_key(&input.stable_crate_id) || !paths.insert(canonical_path.clone()) {
                return Err(
                    "selected metadata has duplicate native identities or path aliases".into(),
                );
            }
            files.insert(
                input.stable_crate_id,
                MetadataFile {
                    svh: input.svh,
                    file: input.file,
                    canonical_path,
                },
            );
        }
        Ok(Self { files })
    }

    /// Check an actual CStore selection against the approved native identity,
    /// SVH and exact path. Unknown paths are rejected before any path lookup.
    pub fn selected(&self, stable_crate_id: u64, svh: u128, path: &Path) -> Result<Digest, String> {
        let file = self
            .files
            .get(&stable_crate_id)
            .ok_or("unapproved native metadata crate")?;
        if file.svh != svh || (path != file.file.path && path != file.canonical_path) {
            return Err("native metadata selection differs from the approved cohort".into());
        }
        Ok(file.file.sha256)
    }

    /// Retained native selection observations for an isolated ordinary worker.
    /// These are input identity data, never a declaration/import constructor.
    #[cfg(feature = "rustc")]
    pub(crate) fn native_input_observations(&self) -> Vec<MetadataInput> {
        self.files
            .iter()
            .map(|(id, file)| MetadataInput {
                stable_crate_id: *id,
                svh: file.svh,
                file: PinnedFile {
                    path: file.canonical_path.clone(),
                    sha256: file.file.sha256,
                },
            })
            .collect()
    }

    #[must_use]
    pub fn digests(&self) -> BTreeSet<Digest> {
        self.files.values().map(|file| file.file.sha256).collect()
    }

    #[must_use]
    pub fn crate_ids(&self) -> BTreeSet<u64> {
        self.files.keys().copied().collect()
    }

    pub fn revalidate(&self) -> Result<(), String> {
        for file in self.files.values() {
            file.file.read()?;
            if file.file.path.canonicalize().map_err(|e| e.to_string())? != file.canonical_path {
                return Err("selected metadata path changed".into());
            }
        }
        Ok(())
    }
}

fn digest(bytes: &[u8]) -> Digest {
    Sha256::digest(bytes).into()
}

fn parse_digest(value: &Value) -> Result<Digest, String> {
    let text = value.as_str().ok_or("missing SHA256 digest")?;
    if text.len() != 64
        || !text
            .bytes()
            .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
    {
        return Err("SHA256 digest is not canonical lowercase hexadecimal".into());
    }
    let mut result = [0; 32];
    for (byte, pair) in result.iter_mut().zip(text.as_bytes().as_chunks::<2>().0) {
        let digit = |c| if c <= b'9' { c - b'0' } else { c - b'a' + 10 };
        *byte = digit(pair[0]) * 16 + digit(pair[1]);
    }
    Ok(result)
}

fn relative(name: &str) -> Result<(), String> {
    if name.is_empty()
        || name.contains('\\')
        || name.split('/').any(|s| matches!(s, "" | "." | ".."))
        || Path::new(name)
            .components()
            .any(|c| !matches!(c, Component::Normal(_)))
    {
        return Err("source manifest path is not a canonical relative path".into());
    }
    Ok(())
}

fn inventory(root: &Path) -> Result<BTreeSet<String>, String> {
    fn walk(root: &Path, dir: &Path, result: &mut BTreeSet<String>) -> Result<(), String> {
        if !fs::symlink_metadata(dir)
            .map_err(|e| e.to_string())?
            .is_dir()
        {
            return Err("source directory became a symlink or non-directory".into());
        }
        for entry in fs::read_dir(dir).map_err(|e| e.to_string())? {
            let entry = entry.map_err(|e| e.to_string())?;
            let path = entry.path();
            let kind = entry.file_type().map_err(|e| e.to_string())?;
            if kind.is_dir() {
                walk(root, &path, result)?;
            } else if kind.is_file() {
                let name = path
                    .strip_prefix(root)
                    .map_err(|e| e.to_string())?
                    .to_str()
                    .ok_or("source path is not UTF-8")?
                    .to_string();
                relative(&name)?;
                result.insert(name);
            } else {
                return Err("source graph contains a symlink or special file".into());
            }
        }
        Ok(())
    }
    let mut result = BTreeSet::new();
    walk(root, root, &mut result)?;
    Ok(result)
}

pub(crate) fn compiler_hash_matches(expected: &str, bytes: &[u8]) -> Result<bool, String> {
    #[cfg(feature = "rustc")]
    {
        extern crate rustc_span;
        use rustc_span::{SourceFileHash, SourceFileHashAlgorithm};
        let (kind, _) = expected
            .split_once('=')
            .ok_or("missing compiler source hash kind")?;
        let kind: SourceFileHashAlgorithm = kind
            .parse()
            .map_err(|()| "unknown compiler source hash kind")?;
        Ok(SourceFileHash::new_in_memory(kind, bytes).to_string() == expected)
    }
    #[cfg(not(feature = "rustc"))]
    {
        // The native compiler feature supplies its own MD5/SHA1/Blake3 source
        // algorithms. The rustc-free codec supports SHA256 and refuses others.
        if !expected.starts_with("sha256=") {
            return Err("this compiler source hash requires the native rustc feature".into());
        }
        let actual = digest(bytes)
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>();
        Ok(expected == format!("sha256={actual}"))
    }
}

#[cfg(test)]
mod tests;
