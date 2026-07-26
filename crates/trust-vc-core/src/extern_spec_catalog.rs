// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Manifest-scoped extern_spec discovery and lookup.

use crate::error::{TrustVcError, TrustVcResult};
use crate::extern_spec_registry::{
    entries_from_source_text, normalize_extern_spec_path, normalize_extern_spec_path_full,
    ExternSpecEntry,
};
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

const MANIFEST_SOURCE_ROOTS: &[&str] = &["src", "tests", "examples", "benches"];
const EXTERN_SPEC_MARKERS: &[&str] = &["extern_spec!", "external_spec!"];

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CatalogMatch {
    pub(crate) source_file: PathBuf,
    pub(crate) entry: ExternSpecEntry,
}

static MANIFEST_CATALOG_CACHE: OnceLock<Mutex<HashMap<PathBuf, Vec<CatalogMatch>>>> =
    OnceLock::new();

/// Looks up an extern_spec in the manifest-scoped catalog.
///
/// When `caller_file` is provided, ambiguous matches are disambiguated by
/// proximity to the caller's file (same file, then subtree). Part of #2658.
pub(crate) fn lookup_extern_spec_in_manifest(
    manifest_dir: &Path,
    target: &str,
    caller_file: Option<&str>,
) -> TrustVcResult<Option<CatalogMatch>> {
    let manifest_dir = canonicalize_manifest_dir(manifest_dir)?;
    let entries = load_catalog(&manifest_dir)?;
    let full_key = normalize_extern_spec_path_full(target)?;

    let mut exact_matches = Vec::new();
    for item in &entries {
        if normalize_extern_spec_path_full(&item.entry.target_path)? == full_key {
            exact_matches.push(item.clone());
        }
    }
    match exact_matches.len() {
        0 => {}
        1 => return Ok(exact_matches.into_iter().next()),
        n => {
            // Try file-scoped disambiguation: prefer match from the caller's
            // file or its directory subtree. Part of #2658 Category E2.
            if let Some(disambiguated) = disambiguate_by_caller_file(&exact_matches, caller_file) {
                return Ok(Some(disambiguated));
            }
            return Err(TrustVcError::Internal {
                context: "lookup extern_spec manifest catalog",
                detail: format!(
                    "ambiguous extern_spec lookup for `{target}`: {n} entries match \
                     exactly within the current package ({})",
                    format_match_sources(&exact_matches)
                ),
            });
        }
    }

    let erased_key = normalize_extern_spec_path(target)?;
    let mut erased_matches = Vec::new();
    for item in &entries {
        if normalize_extern_spec_path(&item.entry.target_path)? == erased_key {
            erased_matches.push(item.clone());
        }
    }

    match erased_matches.len() {
        0 => Ok(None),
        1 => Ok(erased_matches.into_iter().next()),
        n => Err(TrustVcError::Internal {
            context: "lookup extern_spec manifest catalog",
            detail: format!(
                "ambiguous extern_spec lookup for `{target}`: {n} entries match \
                 after generic erasure within the current package ({}) — use \
                 explicit generic arguments to disambiguate",
                format_match_sources(&erased_matches)
            ),
        }),
    }
}

fn canonicalize_manifest_dir(manifest_dir: &Path) -> TrustVcResult<PathBuf> {
    fs::canonicalize(manifest_dir).map_err(|source| TrustVcError::Io {
        context: "canonicalize extern_spec manifest dir",
        source,
    })
}

fn load_catalog(manifest_dir: &Path) -> TrustVcResult<Vec<CatalogMatch>> {
    let cache = MANIFEST_CATALOG_CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    {
        let cache = cache.lock().map_err(|_| TrustVcError::Internal {
            context: "load extern_spec manifest cache",
            detail: "extern_spec manifest cache lock poisoned".to_string(),
        })?;
        if let Some(entries) = cache.get(manifest_dir) {
            return Ok(entries.clone());
        }
    }

    let catalog = build_catalog(manifest_dir)?;

    let mut cache = cache.lock().map_err(|_| TrustVcError::Internal {
        context: "update extern_spec manifest cache",
        detail: "extern_spec manifest cache lock poisoned".to_string(),
    })?;
    Ok(cache
        .entry(manifest_dir.to_path_buf())
        .or_insert_with(|| catalog.clone())
        .clone())
}

fn build_catalog(manifest_dir: &Path) -> TrustVcResult<Vec<CatalogMatch>> {
    let mut rust_files = Vec::new();
    for source_root in MANIFEST_SOURCE_ROOTS {
        let root = manifest_dir.join(source_root);
        if root.is_dir() {
            collect_rust_files(&root, &mut rust_files)?;
        }
    }
    rust_files.sort();

    let mut catalog = Vec::new();
    for source_file in rust_files {
        let source_text = fs::read_to_string(&source_file).map_err(|source| TrustVcError::Io {
            context: "read extern_spec manifest source",
            source,
        })?;
        if !EXTERN_SPEC_MARKERS
            .iter()
            .any(|marker| source_text.contains(marker))
        {
            continue;
        }
        for entry in entries_from_source_text(&source_text)? {
            catalog.push(CatalogMatch {
                source_file: source_file.clone(),
                entry,
            });
        }
    }

    Ok(catalog)
}

fn collect_rust_files(root: &Path, files: &mut Vec<PathBuf>) -> TrustVcResult<()> {
    let mut entries = fs::read_dir(root)
        .map_err(|source| TrustVcError::Io {
            context: "scan extern_spec manifest sources",
            source,
        })?
        .map(|entry| {
            entry
                .map(|entry| entry.path())
                .map_err(|source| TrustVcError::Io {
                    context: "scan extern_spec manifest sources",
                    source,
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    entries.sort();

    for path in entries {
        if path.is_dir() {
            collect_rust_files(&path, files)?;
            continue;
        }
        if path.extension().is_some_and(|ext| ext == "rs") {
            files.push(path);
        }
    }

    Ok(())
}

fn format_match_sources(matches: &[CatalogMatch]) -> String {
    matches
        .iter()
        .map(|item| item.source_file.display().to_string())
        .collect::<Vec<_>>()
        .join(", ")
}

/// Disambiguates multiple catalog matches by proximity to the caller's file.
///
/// Preference order:
/// 1. Exact file match (extern_spec in same file as caller)
/// 2. Subtree match (extern_spec in a subdirectory named after the caller's stem,
///    e.g., `foo.rs` caller prefers matches in `foo/` subdirectory)
///
/// Returns `None` if disambiguation fails (no caller file, or multiple matches
/// even after filtering). Part of #2658 Category E2.
fn disambiguate_by_caller_file(
    matches: &[CatalogMatch],
    caller_file: Option<&str>,
) -> Option<CatalogMatch> {
    let caller = caller_file?;
    let caller_path = Path::new(caller);

    // Use suffix-based matching: `file!()` returns a relative path but
    // catalog entries are canonicalized absolute paths. Check if the
    // absolute path ends with the caller's relative path components.

    // 1. Exact file match (suffix-based)
    let exact: Vec<_> = matches
        .iter()
        .filter(|m| m.source_file.ends_with(caller_path))
        .collect();
    if exact.len() == 1 {
        return Some(exact[0].clone());
    }

    // 2. Subtree match: caller's stem as directory component
    // e.g., caller = "tests/extern_spec_cross_file_verify.rs"
    //   → prefer matches whose path contains "/extern_spec_cross_file_verify/"
    let caller_stem = caller_path.file_stem()?.to_str()?;
    let stem_component = format!("/{caller_stem}/");

    let subtree: Vec<_> = matches
        .iter()
        .filter(|m| {
            let s = m.source_file.to_string_lossy();
            s.contains(&stem_component)
        })
        .collect();
    if subtree.len() == 1 {
        return Some(subtree[0].clone());
    }

    None
}
