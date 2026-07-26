// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-file extern_spec discovery and lookup.
//!
//! Resolution scope tracking: each entry records how it was discovered
//! ([`ResolutionScope`]). Currently only file-local discovery is implemented;
//! manifest-scoped lookup is layered on top in `extern_spec_catalog`, and
//! dependency-crate resolution will be added incrementally.

use crate::error::{TrustVcError, TrustVcResult};
use crate::extern_spec::{try_project_extern_spec_entries, ExternSpecInput};
use crate::extern_spec_helpers::{type_to_full_path_string, type_to_path_string};
use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};
use syn::{parse2, Item, Type};

/// Tracks the discovery scope of an extern_spec entry.
///
/// Used to enforce fail-closed behavior: only `FileLocal` specs are resolved
/// today. Attempts to use same-crate or cross-crate resolution produce a
/// deterministic unsupported-resolution diagnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum ResolutionScope {
    /// The `extern_spec!` block lives in the same source file as the call site.
    FileLocal,
}

/// Known external crate prefixes for fail-closed scope classification.
const EXTERNAL_CRATE_PREFIXES: &[&str] = &["std::", "core::", "alloc::"];

/// Classify a target path's likely resolution scope from its lexical prefix.
///
/// Returns `None` for file-local-compatible paths (no crate qualifier),
/// or `Some(prefix)` for paths that start with a known external crate prefix.
#[must_use]
pub(crate) fn classify_target_scope(target: &str) -> Option<&'static str> {
    let compact: String = target.chars().filter(|ch| !ch.is_whitespace()).collect();
    EXTERNAL_CRATE_PREFIXES
        .iter()
        .find(|prefix| compact.starts_with(*prefix))
        .copied()
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExternSpecEntry {
    pub(crate) target_path: String,
    pub(crate) param_names: Vec<String>,
    pub(crate) requires: Vec<String>,
    pub(crate) ensures: Vec<String>,
    pub(crate) resolution_scope: ResolutionScope,
}

static EXTERN_SPEC_CACHE: OnceLock<Mutex<HashMap<String, Vec<ExternSpecEntry>>>> = OnceLock::new();

pub(crate) fn lookup_extern_spec_source(
    file_path: &str,
    source_text: &str,
    target: &str,
) -> TrustVcResult<Option<ExternSpecEntry>> {
    let full_key = normalize_extern_spec_path_full(target)?;
    let entries = load_entries_for_file(file_path, source_text)?;

    // Phase 1: exact match with generics preserved (#2305)
    for entry in &entries {
        if normalize_extern_spec_path_full(&entry.target_path)? == full_key {
            return Ok(Some(entry.clone()));
        }
    }

    // Phase 2: erased fallback with ambiguity guard
    let erased_key = normalize_extern_spec_path(target)?;
    let mut matches: Vec<ExternSpecEntry> = Vec::new();
    for entry in &entries {
        if normalize_extern_spec_path(&entry.target_path)? == erased_key {
            matches.push(entry.clone());
        }
    }
    match matches.len() {
        0 => Ok(None),
        1 => Ok(matches.into_iter().next()),
        n => Err(TrustVcError::Internal {
            context: "lookup extern_spec source",
            detail: format!(
                "ambiguous extern_spec lookup for `{target}`: {n} entries match \
                 after generic erasure — use explicit generic arguments to disambiguate"
            ),
        }),
    }
}

pub(crate) fn normalize_extern_spec_path_full(path: &str) -> TrustVcResult<String> {
    let compact: String = path.chars().filter(|ch| !ch.is_whitespace()).collect();
    let (type_path, method_name) =
        compact
            .rsplit_once("::")
            .ok_or_else(|| TrustVcError::Internal {
                context: "normalize extern_spec target path",
                detail: format!(
                    "extern_spec target `{path}` is missing a `Type::method` path separator"
                ),
            })?;

    if method_name.is_empty() {
        return Err(TrustVcError::Internal {
            context: "normalize extern_spec target path",
            detail: format!("extern_spec target `{path}` is missing the method name"),
        });
    }

    let ty: Type = syn::parse_str(type_path).map_err(|source| TrustVcError::Parse {
        context: "parse extern_spec target type",
        source,
    })?;
    let full_type = type_to_full_path_string(&ty).ok_or_else(|| TrustVcError::Internal {
        context: "normalize extern_spec target type",
        detail: format!("extern_spec target type must be a simple lexical path: `{type_path}`"),
    })?;
    Ok(format!("{full_type}::{method_name}"))
}

pub(crate) fn normalize_extern_spec_path(path: &str) -> TrustVcResult<String> {
    let compact: String = path.chars().filter(|ch| !ch.is_whitespace()).collect();
    let (type_path, method_name) =
        compact
            .rsplit_once("::")
            .ok_or_else(|| TrustVcError::Internal {
                context: "normalize extern_spec target path",
                detail: format!(
                    "extern_spec target `{path}` is missing a `Type::method` path separator"
                ),
            })?;

    if method_name.is_empty() {
        return Err(TrustVcError::Internal {
            context: "normalize extern_spec target path",
            detail: format!("extern_spec target `{path}` is missing the method name"),
        });
    }

    let ty: Type = syn::parse_str(type_path).map_err(|source| TrustVcError::Parse {
        context: "parse extern_spec target type",
        source,
    })?;
    let normalized_type = type_to_path_string(&ty).ok_or_else(|| TrustVcError::Internal {
        context: "normalize extern_spec target type",
        detail: format!("extern_spec target type must be a simple lexical path: `{type_path}`"),
    })?;
    Ok(format!("{normalized_type}::{method_name}"))
}

fn load_entries_for_file(
    file_path: &str,
    source_text: &str,
) -> TrustVcResult<Vec<ExternSpecEntry>> {
    let cache = EXTERN_SPEC_CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    {
        let cache = cache.lock().map_err(|_| TrustVcError::Internal {
            context: "load extern_spec cache",
            detail: "extern_spec cache lock poisoned".to_string(),
        })?;
        if let Some(entries) = cache.get(file_path) {
            return Ok(entries.clone());
        }
    }

    let parsed = entries_from_source_text(source_text)?;

    let mut cache = cache.lock().map_err(|_| TrustVcError::Internal {
        context: "update extern_spec cache",
        detail: "extern_spec cache lock poisoned".to_string(),
    })?;
    Ok(cache
        .entry(file_path.to_string())
        .or_insert_with(|| parsed.clone())
        .clone())
}

pub(crate) fn entries_from_source_text(source_text: &str) -> TrustVcResult<Vec<ExternSpecEntry>> {
    let file =
        crate::parse_file_allow_tracked(source_text).map_err(|source| TrustVcError::Parse {
            context: "parse source file for extern_spec lookup",
            source,
        })?;
    let mut entries = Vec::new();
    collect_entries(&file.items, &mut entries)?;
    Ok(entries)
}

fn collect_entries(items: &[Item], entries: &mut Vec<ExternSpecEntry>) -> TrustVcResult<()> {
    for item in items {
        match item {
            Item::Macro(item_macro)
                if item_macro.mac.path.segments.last().is_some_and(|segment| {
                    segment.ident == "extern_spec" || segment.ident == "external_spec"
                }) =>
            {
                let input =
                    parse2::<ExternSpecInput>(item_macro.mac.tokens.clone()).map_err(|source| {
                        TrustVcError::Parse {
                            context: "parse extern_spec! declaration from source text",
                            source,
                        }
                    })?;

                for entry in try_project_extern_spec_entries(input)? {
                    normalize_extern_spec_path(&entry.target_path).map_err(|err| {
                        TrustVcError::Internal {
                            context: "validate extern_spec target path",
                            detail: format!(
                                "extern_spec target `{}` cannot be normalized: {err}",
                                entry.target_path
                            ),
                        }
                    })?;
                    entries.push(ExternSpecEntry {
                        target_path: entry.target_path,
                        param_names: entry.param_names,
                        requires: entry.requires,
                        ensures: entry.ensures,
                        resolution_scope: ResolutionScope::FileLocal,
                    });
                }
            }
            Item::Mod(item_mod) => {
                if let Some((_, nested_items)) = &item_mod.content {
                    collect_entries(nested_items, entries)?;
                }
            }
            _ => {}
        }
    }

    Ok(())
}

#[cfg(test)]
#[path = "extern_spec_registry_tests.rs"]
mod tests;
