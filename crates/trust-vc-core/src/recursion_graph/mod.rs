//! Crate-local call graph and SCC-based recursion detection.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Builds a call graph from the crate source tree, computes SCCs using
//! Tarjan's algorithm, and answers "who are this function's recursive peers?"
//! Used by `#[decreases]` to automatically detect mutual recursion without
//! requiring explicit `mutual_with(...)`.
//!
//! Part of #2054, split into directory module as part of #2561.

mod build;
pub(crate) mod tarjan;
#[cfg(test)]
mod tests;

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

use crate::mode_index::{self, CanonicalFnPath, CrateModeIndex};

/// Summary of a function's recursion status within its crate.
#[derive(Debug, Clone)]
pub(crate) struct RecursionSummary {
    /// Canonical path of the queried function.
    pub current: CanonicalFnPath,
    /// All functions in the same SCC (includes `current` if recursive).
    pub scc_members: HashSet<CanonicalFnPath>,
    /// True if the function is self-recursive or in a multi-function SCC.
    pub is_recursive: bool,
}

/// A crate-local call graph mapping each function to its local callees.
#[derive(Debug, Clone)]
pub(super) struct CrateCallGraph {
    /// Edges: caller → set of callees (both as canonical paths).
    pub edges: HashMap<CanonicalFnPath, HashSet<CanonicalFnPath>>,
}

// ========================================================================
// Process-local call graph cache
// ========================================================================

static CALL_GRAPH_CACHE: OnceLock<Mutex<HashMap<PathBuf, CrateCallGraph>>> = OnceLock::new();

fn call_graph_cache() -> &'static Mutex<HashMap<PathBuf, CrateCallGraph>> {
    CALL_GRAPH_CACHE.get_or_init(|| Mutex::new(HashMap::new()))
}

/// Clears the call graph cache. Used in tests.
#[cfg(test)]
pub(crate) fn clear_call_graph_cache() {
    if let Some(map) = CALL_GRAPH_CACHE.get() {
        if let Ok(mut map) = map.lock() {
            map.clear();
        }
    }
}

// ========================================================================
// Public API
// ========================================================================

/// Returns the recursion summary for a function, given its canonical path and
/// the crate root. Builds and caches the call graph on first access.
pub(crate) fn summary_for_canonical(
    current: &CanonicalFnPath,
    crate_root: &Path,
    index: &CrateModeIndex,
) -> Option<RecursionSummary> {
    let graph = get_or_build_call_graph(crate_root, index)?;
    let sccs = tarjan::tarjan_sccs(&graph);

    // Find which SCC contains `current`.
    let mut scc_members = HashSet::new();
    for scc in &sccs {
        if scc.contains(current) {
            scc_members = scc.clone();
            break;
        }
    }

    let is_recursive = if scc_members.len() > 1 {
        true
    } else if scc_members.len() == 1 {
        // Self-loop: current calls itself.
        graph
            .edges
            .get(current)
            .is_some_and(|callees| callees.contains(current))
    } else {
        false
    };

    Some(RecursionSummary {
        current: current.clone(),
        scc_members,
        is_recursive,
    })
}

/// Convenience wrapper: discovers crate root from a source file span,
/// builds the index and call graph, and returns the recursion summary.
pub(crate) fn summary_for_item_fn(
    input: &syn::ItemFn,
    span: proc_macro2::Span,
) -> Option<RecursionSummary> {
    let source_file = span.local_file()?;
    let crate_root = mode_index::discover_crate_root(&source_file)?;
    let index = mode_index::get_or_build_index(&crate_root)?;

    let fn_name = input.sig.ident.to_string();
    let caller_module = determine_module_path(&source_file, &crate_root);
    let mut path_segs = caller_module.clone();
    path_segs.push(fn_name.clone());
    let current = CanonicalFnPath(path_segs);

    // Try direct lookup first (free functions).
    if let Some(summary) = summary_for_canonical(&current, &crate_root, &index) {
        return Some(summary);
    }

    // Fallback: the function might be an impl method. The proc-macro receives
    // it as an ItemFn without knowing the enclosing type. Try type-scoped
    // lookup: [module, *, fn_name]. Fix for #2550 finding F1.
    if let Some(method_path) = index.lookup_method_in_module(&fn_name, &caller_module) {
        return summary_for_canonical(&method_path, &crate_root, &index);
    }

    None
}

/// Returns the caller module path from a span, for use in qualified-path
/// resolution during body transformation.
pub(crate) fn caller_module_from_span(span: proc_macro2::Span) -> Vec<String> {
    let source_file = match span.local_file() {
        Some(f) => f,
        None => return Vec::new(),
    };
    let crate_root = match mode_index::discover_crate_root(&source_file) {
        Some(r) => r,
        None => return Vec::new(),
    };
    determine_module_path(&source_file, &crate_root)
}

// ========================================================================
// Module path determination (shared with mode_scan)
// ========================================================================

/// Determines the module path of a source file relative to the crate root.
///
/// For `src/specs/helpers.rs` with crate root `src/lib.rs`, returns
/// `["specs", "helpers"]`.
fn determine_module_path(source_file: &Path, crate_root: &Path) -> Vec<String> {
    let source_canonical = source_file
        .canonicalize()
        .unwrap_or_else(|_| source_file.to_path_buf());
    let root_canonical = crate_root
        .canonicalize()
        .unwrap_or_else(|_| crate_root.to_path_buf());

    if source_canonical == root_canonical {
        return Vec::new();
    }

    let root_dir = match root_canonical.parent() {
        Some(d) => d,
        None => return Vec::new(),
    };

    let relative = match source_canonical.strip_prefix(root_dir) {
        Ok(r) => r,
        Err(_) => return Vec::new(),
    };

    let mut segments: Vec<String> = relative
        .components()
        .filter_map(|c| {
            if let std::path::Component::Normal(s) = c {
                s.to_str().map(|s| s.to_string())
            } else {
                None
            }
        })
        .collect();

    // Remove the .rs extension from the last segment.
    if let Some(last) = segments.last_mut() {
        if let Some(stripped) = last.strip_suffix(".rs") {
            *last = stripped.to_string();
        }
    }
    // Remove "mod" if it's the last segment (mod.rs files).
    if segments.last().is_some_and(|s| s == "mod") {
        segments.pop();
    }

    segments
}

// ========================================================================
// Call graph building (delegates to build module)
// ========================================================================

fn get_or_build_call_graph(crate_root: &Path, index: &CrateModeIndex) -> Option<CrateCallGraph> {
    let mut cache = call_graph_cache().lock().ok()?;
    if let Some(graph) = cache.get(crate_root) {
        return Some(graph.clone());
    }

    let graph = build::build_call_graph(crate_root, index)?;
    cache.insert(crate_root.to_path_buf(), graph.clone());
    Some(graph)
}
