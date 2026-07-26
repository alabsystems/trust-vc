// trust-vc-oracle — Specification persistence store
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Persists mined specs to a JSON file so they survive across runs.
// Deduplicates by (function_name, template_name), preferring verified
// specs and lower iteration counts.

use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use crate::error::OracleError;
use crate::mining::MinedSpec;

// ---------------------------------------------------------------------------
// Default store path
// ---------------------------------------------------------------------------

/// Default path for the mined-specs store relative to the project root.
pub const DEFAULT_STORE_FILENAME: &str = ".trust_vc/mined-specs.json";

// ---------------------------------------------------------------------------
// Persisted spec format
// ---------------------------------------------------------------------------

/// On-disk representation of a mined spec. Mirrors `MinedSpec` but with
/// serde derives for JSON round-tripping.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct StoredSpec {
    pub function_name: String,
    pub template_name: String,
    pub requires: Vec<String>,
    pub ensures: Vec<String>,
    pub verified: bool,
    pub iterations: usize,
}

impl StoredSpec {
    /// Deduplication key: `(function_name, template_name)`.
    #[must_use]
    pub(crate) fn dedup_key(&self) -> (&str, &str) {
        (&self.function_name, &self.template_name)
    }
}

impl From<&MinedSpec> for StoredSpec {
    fn from(spec: &MinedSpec) -> Self {
        Self {
            function_name: spec.function_name.clone(),
            template_name: spec.template_name.clone(),
            requires: spec.requires.clone(),
            ensures: spec.ensures.clone(),
            verified: spec.verified,
            iterations: spec.iterations,
        }
    }
}

impl From<MinedSpec> for StoredSpec {
    fn from(spec: MinedSpec) -> Self {
        Self {
            function_name: spec.function_name,
            template_name: spec.template_name,
            requires: spec.requires,
            ensures: spec.ensures,
            verified: spec.verified,
            iterations: spec.iterations,
        }
    }
}

impl From<&StoredSpec> for MinedSpec {
    fn from(stored: &StoredSpec) -> Self {
        MinedSpec::new(
            stored.function_name.clone(),
            stored.template_name.clone(),
            stored.requires.clone(),
            stored.ensures.clone(),
            stored.verified,
            stored.iterations,
        )
    }
}

// ---------------------------------------------------------------------------
// SpecStore
// ---------------------------------------------------------------------------

/// Persistent store for mined specifications.
///
/// Backed by a JSON file at a configurable path. Deduplicates by
/// `(function_name, template_name)` — when a duplicate is added, the
/// better spec wins (verified beats unverified; lower iterations wins
/// among verified specs).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpecStore {
    /// Path to the backing JSON file.
    #[serde(skip)]
    path: PathBuf,
    /// All stored specs.
    specs: Vec<StoredSpec>,
}

impl SpecStore {
    /// Create a new empty store that will persist to `path`.
    #[must_use]
    pub fn new(path: impl AsRef<Path>) -> Self {
        Self {
            path: path.as_ref().to_path_buf(),
            specs: Vec::new(),
        }
    }

    /// Create a new empty store at the default path relative to `root`.
    ///
    /// The default store path is `<root>/.trust_vc/mined-specs.json`.
    #[must_use]
    pub fn with_default_path(root: impl AsRef<Path>) -> Self {
        Self::new(root.as_ref().join(DEFAULT_STORE_FILENAME))
    }

    /// Load an existing store from disk. Returns an empty store if the
    /// file does not exist.
    pub fn load(path: impl AsRef<Path>) -> Result<Self, OracleError> {
        let path = path.as_ref();
        if !path.exists() {
            return Ok(Self::new(path));
        }
        let content = std::fs::read_to_string(path).map_err(|e| OracleError::BackendError {
            message: format!("cannot read spec store {}: {e}", path.display()),
        })?;
        let specs: Vec<StoredSpec> =
            serde_json::from_str(&content).map_err(OracleError::Serialization)?;
        Ok(Self {
            path: path.to_path_buf(),
            specs,
        })
    }

    /// Write the current store contents to disk. Creates parent
    /// directories as needed.
    pub fn save(&self) -> Result<(), OracleError> {
        if let Some(parent) = self.path.parent() {
            std::fs::create_dir_all(parent).map_err(|e| OracleError::BackendError {
                message: format!("cannot create directory {}: {e}", parent.display()),
            })?;
        }
        let json = serde_json::to_string_pretty(&self.specs)?;
        std::fs::write(&self.path, json).map_err(|e| OracleError::BackendError {
            message: format!("cannot write spec store {}: {e}", self.path.display()),
        })?;
        Ok(())
    }

    /// Add a spec to the store. If a spec with the same
    /// `(function_name, template_name)` already exists, the better one
    /// wins: verified beats unverified; among equal verification status,
    /// fewer iterations wins.
    pub fn add_spec(&mut self, spec: &MinedSpec) {
        let new = StoredSpec::from(spec);
        let key = (new.function_name.as_str(), new.template_name.as_str());

        if let Some(existing) = self.specs.iter_mut().find(|s| s.dedup_key() == key) {
            if should_replace(existing, &new) {
                *existing = new;
            }
        } else {
            self.specs.push(new);
        }
    }

    /// Retrieve all specs for a given function name.
    #[must_use]
    pub fn get_specs_for_function(&self, name: &str) -> Vec<&StoredSpec> {
        self.specs
            .iter()
            .filter(|s| s.function_name == name)
            .collect()
    }

    /// Remove a spec identified by `(function_name, template_name)`.
    /// Returns `true` if a spec was removed.
    pub fn remove_spec(&mut self, function_name: &str, template_name: &str) -> bool {
        let before = self.specs.len();
        self.specs
            .retain(|s| s.function_name != function_name || s.template_name != template_name);
        self.specs.len() < before
    }

    /// Merge another store into this one, applying the same
    /// deduplication rules as `add_spec`.
    pub fn merge(&mut self, other: &SpecStore) {
        for spec in &other.specs {
            let key = spec.dedup_key();
            if let Some(existing) = self.specs.iter_mut().find(|s| s.dedup_key() == key) {
                if should_replace(existing, spec) {
                    *existing = spec.clone();
                }
            } else {
                self.specs.push(spec.clone());
            }
        }
    }

    /// Number of specs in the store.
    #[must_use]
    pub fn len(&self) -> usize {
        self.specs.len()
    }

    /// Whether the store is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.specs.is_empty()
    }

    /// Iterate over all stored specs.
    pub fn iter(&self) -> impl Iterator<Item = &StoredSpec> {
        self.specs.iter()
    }

    /// The path this store persists to.
    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// All unique function names that have specs in the store.
    #[must_use]
    pub fn function_names(&self) -> Vec<&str> {
        let mut names: Vec<&str> = self
            .specs
            .iter()
            .map(|s| s.function_name.as_str())
            .collect();
        names.sort_unstable();
        names.dedup();
        names
    }
}

// ---------------------------------------------------------------------------
// Dedup decision
// ---------------------------------------------------------------------------

/// Returns `true` if `new` should replace `existing` in the store.
fn should_replace(existing: &StoredSpec, new: &StoredSpec) -> bool {
    match (new.verified, existing.verified) {
        (true, false) => true,                     // verified beats unverified
        (false, true) => false,                    // keep verified
        _ => new.iterations < existing.iterations, // fewer iterations wins
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn make_spec(func: &str, template: &str, verified: bool, iterations: usize) -> MinedSpec {
        MinedSpec::new(
            func.to_string(),
            template.to_string(),
            vec!["x > 0".to_string()],
            vec!["result >= 0".to_string()],
            verified,
            iterations,
        )
    }

    fn temp_store_path(label: &str) -> PathBuf {
        std::env::temp_dir().join(format!(
            "trust_vc_spec_store_test_{}_{}_{}.json",
            label,
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("system clock should be after epoch")
                .as_nanos()
        ))
    }

    // -----------------------------------------------------------------------
    // Save / load roundtrip
    // -----------------------------------------------------------------------

    #[test]
    fn test_store_save_load_roundtrip() {
        let path = temp_store_path("roundtrip");
        let mut store = SpecStore::new(&path);
        store.add_spec(&make_spec("foo", "range", true, 0));
        store.add_spec(&make_spec("bar", "non_negative", true, 2));
        store.save().expect("save should succeed");

        let loaded = SpecStore::load(&path).expect("load should succeed");
        assert_eq!(loaded.len(), 2);
        assert_eq!(loaded.get_specs_for_function("foo").len(), 1);
        assert_eq!(loaded.get_specs_for_function("bar").len(), 1);

        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn test_store_save_load_preserves_fields() {
        let path = temp_store_path("fields");
        let mut store = SpecStore::new(&path);
        let spec = MinedSpec::new(
            "myf".to_string(),
            "sorted".to_string(),
            vec!["a > 0".to_string(), "b > 0".to_string()],
            vec!["result.sorted()".to_string()],
            true,
            3,
        );
        store.add_spec(&spec);
        store.save().expect("save should succeed");

        let loaded = SpecStore::load(&path).expect("load should succeed");
        let s = &loaded.get_specs_for_function("myf")[0];
        assert_eq!(s.function_name, "myf");
        assert_eq!(s.template_name, "sorted");
        assert_eq!(s.requires, vec!["a > 0", "b > 0"]);
        assert_eq!(s.ensures, vec!["result.sorted()"]);
        assert!(s.verified);
        assert_eq!(s.iterations, 3);

        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn test_store_load_nonexistent_returns_empty() {
        let path = PathBuf::from("/tmp/trust_vc_nonexistent_store_12345.json");
        let _ = std::fs::remove_file(&path); // ensure it does not exist
        let store = SpecStore::load(&path).expect("load should succeed for missing file");
        assert!(store.is_empty());
    }

    // -----------------------------------------------------------------------
    // Deduplication
    // -----------------------------------------------------------------------

    #[test]
    fn test_store_dedup_verified_beats_unverified() {
        let path = temp_store_path("dedup_verified");
        let mut store = SpecStore::new(&path);
        store.add_spec(&make_spec("f", "range", false, 3));
        store.add_spec(&make_spec("f", "range", true, 5));
        assert_eq!(store.len(), 1);
        assert!(store.get_specs_for_function("f")[0].verified);
    }

    #[test]
    fn test_store_dedup_keeps_verified_over_unverified() {
        let path = temp_store_path("dedup_keep");
        let mut store = SpecStore::new(&path);
        store.add_spec(&make_spec("f", "range", true, 1));
        store.add_spec(&make_spec("f", "range", false, 0));
        assert_eq!(store.len(), 1);
        assert!(store.get_specs_for_function("f")[0].verified);
        assert_eq!(store.get_specs_for_function("f")[0].iterations, 1);
    }

    #[test]
    fn test_store_dedup_fewer_iterations_wins_among_verified() {
        let path = temp_store_path("dedup_iter");
        let mut store = SpecStore::new(&path);
        store.add_spec(&make_spec("f", "range", true, 3));
        store.add_spec(&make_spec("f", "range", true, 1));
        assert_eq!(store.len(), 1);
        assert_eq!(store.get_specs_for_function("f")[0].iterations, 1);
    }

    #[test]
    fn test_store_dedup_fewer_iterations_wins_among_unverified() {
        let path = temp_store_path("dedup_unverified_iter");
        let mut store = SpecStore::new(&path);
        store.add_spec(&make_spec("f", "range", false, 5));
        store.add_spec(&make_spec("f", "range", false, 2));
        assert_eq!(store.len(), 1);
        assert_eq!(store.get_specs_for_function("f")[0].iterations, 2);
    }

    #[test]
    fn test_store_dedup_different_templates_not_deduped() {
        let path = temp_store_path("dedup_diff_tmpl");
        let mut store = SpecStore::new(&path);
        store.add_spec(&make_spec("f", "range", true, 0));
        store.add_spec(&make_spec("f", "non_negative", true, 0));
        assert_eq!(store.len(), 2);
    }

    #[test]
    fn test_store_dedup_different_functions_not_deduped() {
        let path = temp_store_path("dedup_diff_func");
        let mut store = SpecStore::new(&path);
        store.add_spec(&make_spec("f", "range", true, 0));
        store.add_spec(&make_spec("g", "range", true, 0));
        assert_eq!(store.len(), 2);
    }

    // -----------------------------------------------------------------------
    // Remove
    // -----------------------------------------------------------------------

    #[test]
    fn test_store_remove_existing_spec() {
        let path = temp_store_path("remove_existing");
        let mut store = SpecStore::new(&path);
        store.add_spec(&make_spec("f", "range", true, 0));
        store.add_spec(&make_spec("f", "sorted", true, 1));
        assert!(store.remove_spec("f", "range"));
        assert_eq!(store.len(), 1);
        assert_eq!(store.get_specs_for_function("f")[0].template_name, "sorted");
    }

    #[test]
    fn test_store_remove_nonexistent_returns_false() {
        let path = temp_store_path("remove_none");
        let mut store = SpecStore::new(&path);
        store.add_spec(&make_spec("f", "range", true, 0));
        assert!(!store.remove_spec("f", "non_negative"));
        assert_eq!(store.len(), 1);
    }

    // -----------------------------------------------------------------------
    // Merge
    // -----------------------------------------------------------------------

    #[test]
    fn test_store_merge_combines_disjoint() {
        let path_a = temp_store_path("merge_a");
        let path_b = temp_store_path("merge_b");
        let mut a = SpecStore::new(&path_a);
        let mut b = SpecStore::new(&path_b);
        a.add_spec(&make_spec("f", "range", true, 0));
        b.add_spec(&make_spec("g", "sorted", true, 1));
        a.merge(&b);
        assert_eq!(a.len(), 2);
        assert_eq!(a.get_specs_for_function("f").len(), 1);
        assert_eq!(a.get_specs_for_function("g").len(), 1);
    }

    #[test]
    fn test_store_merge_deduplicates_overlap() {
        let path_a = temp_store_path("merge_dedup_a");
        let path_b = temp_store_path("merge_dedup_b");
        let mut a = SpecStore::new(&path_a);
        let mut b = SpecStore::new(&path_b);
        a.add_spec(&make_spec("f", "range", false, 3));
        b.add_spec(&make_spec("f", "range", true, 1));
        a.merge(&b);
        assert_eq!(a.len(), 1);
        assert!(a.get_specs_for_function("f")[0].verified);
    }

    #[test]
    fn test_store_merge_preserves_better_spec_in_target() {
        let path_a = temp_store_path("merge_keep_a");
        let path_b = temp_store_path("merge_keep_b");
        let mut a = SpecStore::new(&path_a);
        let mut b = SpecStore::new(&path_b);
        a.add_spec(&make_spec("f", "range", true, 0));
        b.add_spec(&make_spec("f", "range", false, 3));
        a.merge(&b);
        assert_eq!(a.len(), 1);
        assert!(a.get_specs_for_function("f")[0].verified);
        assert_eq!(a.get_specs_for_function("f")[0].iterations, 0);
    }

    // -----------------------------------------------------------------------
    // Utility methods
    // -----------------------------------------------------------------------

    #[test]
    fn test_store_function_names() {
        let path = temp_store_path("func_names");
        let mut store = SpecStore::new(&path);
        store.add_spec(&make_spec("beta", "range", true, 0));
        store.add_spec(&make_spec("alpha", "range", true, 0));
        store.add_spec(&make_spec("alpha", "sorted", true, 0));
        let names = store.function_names();
        assert_eq!(names, vec!["alpha", "beta"]);
    }

    #[test]
    fn test_store_iter() {
        let path = temp_store_path("iter");
        let mut store = SpecStore::new(&path);
        store.add_spec(&make_spec("f", "range", true, 0));
        store.add_spec(&make_spec("g", "sorted", true, 1));
        let all: Vec<_> = store.iter().collect();
        assert_eq!(all.len(), 2);
    }

    #[test]
    fn test_store_is_empty_on_new() {
        let store = SpecStore::new("/tmp/empty.json");
        assert!(store.is_empty());
        assert_eq!(store.len(), 0);
    }

    #[test]
    fn test_store_path_accessor() {
        let store = SpecStore::new("/some/path.json");
        assert_eq!(store.path(), Path::new("/some/path.json"));
    }

    #[test]
    fn test_store_save_creates_parent_dirs() {
        let dir = std::env::temp_dir().join(format!(
            "trust_vc_nested_store_{}_{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("system clock should be after epoch")
                .as_nanos()
        ));
        let path = dir.join("sub").join("store.json");
        let mut store = SpecStore::new(&path);
        store.add_spec(&make_spec("f", "range", true, 0));
        store.save().expect("save should create parent dirs");
        assert!(path.exists());
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn test_store_load_corrupt_json_returns_error() {
        let path = temp_store_path("corrupt");
        std::fs::write(&path, "not json!!!").expect("write corrupt file");
        let result = SpecStore::load(&path);
        assert!(result.is_err());
        std::fs::remove_file(&path).ok();
    }
}
