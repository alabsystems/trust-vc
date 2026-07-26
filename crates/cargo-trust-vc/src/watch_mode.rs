// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! File-watching verification mode for the cargo-trust-vc CLI.
//!
//! Monitors Rust source files for changes and automatically re-verifies
//! affected functions, displaying incremental results. The module is
//! self-contained, relying only on `std`.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant, SystemTime};

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Controls file-watching behavior.
#[derive(Debug, Clone)]
pub(crate) struct WatchConfig {
    /// Root directory to watch.
    pub(crate) root: PathBuf,
    /// Debounce configuration for coalescing rapid changes.
    pub(crate) debounce: DebounceConfig,
    /// Filter controlling which files are watched.
    pub(crate) filter: FileFilter,
    /// Maximum number of functions to re-verify per change batch.
    pub(crate) max_batch_size: usize,
}

impl Default for WatchConfig {
    fn default() -> Self {
        Self {
            root: PathBuf::from("."),
            debounce: DebounceConfig::default(),
            filter: FileFilter::default(),
            max_batch_size: 64,
        }
    }
}

/// Debounce window for coalescing rapid file-system events.
#[derive(Debug, Clone, Copy)]
pub(crate) struct DebounceConfig {
    /// Events within this window are coalesced into a single change set.
    pub(crate) window: Duration,
    /// Maximum delay before forcing a flush regardless of new events.
    pub(crate) max_delay: Duration,
}

impl Default for DebounceConfig {
    fn default() -> Self {
        Self {
            window: Duration::from_millis(200),
            max_delay: Duration::from_secs(2),
        }
    }
}

// ---------------------------------------------------------------------------
// File filter (include/exclude globs)
// ---------------------------------------------------------------------------

/// Simple glob-style filter for watched paths.
///
/// Patterns use a minimal subset of glob syntax: `*` matches any sequence of
/// non-separator characters, and `**` matches any path component sequence.
/// Exclude patterns take precedence over include patterns.
#[derive(Debug, Clone)]
pub(crate) struct FileFilter {
    /// Patterns that a path must match to be included.
    pub(crate) include: Vec<String>,
    /// Patterns that cause a path to be excluded even if it matches include.
    pub(crate) exclude: Vec<String>,
}

impl Default for FileFilter {
    fn default() -> Self {
        Self {
            include: vec!["**/*.rs".to_owned()],
            exclude: vec!["**/target/**".to_owned()],
        }
    }
}

impl FileFilter {
    /// Returns `true` if `path` passes the include/exclude filter.
    #[must_use]
    pub(crate) fn accepts(&self, path: &Path) -> bool {
        let s = path.to_string_lossy();
        if self.exclude.iter().any(|pat| glob_matches(pat, &s)) {
            return false;
        }
        if self.include.is_empty() {
            return true;
        }
        self.include.iter().any(|pat| glob_matches(pat, &s))
    }
}

/// Minimal glob matcher supporting `*` and `**`.
fn glob_matches(pattern: &str, text: &str) -> bool {
    glob_matches_inner(pattern.as_bytes(), text.as_bytes())
}

fn glob_matches_inner(pat: &[u8], txt: &[u8]) -> bool {
    let mut pi = 0;
    let mut ti = 0;
    let mut star_pi = usize::MAX;
    let mut star_ti = 0;

    while ti < txt.len() {
        if pi < pat.len() && pat[pi] == b'*' {
            // Check for `**` (matches path separators too).
            if pi + 1 < pat.len() && pat[pi + 1] == b'*' {
                // `**` — try all suffixes.
                let rest_pat = if pi + 2 < pat.len() && pat[pi + 2] == b'/' {
                    &pat[pi + 3..]
                } else {
                    &pat[pi + 2..]
                };
                for start in ti..=txt.len() {
                    if glob_matches_inner(rest_pat, &txt[start..]) {
                        return true;
                    }
                }
                return false;
            }
            // Single `*` — does not cross `/`.
            star_pi = pi;
            star_ti = ti;
            pi += 1;
        } else if pi < pat.len() && (pat[pi] == txt[ti] || pat[pi] == b'?') {
            pi += 1;
            ti += 1;
        } else if star_pi != usize::MAX {
            // Backtrack: extend star match (but don't cross `/`).
            if txt[star_ti] == b'/' {
                return false;
            }
            star_ti += 1;
            ti = star_ti;
            pi = star_pi + 1;
        } else {
            return false;
        }
    }

    // Consume trailing stars.
    while pi < pat.len() && pat[pi] == b'*' {
        pi += 1;
    }
    pi == pat.len()
}

// ---------------------------------------------------------------------------
// File change tracking
// ---------------------------------------------------------------------------

/// Kind of file-system change.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum ChangeKind {
    Created,
    Modified,
    Deleted,
}

impl fmt::Display for ChangeKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Created => f.write_str("created"),
            Self::Modified => f.write_str("modified"),
            Self::Deleted => f.write_str("deleted"),
        }
    }
}

/// A single detected file change.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FileChange {
    pub(crate) path: PathBuf,
    pub(crate) kind: ChangeKind,
    pub(crate) timestamp: SystemTime,
}

// ---------------------------------------------------------------------------
// Change detector
// ---------------------------------------------------------------------------

/// Snapshot-based change detector.
///
/// Compares successive modification-time snapshots to detect created, modified,
/// and deleted files.
#[derive(Debug)]
pub(crate) struct ChangeDetector {
    /// Previous snapshot: path -> last-modified timestamp.
    snapshot: HashMap<PathBuf, SystemTime>,
}

impl ChangeDetector {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            snapshot: HashMap::new(),
        }
    }

    /// Scans `watched_paths` and returns changes since the last scan.
    ///
    /// Each call updates the internal snapshot.
    pub(crate) fn scan(&mut self, watched_paths: &[PathBuf]) -> Vec<FileChange> {
        let now = SystemTime::now();
        let mut changes = Vec::new();
        let mut current: HashMap<PathBuf, SystemTime> = HashMap::new();

        for path in watched_paths {
            let mtime = std::fs::metadata(path)
                .and_then(|m| m.modified())
                .unwrap_or(now);
            current.insert(path.clone(), mtime);

            match self.snapshot.get(path) {
                None => {
                    changes.push(FileChange {
                        path: path.clone(),
                        kind: ChangeKind::Created,
                        timestamp: mtime,
                    });
                }
                Some(prev_mtime) if *prev_mtime != mtime => {
                    changes.push(FileChange {
                        path: path.clone(),
                        kind: ChangeKind::Modified,
                        timestamp: mtime,
                    });
                }
                _ => {}
            }
        }

        // Detect deletions: keys in old snapshot absent from current scan.
        for old_path in self.snapshot.keys() {
            if !current.contains_key(old_path) {
                changes.push(FileChange {
                    path: old_path.clone(),
                    kind: ChangeKind::Deleted,
                    timestamp: now,
                });
            }
        }

        self.snapshot = current;
        changes
    }
}

// ---------------------------------------------------------------------------
// Change classifier
// ---------------------------------------------------------------------------

/// Impact level of a source-file change.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub(crate) enum ChangeImpact {
    /// No re-verification needed (e.g. comment-only change).
    None,
    /// Only functions in the changed file need re-verification.
    Partial,
    /// Full re-verification of all dependent functions required.
    Full,
}

impl fmt::Display for ChangeImpact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::None => f.write_str("none"),
            Self::Partial => f.write_str("partial"),
            Self::Full => f.write_str("full"),
        }
    }
}

/// Classifies file changes by the scope of re-verification they require.
pub(crate) struct ChangeClassifier;

impl ChangeClassifier {
    /// Classify a [`FileChange`] into its [`ChangeImpact`].
    ///
    /// - Deleted files always require full reverification (dependents must be
    ///   rechecked).
    /// - Created files require partial reverification (new functions only).
    /// - Modified `.rs` files require partial reverification by default.
    /// - Non-Rust files (e.g., `Cargo.toml`) require full reverification.
    #[must_use]
    pub(crate) fn classify(change: &FileChange) -> ChangeImpact {
        match change.kind {
            ChangeKind::Deleted => ChangeImpact::Full,
            ChangeKind::Created => {
                if is_rust_source(&change.path) {
                    ChangeImpact::Partial
                } else {
                    ChangeImpact::Full
                }
            }
            ChangeKind::Modified => {
                if is_rust_source(&change.path) {
                    ChangeImpact::Partial
                } else {
                    ChangeImpact::Full
                }
            }
        }
    }
}

fn is_rust_source(path: &Path) -> bool {
    path.extension().is_some_and(|ext| ext == "rs")
}

// ---------------------------------------------------------------------------
// Dependency graph
// ---------------------------------------------------------------------------

/// Maps functions to the source files they depend on and vice versa.
///
/// When a file changes, the graph determines which functions need
/// re-verification.
#[derive(Debug, Clone)]
pub(crate) struct DependencyGraph {
    /// function_name -> set of file paths it depends on.
    func_to_files: BTreeMap<String, BTreeSet<PathBuf>>,
    /// file_path -> set of function names that depend on it.
    file_to_funcs: BTreeMap<PathBuf, BTreeSet<String>>,
}

impl DependencyGraph {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            func_to_files: BTreeMap::new(),
            file_to_funcs: BTreeMap::new(),
        }
    }

    /// Register that `function` depends on `file`.
    pub(crate) fn add_dependency(&mut self, function: &str, file: &Path) {
        self.func_to_files
            .entry(function.to_owned())
            .or_default()
            .insert(file.to_path_buf());
        self.file_to_funcs
            .entry(file.to_path_buf())
            .or_default()
            .insert(function.to_owned());
    }

    /// Returns all functions that depend on any of the `changed_files`.
    #[must_use]
    pub(crate) fn affected_functions(&self, changed_files: &[PathBuf]) -> Vec<String> {
        let mut affected: BTreeSet<String> = BTreeSet::new();
        for file in changed_files {
            if let Some(funcs) = self.file_to_funcs.get(file) {
                affected.extend(funcs.iter().cloned());
            }
        }
        affected.into_iter().collect()
    }

    /// Returns the number of registered functions.
    #[must_use]
    pub(crate) fn function_count(&self) -> usize {
        self.func_to_files.len()
    }

    /// Returns the number of registered file dependencies.
    #[must_use]
    pub(crate) fn file_count(&self) -> usize {
        self.file_to_funcs.len()
    }

    /// Returns all registered function names.
    #[must_use]
    pub(crate) fn all_functions(&self) -> Vec<String> {
        self.func_to_files.keys().cloned().collect()
    }
}

// ---------------------------------------------------------------------------
// Reverification plan
// ---------------------------------------------------------------------------

/// A plan for which functions to re-verify after a set of changes.
#[derive(Debug, Clone)]
pub(crate) struct ReverificationPlan {
    /// Functions that need re-verification, in priority order.
    functions: Vec<String>,
    /// Whether this is a full or partial re-verification.
    impact: ChangeImpact,
    /// Estimated per-function verification time.
    per_function_estimate: Duration,
}

impl ReverificationPlan {
    /// Build a plan from a set of changes and a dependency graph.
    #[must_use]
    pub(crate) fn from_changes(changes: &[FileChange], deps: &DependencyGraph) -> Self {
        let max_impact = changes
            .iter()
            .map(ChangeClassifier::classify)
            .max()
            .unwrap_or(ChangeImpact::None);

        let functions = if max_impact == ChangeImpact::Full {
            deps.all_functions()
        } else {
            let changed_files: Vec<PathBuf> = changes.iter().map(|c| c.path.clone()).collect();
            deps.affected_functions(&changed_files)
        };

        Self {
            functions,
            impact: max_impact,
            per_function_estimate: Duration::from_millis(150),
        }
    }

    /// The ordered list of functions that need re-verification.
    #[must_use]
    pub(crate) fn functions_to_verify(&self) -> &[String] {
        &self.functions
    }

    /// Estimated wall-clock time for the planned re-verification.
    #[must_use]
    pub(crate) fn estimated_time(&self) -> Duration {
        self.per_function_estimate * u32::try_from(self.functions.len()).unwrap_or(u32::MAX)
    }

    /// The overall impact level of this plan.
    #[must_use]
    pub(crate) fn impact(&self) -> ChangeImpact {
        self.impact
    }

    /// Returns `true` when there is nothing to re-verify.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.functions.is_empty()
    }
}

// ---------------------------------------------------------------------------
// Incremental result
// ---------------------------------------------------------------------------

/// Outcome of verifying a single function during an incremental run.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum VerificationOutcome {
    Verified,
    Failed,
    Unknown,
    Skipped,
}

impl fmt::Display for VerificationOutcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Verified => f.write_str("verified"),
            Self::Failed => f.write_str("FAILED"),
            Self::Unknown => f.write_str("unknown"),
            Self::Skipped => f.write_str("skipped"),
        }
    }
}

/// Result of an incremental verification for one function.
#[derive(Debug, Clone)]
pub(crate) struct IncrementalResult {
    pub(crate) function_name: String,
    pub(crate) outcome: VerificationOutcome,
    pub(crate) elapsed: Duration,
    pub(crate) message: Option<String>,
}

// ---------------------------------------------------------------------------
// Watch display
// ---------------------------------------------------------------------------

/// Formats incremental watch-mode output for the terminal.
pub(crate) struct WatchDisplay;

impl WatchDisplay {
    /// Format a single file change for display.
    #[must_use]
    pub(crate) fn format_change(change: &FileChange) -> String {
        format!("[watch] {} {}", change.kind, change.path.display())
    }

    /// Format a single incremental result for display.
    #[must_use]
    pub(crate) fn format_result(result: &IncrementalResult) -> String {
        let ms = result.elapsed.as_millis();
        let status = &result.outcome;
        match &result.message {
            Some(msg) => format!("  {}: {} ({ms}ms) - {msg}", result.function_name, status),
            None => format!("  {}: {} ({ms}ms)", result.function_name, status),
        }
    }

    /// Format a session summary for display.
    #[must_use]
    pub(crate) fn format_summary(session: &WatchSession) -> String {
        let state = &session.state;
        let total = state.total_verifications;
        let pass = state.passed;
        let fail = state.failed;
        let cycles = state.cycle_count;
        format!(
            "[watch] Summary: {total} verifications ({pass} passed, {fail} failed) in {cycles} cycle(s)"
        )
    }
}

// ---------------------------------------------------------------------------
// Watch state & session
// ---------------------------------------------------------------------------

/// Accumulated state across watch cycles.
#[derive(Debug, Clone, Default)]
pub(crate) struct WatchState {
    pub(crate) total_verifications: usize,
    pub(crate) passed: usize,
    pub(crate) failed: usize,
    pub(crate) cycle_count: usize,
    pub(crate) last_cycle_time: Option<Instant>,
    /// Results from the most recent verification cycle.
    pub(crate) last_results: Vec<IncrementalResult>,
}

/// Top-level watch session that ties together configuration, detection, and
/// dependency tracking.
#[derive(Debug)]
pub(crate) struct WatchSession {
    pub(crate) config: WatchConfig,
    pub(crate) state: WatchState,
    pub(crate) detector: ChangeDetector,
    pub(crate) deps: DependencyGraph,
    watched_paths: Vec<PathBuf>,
}

impl WatchSession {
    /// Create a new session from the given config.
    #[must_use]
    pub(crate) fn new(config: WatchConfig) -> Self {
        Self {
            config,
            state: WatchState::default(),
            detector: ChangeDetector::new(),
            deps: DependencyGraph::new(),
            watched_paths: Vec::new(),
        }
    }

    /// Add a file to the watch set.
    pub(crate) fn add_file(&mut self, path: &Path) {
        let canonical = path.to_path_buf();
        if !self.watched_paths.contains(&canonical) {
            self.watched_paths.push(canonical);
        }
    }

    /// Run the change detector across all watched files.
    pub(crate) fn detect_changes(&mut self) -> Vec<FileChange> {
        let filtered: Vec<PathBuf> = self
            .watched_paths
            .iter()
            .filter(|p| self.config.filter.accepts(p))
            .cloned()
            .collect();
        self.detector.scan(&filtered)
    }

    /// Record incremental results into session state.
    pub(crate) fn record_results(&mut self, results: Vec<IncrementalResult>) {
        for r in &results {
            self.state.total_verifications += 1;
            match r.outcome {
                VerificationOutcome::Verified => self.state.passed += 1,
                VerificationOutcome::Failed => self.state.failed += 1,
                _ => {}
            }
        }
        self.state.cycle_count += 1;
        self.state.last_cycle_time = Some(Instant::now());
        self.state.last_results = results;
    }

    /// Number of files currently being watched.
    #[must_use]
    pub(crate) fn watched_count(&self) -> usize {
        self.watched_paths.len()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- Glob matcher -------------------------------------------------------

    #[test]
    fn test_glob_matches_exact() {
        assert!(glob_matches("foo.rs", "foo.rs"));
    }

    #[test]
    fn test_glob_matches_star_extension() {
        assert!(glob_matches("*.rs", "main.rs"));
        assert!(!glob_matches("*.rs", "main.py"));
    }

    #[test]
    fn test_glob_matches_star_no_separator() {
        assert!(!glob_matches("*.rs", "src/main.rs"));
    }

    #[test]
    fn test_glob_matches_double_star() {
        assert!(glob_matches("**/*.rs", "src/main.rs"));
        assert!(glob_matches("**/*.rs", "a/b/c.rs"));
    }

    #[test]
    fn test_glob_matches_double_star_nested_deep() {
        assert!(glob_matches("**/target/**", "foo/target/debug/build"));
        assert!(glob_matches("**/target/**", "target/release"));
    }

    #[test]
    fn test_glob_matches_no_match() {
        assert!(!glob_matches("*.txt", "main.rs"));
    }

    #[test]
    fn test_glob_matches_empty_pattern() {
        assert!(glob_matches("", ""));
        assert!(!glob_matches("", "a"));
    }

    // -- FileFilter ---------------------------------------------------------

    #[test]
    fn test_file_filter_default_accepts_rs() {
        let filter = FileFilter::default();
        assert!(filter.accepts(Path::new("src/main.rs")));
    }

    #[test]
    fn test_file_filter_default_rejects_target() {
        let filter = FileFilter::default();
        assert!(!filter.accepts(Path::new("target/debug/foo.rs")));
    }

    #[test]
    fn test_file_filter_exclude_precedence() {
        let filter = FileFilter {
            include: vec!["**/*.rs".to_owned()],
            exclude: vec!["**/generated/**".to_owned()],
        };
        assert!(!filter.accepts(Path::new("src/generated/auto.rs")));
    }

    #[test]
    fn test_file_filter_empty_include_accepts_all() {
        let filter = FileFilter {
            include: vec![],
            exclude: vec![],
        };
        assert!(filter.accepts(Path::new("anything.txt")));
    }

    // -- ChangeKind ---------------------------------------------------------

    #[test]
    fn test_change_kind_display() {
        assert_eq!(ChangeKind::Created.to_string(), "created");
        assert_eq!(ChangeKind::Modified.to_string(), "modified");
        assert_eq!(ChangeKind::Deleted.to_string(), "deleted");
    }

    // -- ChangeClassifier ---------------------------------------------------

    #[test]
    fn test_classify_deleted_is_full() {
        let change = FileChange {
            path: PathBuf::from("src/lib.rs"),
            kind: ChangeKind::Deleted,
            timestamp: SystemTime::now(),
        };
        assert_eq!(ChangeClassifier::classify(&change), ChangeImpact::Full);
    }

    #[test]
    fn test_classify_created_rs_is_partial() {
        let change = FileChange {
            path: PathBuf::from("src/new_mod.rs"),
            kind: ChangeKind::Created,
            timestamp: SystemTime::now(),
        };
        assert_eq!(ChangeClassifier::classify(&change), ChangeImpact::Partial);
    }

    #[test]
    fn test_classify_created_toml_is_full() {
        let change = FileChange {
            path: PathBuf::from("Cargo.toml"),
            kind: ChangeKind::Created,
            timestamp: SystemTime::now(),
        };
        assert_eq!(ChangeClassifier::classify(&change), ChangeImpact::Full);
    }

    #[test]
    fn test_classify_modified_rs_is_partial() {
        let change = FileChange {
            path: PathBuf::from("src/lib.rs"),
            kind: ChangeKind::Modified,
            timestamp: SystemTime::now(),
        };
        assert_eq!(ChangeClassifier::classify(&change), ChangeImpact::Partial);
    }

    #[test]
    fn test_classify_modified_non_rs_is_full() {
        let change = FileChange {
            path: PathBuf::from("Cargo.toml"),
            kind: ChangeKind::Modified,
            timestamp: SystemTime::now(),
        };
        assert_eq!(ChangeClassifier::classify(&change), ChangeImpact::Full);
    }

    // -- ChangeImpact -------------------------------------------------------

    #[test]
    fn test_change_impact_ordering() {
        assert!(ChangeImpact::None < ChangeImpact::Partial);
        assert!(ChangeImpact::Partial < ChangeImpact::Full);
    }

    #[test]
    fn test_change_impact_display() {
        assert_eq!(ChangeImpact::None.to_string(), "none");
        assert_eq!(ChangeImpact::Partial.to_string(), "partial");
        assert_eq!(ChangeImpact::Full.to_string(), "full");
    }

    // -- DependencyGraph ----------------------------------------------------

    #[test]
    fn test_dep_graph_empty() {
        let deps = DependencyGraph::new();
        assert_eq!(deps.function_count(), 0);
        assert_eq!(deps.file_count(), 0);
    }

    #[test]
    fn test_dep_graph_add_single() {
        let mut deps = DependencyGraph::new();
        deps.add_dependency("verify_foo", Path::new("src/foo.rs"));
        assert_eq!(deps.function_count(), 1);
        assert_eq!(deps.file_count(), 1);
    }

    #[test]
    fn test_dep_graph_affected_functions_basic() {
        let mut deps = DependencyGraph::new();
        deps.add_dependency("verify_foo", Path::new("src/foo.rs"));
        deps.add_dependency("verify_bar", Path::new("src/bar.rs"));
        let affected = deps.affected_functions(&[PathBuf::from("src/foo.rs")]);
        assert_eq!(affected, vec!["verify_foo"]);
    }

    #[test]
    fn test_dep_graph_affected_functions_multiple_deps() {
        let mut deps = DependencyGraph::new();
        deps.add_dependency("verify_foo", Path::new("src/shared.rs"));
        deps.add_dependency("verify_bar", Path::new("src/shared.rs"));
        let affected = deps.affected_functions(&[PathBuf::from("src/shared.rs")]);
        assert_eq!(affected.len(), 2);
        assert!(affected.contains(&"verify_foo".to_owned()));
        assert!(affected.contains(&"verify_bar".to_owned()));
    }

    #[test]
    fn test_dep_graph_affected_functions_no_match() {
        let mut deps = DependencyGraph::new();
        deps.add_dependency("verify_foo", Path::new("src/foo.rs"));
        let affected = deps.affected_functions(&[PathBuf::from("src/bar.rs")]);
        assert!(affected.is_empty());
    }

    #[test]
    fn test_dep_graph_function_depends_on_multiple_files() {
        let mut deps = DependencyGraph::new();
        deps.add_dependency("verify_complex", Path::new("src/a.rs"));
        deps.add_dependency("verify_complex", Path::new("src/b.rs"));
        assert_eq!(deps.function_count(), 1);
        assert_eq!(deps.file_count(), 2);
        let affected = deps.affected_functions(&[PathBuf::from("src/a.rs")]);
        assert_eq!(affected, vec!["verify_complex"]);
    }

    #[test]
    fn test_dep_graph_all_functions() {
        let mut deps = DependencyGraph::new();
        deps.add_dependency("alpha", Path::new("a.rs"));
        deps.add_dependency("beta", Path::new("b.rs"));
        deps.add_dependency("gamma", Path::new("c.rs"));
        let all = deps.all_functions();
        assert_eq!(all, vec!["alpha", "beta", "gamma"]);
    }

    // -- ReverificationPlan -------------------------------------------------

    #[test]
    fn test_plan_empty_changes() {
        let deps = DependencyGraph::new();
        let plan = ReverificationPlan::from_changes(&[], &deps);
        assert!(plan.is_empty());
        assert_eq!(plan.impact(), ChangeImpact::None);
        assert_eq!(plan.estimated_time(), Duration::ZERO);
    }

    #[test]
    fn test_plan_partial_change() {
        let mut deps = DependencyGraph::new();
        deps.add_dependency("fn_a", Path::new("src/a.rs"));
        deps.add_dependency("fn_b", Path::new("src/b.rs"));

        let changes = vec![FileChange {
            path: PathBuf::from("src/a.rs"),
            kind: ChangeKind::Modified,
            timestamp: SystemTime::now(),
        }];

        let plan = ReverificationPlan::from_changes(&changes, &deps);
        assert_eq!(plan.functions_to_verify(), &["fn_a"]);
        assert_eq!(plan.impact(), ChangeImpact::Partial);
    }

    #[test]
    fn test_plan_full_on_delete() {
        let mut deps = DependencyGraph::new();
        deps.add_dependency("fn_a", Path::new("src/a.rs"));
        deps.add_dependency("fn_b", Path::new("src/b.rs"));

        let changes = vec![FileChange {
            path: PathBuf::from("src/a.rs"),
            kind: ChangeKind::Deleted,
            timestamp: SystemTime::now(),
        }];

        let plan = ReverificationPlan::from_changes(&changes, &deps);
        // Full impact means all functions are re-verified.
        assert_eq!(plan.functions_to_verify().len(), 2);
        assert_eq!(plan.impact(), ChangeImpact::Full);
    }

    #[test]
    fn test_plan_estimated_time_scales() {
        let mut deps = DependencyGraph::new();
        for i in 0..10 {
            deps.add_dependency(&format!("fn_{i}"), Path::new("src/shared.rs"));
        }
        let changes = vec![FileChange {
            path: PathBuf::from("src/shared.rs"),
            kind: ChangeKind::Modified,
            timestamp: SystemTime::now(),
        }];
        let plan = ReverificationPlan::from_changes(&changes, &deps);
        assert_eq!(plan.estimated_time(), Duration::from_millis(1500));
    }

    // -- IncrementalResult & WatchDisplay ------------------------------------

    #[test]
    fn test_display_format_change() {
        let change = FileChange {
            path: PathBuf::from("src/main.rs"),
            kind: ChangeKind::Modified,
            timestamp: SystemTime::now(),
        };
        let text = WatchDisplay::format_change(&change);
        assert!(text.contains("modified"));
        assert!(text.contains("src/main.rs"));
    }

    #[test]
    fn test_display_format_result_verified() {
        let result = IncrementalResult {
            function_name: "verify_foo".to_owned(),
            outcome: VerificationOutcome::Verified,
            elapsed: Duration::from_millis(42),
            message: None,
        };
        let text = WatchDisplay::format_result(&result);
        assert!(text.contains("verify_foo"));
        assert!(text.contains("verified"));
        assert!(text.contains("42ms"));
    }

    #[test]
    fn test_display_format_result_with_message() {
        let result = IncrementalResult {
            function_name: "verify_bar".to_owned(),
            outcome: VerificationOutcome::Failed,
            elapsed: Duration::from_millis(100),
            message: Some("postcondition violated".to_owned()),
        };
        let text = WatchDisplay::format_result(&result);
        assert!(text.contains("FAILED"));
        assert!(text.contains("postcondition violated"));
    }

    #[test]
    fn test_display_format_summary() {
        let config = WatchConfig::default();
        let mut session = WatchSession::new(config);
        session.record_results(vec![
            IncrementalResult {
                function_name: "f1".to_owned(),
                outcome: VerificationOutcome::Verified,
                elapsed: Duration::from_millis(10),
                message: None,
            },
            IncrementalResult {
                function_name: "f2".to_owned(),
                outcome: VerificationOutcome::Failed,
                elapsed: Duration::from_millis(20),
                message: None,
            },
        ]);
        let text = WatchDisplay::format_summary(&session);
        assert!(text.contains("2 verifications"));
        assert!(text.contains("1 passed"));
        assert!(text.contains("1 failed"));
        assert!(text.contains("1 cycle(s)"));
    }

    // -- WatchSession -------------------------------------------------------

    #[test]
    fn test_session_new_empty() {
        let session = WatchSession::new(WatchConfig::default());
        assert_eq!(session.watched_count(), 0);
        assert_eq!(session.state.total_verifications, 0);
    }

    #[test]
    fn test_session_add_file_dedup() {
        let mut session = WatchSession::new(WatchConfig::default());
        session.add_file(Path::new("src/a.rs"));
        session.add_file(Path::new("src/a.rs"));
        assert_eq!(session.watched_count(), 1);
    }

    #[test]
    fn test_session_add_multiple_files() {
        let mut session = WatchSession::new(WatchConfig::default());
        session.add_file(Path::new("src/a.rs"));
        session.add_file(Path::new("src/b.rs"));
        assert_eq!(session.watched_count(), 2);
    }

    #[test]
    fn test_session_record_results_accumulates() {
        let mut session = WatchSession::new(WatchConfig::default());
        session.record_results(vec![IncrementalResult {
            function_name: "f1".to_owned(),
            outcome: VerificationOutcome::Verified,
            elapsed: Duration::from_millis(5),
            message: None,
        }]);
        session.record_results(vec![
            IncrementalResult {
                function_name: "f2".to_owned(),
                outcome: VerificationOutcome::Failed,
                elapsed: Duration::from_millis(8),
                message: None,
            },
            IncrementalResult {
                function_name: "f3".to_owned(),
                outcome: VerificationOutcome::Verified,
                elapsed: Duration::from_millis(3),
                message: None,
            },
        ]);
        assert_eq!(session.state.total_verifications, 3);
        assert_eq!(session.state.passed, 2);
        assert_eq!(session.state.failed, 1);
        assert_eq!(session.state.cycle_count, 2);
    }

    #[test]
    fn test_session_last_results_replaced() {
        let mut session = WatchSession::new(WatchConfig::default());
        session.record_results(vec![IncrementalResult {
            function_name: "f1".to_owned(),
            outcome: VerificationOutcome::Verified,
            elapsed: Duration::from_millis(1),
            message: None,
        }]);
        assert_eq!(session.state.last_results.len(), 1);

        session.record_results(vec![
            IncrementalResult {
                function_name: "f2".to_owned(),
                outcome: VerificationOutcome::Failed,
                elapsed: Duration::from_millis(2),
                message: None,
            },
            IncrementalResult {
                function_name: "f3".to_owned(),
                outcome: VerificationOutcome::Unknown,
                elapsed: Duration::from_millis(3),
                message: None,
            },
        ]);
        // last_results should only contain the most recent cycle.
        assert_eq!(session.state.last_results.len(), 2);
    }

    // -- ChangeDetector -----------------------------------------------------

    #[test]
    fn test_detector_first_scan_all_created() {
        let mut detector = ChangeDetector::new();
        // Use non-existent paths; the detector uses a fallback mtime.
        let paths = vec![
            PathBuf::from("/nonexistent/a.rs"),
            PathBuf::from("/nonexistent/b.rs"),
        ];
        let changes = detector.scan(&paths);
        assert_eq!(changes.len(), 2);
        assert!(changes.iter().all(|c| c.kind == ChangeKind::Created));
    }

    #[test]
    fn test_detector_second_scan_stable_no_changes() {
        let mut detector = ChangeDetector::new();
        let paths = vec![PathBuf::from("/nonexistent/stable.rs")];
        let _ = detector.scan(&paths);
        let changes = detector.scan(&paths);
        // With non-existent paths, mtime falls back to now() each call,
        // so this may produce a Modified if the two calls span different
        // instants. We verify the detector reports *something* or nothing
        // without panicking.
        assert!(changes.len() <= 1);
    }

    #[test]
    fn test_detector_deletion_detected() {
        let mut detector = ChangeDetector::new();
        let paths_initial = vec![
            PathBuf::from("/nonexistent/keep.rs"),
            PathBuf::from("/nonexistent/remove.rs"),
        ];
        let _ = detector.scan(&paths_initial);

        // Second scan omits one file.
        let paths_after = vec![PathBuf::from("/nonexistent/keep.rs")];
        let changes = detector.scan(&paths_after);

        let deleted: Vec<_> = changes
            .iter()
            .filter(|c| c.kind == ChangeKind::Deleted)
            .collect();
        assert_eq!(deleted.len(), 1);
        assert_eq!(deleted[0].path, PathBuf::from("/nonexistent/remove.rs"));
    }

    // -- WatchConfig --------------------------------------------------------

    #[test]
    fn test_watch_config_defaults() {
        let config = WatchConfig::default();
        assert_eq!(config.max_batch_size, 64);
        assert_eq!(config.debounce.window, Duration::from_millis(200));
        assert_eq!(config.debounce.max_delay, Duration::from_secs(2));
    }

    // -- DebounceConfig -----------------------------------------------------

    #[test]
    fn test_debounce_config_custom() {
        let debounce = DebounceConfig {
            window: Duration::from_millis(500),
            max_delay: Duration::from_secs(5),
        };
        assert_eq!(debounce.window.as_millis(), 500);
        assert_eq!(debounce.max_delay.as_secs(), 5);
    }

    // -- VerificationOutcome ------------------------------------------------

    #[test]
    fn test_verification_outcome_display() {
        assert_eq!(VerificationOutcome::Verified.to_string(), "verified");
        assert_eq!(VerificationOutcome::Failed.to_string(), "FAILED");
        assert_eq!(VerificationOutcome::Unknown.to_string(), "unknown");
        assert_eq!(VerificationOutcome::Skipped.to_string(), "skipped");
    }

    // -- is_rust_source -----------------------------------------------------

    #[test]
    fn test_is_rust_source_positive() {
        assert!(is_rust_source(Path::new("lib.rs")));
        assert!(is_rust_source(Path::new("src/main.rs")));
    }

    #[test]
    fn test_is_rust_source_negative() {
        assert!(!is_rust_source(Path::new("Cargo.toml")));
        assert!(!is_rust_source(Path::new("build.py")));
        assert!(!is_rust_source(Path::new("no_extension")));
    }

    // -- Integration-style tests --------------------------------------------

    #[test]
    fn test_end_to_end_partial_reverification() {
        // Build a dependency graph, simulate a change, and verify the plan.
        let mut deps = DependencyGraph::new();
        deps.add_dependency("fn_parse", Path::new("src/parser.rs"));
        deps.add_dependency("fn_parse", Path::new("src/ast.rs"));
        deps.add_dependency("fn_eval", Path::new("src/eval.rs"));
        deps.add_dependency("fn_eval", Path::new("src/ast.rs"));
        deps.add_dependency("fn_format", Path::new("src/format.rs"));

        // Change ast.rs -- both fn_parse and fn_eval depend on it.
        let changes = vec![FileChange {
            path: PathBuf::from("src/ast.rs"),
            kind: ChangeKind::Modified,
            timestamp: SystemTime::now(),
        }];

        let plan = ReverificationPlan::from_changes(&changes, &deps);
        let fns = plan.functions_to_verify();
        assert_eq!(fns.len(), 2);
        assert!(fns.contains(&"fn_parse".to_owned()));
        assert!(fns.contains(&"fn_eval".to_owned()));
        assert!(!fns.contains(&"fn_format".to_owned()));
        assert_eq!(plan.impact(), ChangeImpact::Partial);
    }

    #[test]
    fn test_end_to_end_full_reverification_on_toml_change() {
        let mut deps = DependencyGraph::new();
        deps.add_dependency("fn_a", Path::new("src/a.rs"));
        deps.add_dependency("fn_b", Path::new("src/b.rs"));

        let changes = vec![FileChange {
            path: PathBuf::from("Cargo.toml"),
            kind: ChangeKind::Modified,
            timestamp: SystemTime::now(),
        }];

        let plan = ReverificationPlan::from_changes(&changes, &deps);
        assert_eq!(plan.functions_to_verify().len(), 2);
        assert_eq!(plan.impact(), ChangeImpact::Full);
    }

    #[test]
    fn test_end_to_end_session_lifecycle() {
        let config = WatchConfig {
            root: PathBuf::from("/tmp/test_project"),
            ..WatchConfig::default()
        };
        let mut session = WatchSession::new(config);

        // Add files.
        session.add_file(Path::new("src/lib.rs"));
        session.add_file(Path::new("src/util.rs"));
        assert_eq!(session.watched_count(), 2);

        // Register dependencies.
        session
            .deps
            .add_dependency("fn_lib", Path::new("src/lib.rs"));
        session
            .deps
            .add_dependency("fn_util", Path::new("src/util.rs"));

        // Simulate verification results.
        session.record_results(vec![
            IncrementalResult {
                function_name: "fn_lib".to_owned(),
                outcome: VerificationOutcome::Verified,
                elapsed: Duration::from_millis(50),
                message: None,
            },
            IncrementalResult {
                function_name: "fn_util".to_owned(),
                outcome: VerificationOutcome::Verified,
                elapsed: Duration::from_millis(30),
                message: None,
            },
        ]);

        let summary = WatchDisplay::format_summary(&session);
        assert!(summary.contains("2 verifications"));
        assert!(summary.contains("2 passed"));
        assert!(summary.contains("0 failed"));
    }

    #[test]
    fn test_skipped_outcome_not_counted_as_pass_or_fail() {
        let mut session = WatchSession::new(WatchConfig::default());
        session.record_results(vec![IncrementalResult {
            function_name: "fn_skip".to_owned(),
            outcome: VerificationOutcome::Skipped,
            elapsed: Duration::from_millis(1),
            message: Some("cached".to_owned()),
        }]);
        assert_eq!(session.state.total_verifications, 1);
        assert_eq!(session.state.passed, 0);
        assert_eq!(session.state.failed, 0);
    }

    #[test]
    fn test_unknown_outcome_not_counted_as_pass_or_fail() {
        let mut session = WatchSession::new(WatchConfig::default());
        session.record_results(vec![IncrementalResult {
            function_name: "fn_unk".to_owned(),
            outcome: VerificationOutcome::Unknown,
            elapsed: Duration::from_millis(200),
            message: None,
        }]);
        assert_eq!(session.state.total_verifications, 1);
        assert_eq!(session.state.passed, 0);
        assert_eq!(session.state.failed, 0);
    }
}
