//! Crate-local mode index — recursive source scanning for canonical function paths.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Builds a cached index of every function in the current crate, recording its
//! canonical crate-relative path and mode (exec/proof/spec). This enables
//! mode validation for qualified call paths like `self::helper()`,
//! `crate::specs::foo()`, and `super::proofs::lemma()`.
//!
//! Part of #2066.

use crate::mode::FunctionMode;
use crate::mode_attrs;
use crate::source_tree;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, OnceLock};

/// Canonical crate-relative function path segments (e.g., `["specs", "helper"]`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CanonicalFnPath(pub Vec<String>);

impl CanonicalFnPath {
    /// The tail function name (last segment).
    #[cfg(test)]
    pub(crate) fn fn_name(&self) -> &str {
        self.0.last().map(|s| s.as_str()).unwrap_or("")
    }
}

/// A function discovered in the crate source tree.
#[derive(Debug, Clone)]
pub(crate) struct IndexedFn {
    pub mode: FunctionMode,
}

/// Index of all functions in a crate, keyed by canonical path.
#[derive(Debug, Clone)]
pub(crate) struct CrateModeIndex {
    /// All functions keyed by canonical path.
    functions: HashMap<CanonicalFnPath, IndexedFn>,
    /// Reverse index: function tail name → list of canonical paths.
    #[cfg(test)]
    by_name: HashMap<String, Vec<CanonicalFnPath>>,
}

impl CrateModeIndex {
    /// Looks up a function by its exact canonical path.
    pub(crate) fn lookup(&self, path: &CanonicalFnPath) -> Option<&IndexedFn> {
        self.functions.get(path)
    }

    /// Looks up all functions with a given tail name.
    #[cfg(test)]
    pub(crate) fn lookup_by_name(&self, name: &str) -> &[CanonicalFnPath] {
        self.by_name.get(name).map(|v| v.as_slice()).unwrap_or(&[])
    }

    /// Finds a method with the given name in any impl block within the module.
    /// Returns the first match. For recursion detection, false positives
    /// (detecting recursion that isn't there) are safe — they inject
    /// unnecessary decrease checks but cannot miss real recursion.
    /// Used for resolving single-segment method calls (e.g., `recurse(n-1)`)
    /// to type-scoped canonical paths (e.g., `["mod", "Tree", "recurse"]`).
    /// Fix for #2550 finding F1.
    #[allow(clippy::indexing_slicing)] // path.0[..module_path.len()] is only sliced after confirming path.0.len() == module_path.len() + 2
    pub(crate) fn lookup_method_in_module(
        &self,
        method_name: &str,
        module_path: &[String],
    ) -> Option<CanonicalFnPath> {
        // Look for paths like [module..., TypeName, method_name]
        // where TypeName is a single segment between the module and the method.
        self.functions
            .keys()
            .find(|path| {
                path.0.last().map(|s| s.as_str()) == Some(method_name)
                    && path.0.len() == module_path.len() + 2
                    && path.0[..module_path.len()] == *module_path
            })
            .cloned()
    }

    /// Builds an index from a list of (path, mode) entries. Test-only.
    #[cfg(test)]
    pub(crate) fn from_entries(entries: &[(&[&str], FunctionMode)]) -> Self {
        let mut functions = HashMap::new();
        let mut by_name: HashMap<String, Vec<CanonicalFnPath>> = HashMap::new();
        for (path, mode) in entries {
            let segs: Vec<String> = path.iter().map(|s| s.to_string()).collect();
            let canonical = CanonicalFnPath(segs);
            let name = canonical.fn_name().to_string();
            by_name.entry(name).or_default().push(canonical.clone());
            functions.insert(canonical, IndexedFn { mode: *mode });
        }
        Self { functions, by_name }
    }
}

// ========================================================================
// Process-local cache
// ========================================================================

static MODE_INDEX_CACHE: OnceLock<Mutex<HashMap<PathBuf, Arc<CrateModeIndex>>>> = OnceLock::new();

fn cache() -> &'static Mutex<HashMap<PathBuf, Arc<CrateModeIndex>>> {
    MODE_INDEX_CACHE.get_or_init(|| Mutex::new(HashMap::new()))
}

/// Returns the crate mode index for the given crate root, building and
/// caching it on first access.
pub(crate) fn get_or_build_index(crate_root: &Path) -> Option<Arc<CrateModeIndex>> {
    let mut map = cache().lock().ok()?;
    if let Some(idx) = map.get(crate_root) {
        return Some(Arc::clone(idx));
    }
    let idx = build_index(crate_root)?;
    let arc = Arc::new(idx);
    map.insert(crate_root.to_path_buf(), Arc::clone(&arc));
    Some(arc)
}

/// Clears the cache. Used in tests.
#[cfg(test)]
pub(crate) fn clear_cache() {
    if let Some(map) = MODE_INDEX_CACHE.get() {
        if let Ok(mut map) = map.lock() {
            map.clear();
        }
    }
}

// ========================================================================
// Crate root discovery
// ========================================================================

/// Discovers the crate root file from a source file path.
///
/// - If the file is itself a crate root (`src/lib.rs`, `src/main.rs`,
///   `tests/*.rs`, `examples/*.rs`, `benches/*.rs`, `src/bin/*.rs`), return it.
/// - Otherwise, walk up from the file to find `src/lib.rs` or `src/main.rs`.
/// - For trybuild single-file fixtures (no `src/` parent), the file itself
///   is the crate root.
pub(crate) fn discover_crate_root(source_file: &Path) -> Option<PathBuf> {
    let canonical = source_file.canonicalize().ok()?;

    // Check if the file is already a recognized crate root or test/example entry.
    if let Some(file_name) = canonical.file_name().and_then(|f| f.to_str()) {
        if let Some(parent) = canonical.parent() {
            let parent_name = parent.file_name().and_then(|f| f.to_str()).unwrap_or("");
            // src/lib.rs or src/main.rs
            if parent_name == "src" && (file_name == "lib.rs" || file_name == "main.rs") {
                return Some(canonical);
            }
            // src/bin/*.rs
            if parent_name == "bin" {
                if let Some(grandparent) = parent.parent() {
                    if grandparent
                        .file_name()
                        .and_then(|f| f.to_str())
                        .unwrap_or("")
                        == "src"
                    {
                        return Some(canonical);
                    }
                }
            }
            // tests/*.rs, examples/*.rs, benches/*.rs
            if matches!(parent_name, "tests" | "examples" | "benches") {
                return Some(canonical);
            }
        }
    }

    // Walk up to find src/lib.rs or src/main.rs
    let mut dir = canonical.parent()?;
    loop {
        if dir.file_name().and_then(|f| f.to_str()) == Some("src") {
            let lib = dir.join("lib.rs");
            if lib.exists() {
                return Some(lib);
            }
            let main = dir.join("main.rs");
            if main.exists() {
                return Some(main);
            }
        }
        match dir.parent() {
            Some(p) => dir = p,
            None => break,
        }
    }

    // Fallback: treat the file itself as the crate root (trybuild single-file).
    Some(canonical)
}

// ========================================================================
// Index building
// ========================================================================

/// Builds a `CrateModeIndex` by parsing the crate root and walking modules.
fn build_index(crate_root: &Path) -> Option<CrateModeIndex> {
    let mut functions = HashMap::new();

    source_tree::walk_crate_modules(crate_root, &mut |m| {
        for item in m.items {
            match item {
                syn::Item::Fn(item_fn) => {
                    let fn_name = item_fn.sig.ident.to_string();
                    let mut path_segs = m.module_path.to_vec();
                    path_segs.push(fn_name);
                    let canonical = CanonicalFnPath(path_segs);
                    let mode = mode_attrs::classify_item_fn(item_fn);
                    functions.insert(canonical, IndexedFn { mode });
                }
                // Index methods inside impl blocks with canonical path
                // [module..., TypeName, method_name]. Fix for #2550 finding F1.
                syn::Item::Impl(item_impl) => {
                    if let Some(type_name) = mode_attrs::extract_impl_type_name(&item_impl.self_ty)
                    {
                        let mut impl_path = m.module_path.to_vec();
                        impl_path.push(type_name);
                        for impl_item in &item_impl.items {
                            if let syn::ImplItem::Fn(method) = impl_item {
                                let method_name = method.sig.ident.to_string();
                                let mut path_segs = impl_path.clone();
                                path_segs.push(method_name);
                                let canonical = CanonicalFnPath(path_segs);
                                let mode = mode_attrs::classify_impl_method(method);
                                functions.insert(canonical, IndexedFn { mode });
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    })?;

    #[cfg(test)]
    let by_name = {
        let mut by_name: HashMap<String, Vec<CanonicalFnPath>> = HashMap::new();
        for path in functions.keys() {
            let name = path.fn_name().to_string();
            by_name.entry(name).or_default().push(path.clone());
        }
        by_name
    };

    Some(CrateModeIndex {
        functions,
        #[cfg(test)]
        by_name,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    /// Creates a unique temp directory for a test.
    fn test_dir(name: &str) -> PathBuf {
        let dir = std::env::temp_dir()
            .join("trust_vc_mode_index_tests")
            .join(name);
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).expect("create test dir");
        dir
    }

    // classify_item_fn / classify_impl_method tests moved to mode_attrs::tests.

    #[test]
    fn test_build_index_inline_modules() {
        let dir = test_dir("inline_modules");
        let root = dir.join("lib.rs");
        fs::write(
            &root,
            r#"
            fn top_exec() {}

            mod proofs {
                #[trust_vc::proof]
                fn my_lemma() {}
            }

            mod specs {
                #[trust_vc::spec]
                fn my_spec() -> i32 { 42 }
            }
            "#,
        )
        .expect("write");

        let idx = build_index(&root).expect("build_index");

        let top = idx.lookup(&CanonicalFnPath(vec!["top_exec".into()]));
        assert!(top.is_some());
        assert_eq!(top.unwrap().mode, FunctionMode::Exec);

        let proof = idx.lookup(&CanonicalFnPath(vec!["proofs".into(), "my_lemma".into()]));
        assert!(proof.is_some());
        assert_eq!(proof.unwrap().mode, FunctionMode::Proof);

        let spec = idx.lookup(&CanonicalFnPath(vec!["specs".into(), "my_spec".into()]));
        assert!(spec.is_some());
        assert_eq!(spec.unwrap().mode, FunctionMode::Spec);

        let lemma_paths = idx.lookup_by_name("my_lemma");
        assert_eq!(lemma_paths.len(), 1);
    }

    #[test]
    fn test_build_index_out_of_line_module() {
        let dir = test_dir("out_of_line");
        let root = dir.join("lib.rs");
        fs::write(&root, "mod helpers;\nfn main_fn() {}\n").expect("write root");
        fs::write(
            dir.join("helpers.rs"),
            "#[trust_vc::proof]\nfn helper_proof() {}\n",
        )
        .expect("write helpers");

        let idx = build_index(&root).expect("build_index");

        let proof = idx.lookup(&CanonicalFnPath(vec![
            "helpers".into(),
            "helper_proof".into(),
        ]));
        assert!(proof.is_some());
        assert_eq!(proof.unwrap().mode, FunctionMode::Proof);
    }

    #[test]
    fn test_discover_crate_root_src_lib() {
        let dir = test_dir("src_lib");
        let src = dir.join("src");
        fs::create_dir_all(&src).expect("mkdir");
        fs::write(src.join("lib.rs"), "").expect("write lib");
        let sub = src.join("sub");
        fs::create_dir_all(&sub).expect("mkdir sub");
        fs::write(sub.join("foo.rs"), "").expect("write foo");

        let root = discover_crate_root(&sub.join("foo.rs")).expect("discover");
        assert!(root.ends_with("lib.rs"), "expected lib.rs, got {:?}", root);
    }

    #[test]
    fn test_discover_crate_root_single_file() {
        let dir = test_dir("single_file");
        let file = dir.join("standalone.rs");
        fs::write(&file, "fn main() {}").expect("write");

        let root = discover_crate_root(&file).expect("discover");
        assert_eq!(root, file.canonicalize().unwrap());
    }

    /// #2550 F1: impl methods should be indexed with type-scoped canonical paths.
    #[test]
    fn test_build_index_impl_methods() {
        let dir = test_dir("impl_methods");
        let root = dir.join("lib.rs");
        fs::write(
            &root,
            r#"
            struct Tree;

            impl Tree {
                fn count(&self) -> u64 { 0 }

                #[trust_vc::proof]
                fn lemma_count(&self) {}
            }

            fn free_fn() {}
            "#,
        )
        .expect("write");

        let idx = build_index(&root).expect("build_index");

        // Free function at root level
        let free = idx.lookup(&CanonicalFnPath(vec!["free_fn".into()]));
        assert!(free.is_some(), "free_fn should be indexed");
        assert_eq!(free.unwrap().mode, FunctionMode::Exec);

        // Impl method: [TypeName, method_name]
        let count = idx.lookup(&CanonicalFnPath(vec!["Tree".into(), "count".into()]));
        assert!(count.is_some(), "Tree::count should be indexed");
        assert_eq!(count.unwrap().mode, FunctionMode::Exec);

        // Proof method in impl block
        let lemma = idx.lookup(&CanonicalFnPath(vec!["Tree".into(), "lemma_count".into()]));
        assert!(lemma.is_some(), "Tree::lemma_count should be indexed");
        assert_eq!(lemma.unwrap().mode, FunctionMode::Proof);
    }

    /// #2550 F1: lookup_method_in_module should find type-scoped methods.
    #[test]
    fn test_lookup_method_in_module() {
        let idx = CrateModeIndex::from_entries(&[
            (&["Tree", "count"], FunctionMode::Exec),
            (&["m", "Foo", "bar"], FunctionMode::Exec),
            (&["helper"], FunctionMode::Exec),
        ]);

        // Should find Tree::count in root module
        let result = idx.lookup_method_in_module("count", &[]);
        assert_eq!(
            result,
            Some(CanonicalFnPath(vec!["Tree".into(), "count".into()]))
        );

        // Should find m::Foo::bar in module "m"
        let result = idx.lookup_method_in_module("bar", &["m".into()]);
        assert_eq!(
            result,
            Some(CanonicalFnPath(vec![
                "m".into(),
                "Foo".into(),
                "bar".into()
            ]))
        );

        // Should NOT find helper (it's a free function, not a method)
        let result = idx.lookup_method_in_module("helper", &[]);
        assert!(result.is_none(), "helper is not a method in an impl block");

        // Should NOT find count in module "m"
        let result = idx.lookup_method_in_module("count", &["m".into()]);
        assert!(result.is_none(), "Tree::count is in root, not module m");
    }
}
