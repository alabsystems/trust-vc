//! Shared crate-source traversal — recursive module walk and file resolution.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Both `mode_index` and `recursion_graph` need to walk the crate's module tree.
//! This module provides the shared traversal so the logic lives in one place.
//!
//! Part of #2561.

use std::path::{Path, PathBuf};

/// A batch of items discovered during crate-source traversal.
pub(crate) struct ModuleItems<'a> {
    /// Module path segments relative to the crate root (e.g., `["specs", "helpers"]`).
    pub module_path: &'a [String],
    /// The parsed items in this module.
    pub items: &'a [syn::Item],
}

/// Walks the crate source tree starting from `crate_root`, calling `visit` for
/// each module's items (including the root).
///
/// Returns `None` if the crate root cannot be read or parsed.
pub(crate) fn walk_crate_modules(
    crate_root: &Path,
    visit: &mut impl FnMut(ModuleItems<'_>),
) -> Option<()> {
    let source = std::fs::read_to_string(crate_root).ok()?;
    let parsed = crate::parse_file_allow_tracked(&source).ok()?;
    let root_dir = crate_root.parent()?;
    walk_items_recursive(&parsed.items, &[], root_dir, visit);
    Some(())
}

/// Recursive descent through items, resolving out-of-line modules.
fn walk_items_recursive(
    items: &[syn::Item],
    module_path: &[String],
    current_dir: &Path,
    visit: &mut impl FnMut(ModuleItems<'_>),
) {
    // Surface this module's items to the caller.
    visit(ModuleItems { module_path, items });

    // Recurse into child modules.
    for item in items {
        if let syn::Item::Mod(item_mod) = item {
            let mod_name = item_mod.ident.to_string();
            let mut child_path = module_path.to_vec();
            child_path.push(mod_name.clone());

            if let Some((_, ref mod_items)) = item_mod.content {
                // Inline module: recurse directly.
                walk_items_recursive(mod_items, &child_path, current_dir, visit);
            } else {
                // Out-of-line module: resolve file and recurse.
                if let Some(file_path) = resolve_module_file(item_mod, current_dir, &mod_name) {
                    if let Ok(source) = std::fs::read_to_string(&file_path) {
                        if let Ok(parsed) = crate::parse_file_allow_tracked(&source) {
                            let child_dir = file_path.parent().unwrap_or(current_dir);
                            walk_items_recursive(&parsed.items, &child_path, child_dir, visit);
                        }
                    }
                }
            }
        }
    }
}

/// Resolves an out-of-line module to its source file.
///
/// Checks for `#[path = "..."]` attribute first, then standard resolution:
/// `mod_name.rs` or `mod_name/mod.rs`.
pub(crate) fn resolve_module_file(
    item_mod: &syn::ItemMod,
    current_dir: &Path,
    mod_name: &str,
) -> Option<PathBuf> {
    let explicit_path = item_mod.attrs.iter().find_map(|attr| {
        if attr.path().is_ident("path") {
            if let syn::Meta::NameValue(nv) = &attr.meta {
                if let syn::Expr::Lit(syn::ExprLit {
                    lit: syn::Lit::Str(s),
                    ..
                }) = &nv.value
                {
                    return Some(s.value());
                }
            }
        }
        None
    });

    if let Some(explicit) = explicit_path {
        let p = current_dir.join(&explicit);
        if p.exists() {
            return Some(p);
        }
        return None;
    }

    // Standard resolution: mod_name.rs or mod_name/mod.rs
    let direct = current_dir.join(format!("{mod_name}.rs"));
    if direct.exists() {
        return Some(direct);
    }
    let dir_mod = current_dir.join(mod_name).join("mod.rs");
    if dir_mod.exists() {
        return Some(dir_mod);
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    fn test_dir(name: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir()
            .join("trust_vc_source_tree_tests")
            .join(name);
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).expect("create test dir");
        dir
    }

    #[test]
    fn test_walk_inline_modules() {
        let dir = test_dir("inline");
        let root = dir.join("lib.rs");
        fs::write(
            &root,
            r#"
            fn top() {}
            mod sub {
                fn inner() {}
            }
            "#,
        )
        .unwrap();

        let mut visited = Vec::new();
        walk_crate_modules(&root, &mut |m| {
            let path: Vec<String> = m.module_path.to_vec();
            let count = m.items.len();
            visited.push((path, count));
        });

        assert!(visited.len() >= 2, "should visit root and sub module");
        assert!(visited[0].0.is_empty(), "root has empty module path");
        assert_eq!(visited[1].0, vec!["sub"]);
    }

    #[test]
    fn test_walk_out_of_line_module() {
        let dir = test_dir("out_of_line");
        let root = dir.join("lib.rs");
        fs::write(&root, "mod helpers;\nfn main_fn() {}\n").unwrap();
        fs::write(dir.join("helpers.rs"), "fn helper_fn() {}\n").unwrap();

        let mut modules = Vec::new();
        walk_crate_modules(&root, &mut |m| {
            modules.push(m.module_path.to_vec());
        });

        assert!(modules.contains(&vec!["helpers".to_string()]));
    }

    #[test]
    fn test_walk_directory_module() {
        let dir = test_dir("dir_module");
        let root = dir.join("lib.rs");
        fs::write(&root, "mod nested;\n").unwrap();
        fs::create_dir_all(dir.join("nested")).unwrap();
        fs::write(dir.join("nested").join("mod.rs"), "fn deep() {}\n").unwrap();

        let mut modules = Vec::new();
        walk_crate_modules(&root, &mut |m| {
            modules.push(m.module_path.to_vec());
        });

        assert!(modules.contains(&vec!["nested".to_string()]));
    }

    #[test]
    fn test_walk_path_attribute() {
        let dir = test_dir("path_attr");
        let root = dir.join("lib.rs");
        fs::write(&root, "#[path = \"alt.rs\"]\nmod renamed;\n").unwrap();
        fs::write(dir.join("alt.rs"), "fn alt_fn() {}\n").unwrap();

        let mut modules = Vec::new();
        walk_crate_modules(&root, &mut |m| {
            modules.push(m.module_path.to_vec());
        });

        assert!(modules.contains(&vec!["renamed".to_string()]));
    }

    #[test]
    fn test_resolve_module_file_standard() {
        let dir = test_dir("resolve_std");
        fs::write(dir.join("foo.rs"), "").unwrap();

        let item_mod: syn::ItemMod = syn::parse_quote! { mod foo; };
        let result = resolve_module_file(&item_mod, &dir, "foo");
        assert!(result.is_some());
        assert!(result.unwrap().ends_with("foo.rs"));
    }

    #[test]
    fn test_resolve_module_file_dir_mod() {
        let dir = test_dir("resolve_dir");
        fs::create_dir_all(dir.join("bar")).unwrap();
        fs::write(dir.join("bar").join("mod.rs"), "").unwrap();

        let item_mod: syn::ItemMod = syn::parse_quote! { mod bar; };
        let result = resolve_module_file(&item_mod, &dir, "bar");
        assert!(result.is_some());
        assert!(result.unwrap().ends_with("mod.rs"));
    }

    #[test]
    fn test_resolve_module_file_path_attr() {
        let dir = test_dir("resolve_path");
        fs::write(dir.join("custom.rs"), "").unwrap();

        let item_mod: syn::ItemMod = syn::parse_quote! {
            #[path = "custom.rs"]
            mod whatever;
        };
        let result = resolve_module_file(&item_mod, &dir, "whatever");
        assert!(result.is_some());
        assert!(result.unwrap().ends_with("custom.rs"));
    }

    #[test]
    fn test_resolve_module_file_not_found() {
        let dir = test_dir("resolve_missing");
        let item_mod: syn::ItemMod = syn::parse_quote! { mod nonexistent; };
        let result = resolve_module_file(&item_mod, &dir, "nonexistent");
        assert!(result.is_none());
    }

    #[test]
    fn test_walk_crate_modules_nonexistent_path_returns_none() {
        let dir = test_dir("nonexistent_root");
        let bogus = dir.join("does_not_exist.rs");
        let result = walk_crate_modules(&bogus, &mut |_| {
            panic!("visitor should never be called for a nonexistent file");
        });
        assert!(
            result.is_none(),
            "walk_crate_modules must return None for missing files"
        );
    }

    #[test]
    fn test_walk_crate_modules_unparseable_source_returns_none() {
        let dir = test_dir("unparseable");
        let root = dir.join("lib.rs");
        // Write syntactically invalid Rust that tokenizes but won't parse as a file.
        fs::write(&root, "fn {{{ not valid rust +++").unwrap();

        let result = walk_crate_modules(&root, &mut |_| {
            panic!("visitor should never be called for unparseable source");
        });
        assert!(
            result.is_none(),
            "walk_crate_modules must return None for unparseable source"
        );
    }

    #[test]
    fn test_walk_crate_modules_empty_file_visits_root_only() {
        let dir = test_dir("empty_file");
        let root = dir.join("lib.rs");
        fs::write(&root, "").unwrap();

        let mut visited = Vec::new();
        let result = walk_crate_modules(&root, &mut |m| {
            visited.push((m.module_path.to_vec(), m.items.len()));
        });
        assert!(result.is_some(), "empty file should parse successfully");
        assert_eq!(
            visited.len(),
            1,
            "should visit exactly one module (the root)"
        );
        assert!(visited[0].0.is_empty(), "root module path must be empty");
        assert_eq!(visited[0].1, 0, "empty file has zero items");
    }

    #[test]
    fn test_walk_deeply_nested_inline_modules() {
        let dir = test_dir("deep_inline");
        let root = dir.join("lib.rs");
        fs::write(
            &root,
            r#"
            mod a {
                mod b {
                    mod c {
                        fn leaf() {}
                    }
                }
            }
            "#,
        )
        .unwrap();

        let mut paths: Vec<Vec<String>> = Vec::new();
        walk_crate_modules(&root, &mut |m| {
            paths.push(m.module_path.to_vec());
        });

        let expected: Vec<Vec<String>> = vec![
            vec![],
            vec!["a".into()],
            vec!["a".into(), "b".into()],
            vec!["a".into(), "b".into(), "c".into()],
        ];
        assert_eq!(paths, expected, "must visit all four levels in DFS order");
    }

    #[test]
    fn test_walk_nested_out_of_line_modules() {
        // Use the directory-based module pattern (outer/mod.rs) so that
        // child_dir resolves to outer/, allowing inner.rs to be found there.
        let dir = test_dir("nested_out_of_line");
        let root = dir.join("lib.rs");
        fs::write(&root, "mod outer;\n").unwrap();

        let outer_dir = dir.join("outer");
        fs::create_dir_all(&outer_dir).unwrap();
        fs::write(outer_dir.join("mod.rs"), "mod inner;\n").unwrap();
        fs::write(outer_dir.join("inner.rs"), "fn deep() {}\n").unwrap();

        let mut paths: Vec<Vec<String>> = Vec::new();
        walk_crate_modules(&root, &mut |m| {
            paths.push(m.module_path.to_vec());
        });

        assert!(
            paths.contains(&vec!["outer".to_string()]),
            "should visit outer module"
        );
        assert!(
            paths.contains(&vec!["outer".to_string(), "inner".to_string()]),
            "should visit nested inner module resolved from outer/inner.rs"
        );
    }

    #[test]
    fn test_resolve_module_file_prefers_direct_over_dir_mod() {
        // When both `foo.rs` and `foo/mod.rs` exist, resolve should return `foo.rs`
        // because the standard resolution checks `mod_name.rs` first.
        let dir = test_dir("resolve_preference");
        fs::write(dir.join("foo.rs"), "").unwrap();
        fs::create_dir_all(dir.join("foo")).unwrap();
        fs::write(dir.join("foo").join("mod.rs"), "").unwrap();

        let item_mod: syn::ItemMod = syn::parse_quote! { mod foo; };
        let result = resolve_module_file(&item_mod, &dir, "foo");
        assert!(result.is_some());
        let resolved = result.unwrap();
        assert!(
            resolved.ends_with("foo.rs") && !resolved.ends_with("mod.rs"),
            "direct foo.rs must be preferred over foo/mod.rs, got: {:?}",
            resolved
        );
    }

    #[test]
    fn test_resolve_module_file_explicit_path_missing_returns_none() {
        let dir = test_dir("resolve_explicit_missing");
        // File referenced by #[path] does not exist.
        let item_mod: syn::ItemMod = syn::parse_quote! {
            #[path = "ghost.rs"]
            mod phantom;
        };
        let result = resolve_module_file(&item_mod, &dir, "phantom");
        assert!(
            result.is_none(),
            "explicit #[path] to a missing file must return None"
        );
    }

    #[test]
    fn test_walk_skips_unparseable_out_of_line_module() {
        let dir = test_dir("skip_bad_child");
        let root = dir.join("lib.rs");
        fs::write(&root, "mod good;\nmod bad;\nfn top() {}\n").unwrap();
        fs::write(dir.join("good.rs"), "fn ok() {}\n").unwrap();
        // bad.rs contains invalid Rust — should be silently skipped.
        fs::write(dir.join("bad.rs"), "fn {{{ broken +++").unwrap();

        let mut paths: Vec<Vec<String>> = Vec::new();
        walk_crate_modules(&root, &mut |m| {
            paths.push(m.module_path.to_vec());
        });

        assert!(
            paths.contains(&vec!["good".to_string()]),
            "valid child module should be visited"
        );
        // The bad module should NOT appear because it fails to parse.
        assert!(
            !paths.contains(&vec!["bad".to_string()]),
            "unparseable child module must be silently skipped"
        );
    }
}
