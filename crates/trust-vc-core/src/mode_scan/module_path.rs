// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::fs;
use std::path::Path;

use super::scan::item_matches_target;

/// Determines the caller's module path within the crate.
///
/// Combines two sources:
/// 1. File-path based: for out-of-line modules, derives the path from the
///    file location relative to the crate root.
/// 2. AST-based: for inline modules, walks the source file's parse tree to
///    find which `mod` block contains the target function.
pub(super) fn determine_caller_module(
    source_file: &Path,
    crate_root: &Path,
    fn_name: &str,
    fn_tokens: &str,
) -> Vec<String> {
    let source_canonical = source_file
        .canonicalize()
        .unwrap_or(source_file.to_path_buf());
    let root_canonical = crate_root
        .canonicalize()
        .unwrap_or(crate_root.to_path_buf());

    // Start with file-path-based module prefix for out-of-line modules.
    let mut file_prefix = Vec::new();
    if source_canonical != root_canonical {
        let root_dir = root_canonical.parent().unwrap_or(&root_canonical);
        if let Ok(relative) = source_canonical.strip_prefix(root_dir) {
            let mut segments: Vec<String> = relative
                .components()
                .filter_map(|component| {
                    if let std::path::Component::Normal(segment) = component {
                        segment.to_str().map(ToString::to_string)
                    } else {
                        None
                    }
                })
                .collect();
            if let Some(last) = segments.last_mut() {
                if last.ends_with(".rs") {
                    *last = last.trim_end_matches(".rs").to_string();
                }
                if *last == "mod" {
                    segments.pop();
                }
            }
            file_prefix = segments;
        }
    }

    // Now determine inline module nesting by walking the source AST.
    if let Ok(source) = fs::read_to_string(source_file) {
        if let Ok(parsed) = crate::parse_file_allow_tracked(&source) {
            if let Some(inline_path) =
                find_inline_module_path(&parsed.items, fn_name, fn_tokens, &[])
            {
                let mut result = file_prefix;
                result.extend(inline_path);
                return result;
            }
        }
    }

    file_prefix
}

/// Walks the parse tree to find the inline module path containing the target.
///
/// Returns `Some(module_path)` where `module_path` is the inline nesting
/// (e.g., `["specs"]` for `mod specs { fn helper() {} }`). Returns `Some([])`
/// if the function is at the top level.
pub(super) fn find_inline_module_path(
    items: &[syn::Item],
    target_name: &str,
    target_tokens: &str,
    current_path: &[String],
) -> Option<Vec<String>> {
    let has_match = items.iter().any(|item| {
        if let syn::Item::Fn(item_fn) = item {
            item_matches_target(item_fn, target_name, target_tokens)
        } else {
            false
        }
    });
    if has_match {
        return Some(current_path.to_vec());
    }

    for item in items {
        if let syn::Item::Mod(item_mod) = item {
            if let Some((_, ref mod_items)) = item_mod.content {
                let mut child_path = current_path.to_vec();
                child_path.push(item_mod.ident.to_string());
                if let Some(result) =
                    find_inline_module_path(mod_items, target_name, target_tokens, &child_path)
                {
                    return Some(result);
                }
            }
        }
    }

    None
}
