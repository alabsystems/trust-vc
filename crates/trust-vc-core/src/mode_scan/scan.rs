// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;

use crate::mode::FunctionMode;
use crate::mode_attrs;
use quote::quote;
use syn::ItemFn;

/// Result of scanning the current source file for sibling function modes.
pub(crate) struct ModeScan {
    /// Map from function name to its mode, for all siblings in the same module.
    pub sibling_modes: HashMap<String, FunctionMode>,
}

/// Outcome of attempting to locate the current function's enclosing module.
pub(crate) enum ScanOutcome {
    /// The source scan uniquely identified the current module.
    Found(ModeScan),
    /// Multiple inline modules matched the current function token signature.
    AmbiguousMatch,
    /// Source metadata was unavailable or the function could not be located.
    Unavailable,
}

/// Normalizes an `ItemFn` to a comparable token string by stripping attributes
/// and comparing only the signature and body.
pub(super) fn normalize_fn_tokens(item: &ItemFn) -> String {
    let sig = &item.sig;
    let block = &item.block;
    quote!(#sig #block).to_string()
}

/// Attempts to find the module containing `current_fn` by scanning the source
/// file located via `span`.
pub(super) fn sibling_modes_from_items(items: &[syn::Item]) -> HashMap<String, FunctionMode> {
    items
        .iter()
        .filter_map(|item| {
            if let syn::Item::Fn(item_fn) = item {
                Some((
                    item_fn.sig.ident.to_string(),
                    mode_attrs::classify_item_fn(item_fn),
                ))
            } else {
                None
            }
        })
        .collect()
}

/// Returns `ScanOutcome::Found` when the current function can be uniquely
/// mapped to a single inline module, `ScanOutcome::AmbiguousMatch` when
/// multiple modules contain indistinguishable matches, and
/// `ScanOutcome::Unavailable` for infrastructure failures.
pub(super) fn scan_module(current_fn: &ItemFn, span: proc_macro2::Span) -> ScanOutcome {
    let Some(file_path): Option<PathBuf> = span.local_file() else {
        return ScanOutcome::Unavailable;
    };
    let Ok(source) = fs::read_to_string(&file_path) else {
        return ScanOutcome::Unavailable;
    };
    let Ok(parsed) = crate::parse_file_allow_tracked(&source) else {
        return ScanOutcome::Unavailable;
    };

    let current_name = current_fn.sig.ident.to_string();
    let current_tokens = normalize_fn_tokens(current_fn);
    let mut matches = Vec::new();
    collect_matching_modules(&parsed.items, &current_name, &current_tokens, &mut matches);

    match matches.as_slice() {
        [module_items] => ScanOutcome::Found(ModeScan {
            sibling_modes: sibling_modes_from_items(module_items),
        }),
        [] => ScanOutcome::Unavailable,
        _ => ScanOutcome::AmbiguousMatch,
    }
}

pub(super) fn item_matches_target(
    item_fn: &ItemFn,
    target_name: &str,
    target_tokens: &str,
) -> bool {
    item_fn.sig.ident == target_name && normalize_fn_tokens(item_fn) == *target_tokens
}

/// Finds the unique inline-module item list containing `target_name`.
///
/// Returns `None` when the current function cannot be located or when
/// multiple modules contain an indistinguishable match, so mode scanning
/// never silently selects the wrong sibling set.
pub(super) fn locate_unique_module_items<'a>(
    items: &'a [syn::Item],
    target_name: &str,
    target_tokens: &str,
) -> Option<&'a [syn::Item]> {
    let mut matches = Vec::new();
    collect_matching_modules(items, target_name, target_tokens, &mut matches);
    match matches.as_slice() {
        [module_items] => Some(*module_items),
        _ => None,
    }
}

pub(super) fn collect_matching_modules<'a>(
    items: &'a [syn::Item],
    target_name: &str,
    target_tokens: &str,
    matches: &mut Vec<&'a [syn::Item]>,
) {
    let has_match = items.iter().any(|item| {
        if let syn::Item::Fn(item_fn) = item {
            item_matches_target(item_fn, target_name, target_tokens)
        } else {
            false
        }
    });
    if has_match {
        matches.push(items);
    }

    for item in items {
        if let syn::Item::Mod(item_mod) = item {
            if let Some((_, ref mod_items)) = item_mod.content {
                collect_matching_modules(mod_items, target_name, target_tokens, matches);
            }
        }
    }
}
