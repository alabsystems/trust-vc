// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Manifest-scoped trait metadata discovery for verification.

use crate::error::{TrustVcError, TrustVcResult};
use crate::ir::{TraitDecl, TraitImplDecl};
use crate::trait_expand::{parse_trait_decl, parse_trait_impl_decl};
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};
use syn::{Attribute, File, Item};

const MANIFEST_SOURCE_ROOTS: &[&str] = &["src", "tests", "examples", "benches"];
const TRAIT_MARKERS: &[&str] = &["trait_spec", "trait_impl"];

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct TraitCatalog {
    pub(crate) trait_decls: Vec<TraitDecl>,
    pub(crate) trait_impl_decls: Vec<TraitImplDecl>,
}

impl TraitCatalog {
    fn extend(&mut self, other: Self) {
        self.trait_decls.extend(other.trait_decls);
        self.trait_impl_decls.extend(other.trait_impl_decls);
    }
}

static MANIFEST_TRAIT_CACHE: OnceLock<Mutex<HashMap<PathBuf, TraitCatalog>>> = OnceLock::new();

pub(crate) fn traits_from_source_text(source_text: &str) -> TrustVcResult<TraitCatalog> {
    let file = syn::parse_file(source_text).map_err(|source| TrustVcError::Parse {
        context: "parse source file for trait metadata",
        source,
    })?;
    // Same duplicate-trait prune the file lane performs, and for the same
    // reason: a same-named declaration this file's impl headers do not name must
    // not occupy the bare-ident key. Both producers must agree, because their
    // decls have to stay EQUAL for the dedup in `register_trait_impl`.
    let pruned = crate::trait_path_resolution::prune_shadowed_duplicate_traits(&file)?;
    let file = pruned.as_ref().unwrap_or(&file);
    let mut catalog = TraitCatalog::default();
    // Same resolution the file lane performs, so the two producers agree on
    // which trait an `impl` names. See `crate::trait_path_resolution`.
    let scope_index = crate::trait_path_resolution::TraitScopeIndex::build(file);
    scope_index.reject_duplicate_trait_names()?;
    collect_traits(
        file,
        &file.items,
        &mut Vec::new(),
        &scope_index,
        &mut catalog,
    )?;
    Ok(catalog)
}

pub(crate) fn traits_in_manifest(manifest_dir: &Path) -> TrustVcResult<TraitCatalog> {
    let manifest_dir = canonicalize_manifest_dir(manifest_dir)?;
    let cache = MANIFEST_TRAIT_CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    {
        let cache = cache.lock().map_err(|_| TrustVcError::Internal {
            context: "load trait manifest cache",
            detail: "trait manifest cache lock poisoned".to_string(),
        })?;
        if let Some(entries) = cache.get(&manifest_dir) {
            return Ok(entries.clone());
        }
    }

    let catalog = build_catalog(&manifest_dir)?;

    let mut cache = cache.lock().map_err(|_| TrustVcError::Internal {
        context: "update trait manifest cache",
        detail: "trait manifest cache lock poisoned".to_string(),
    })?;
    Ok(cache
        .entry(manifest_dir)
        .or_insert_with(|| catalog.clone())
        .clone())
}

fn canonicalize_manifest_dir(manifest_dir: &Path) -> TrustVcResult<PathBuf> {
    fs::canonicalize(manifest_dir).map_err(|source| TrustVcError::Io {
        context: "canonicalize trait manifest dir",
        source,
    })
}

fn build_catalog(manifest_dir: &Path) -> TrustVcResult<TraitCatalog> {
    let mut rust_files = Vec::new();
    for source_root in MANIFEST_SOURCE_ROOTS {
        let root = manifest_dir.join(source_root);
        if root.is_dir() {
            collect_rust_files(&root, &mut rust_files)?;
        }
    }
    rust_files.sort();

    let mut catalog = TraitCatalog::default();
    for source_file in rust_files {
        let source_text = fs::read_to_string(&source_file).map_err(|source| TrustVcError::Io {
            context: "read trait manifest source",
            source,
        })?;
        if !TRAIT_MARKERS
            .iter()
            .any(|marker| source_text.contains(marker))
        {
            continue;
        }
        catalog.extend(traits_from_source_text(&source_text)?);
    }

    Ok(catalog)
}

fn collect_rust_files(root: &Path, files: &mut Vec<PathBuf>) -> TrustVcResult<()> {
    let mut entries = fs::read_dir(root)
        .map_err(|source| TrustVcError::Io {
            context: "scan trait manifest sources",
            source,
        })?
        .map(|entry| {
            entry
                .map(|entry| entry.path())
                .map_err(|source| TrustVcError::Io {
                    context: "scan trait manifest sources",
                    source,
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    entries.sort();

    for path in entries {
        if path.is_dir() {
            collect_rust_files(&path, files)?;
        } else if path.extension().is_some_and(|ext| ext == "rs") {
            files.push(path);
        }
    }

    Ok(())
}

/// `root_file` is the whole file; `items` is the (possibly `mod`-nested) slice
/// being walked. The two are separate because `shadowed_trait_impl_methods`
/// resolves each impl method against EVERY competing declaration in the file,
/// and a `mod`-local view would report a nested one as unshadowed.
///
/// Computing the shadow set here as well as in the file lane keeps the two
/// producers' decls EQUAL for the dedup in `register_trait_impl`; that dedup
/// additionally unions the sets, so a scope that genuinely cannot see the
/// competing declaration still fails closed rather than resurrecting an
/// unshadowed copy.
fn collect_traits(
    root_file: &File,
    items: &[Item],
    module: &mut Vec<String>,
    scope_index: &crate::trait_path_resolution::TraitScopeIndex,
    catalog: &mut TraitCatalog,
) -> TrustVcResult<()> {
    for item in items {
        match item {
            Item::Trait(item_trait) if has_trust_vc_attr(&item_trait.attrs, "trait_spec") => {
                let mut decl = parse_trait_decl(item_trait)?;
                // Supertraits are keyed by the bound path's LAST SEGMENT inside
                // `parse_trait_decl`, which a `use` rename defeats — a measured
                // cardinal. Re-key against the trait's own module scope, in
                // lockstep with `trait_contracts::collect_source_trait_declarations`
                // so the two views of `TraitDecl::supertraits` cannot drift.
                decl.supertraits = crate::trait_path_resolution::resolved_supertrait_names(
                    scope_index,
                    module,
                    item_trait,
                );
                catalog.trait_decls.push(decl);
            }
            Item::Impl(item_impl) if has_trust_vc_attr(&item_impl.attrs, "trait_impl") => {
                let mut decl = parse_trait_impl_decl(item_impl)?.with_inherent_shadowed_methods(
                    crate::vc_extraction::shadowed_trait_impl_methods(root_file, item_impl),
                );
                if let Some(resolved) = crate::trait_path_resolution::resolved_impl_trait_name(
                    scope_index,
                    module,
                    item_impl,
                )? {
                    decl.trait_name = resolved;
                }
                catalog.trait_impl_decls.push(decl);
            }
            Item::Mod(item_mod) => {
                if let Some((_, nested_items)) = &item_mod.content {
                    module.push(item_mod.ident.to_string());
                    let nested =
                        collect_traits(root_file, nested_items, module, scope_index, catalog);
                    module.pop();
                    nested?;
                }
            }
            _ => {}
        }
    }

    Ok(())
}

fn has_trust_vc_attr(attrs: &[Attribute], marker: &str) -> bool {
    attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == marker)
    })
}
