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
use syn::{Attribute, Item};

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
    let mut catalog = TraitCatalog::default();
    collect_traits(&file.items, &mut catalog)?;
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

fn collect_traits(items: &[Item], catalog: &mut TraitCatalog) -> TrustVcResult<()> {
    for item in items {
        match item {
            Item::Trait(item_trait) if has_trust_vc_attr(&item_trait.attrs, "trait_spec") => {
                catalog.trait_decls.push(parse_trait_decl(item_trait)?);
            }
            Item::Impl(item_impl) if has_trust_vc_attr(&item_impl.attrs, "trait_impl") => {
                catalog
                    .trait_impl_decls
                    .push(parse_trait_impl_decl(item_impl)?);
            }
            Item::Mod(item_mod) => {
                if let Some((_, nested_items)) = &item_mod.content {
                    collect_traits(nested_items, catalog)?;
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
