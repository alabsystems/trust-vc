// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Thread-local trait metadata bridge for verification.

use crate::trait_catalog::{traits_from_source_text, traits_in_manifest, TraitCatalog};
use crate::vc::VerificationContext;
use crate::{TrustVcError, TrustVcResult};
use std::cell::RefCell;
use std::path::Path;

thread_local! {
    static REGISTERED_TRAITS: RefCell<TraitCatalog> = RefCell::new(TraitCatalog::default());
}

pub fn register_traits_from_source(file_path: &str, source_text: &str) -> TrustVcResult<()> {
    register_traits_from_source_inner(file_path, source_text)
}

fn register_traits_from_source_inner(file_path: &str, source_text: &str) -> TrustVcResult<()> {
    let catalog = traits_from_source_text(source_text).map_err(|err| TrustVcError::Internal {
        context: "register traits from source",
        detail: format!("failed to collect trait metadata from `{file_path}`: {err}"),
    })?;
    merge_catalog(catalog)
}

pub fn register_traits_from_manifest_scope(
    file_path: &str,
    manifest_dir: &str,
) -> TrustVcResult<()> {
    register_traits_from_manifest_scope_inner(file_path, manifest_dir)
}

fn register_traits_from_manifest_scope_inner(
    file_path: &str,
    manifest_dir: &str,
) -> TrustVcResult<()> {
    let catalog =
        traits_in_manifest(Path::new(manifest_dir)).map_err(|err| TrustVcError::Internal {
            context: "register traits from manifest scope",
            detail: format!(
                "failed to collect trait metadata for `{file_path}` from `{manifest_dir}`: {err}"
            ),
        })?;
    merge_catalog(catalog)
}

fn merge_catalog(catalog: TraitCatalog) -> TrustVcResult<()> {
    REGISTERED_TRAITS.with(|registered| {
        let mut registered = registered
            .try_borrow_mut()
            .map_err(|_| TrustVcError::Internal {
                context: "merge trait catalog",
                detail: "registered trait metadata is already borrowed".to_string(),
            })?;
        for decl in catalog.trait_decls {
            if !registered.trait_decls.contains(&decl) {
                registered.trait_decls.push(decl);
            }
        }
        for decl in catalog.trait_impl_decls {
            if !registered.trait_impl_decls.contains(&decl) {
                registered.trait_impl_decls.push(decl);
            }
        }
        Ok(())
    })
}

pub(crate) fn apply_registered_traits_to_context(
    ctx: &mut VerificationContext,
) -> TrustVcResult<()> {
    REGISTERED_TRAITS.with(|registered| {
        let registered = registered
            .try_borrow()
            .map_err(|_| TrustVcError::Internal {
                context: "apply registered traits to context",
                detail: "registered trait metadata is already borrowed".to_string(),
            })?;
        for decl in &registered.trait_decls {
            ctx.register_trait_decl(decl.clone());
        }
        for decl in &registered.trait_impl_decls {
            ctx.register_trait_impl(decl.clone());
        }
        Ok(())
    })
}

pub(crate) fn clear_registered_traits() {
    REGISTERED_TRAITS.with(|registered| {
        if let Ok(mut registered) = registered.try_borrow_mut() {
            registered.trait_decls.clear();
            registered.trait_impl_decls.clear();
        }
    });
}

/// Returns the number of registered trait declarations. Test-only.
#[cfg(test)]
pub(crate) fn registered_trait_decl_count() -> usize {
    REGISTERED_TRAITS.with(|registered| {
        registered
            .try_borrow()
            .map(|r| r.trait_decls.len())
            .unwrap_or(0)
    })
}

/// Returns the number of registered trait impl declarations. Test-only.
#[cfg(test)]
pub(crate) fn registered_trait_impl_decl_count() -> usize {
    REGISTERED_TRAITS.with(|registered| {
        registered
            .try_borrow()
            .map(|r| r.trait_impl_decls.len())
            .unwrap_or(0)
    })
}

/// Test helpers for creating borrow-conflict scenarios.
#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;

    /// Holds a mutable borrow on REGISTERED_TRAITS and calls the given closure.
    pub fn with_registered_traits_borrowed<F: FnOnce()>(f: F) {
        REGISTERED_TRAITS.with(|registered| {
            let _borrow = registered.borrow_mut();
            f();
        });
    }
}
