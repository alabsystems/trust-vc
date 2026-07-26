// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Verification support for extern_spec contracts.
//!
//! This module provides runtime checking of extern_spec contracts during test
//! mode verification.

use crate::extern_spec_call_bindings::{
    bindings_from_call_expr_source, substitute_contract_placeholders, ExternSpecCallBindings,
};
use crate::extern_spec_registry::{classify_target_scope, lookup_extern_spec_source};
use crate::vc::{ProofObligation, VerificationContext};
use crate::{TrustVcError, TrustVcResult};
use std::cell::RefCell;
use std::fs;
use std::path::Path;

const EXTERN_SPEC_ALIAS_GUIDANCE: &str = "`external_spec!` (preferred) or legacy `extern_spec!`";

thread_local! {
    /// Thread-local storage for extern spec contracts being checked.
    static EXTERN_SPEC_CONTRACTS: RefCell<Vec<ExternSpecContract>> = const { RefCell::new(Vec::new()) };
}

/// An extern spec contract to be verified.
#[derive(Debug, Clone)]
pub(crate) struct ExternSpecContract {
    pub(crate) target: String,
    pub(crate) param_names: Vec<String>,
    pub(crate) requires: Vec<String>,
    pub(crate) ensures: Vec<String>,
    pub(crate) bindings: Option<ExternSpecCallBindings>,
}

/// Registers an extern spec contract for verification.
/// This is called by generated code when an extern function with a spec is
/// about to be called.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn register_extern_spec(target: &str, requires: &[String], ensures: &[String]) {
    EXTERN_SPEC_CONTRACTS.with(|contracts| {
        contracts.borrow_mut().push(ExternSpecContract {
            target: target.to_string(),
            param_names: Vec::new(),
            requires: requires.to_vec(),
            ensures: ensures.to_vec(),
            bindings: None,
        });
    });
}

fn register_extern_spec_entry(
    entry: crate::extern_spec_registry::ExternSpecEntry,
    bindings: Option<ExternSpecCallBindings>,
) {
    EXTERN_SPEC_CONTRACTS.with(|contracts| {
        contracts.borrow_mut().push(ExternSpecContract {
            target: entry.target_path,
            param_names: entry.param_names,
            requires: entry.requires,
            ensures: entry.ensures,
            bindings,
        });
    });
}

pub fn register_extern_spec_from_source(
    file_path: &str,
    source_text: &str,
    target: &str,
) -> TrustVcResult<()> {
    register_extern_spec_from_source_inner(file_path, source_text, target)
}

fn register_extern_spec_from_source_inner(
    file_path: &str,
    source_text: &str,
    target: &str,
) -> TrustVcResult<()> {
    let contract = lookup_extern_spec_source(file_path, source_text, target)?.ok_or_else(|| {
        let detail = if let Some(crate_prefix) = classify_target_scope(target) {
            format!(
                "no extern_spec for `{target}` found in `{file_path}`; \
                 target path starts with `{crate_prefix}` which indicates a cross-crate extern spec — \
                 cross-crate and same-crate resolution is not yet supported (#2392). \
                 Place the {EXTERN_SPEC_ALIAS_GUIDANCE} block in the same file as the call site."
            )
        } else {
            format!(
                "no extern_spec for `{target}` found in `{file_path}`; \
                 lookup is file-local only — the {EXTERN_SPEC_ALIAS_GUIDANCE} block must be in the same source file as the call site"
            )
        };
        TrustVcError::Internal {
            context: "register extern_spec from source",
            detail,
        }
    })?;

    register_extern_spec_entry(contract, None);
    Ok(())
}

fn load_call_site_source_text(file_path: &str, manifest_dir: &str) -> TrustVcResult<String> {
    let file_path = Path::new(file_path);
    if file_path.is_absolute() {
        return fs::read_to_string(file_path).map_err(|source| TrustVcError::Io {
            context: "read absolute call-site source",
            source,
        });
    }

    let manifest_dir = Path::new(manifest_dir);
    let mut attempted_paths = Vec::new();

    for base_dir in manifest_dir.ancestors() {
        let candidate = base_dir.join(file_path);
        attempted_paths.push(candidate.clone());
        if candidate.is_file() {
            return fs::read_to_string(&candidate).map_err(|source| TrustVcError::Io {
                context: "read call-site source",
                source,
            });
        }
    }

    let attempted_paths = attempted_paths
        .iter()
        .map(|path| path.display().to_string())
        .collect::<Vec<_>>()
        .join(", ");
    Err(TrustVcError::Internal {
        context: "locate call-site source",
        detail: format!(
            "failed to locate call-site source `{}` from manifest dir `{}`; tried: {attempted_paths}",
            file_path.display(),
            manifest_dir.display()
        ),
    })
}

fn lookup_extern_spec_from_supported_scope(
    file_path: &str,
    source_text: &str,
    manifest_dir: &str,
    target: &str,
) -> TrustVcResult<crate::extern_spec_registry::ExternSpecEntry> {
    if let Some(contract) = lookup_extern_spec_source(file_path, source_text, target)? {
        return Ok(contract);
    }

    if let Some(contract) = crate::extern_spec_catalog::lookup_extern_spec_in_manifest(
        Path::new(manifest_dir),
        target,
        Some(file_path),
    )? {
        return Ok(contract.entry);
    }

    Err(supported_scope_lookup_error(
        file_path,
        manifest_dir,
        target,
    ))
}

fn supported_scope_lookup_error(file_path: &str, manifest_dir: &str, target: &str) -> TrustVcError {
    let scope_note = classify_target_scope(target).map_or_else(
        || {
            "verify_extern_call! currently supports explicit same-package lookup only, and dependency crates are not searched"
                .to_string()
        },
        |crate_prefix| {
            format!(
                "target path starts with `{crate_prefix}`, which indicates a dependency-crate extern spec; \
                 verify_extern_call! currently supports explicit same-package lookup only, and dependency crates are not searched"
            )
        },
    );

    TrustVcError::Internal {
        context: "register extern_spec from manifest scope",
        detail: format!(
            "no extern_spec for `{target}` found in call-site file `{file_path}` or anywhere in the current package rooted at `{manifest_dir}`; {scope_note}"
        ),
    }
}

pub fn register_extern_spec_from_manifest_scope(
    file_path: &str,
    manifest_dir: &str,
    target: &str,
) -> TrustVcResult<()> {
    load_call_site_source_text(file_path, manifest_dir)
        .and_then(|source_text| {
            lookup_extern_spec_from_supported_scope(file_path, &source_text, manifest_dir, target)
        })
        .map(|contract| register_extern_spec_entry(contract, None))
}

pub fn register_extern_spec_from_manifest_scope_for_call(
    file_path: &str,
    manifest_dir: &str,
    target: &str,
    call_expr_source: &str,
    result_expr: Option<&str>,
) -> TrustVcResult<()> {
    load_call_site_source_text(file_path, manifest_dir).and_then(|source_text| {
        let contract =
            lookup_extern_spec_from_supported_scope(file_path, &source_text, manifest_dir, target)?;
        let bindings = bindings_from_call_expr_source(call_expr_source, result_expr)?;
        register_extern_spec_entry(contract, Some(bindings));
        Ok(())
    })
}

pub fn register_extern_spec_from_call_site(
    file_path: &str,
    manifest_dir: &str,
    target: &str,
) -> TrustVcResult<()> {
    register_extern_spec_from_manifest_scope(file_path, manifest_dir, target)
}

/// Collects all registered extern spec contracts and adds them to
/// the verification context.
///
/// This is called by verify_markers! to include extern spec checks
/// in the verification.
pub(crate) fn apply_extern_specs_to_context(ctx: &mut VerificationContext) -> TrustVcResult<()> {
    EXTERN_SPEC_CONTRACTS.with(|contracts| {
        let contracts = contracts.borrow();
        for contract in contracts.iter() {
            // At the call site, the caller must PROVE preconditions hold (assert).
            for (i, req) in contract.requires.iter().enumerate() {
                let name = format!("{}_requires_{}", contract.target, i);
                let condition = if let Some(bindings) = &contract.bindings {
                    substitute_contract_placeholders(req, &contract.param_names, bindings)?
                } else {
                    req.clone()
                };
                ctx.push_obligation(ProofObligation::assert(&name, &condition));
            }

            // At the call site, the caller ASSUMES postconditions (the extern
            // function guarantees them). Fixes inverted polarity found during
            // #1512 follow-up audit.
            for (i, ens) in contract.ensures.iter().enumerate() {
                let name = format!("{}_ensures_{}", contract.target, i);
                let condition = if let Some(bindings) = &contract.bindings {
                    substitute_contract_placeholders(ens, &contract.param_names, bindings)?
                } else {
                    ens.clone()
                };
                ctx.push_obligation(ProofObligation::assume(&name, &condition));
            }
        }
        Ok(())
    })
}

/// Manual verification helper for extern spec contracts.
///
/// This remains an explicit helper for #2392: it searches the call-site file
/// first, then the current package rooted at `CARGO_MANIFEST_DIR`.
#[macro_export]
macro_rules! verify_extern_call {
    ($target:expr, $call:expr) => {{
        let __trust_vc_extern_call_value_name =
            format!("__trust_vc_extern_call_value_{}_{}", line!(), column!());
        $crate::register_extern_spec_from_manifest_scope_for_call(
            file!(),
            env!("CARGO_MANIFEST_DIR"),
            $target,
            stringify!($call),
            Some(__trust_vc_extern_call_value_name.as_str()),
        )
        .unwrap_or_else(|err| {
            $crate::__trust_vc_runtime_boundary(format!(
                "verify_extern_call! could not register extern_spec for `{}` in `{}`: {}",
                $target,
                file!(),
                err
            ))
        });

        let __trust_vc_extern_call_value = $call;
        // Declare the temp variable in the verification context so the
        // lowerer can resolve it. Without this, the let-binding assumption
        // references an undeclared variable. Part of #2658.
        $crate::collect_variable_runtime(
            &__trust_vc_extern_call_value_name,
            &__trust_vc_extern_call_value,
        );
        $crate::collect_let_binding_runtime_value_from_ref(
            &__trust_vc_extern_call_value_name,
            &__trust_vc_extern_call_value,
        );
        __trust_vc_extern_call_value
    }};
}

/// Clears all registered extern spec contracts.
///
/// This should be called at the end of each test to prevent
/// memory leaks from accumulated contract registrations.
pub fn clear_extern_contracts() {
    // Graceful skip on borrow conflict: panicking during cleanup aborts
    // ALL subsequent clears in clear_all_thread_locals. Part of #1955.
    EXTERN_SPEC_CONTRACTS.with(|c| {
        if let Ok(mut contracts) = c.try_borrow_mut() {
            contracts.clear();
        }
    });
}

/// Test helpers for creating borrow-conflict scenarios.
#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;

    /// Holds a mutable borrow on EXTERN_SPEC_CONTRACTS and calls the given closure.
    pub fn with_extern_spec_contracts_borrowed<F: FnOnce()>(f: F) {
        EXTERN_SPEC_CONTRACTS.with(|c| {
            let _borrow = c.borrow_mut();
            f();
        });
    }
}

#[cfg(test)]
#[path = "extern_spec_verify_tests.rs"]
mod tests;
