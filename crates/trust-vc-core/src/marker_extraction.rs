//! Source-extraction verification for trust_vc proof markers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Extracted from verify_macro.rs as part of #1740 (god module splitting).
//! Contains verify_markers_impl (the implementation behind the verify_markers!
//! macro), and the source-extraction pipeline for parsing trust-vc-generated
//! markers (`__trust_vc_requires`, `__trust_vc_ensures`, `__trust_vc_decreases`)
//! from source files.

use crate::error::{TrustVcError, TrustVcResult};
use crate::proof_session::{try_with_session, try_with_session_mut};
use crate::vc::{ProofObligation, VerificationContext};
use std::path::{Path, PathBuf};
use syn::{Attribute, ItemFn};

/// Implementation of verify_markers macro.
///
/// Uses thread-local collected obligations if available, otherwise extracts markers.
#[doc(hidden)]
pub fn verify_markers_impl(module_path: &str, file_path: &str) -> Result<(), String> {
    try_verify_markers_impl(module_path, file_path).map_err(legacy_marker_error_message)
}

/// Part of #1690: typed inner path returning `TrustVcResult` instead of
/// `Result<(), String>`. Used by crate-internal callers that want structured
/// error context.
pub(crate) fn try_verify_markers_impl(module_path: &str, file_path: &str) -> TrustVcResult<()> {
    let result = verify_markers_impl_inner(file_path)?;
    process_verification_result(module_path, result)
}

fn legacy_marker_error_message(err: TrustVcError) -> String {
    match err {
        TrustVcError::Io { source, .. } => format!("Failed to read file: {source}"),
        TrustVcError::Parse { source, .. } => format!("Failed to parse file: {source}"),
        TrustVcError::Encoding { detail, .. } | TrustVcError::Internal { detail, .. } => detail,
        other => other.into_legacy_string(),
    }
}

fn verify_markers_impl_inner(file_path: &str) -> TrustVcResult<crate::VerifyResult> {
    use crate::VerifyResult;
    use std::fs;
    use syn::Item;

    // First check if we have thread-local collected obligations
    let has_collected = try_with_session(|s| {
        s.context
            .as_ref()
            .is_some_and(|c| !c.obligations.is_empty())
    })
    .map_err(|_| TrustVcError::Internal {
        context: "verify_markers_impl: access proof session",
        detail: "proof session is already borrowed — possible reentrant \
                 macro expansion (#1716)"
            .to_string(),
    })?;

    let result = if has_collected {
        let manifest_dir = find_manifest_dir(file_path)?;
        crate::register_traits_from_manifest_scope(
            file_path,
            manifest_dir.to_string_lossy().as_ref(),
        )
        .map_err(|err| TrustVcError::Internal {
            context: "register trait metadata for marker verification",
            detail: err.to_string(),
        })?;

        // Use the thread-local collected obligations
        // First apply any extern_spec contracts
        try_with_session_mut(|s| {
            if let Some(context) = s.context.as_mut() {
                crate::trait_registry::apply_registered_traits_to_context(context).map_err(
                    |err| TrustVcError::Internal {
                        context: "apply trait metadata to marker context",
                        detail: format!(
                            "SOUNDNESS: Failed to apply trait metadata: {}. \
                             Verification without trait metadata would bypass \
                             trait method registration and trait-bound routing.",
                            err
                        ),
                    },
                )?;
                // Apply extern_spec contracts before verification
                crate::extern_spec_verify::apply_extern_specs_to_context(context).map_err(
                    |err| TrustVcError::Internal {
                        context: "apply extern_spec contracts to marker context",
                        detail: format!(
                            "SOUNDNESS: Failed to apply extern_spec contracts: {}. \
                             Verification without extern specs would bypass call-site \
                             obligations (#1778).",
                            err
                        ),
                    },
                )?;
            }
            Ok::<(), TrustVcError>(())
        })
        .map_err(|_| TrustVcError::Internal {
            context: "verify_markers_impl: mutably access proof session",
            detail: "proof session is already borrowed — possible reentrant \
                     macro expansion (#1716)"
                .to_string(),
        })??;
        crate::verify_macro::verify_collected()
    } else {
        // Fall back to extracting markers from source
        // Read and parse the source file
        let source = fs::read_to_string(file_path).map_err(|source| TrustVcError::Io {
            context: "read marker source file",
            source,
        })?;
        let file = syn::parse_file(&source).map_err(|source| TrustVcError::Parse {
            context: "parse marker source file",
            source,
        })?;
        // This raw parse never runs the `state_machine!` expansion, so a file
        // that declares one must not be verified here.
        if crate::state_machine_dsl::has_item_position_invocation(&file) {
            return Ok(VerifyResult::Error {
                message: "files containing state_machine! are verified through the file lane \
                          (cargo trust-vc check), not verify!() markers"
                    .to_string(),
            });
        }

        // Create verification context
        let mut ctx = VerificationContext::new();
        crate::register_traits_from_source(file_path, &source).map_err(|err| {
            TrustVcError::Internal {
                context: "register trait metadata from marker source",
                detail: err.to_string(),
            }
        })?;
        crate::trait_registry::apply_registered_traits_to_context(&mut ctx).map_err(|err| {
            TrustVcError::Internal {
                context: "apply trait metadata to extracted marker context",
                detail: err.to_string(),
            }
        })?;
        let mut found_markers = false;

        // Extract markers from functions
        for item in file.items {
            if let Item::Fn(func) = item {
                if let Some(markers) = extract_function_markers(&func)? {
                    found_markers = true;
                    apply_markers_to_context(
                        &mut ctx,
                        &func.sig.ident.to_string(),
                        &markers,
                        &func,
                    )?;
                }
            }
        }

        // If no markers found, report that nothing was verified (fixes #1518)
        if !found_markers {
            VerifyResult::Error {
                message: format!(
                    "No trust_vc verification markers found in '{}'. \
                     Ensure the source file contains trust_vc verification \
                     contracts (trust_vc::requires!, trust_vc::ensures!, etc.).",
                    file_path
                ),
            }
        } else {
            // Run verification
            ctx.verify()
        }
    };
    Ok(result)
}

fn find_manifest_dir(file_path: &str) -> TrustVcResult<PathBuf> {
    let resolved = fs_resolve(file_path)?;
    let mut current = resolved
        .parent()
        .ok_or_else(|| TrustVcError::Internal {
            context: "locate marker manifest dir",
            detail: format!("`{}` has no parent directory", resolved.display()),
        })?
        .to_path_buf();

    loop {
        if current.join("Cargo.toml").is_file() {
            return Ok(current);
        }
        if !current.pop() {
            break;
        }
    }

    Err(TrustVcError::Internal {
        context: "locate marker manifest dir",
        detail: format!(
            "failed to locate Cargo.toml for marker source `{}`",
            resolved.display()
        ),
    })
}

fn fs_resolve(file_path: &str) -> TrustVcResult<PathBuf> {
    let path = Path::new(file_path);
    let candidate = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir()
            .map_err(|source| TrustVcError::Io {
                context: "resolve marker source path",
                source,
            })?
            .join(path)
    };
    std::fs::canonicalize(&candidate).map_err(|source| TrustVcError::Io {
        context: "resolve marker source path",
        source,
    })
}

fn process_verification_result(
    module_path: &str,
    result: crate::VerifyResult,
) -> TrustVcResult<()> {
    use crate::VerifyResult;

    match result {
        VerifyResult::Verified => Ok(()),
        VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        } => Err(TrustVcError::Encoding {
            context: "marker verification",
            detail: format!(
                "✗ Verification failed for {}\n  Obligation: {}\n  Counterexample: {}",
                module_path,
                obligation_name,
                model.as_deref().unwrap_or("(no model)")
            ),
        }),
        // A failure, but with no model — so no counterexample is narrated.
        VerifyResult::NotProved { reason, .. } => Err(TrustVcError::Encoding {
            context: "marker verification",
            detail: format!(
                "✗ Verification failed for {}\n  Obligation not proved (no model): {}",
                module_path, reason
            ),
        }),
        VerifyResult::Unknown { reason, .. } => Err(TrustVcError::Encoding {
            context: "marker verification",
            detail: format!(
                "? Verification unknown for {}\n  Reason: {}",
                module_path, reason
            ),
        }),
        VerifyResult::Error { message } => Err(TrustVcError::Encoding {
            context: "marker verification",
            detail: format!(
                "✗ Verification error for {}\n  Error: {}",
                module_path, message
            ),
        }),
    }
}

/// Extracted markers from a function
#[derive(Debug, Default)]
pub(crate) struct FunctionMarkers {
    pub(crate) requires: Vec<String>,
    pub(crate) ensures: Vec<String>,
    pub(crate) decreases: Option<String>,
}

/// Extract trust_vc markers from a function
fn extract_function_markers(func: &ItemFn) -> TrustVcResult<Option<FunctionMarkers>> {
    let mut markers = FunctionMarkers::default();
    let mut has_markers = false;

    for attr in &func.attrs {
        if let Some(marker_value) = extract_marker_value(attr, "__trust_vc_requires")? {
            markers.requires.push(marker_value);
            has_markers = true;
        } else if let Some(marker_value) = extract_marker_value(attr, "__trust_vc_ensures")? {
            markers.ensures.push(marker_value);
            has_markers = true;
        } else if let Some(marker_value) = extract_marker_value(attr, "__trust_vc_decreases")? {
            markers.decreases = Some(marker_value);
            has_markers = true;
        }
    }

    if has_markers {
        Ok(Some(markers))
    } else {
        Ok(None)
    }
}

/// Extract the value from a marker attribute
fn extract_marker_value(attr: &Attribute, marker_name: &str) -> TrustVcResult<Option<String>> {
    if !attr.path().is_ident(marker_name) {
        return Ok(None);
    }

    // Handle both #[attr = "value"] and #[attr("value")] formats.
    if let syn::Meta::NameValue(name_value) = &attr.meta {
        return match &name_value.value {
            syn::Expr::Lit(lit_expr) => match &lit_expr.lit {
                syn::Lit::Str(lit_str) => Ok(Some(lit_str.value())),
                _ => Err(TrustVcError::Encoding {
                    context: "extract marker value",
                    detail: format!(
                        "Malformed marker #[{}]: expected string literal payload",
                        marker_name
                    ),
                }),
            },
            _ => Err(TrustVcError::Encoding {
                context: "extract marker value",
                detail: format!(
                    "Malformed marker #[{}]: expected string literal payload",
                    marker_name
                ),
            }),
        };
    }

    // Function-like form: #[attr("value")]
    match attr.parse_args::<syn::LitStr>() {
        Ok(value) => Ok(Some(value.value())),
        Err(parse_err) => Err(TrustVcError::Encoding {
            context: "extract marker value",
            detail: format!(
                "Malformed marker #[{}]: expected #[{} = \"...\"] or #[{}(\"...\")] ({})",
                marker_name, marker_name, marker_name, parse_err
            ),
        }),
    }
}

/// Apply extracted markers to the verification context
pub(crate) fn apply_markers_to_context(
    ctx: &mut VerificationContext,
    func_name: &str,
    markers: &FunctionMarkers,
    func: &ItemFn,
) -> TrustVcResult<()> {
    // First declare function parameters as variables
    for input in &func.sig.inputs {
        if let syn::FnArg::Typed(pat_type) = input {
            if let syn::Pat::Ident(pat_ident) = pat_type.pat.as_ref() {
                let var_name = pat_ident.ident.to_string();
                // Keep the original Rust type - the encoder will map it to ay sorts
                let ty = &pat_type.ty;
                let var_type = quote::quote!(#ty).to_string().replace(" ", "");
                ctx.declare_var_typed(
                    &var_name,
                    crate::ir::TrustVcType::parse_or_opaque(&var_type),
                );
            }
        }
    }

    // Add requires as assumptions
    for (i, req) in markers.requires.iter().enumerate() {
        let name = format!("{}_requires_{}", func_name, i);
        ctx.push_obligation(ProofObligation::assume(&name, req));
    }

    // Add ensures as assertions
    for (i, ens) in markers.ensures.iter().enumerate() {
        let name = format!("{}_ensures_{}", func_name, i);
        ctx.push_obligation(ProofObligation::assert(&name, ens));
    }

    // Handle decreases if present — add MeasureNonNegative for each component.
    //
    // LIMITATION: The source-extraction path can only generate MeasureNonNegative
    // obligations (measure >= 0). It cannot generate MeasureDecreases obligations
    // because it does not analyze the function body for recursive call sites.
    // Full termination checking requires the runtime collection path
    // (collect_decreases_measure + collect_decrease_obligation).
    if let Some(dec) = &markers.decreases {
        let trimmed = dec.trim();
        let tuple_components = if trimmed.starts_with('(') && trimmed.ends_with(')') {
            crate::type_syntax::parse_tuple_expr_components(trimmed).map_err(|err| {
                TrustVcError::Encoding {
                    context: "apply markers to verification context",
                    detail: format!(
                        "INVALID: #[decreases] tuple measure '{}' could not be parsed: {}",
                        dec, err
                    ),
                }
            })?
        } else {
            None
        };

        if let Some(components) = tuple_components {
            let components: Vec<String> =
                components.into_iter().filter(|s| !s.is_empty()).collect();
            if components.is_empty() {
                return Err(TrustVcError::Encoding {
                    context: "apply markers to verification context",
                    detail: format!(
                        "INVALID: #[decreases] tuple measure has no valid components: '{}'",
                        dec
                    ),
                });
            }
            for component in &components {
                if !crate::decreases_runtime::is_valid_measure_component(component) {
                    return Err(TrustVcError::Encoding {
                        context: "apply markers to verification context",
                        detail: format!(
                            "INVALID: #[decreases] measure component '{}' must reference a variable",
                            component
                        ),
                    });
                }
                ctx.add_measure_nonneg(component);
            }
        } else if trimmed.is_empty() {
            return Err(TrustVcError::Encoding {
                context: "apply markers to verification context",
                detail: "INVALID: #[decreases] measure is empty".to_string(),
            });
        } else if !crate::decreases_runtime::is_valid_measure_component(trimmed) {
            return Err(TrustVcError::Encoding {
                context: "apply markers to verification context",
                detail: format!(
                    "INVALID: #[decreases] measure '{}' must reference a variable",
                    trimmed
                ),
            });
        } else {
            ctx.add_measure_nonneg(trimmed);
        }
    }

    Ok(())
}

#[cfg(test)]
#[path = "marker_extraction_tests.rs"]
mod tests;
