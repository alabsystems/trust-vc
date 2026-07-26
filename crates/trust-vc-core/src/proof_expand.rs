//! Proof function expansion: `#[trust_vc::proof]` and `#[trust_vc::spec_mode]`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Extracted from `lib.rs` to keep that file under 500 lines.
//! Part of #2608.

use proc_macro2::TokenStream;
use quote::quote;
use syn::ItemFn;

use crate::local_vars::{extract_local_variables, extract_type_string, LocalVarExtraction};

/// Registers a symbolic invariant predicate helper in the current context.
///
/// `open_local_invariant!` generates a fresh helper name per expansion so the
/// typed pipeline can register a matching UF with the current inner value type.
#[doc(hidden)]
pub fn register_invariant_predicate_helper(name: &str, value_type: &str) {
    let value_ty = crate::ir::TrustVcType::parse_or_opaque(value_type);
    let _ = crate::proof_session::try_with_session_mut(|s| {
        s.context
            .get_or_insert_with(crate::vc::VerificationContext::new)
            .declare_helper_function_typed(
                name,
                crate::ir::TrustVcType::Bool,
                vec![
                    (
                        "namespace".to_string(),
                        crate::ir::TrustVcType::Int { width: 64 },
                    ),
                    ("value".to_string(), value_ty.clone()),
                ],
            );
    });
}

pub(crate) fn has_decreases_metadata(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "decreases")
    }) || crate::attr_doc_metadata::extract_decreases_doc_metadata(attrs)
        .ok()
        .flatten()
        .is_some()
}

/// Expands a proof function attribute.
///
/// # Verification Pipeline
///
/// 1. Parse: Extract function signature and body
/// 2. Transform: Replace trust_vc::assert! with verification markers
/// 3. Emit: Generate ghost function with verification marker
/// 4. Verify: cfg(test) → VerificationPipeline routes to ay; cfg(trust_mc) → trust_mc (not yet connected)
/// 5. Erase: Proof body removed from final binary
///
/// # Generated Code
///
/// The expansion produces:
/// - Internal marker attribute for trust_mc detection
/// - Original function body wrapped in cfg(trust_mc) conditional
/// - Runtime erased body (unreachable panic if called)
///
/// # Postcondition
///
/// Output contains cfg(trust_mc) block for verification mode detection.
#[doc(hidden)]
pub fn expand_proof(input: ItemFn) -> TokenStream {
    expand_proof_with_tracked(input, &[])
}

/// Expand a proof function with tracked parameter metadata.
///
/// Like `expand_proof`, but also emits `register_tracked_param` calls for
/// parameters that were annotated with `tracked` in the source. Part of #2427.
#[doc(hidden)]
pub fn expand_proof_with_tracked(input: ItemFn, tracked_params: &[String]) -> TokenStream {
    let attrs = &input.attrs;
    let vis = &input.vis;
    let sig = &input.sig;
    let block = &input.block;
    let fn_name = &sig.ident;
    let fn_name_str = fn_name.to_string();
    let function_solver_mode = match crate::mode_attrs::extract_function_solver_mode(attrs) {
        Ok(mode) => mode,
        Err(err) => {
            return syn::Error::new_spanned(fn_name, err.to_string()).to_compile_error();
        }
    };

    if let Some(unsafety) = &sig.unsafety {
        return syn::Error::new_spanned(
            unsafety,
            "'unsafe' only makes sense on exec-mode functions",
        )
        .to_compile_error();
    }

    // Order-independent mode validation: outbound + inbound audit (#2300).
    crate::mode::register_compile_time_function_mode(
        &fn_name_str,
        crate::mode::FunctionMode::Proof,
    );
    let (_scan, mode_errors) =
        crate::mode_scan::validate_mode(&input, crate::mode::FunctionMode::Proof, block);
    if !mode_errors.is_empty() {
        return quote! {
            #(#mode_errors)*
        };
    }

    let is_recursive = crate::recursion_graph::summary_for_item_fn(&input, fn_name.span())
        .map_or_else(
            || crate::block_contains_self_call(&fn_name_str, block),
            |summary| summary.is_recursive,
        );
    if is_recursive && !has_decreases_metadata(attrs) {
        return syn::Error::new_spanned(
            fn_name,
            "recursive #[trust_vc::proof] functions require #[trust_vc::decreases(...)]",
        )
        .to_compile_error();
    }

    let (req_clauses, ens_clauses) = crate::contract_registry::extract_contracts_from_block(block);

    // Generate the proof function
    // - Marked with internal attribute for trust_mc to detect
    // - Body is kept for verification but optimized away at runtime
    // Extract local variable declarations and runtime captures from the block
    let mut_ref_transform = crate::mut_ref_proof::transform_proof_body(sig, block);
    let mut_ref_errors = &mut_ref_transform.errors;

    // Inject call-site contract checking before local-variable lowering turns
    // the block back into tokens. Part of #2513.
    let transformed_proof_block = match crate::contract_registry::inject_call_site_contracts(
        &mut_ref_transform.transformed_block,
    ) {
        Ok(block) => block,
        Err(err) => return err.to_compile_error(),
    };
    let transformed_proof_block =
        match crate::proof_stmt_bridge::bridge_proof_statements(&transformed_proof_block) {
            Ok(block) => block,
            Err(err) => return err.to_compile_error(),
        };

    let LocalVarExtraction {
        pre_block: local_var_declarations,
        transformed_block,
    } = extract_local_variables(&transformed_proof_block);

    // Extract parameter names and types for ay variable declaration
    let support_root = crate::support_root::macro_support_root();
    let function_solver_mode_guard = function_solver_mode.map(|mode| {
        let mode_tokens = match mode {
            crate::vc::SolverMode::Default => quote! { #support_root::vc::SolverMode::Default },
            crate::vc::SolverMode::NonlinearArith => {
                quote! { #support_root::vc::SolverMode::NonlinearArith }
            }
            crate::vc::SolverMode::BitVector => quote! { #support_root::vc::SolverMode::BitVector },
            crate::vc::SolverMode::Compute => quote! { #support_root::vc::SolverMode::Compute },
        };
        quote! {
            let __trust_vc_solver_mode_guard =
                #support_root::verify_macro::enter_function_solver_mode_scope(#mode_tokens);
        }
    });
    let mut param_errors = Vec::new();
    let mut param_doc_attrs = Vec::new();
    let param_declarations: Vec<_> = sig
        .inputs
        .iter()
        .filter_map(|arg| match arg {
            syn::FnArg::Typed(pat_type) => match &*pat_type.pat {
                syn::Pat::Ident(pat_ident) => {
                    let param_name = pat_ident.ident.to_string();
                    if mut_ref_transform.skipped_params.contains(&param_name) {
                        return None;
                    }
                    let param_type = extract_type_string(&pat_type.ty);
                    let doc_value = format!(
                        "{}{}:{}",
                        crate::proof_doc_metadata::PARAM_DOC_PREFIX,
                        param_name,
                        param_type
                    );
                    param_doc_attrs.push(quote! { #[doc = #doc_value] });
                    Some(quote! {
                        #support_root::verify_macro::collect_variable(
                            #param_name.to_string(),
                            #param_type.to_string()
                        );
                    })
                }
                _ => {
                    let err = syn::LitStr::new(
                        &format!(
                            "trust_vc::proof does not support complex parameter patterns. Use simple named parameters instead of: {}",
                            quote!(#pat_type)
                        ),
                        proc_macro2::Span::call_site(),
                    );
                    param_errors.push(quote! {
                        compile_error!(#err);
                    });
                    None
                }
            },
            syn::FnArg::Receiver(_) => {
                let err = syn::LitStr::new(
                    "trust_vc::proof does not support self parameters. Use a free function with an explicit parameter instead.",
                    proc_macro2::Span::call_site(),
                );
                param_errors.push(quote! {
                    compile_error!(#err);
                });
                None
            }
        })
        .collect();

    // Fail closed: compile-error expansions must not publish durable proof
    // metadata or call-site contracts that future compile-time consumers could
    // mistake for a valid proof definition.
    let emit_static_metadata = param_errors.is_empty() && mut_ref_errors.is_empty();

    // Register this function's requires/ensures contract for call-site
    // postcondition propagation only after signature/body rewrites succeed.
    // Part of #2513, #2593.
    if emit_static_metadata && (!req_clauses.is_empty() || !ens_clauses.is_empty()) {
        let param_names = crate::contract_registry::extract_param_names(sig);
        crate::contract_registry::register_compile_time_function_contract(
            &fn_name_str,
            crate::contract_registry::FunctionContract {
                param_names,
                requires: req_clauses.clone(),
                ensures: ens_clauses.clone(),
            },
        );
    }

    let tracked_registrations: Vec<_> = tracked_params
        .iter()
        .map(|name| {
            quote! {
                #support_root::verify_macro::register_tracked_param(#name.to_string());
            }
        })
        .collect();

    // Durable proof-doc metadata attrs (Part of #2482, #1558).
    // Emitted outside any cfg() branch so compile-time consumers can discover
    // proof identity without executing macro-generated code.
    let tracked_doc_attrs: Vec<_> = if emit_static_metadata {
        tracked_params
            .iter()
            .map(|name| {
                let value = format!(
                    "{}{}",
                    crate::proof_doc_metadata::TRACKED_PARAM_PREFIX,
                    name,
                );
                quote! { #[doc = #value] }
            })
            .collect()
    } else {
        Vec::new()
    };
    let requires_doc_attrs: Vec<_> = if emit_static_metadata {
        req_clauses
            .iter()
            .map(|condition| {
                let value = format!(
                    "{}{}",
                    crate::proof_doc_metadata::REQUIRES_DOC_PREFIX,
                    condition
                );
                quote! { #[doc = #value] }
            })
            .collect()
    } else {
        Vec::new()
    };
    let ensures_doc_attrs: Vec<_> = if emit_static_metadata {
        ens_clauses
            .iter()
            .map(|condition| {
                let value = format!(
                    "{}{}",
                    crate::proof_doc_metadata::ENSURES_DOC_PREFIX,
                    condition
                );
                quote! { #[doc = #value] }
            })
            .collect()
    } else {
        Vec::new()
    };
    let param_doc_attrs = if emit_static_metadata {
        param_doc_attrs
    } else {
        Vec::new()
    };
    let proof_marker_doc_attr = if emit_static_metadata {
        let proof_marker = crate::proof_doc_metadata::PROOF_DOC_MARKER;
        quote! { #[doc = #proof_marker] }
    } else {
        quote! {}
    };

    quote! {
        #(#attrs)*
        /// Proof function - verified by trust_vc/trust_mc, erased at runtime
        #[doc(hidden)]
        #proof_marker_doc_attr
        #(#tracked_doc_attrs)*
        #(#requires_doc_attrs)*
        #(#ensures_doc_attrs)*
        #(#param_doc_attrs)*
        #[allow(dead_code, unused_variables, unused_mut)]
        #vis #sig {
            #[cfg(any(test, trust_mc))]
            #support_root::mode::register_function_mode(
                stringify!(#fn_name),
                #support_root::mode::FunctionMode::Proof
            );

            #(#param_errors)*
            #(#mut_ref_errors)*

            // Proof body - processed by trust_mc's ay backend
            // At compile time, this is analyzed for verification
            // At runtime, this should never execute
            #[cfg(trust_mc)]
            {
                #transformed_proof_block
            }
            #[cfg(all(test, not(trust_mc)))]
            {
                // CRITICAL: Save and replace the thread-local verification context.
                // Each proof function gets a fresh scope. This prevents:
                // 1. Residual state from prior tests on the same thread (Rust reuses
                //    threads in its test pool) causing stale formulas or hangs.
                // 2. Nested/recursive proof calls from polluting the outer context.
                // ContextGuard restores on drop, so context is safe even if the
                // body panics. (Fixes #1525)
                let __trust_vc_guard = #support_root::verify_macro::save_context_guard();
                #function_solver_mode_guard

                // In test mode: set proof mode, declare parameters, execute block, then verify
                #support_root::verify_macro::set_proof_mode(true);

                // CRITICAL: Auto-declare function parameters as ay variables (Option A fix)
                #(#param_declarations)*

                // Record which parameters were annotated with `tracked` (#2427 Slice 3)
                #(#tracked_registrations)*

                // Declare local variables extracted from the block
                // This registers variables with the verification context before use
                #(#local_var_declarations)*

                // Execute the proof block with injected runtime value captures.
                // The transformed block inserts collect_let_binding_runtime_value()
                // calls after each function-call let-binding, capturing concrete
                // values (e.g., step2(5) == 7) as ay assumptions. Fixes #1556.
                let result = #transformed_block;
                #support_root::verify_macro::set_proof_mode(false);

                // AUTO-VERIFICATION: Check all collected obligations (fix for #469)
                // This makes proof functions automatically verify their assertions
                // NOW USING THE BRIDGE: Connect proc macros to ay verification
                let verify_result = match #support_root::register_traits_from_manifest_scope(
                    file!(),
                    env!("CARGO_MANIFEST_DIR"),
                ) {
                    Ok(()) => {
                        let pipeline =
                            #support_root::verification_bridge::VerificationPipeline::collect_from_macros();
                        pipeline.verify()
                    }
                    Err(err) => #support_root::VerifyResult::Error {
                        message: format!(
                            "trait metadata registration failed for `{}` in `{}`: {}",
                            module_path!(),
                            file!(),
                            err
                        ),
                    },
                };

                // Explicitly restore context before the boundary check (which may abort).
                // If we didn't call this, the Drop impl would still restore on failure.
                __trust_vc_guard.restore();

                let verification_failure = match verify_result {
                    #support_root::VerifyResult::Verified => {
                        // Verification succeeded - return the result
                        None
                    }
                    #support_root::VerifyResult::Counterexample {
                        obligation_name,
                        model,
                        ..
                    } => Some(format!(
                        "Proof verification failed: obligation '{}' violated. Counterexample: {:?}",
                        obligation_name, model
                    )),
                    #support_root::VerifyResult::NotProved { reason, .. } => {
                        // A model-less verification failure — no counterexample
                        // is narrated because none was found.
                        Some(format!(
                            "Proof verification failed: obligation not proved (no model): {}",
                            reason
                        ))
                    },
                    #support_root::VerifyResult::Unknown { reason, .. } => {
                        // Unknown results fail for soundness (issue #519)
                        // The solver couldn't prove the assertion is valid
                        Some(format!(
                            "Proof verification returned Unknown - cannot prove correctness: {}",
                            reason
                        ))
                    },
                    #support_root::VerifyResult::Error { message } => {
                        Some(format!("Proof verification error: {}", message))
                    },
                    other => {
                        Some(format!(
                            "Proof verification returned unexpected result: {:?}",
                            other
                        ))
                    }
                };
                if let Some(message) = verification_failure {
                    #support_root::__trust_vc_runtime_boundary(message);
                }

                result
            }
            #[cfg(not(any(trust_mc, test)))]
            {
                // Type-check the block at compile time (never executed)
                #[allow(unreachable_code)]
                if false {
                    return { #transformed_proof_block };
                }
                loop {
                    unreachable!(concat!(
                        "proof function `",
                        stringify!(#fn_name),
                        "` called at runtime - proof functions are ghost code"
                    ));
                }
            }
        }
    }
}

/// Registers a function as Spec mode and validates its body as Spec.
///
/// Unlike `expand_spec`, this does not erase the function at runtime or add
/// verification infrastructure. It registers the function in the compile-time
/// mode registry, validates outbound calls as Spec, and audits inbound exec
/// callers in the same module (#2300).
///
/// Use for test helper functions that are semantically spec (pure computation)
/// but need to remain callable at runtime for test execution.
#[doc(hidden)]
pub fn expand_spec_mode(input: ItemFn) -> TokenStream {
    let fn_name_str = input.sig.ident.to_string();
    crate::mode::register_compile_time_function_mode(&fn_name_str, crate::mode::FunctionMode::Spec);

    // Order-independent mode validation: outbound + inbound audit (#2300).
    let (_scan, mode_errors) =
        crate::mode_scan::validate_mode(&input, crate::mode::FunctionMode::Spec, &input.block);
    if !mode_errors.is_empty() {
        return quote! { #(#mode_errors)* };
    }

    quote! { #input }
}
