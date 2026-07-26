//! Local variable extraction and type inference for proof functions.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Extracts local variable declarations from proof function blocks and infers
//! types for ay variable declaration. Handles runtime value capture injection
//! for function-call let-bindings.

use proc_macro2::TokenStream;
use quote::quote;
use syn::{Pat, Stmt};

pub(crate) use crate::local_vars_helpers::extract_type_string;
use crate::local_vars_helpers::{
    infer_type_from_expr, is_arbitrary_expr, is_encodable_expr, is_mut_ref_shadow_var,
    is_string_literal_expr, is_verification_wrapper_type, TypeInference,
};
// Re-export for local_vars_tests.rs (uses `super::*`)
#[cfg(test)]
use crate::local_vars_helpers::extract_first_ident;

/// Result of extracting local variable declarations from a proof function block.
///
/// Contains pre-block declarations AND a transformed block with runtime value
/// captures injected after each function-call let-binding.
pub(crate) struct LocalVarExtraction {
    /// TokenStreams to run BEFORE the block: declare variables and add
    /// compile-time-encodable let-binding constraints.
    pub(crate) pre_block: Vec<TokenStream>,
    /// Transformed block with runtime value capture calls injected after each
    /// function-call let-binding. For example, `let result: i32 = step2(5);`
    /// becomes:
    /// ```ignore
    /// let result: i32 = step2(5);
    /// collect_let_binding_runtime_value("result", result as i64);
    /// ```
    /// This captures the concrete runtime value and adds it as an assumption
    /// to the verification context. Fixes #1556.
    pub(crate) transformed_block: TokenStream,
}

/// Helper function to extract local variable declarations from a block.
///
/// Walks through all statements in the block and collects let bindings.
/// Returns `LocalVarExtraction` with pre-block declarations and a transformed
/// block that injects runtime value captures after function-call let-bindings.
pub(crate) fn extract_local_variables(block: &syn::Block) -> LocalVarExtraction {
    let support_root = crate::macro_support_root();
    let mut pre_block = Vec::new();
    // Collect (var_name, var_type) pairs for function-call let-bindings
    // that need runtime value capture within the block.
    let mut runtime_captures: Vec<(String, String)> = Vec::new();

    for stmt in &block.stmts {
        if let Stmt::Local(local) = stmt {
            if local
                .init
                .as_ref()
                .is_some_and(|init| is_string_literal_expr(&init.expr))
            {
                pre_block.push(quote! {
                    compile_error!(
                        "trust_vc: string literals are not yet supported in proof-function locals; bind a symbolic String/str value instead."
                    );
                });
                continue;
            }
            let binding_name = match &local.pat {
                Pat::Type(pat_type) => match pat_type.pat.as_ref() {
                    Pat::Ident(pat_ident) => Some(pat_ident.ident.to_string()),
                    _ => None,
                },
                Pat::Ident(pat_ident) => Some(pat_ident.ident.to_string()),
                _ => None,
            };
            if binding_name.as_deref().is_some_and(is_mut_ref_shadow_var) {
                continue;
            }
            let original_ty = match &local.pat {
                Pat::Type(pat_type) => Some(pat_type.ty.as_ref()),
                _ => None,
            };

            // `arbitrary!()` initializers produce unconstrained symbolic values.
            // Skip ALL let-binding constraints (both encodable and runtime capture)
            // so the variable remains a fresh ay constant. Part of #2518.
            let is_arbitrary = local
                .init
                .as_ref()
                .is_some_and(|init| is_arbitrary_expr(&init.expr));

            // Serialize the initializer expression (if present) for let-binding
            // constraints. This is the RHS of `let x = EXPR` — we need it as a
            // string so the encoder can add the assumption `x == EXPR`.
            // Only emit for expressions the ay encoder can parse: literals,
            // arithmetic, variables, casts, negation. Skip function calls
            // and other opaque expressions that the encoder can't evaluate.
            // Fixes #1556: runtime let-bindings not encoded as ay assumptions.
            let is_encodable = !is_arbitrary
                && local
                    .init
                    .as_ref()
                    .map(|init| is_encodable_expr(&init.expr))
                    .unwrap_or(false);
            let init_expr_string = if is_encodable {
                local.init.as_ref().map(|init| {
                    let expr = &init.expr;
                    quote!(#expr).to_string()
                })
            } else {
                None
            };

            // Extract variable name and optional type from let binding.
            // Handles both `let x: u64 = ...` (Pat::Type) and `let x = ...` (Pat::Ident).
            let (var_name, var_type) = match &local.pat {
                Pat::Type(pat_type) => {
                    // Typed binding: `let x: u64 = ...`
                    let name = match pat_type.pat.as_ref() {
                        Pat::Ident(pat_ident) => Some(pat_ident.ident.to_string()),
                        _ => None,
                    };
                    let ty = extract_type_string(&pat_type.ty);
                    match name {
                        Some(n) => (n, ty),
                        None => continue,
                    }
                }
                Pat::Ident(pat_ident) => {
                    // Untyped binding: `let x = ...`
                    // Try to infer type from initializer (#1549)
                    let var_name = pat_ident.ident.to_string();
                    let infer_result = local
                        .init
                        .as_ref()
                        .map(|init| infer_type_from_expr(&init.expr))
                        .unwrap_or(TypeInference::Unknown);
                    match infer_result {
                        TypeInference::Inferred(ty) => (var_name, ty),
                        TypeInference::InferFromRef(ref_name) => {
                            // Variable reference or binary expression — infer type from
                            // referenced variable at runtime (#1603).
                            pre_block.push(quote! {
                                #support_root::verify_macro::collect_variable_from_ref(
                                    #var_name.to_string(),
                                    #ref_name.to_string()
                                );
                            });
                            // Also add the let-binding constraint (#1556)
                            if let Some(ref init_str) = init_expr_string {
                                pre_block.push(quote! {
                                    #support_root::verify_macro::collect_let_binding(
                                        #var_name.to_string(),
                                        #init_str.to_string()
                                    );
                                });
                            }
                            continue;
                        }
                        TypeInference::UnsupportedStringLiteral => {
                            let ident = &pat_ident.ident;
                            pre_block.push(quote! {
                                compile_error!(concat!(
                                    "trust_vc: string literal initializer for `let ",
                                    stringify!(#ident),
                                    "` is not yet supported; use a symbolic String/str value instead."
                                ));
                            });
                            continue;
                        }
                        TypeInference::Unknown => {
                            // Cannot infer type — emit compile error
                            let ident = &pat_ident.ident;
                            pre_block.push(quote! {
                                compile_error!(concat!(
                                    "trust_vc: untyped `let ",
                                    stringify!(#ident),
                                    "` in proof function — add a type annotation (e.g., `let ",
                                    stringify!(#ident),
                                    ": i32 = ...`). Proof functions require explicit types for sound verification."
                                ));
                            });
                            continue;
                        }
                    }
                }
                _ => continue,
            };

            pre_block.push(quote! {
                #support_root::verify_macro::collect_variable(
                    #var_name.to_string(),
                    #var_type.to_string()
                );
            });

            // Add let-binding constraint: `var_name == init_expr` as an Assume
            // obligation. This ensures the ay solver knows the variable's value
            // instead of treating it as unconstrained. Fixes #1556.
            let is_verification_wrapper = original_ty.is_some_and(is_verification_wrapper_type);
            if let Some(ref init_str) = init_expr_string {
                pre_block.push(quote! {
                    #support_root::verify_macro::collect_let_binding(
                        #var_name.to_string(),
                        #init_str.to_string()
                    );
                });
            } else if !is_encodable
                && !is_arbitrary
                && !is_verification_wrapper
                && local.init.is_some()
            {
                // Non-encodable initializer (function call, method call, etc.).
                // Record for runtime value capture inside the block. Fixes #1556.
                // Skip for arbitrary!() — variable must remain unconstrained (#2518).
                runtime_captures.push((var_name, var_type));
            }
        }
    }

    // Build the transformed block by interleaving original statements with
    // runtime capture calls after each function-call let-binding.
    let transformed_block = build_transformed_block(block, &runtime_captures);

    LocalVarExtraction {
        pre_block,
        transformed_block,
    }
}

/// Builds a transformed block that injects runtime value capture calls after
/// each let-binding that has a non-encodable initializer (function call, etc.).
///
/// The capture calls read the variable's runtime value and add an assumption
/// like `result == 7` to the verification context. This must happen inside
/// the block because the variables are scoped to it.
fn build_transformed_block(
    block: &syn::Block,
    runtime_captures: &[(String, String)],
) -> TokenStream {
    if runtime_captures.is_empty() {
        // No captures needed — return original block unchanged
        return quote! { #block };
    }

    // Build a map from variable name to its type for quick lookup
    let capture_map: std::collections::HashMap<&str, &str> = runtime_captures
        .iter()
        .map(|(name, ty)| (name.as_str(), ty.as_str()))
        .collect();

    // Reconstruct the block, inserting capture calls after matching let-bindings
    let mut transformed_stmts = Vec::new();
    for stmt in &block.stmts {
        // Emit the original statement
        transformed_stmts.push(quote! { #stmt });

        // Check if this is a let-binding that needs a runtime capture
        if let Stmt::Local(local) = stmt {
            let var_name = match &local.pat {
                Pat::Type(pat_type) => match pat_type.pat.as_ref() {
                    Pat::Ident(pat_ident) => Some(pat_ident.ident.to_string()),
                    _ => None,
                },
                Pat::Ident(pat_ident) => Some(pat_ident.ident.to_string()),
                _ => None,
            };

            if let Some(name) = var_name {
                if let Some(&var_type) = capture_map.get(name.as_str()) {
                    if let Some(capture) = emit_runtime_value_capture(&name, var_type) {
                        transformed_stmts.push(capture);
                    }
                }
            }
        }
    }

    quote! { { #(#transformed_stmts)* } }
}

/// Emits a TokenStream that captures a variable's runtime value as a let-binding
/// assumption. Inserted inside the block right after the let-binding statement.
///
/// Returns `None` for types that can't be captured as BV constants (str, f64, etc.).
/// For integer types, generates a call to `collect_let_binding_runtime_value` or
/// `collect_let_binding_runtime_value_i128` with the appropriate cast.
fn emit_runtime_value_capture(var_name: &str, var_type: &str) -> Option<TokenStream> {
    let ident = syn::Ident::new(var_name, proc_macro2::Span::call_site());
    let support_root = crate::macro_support_root();

    // Map Rust type to the appropriate runtime capture call.
    // Integer types that fit in i64 use the i64 variant; larger types use i128.
    match var_type {
        "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" => Some(quote! {
            #support_root::verify_macro::collect_let_binding_runtime_value(
                #var_name.to_string(),
                #ident as i64,
            );
        }),
        "u64" | "usize" | "isize" | "i128" => Some(quote! {
            #support_root::verify_macro::collect_let_binding_runtime_value_i128(
                #var_name.to_string(),
                #ident as i128,
            );
        }),
        "u128" => Some(quote! {
            #support_root::verify_macro::collect_let_binding_runtime_value_u128(
                #var_name.to_string(),
                #ident,
            );
        }),
        "bool" => {
            // For booleans, use string "true"/"false" to avoid Bool vs Int
            // sort mismatch in ay encoding. Fixes #2558.
            Some(quote! {
                #support_root::verify_macro::collect_let_binding(
                    #var_name.to_string(),
                    if #ident { "true".to_string() } else { "false".to_string() },
                );
            })
        }
        // str, f64, f32, and other non-BV types: skip (not encodable)
        _ => None,
    }
}

#[cfg(test)]
#[path = "local_vars_tests/mod.rs"]
mod tests;

#[cfg(test)]
mod proph_wrapper_tests {
    use super::extract_type_string;

    #[test]
    fn test_extract_type_string_proph_i32_erases() {
        let ty: syn::Type = syn::parse_str("Proph<i32>").expect("invariant: test input is valid");
        assert_eq!(extract_type_string(&ty), "i32");
    }

    #[test]
    fn test_extract_type_string_ref_proph_seq_erases_both() {
        let ty: syn::Type =
            syn::parse_str("&Proph<Seq<u64>>").expect("invariant: test input is valid");
        assert_eq!(extract_type_string(&ty), "Seq<u64>");
    }
}
