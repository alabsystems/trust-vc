// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Extended expansion logic for trust_vc proc macros.
//!
//! Handles: quantifiers (forall, exists), solver-mode assertions
//! (nonlinear, bit_vector, compute), loop macros (invariant, loop_decreases),
//! and decreases_to.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use quote::quote;
use std::collections::BTreeSet;
use syn::fold::{self, Fold};
use syn::visit::{self, Visit};

use crate::condition_idents::generate_variable_registrations;
use crate::macro_expand::{
    canonical_expr_ast_string, generate_obligation_collection, normalize_expr_tokens,
    parse_expr_with_chains,
};
use trust_vc_core::{closure_to_quantifier_tokens, expr_to_try_builder_tokens};

/// Generates the obligation collection call for a solver-mode-specific assertion.
///
/// Tries the typed `TrustVcExpr` path first (Phase 5 Step 3b). Falls back to
/// string-based `collect_solver_mode_obligation` for unsupported expression forms.
/// Attaches a `SolverMode` to the obligation so the encoder can dispatch to the
/// correct solver or fail closed with Unknown. Part of #2144.
fn generate_solver_mode_obligation_collection(
    expr_tokens: &proc_macro2::TokenStream,
    ast_string: &str,
    kind_tokens: proc_macro2::TokenStream,
    name_prefix: &str,
    solver_mode: &str,
) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let parsed = parse_expr_with_chains(expr_tokens).ok();
    let try_builder = parsed.as_ref().and_then(expr_to_try_builder_tokens);

    if let Some(builder) = try_builder {
        // Runtime fallback: if variable type lookup fails, use string path. #2233.
        quote! {
            if let Some(__trust_vc_expr) = { #builder } {
                #support_root::verify_macro::collect_solver_mode_obligation_expr(
                    #kind_tokens,
                    format!("{}{}", #name_prefix, line!()),
                    #ast_string.to_string(),
                    __trust_vc_expr,
                    Some(format!("{}:{}", file!(), line!())),
                    #solver_mode,
                );
            } else {
                #support_root::verify_macro::collect_solver_mode_obligation(
                    #kind_tokens,
                    format!("{}{}", #name_prefix, line!()),
                    #ast_string.to_string(),
                    Some(format!("{}:{}", file!(), line!())),
                    #solver_mode,
                );
            }
        }
    } else {
        quote! {
            #support_root::verify_macro::collect_solver_mode_obligation(
                #kind_tokens,
                format!("{}{}", #name_prefix, line!()),
                #ast_string.to_string(),
                Some(format!("{}:{}", file!(), line!())),
                #solver_mode,
            );
        }
    }
}

/// Generates the obligation collection call for a quantifier (forall/exists).
///
/// Phase 5 Step 3b (#1866): Tries `closure_to_quantifier_tokens` first for the
/// typed `TrustVcExpr` path. Falls back to string-based `collect_obligation` for
/// unsupported closure forms (e.g. non-typed parameters, complex body).
fn generate_quantifier_obligation_collection(
    closure_tokens: &proc_macro2::TokenStream,
    kind: &str,
    name: &str,
    condition_str: &str,
) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let parsed = syn::parse2::<syn::Expr>(closure_tokens.clone()).ok();
    let builder_tokens = parsed.as_ref().and_then(|expr| {
        if let syn::Expr::Closure(closure) = expr {
            closure_to_quantifier_tokens(closure, kind)
        } else {
            None
        }
    });

    if let Some(builder) = builder_tokens {
        // closure_to_quantifier_tokens returns Option<TrustVcExpr> at runtime.
        // Runtime fallback if free variable type lookup fails. #2233.
        quote! {
            if let Some(__trust_vc_expr) = { #builder } {
                #support_root::verify_macro::collect_obligation_expr(
                    #support_root::vc::ObligationKind::Assert,
                    #name.to_string(),
                    #condition_str.to_string(),
                    __trust_vc_expr,
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                );
            } else {
                #support_root::verify_macro::collect_obligation(
                    #support_root::vc::ObligationKind::Assert,
                    #name.to_string(),
                    #condition_str.to_string(),
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                );
            }
        }
    } else {
        quote! {
            #support_root::verify_macro::collect_obligation(
                #support_root::vc::ObligationKind::Assert,
                #name.to_string(),
                #condition_str.to_string(),
                Some(format!("{}:{}:{}", file!(), line!(), column!())),
            );
        }
    }
}

struct TriggerAttrStripper;

impl Fold for TriggerAttrStripper {
    fn fold_expr(&mut self, expr: syn::Expr) -> syn::Expr {
        let mut expr = fold::fold_expr(self, expr);
        strip_expr_trigger_attrs(&mut expr);
        expr
    }
}

fn strip_expr_trigger_attrs(expr: &mut syn::Expr) {
    let Some(attrs) = expr_attrs_mut(expr) else {
        return;
    };
    attrs.retain(|attr| !attr_path_ends_with(attr, "trigger"));
}

fn expr_attrs_mut(expr: &mut syn::Expr) -> Option<&mut Vec<syn::Attribute>> {
    match expr {
        syn::Expr::Array(expr) => Some(&mut expr.attrs),
        syn::Expr::Assign(expr) => Some(&mut expr.attrs),
        syn::Expr::Async(expr) => Some(&mut expr.attrs),
        syn::Expr::Await(expr) => Some(&mut expr.attrs),
        syn::Expr::Binary(expr) => Some(&mut expr.attrs),
        syn::Expr::Block(expr) => Some(&mut expr.attrs),
        syn::Expr::Break(expr) => Some(&mut expr.attrs),
        syn::Expr::Call(expr) => Some(&mut expr.attrs),
        syn::Expr::Cast(expr) => Some(&mut expr.attrs),
        syn::Expr::Closure(expr) => Some(&mut expr.attrs),
        syn::Expr::Const(expr) => Some(&mut expr.attrs),
        syn::Expr::Continue(expr) => Some(&mut expr.attrs),
        syn::Expr::Field(expr) => Some(&mut expr.attrs),
        syn::Expr::ForLoop(expr) => Some(&mut expr.attrs),
        syn::Expr::Group(expr) => Some(&mut expr.attrs),
        syn::Expr::If(expr) => Some(&mut expr.attrs),
        syn::Expr::Index(expr) => Some(&mut expr.attrs),
        syn::Expr::Infer(expr) => Some(&mut expr.attrs),
        syn::Expr::Let(expr) => Some(&mut expr.attrs),
        syn::Expr::Lit(expr) => Some(&mut expr.attrs),
        syn::Expr::Loop(expr) => Some(&mut expr.attrs),
        syn::Expr::Macro(expr) => Some(&mut expr.attrs),
        syn::Expr::Match(expr) => Some(&mut expr.attrs),
        syn::Expr::MethodCall(expr) => Some(&mut expr.attrs),
        syn::Expr::Paren(expr) => Some(&mut expr.attrs),
        syn::Expr::Path(expr) => Some(&mut expr.attrs),
        syn::Expr::Range(expr) => Some(&mut expr.attrs),
        syn::Expr::Reference(expr) => Some(&mut expr.attrs),
        syn::Expr::Repeat(expr) => Some(&mut expr.attrs),
        syn::Expr::Return(expr) => Some(&mut expr.attrs),
        syn::Expr::Struct(expr) => Some(&mut expr.attrs),
        syn::Expr::Try(expr) => Some(&mut expr.attrs),
        syn::Expr::TryBlock(expr) => Some(&mut expr.attrs),
        syn::Expr::Tuple(expr) => Some(&mut expr.attrs),
        syn::Expr::Unary(expr) => Some(&mut expr.attrs),
        syn::Expr::Unsafe(expr) => Some(&mut expr.attrs),
        _ => None,
    }
}

fn attr_path_ends_with(attr: &syn::Attribute, name: &str) -> bool {
    attr.path()
        .segments
        .last()
        .is_some_and(|segment| segment.ident == name)
}

fn strip_quantifier_typecheck_triggers(
    closure: &proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    let Ok(expr) = syn::parse2::<syn::Expr>(closure.clone()) else {
        return closure.clone();
    };
    let sanitized = TriggerAttrStripper.fold_expr(expr);
    quote! { #sanitized }
}

/// Expands `forall!(|x: T| expr)`.
///
/// Phase 5 Step 3b (#1866): Tries TrustVcExpr builder path for the closure.
/// Falls back to string-based collection if the closure body is unsupported.
pub(crate) fn expand_forall(closure: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let closure_string = closure.to_string();
    let condition_str = format!("forall({})", closure_string);
    let collection =
        generate_quantifier_obligation_collection(&closure, "Forall", "forall", &condition_str);
    let typecheck_closure = strip_quantifier_typecheck_triggers(&closure);

    quote! {
        {
            let _forall_closure = #typecheck_closure;

            #[cfg(trust_mc)]
            {
                #support_root::verify_macro::collect_obligation(
                    #support_root::vc::ObligationKind::Assert,
                    "forall".to_string(),
                    #condition_str.to_string(),
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                );
            }
            #[cfg(all(test, not(trust_mc)))]
            {
                #collection
            }
            #[cfg(not(any(trust_mc, test, trust_vc_driver)))]
            {
                true
            }
            // Surface bridge: under `--cfg trust_vc_driver` the leaf is a REAL
            // `forall(<closure>)` marker call (never a vacuous `true`), so the
            // rustc-driver front end reads the CLOSURE arg and lowers the REAL
            // universal quantifier. Mutually exclusive with the `true` arm above.
            #[cfg(trust_vc_driver)]
            {
                ::trust_vc_core::__driver_markers::forall(#typecheck_closure)
            }
            #[cfg(any(trust_mc, test))]
            {
                #support_root::verify_macro::verify_quantifier_inline(#condition_str)
            }
        }
    }
}

/// Expands `exists!(|x: T| expr)`.
///
/// Phase 5 Step 3b (#1866): Tries TrustVcExpr builder path for the closure.
/// Falls back to string-based collection if the closure body is unsupported.
pub(crate) fn expand_exists(closure: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let closure_string = closure.to_string();
    let condition_str = format!("exists({})", closure_string);
    let collection =
        generate_quantifier_obligation_collection(&closure, "Exists", "exists", &condition_str);
    let typecheck_closure = strip_quantifier_typecheck_triggers(&closure);

    quote! {
        {
            let _exists_closure = #typecheck_closure;

            #[cfg(trust_mc)]
            {
                #support_root::verify_macro::collect_obligation(
                    #support_root::vc::ObligationKind::Assert,
                    "exists".to_string(),
                    #condition_str.to_string(),
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                );
            }
            #[cfg(all(test, not(trust_mc)))]
            {
                #collection
            }
            #[cfg(not(any(trust_mc, test, trust_vc_driver)))]
            {
                true
            }
            // Surface bridge: under `--cfg trust_vc_driver` the leaf is a REAL
            // `exists(<closure>)` marker call (never a vacuous `true`), so the
            // rustc-driver front end reads the CLOSURE arg and lowers the REAL
            // existential quantifier. Mutually exclusive with the `true` arm above.
            #[cfg(trust_vc_driver)]
            {
                ::trust_vc_core::__driver_markers::exists(#typecheck_closure)
            }
            #[cfg(any(trust_mc, test))]
            {
                #support_root::verify_macro::verify_quantifier_inline(#condition_str)
            }
        }
    }
}

/// Expands `choose!(|x: T| cond(x))`.
///
/// Witness extraction from an existential quantifier. Returns a value of type T
/// satisfying the condition if one exists, otherwise an arbitrary T.
/// Part of #2143.
pub(crate) fn expand_choose(closure: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let closure_string = closure.to_string();
    let condition_str = format!("choose({})", closure_string);

    // Parse the closure to extract the binder type for the runtime default value.
    let parsed = syn::parse2::<syn::Expr>(closure.clone()).ok();
    let default_expr = parsed
        .as_ref()
        .and_then(|expr| {
            if let syn::Expr::Closure(c) = expr {
                // Extract the first parameter's type
                c.inputs.first().and_then(|input| {
                    if let syn::Pat::Type(pt) = input {
                        let ty = &pt.ty;
                        Some(quote! { <#ty as ::core::default::Default>::default() })
                    } else {
                        None
                    }
                })
            } else {
                None
            }
        })
        .unwrap_or_else(|| quote! { Default::default() });

    let collection =
        generate_quantifier_obligation_collection(&closure, "Choose", "choose", &condition_str);

    quote! {
        {
            let _choose_closure = #closure;

            #[cfg(all(test, not(trust_mc)))]
            {
                #collection
            }
            #[cfg(trust_mc)]
            {
                #support_root::verify_macro::collect_obligation(
                    #support_root::vc::ObligationKind::Assert,
                    "choose".to_string(),
                    #condition_str.to_string(),
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                );
            }
            // Runtime placeholder — symbolic meaning comes from the encoder.
            #default_expr
        }
    }
}

/// Expands `assert_by_nonlinear!(condition)`.
pub(crate) fn expand_assert_by_nonlinear(
    tokens: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let parsed_input = match trust_vc_core::parse_solver_mode_assert(tokens.clone()) {
        Ok(parsed) => parsed,
        Err(err) => return err.to_compile_error(),
    };
    if parsed_input.body.is_some() {
        // Fail-closed: the compiled proc-macro (test-mode) path does not lower
        // scoped proof blocks yet; only the source-level vc_extraction path
        // does (#2778). Rejecting at compile time prevents silently dropping
        // the block's proof obligations.
        return syn::Error::new(
            proc_macro2::Span::call_site(),
            "`{ .. }` proof blocks are not supported by the compiled macro path; \
             use the source-level verifier (cargo trust-vc check)",
        )
        .to_compile_error();
    }
    if parsed_input.compute_only {
        return syn::Error::new(
            proc_macro2::Span::call_site(),
            "`compute_only` is only supported by assert_by_compute!",
        )
        .to_compile_error();
    }
    let condition_tokens = parsed_input.condition_tokens();
    let requires_tokens = parsed_input.requires_tokens();
    let normalized_tokens = match normalize_expr_tokens(&condition_tokens) {
        Ok(tokens) => tokens,
        Err(err) => return err.to_compile_error(),
    };
    let ast_string = canonical_expr_ast_string(&normalized_tokens);
    let mut var_registrations = vec![generate_variable_registrations(&normalized_tokens)];
    let mut requires_collections = Vec::new();
    let mut requires_type_checks = Vec::new();
    for requires in &requires_tokens {
        let normalized_requires = match normalize_expr_tokens(requires) {
            Ok(tokens) => tokens,
            Err(err) => return err.to_compile_error(),
        };
        let requires_ast_string = canonical_expr_ast_string(&normalized_requires);
        var_registrations.push(generate_variable_registrations(&normalized_requires));
        requires_collections.push(generate_obligation_collection(
            &normalized_requires,
            &requires_ast_string,
            quote! { #support_root::vc::ObligationKind::Requires },
            "assert_by_nonlinear_requires_line_",
        ));
        requires_type_checks.push(quote! {
            if false { let _ = || -> bool { #normalized_requires }; }
        });
    }
    let collection = generate_solver_mode_obligation_collection(
        &normalized_tokens,
        &ast_string,
        quote! { #support_root::vc::ObligationKind::Assert },
        "assert_by_nonlinear_line_",
        "nonlinear_arith",
    );
    let scope_key = quote! {
        format!("assert_by_nonlinear_line_{}_col_{}", line!(), column!())
    };
    let scoped_collection = generate_solver_mode_assert_by_scope_end(
        &normalized_tokens,
        &ast_string,
        quote! { #support_root::vc::SolverMode::NonlinearArith },
    );
    let proof_body = if requires_tokens.is_empty() {
        quote! {
            #collection
        }
    } else {
        quote! {
            #support_root::verify_macro::begin_assert_by_scope(#scope_key);
            #(#requires_collections)*
            let condition_str = #ast_string.to_string();
            #scoped_collection
        }
    };
    quote! {
        {
            #[cfg(trust_mc)]
            {
                let __trust_vc_solver_mode = "nonlinear_arith";
                let __trust_vc_assert_expr = #ast_string;
            }
            #[cfg(test)]
            {
                #(#var_registrations)*
                #proof_body
                if false { let _ = || { #normalized_tokens }; }
                #(#requires_type_checks)*
            }
            #[cfg(not(any(trust_mc, test)))]
            {
                if false { let _ = || { #normalized_tokens }; }
                #(#requires_type_checks)*
            }
        }
    }
}

/// Expands `assert_by_bit_vector!(condition)`.
pub(crate) fn expand_assert_by_bit_vector(
    tokens: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let parsed_input = match trust_vc_core::parse_solver_mode_assert(tokens.clone()) {
        Ok(parsed) => parsed,
        Err(err) => return err.to_compile_error(),
    };
    if parsed_input.body.is_some() {
        // Fail-closed: the compiled proc-macro (test-mode) path does not lower
        // scoped proof blocks yet; only the source-level vc_extraction path
        // does (#2778). Rejecting at compile time prevents silently dropping
        // the block's proof obligations.
        return syn::Error::new(
            proc_macro2::Span::call_site(),
            "`{ .. }` proof blocks are not supported by the compiled macro path; \
             use the source-level verifier (cargo trust-vc check)",
        )
        .to_compile_error();
    }
    if parsed_input.compute_only {
        return syn::Error::new(
            proc_macro2::Span::call_site(),
            "`compute_only` is only supported by assert_by_compute!",
        )
        .to_compile_error();
    }
    let condition_tokens = parsed_input.condition_tokens();
    let requires_tokens = parsed_input.requires_tokens();
    let normalized_tokens = match normalize_expr_tokens(&condition_tokens) {
        Ok(tokens) => tokens,
        Err(err) => return err.to_compile_error(),
    };
    let ast_string = canonical_expr_ast_string(&normalized_tokens);
    let mut var_registrations = vec![generate_variable_registrations(&normalized_tokens)];
    let mut requires_collections = Vec::new();
    let mut requires_type_checks = Vec::new();
    for requires in &requires_tokens {
        let normalized_requires = match normalize_expr_tokens(requires) {
            Ok(tokens) => tokens,
            Err(err) => return err.to_compile_error(),
        };
        let requires_ast_string = canonical_expr_ast_string(&normalized_requires);
        var_registrations.push(generate_variable_registrations(&normalized_requires));
        requires_collections.push(generate_obligation_collection(
            &normalized_requires,
            &requires_ast_string,
            quote! { #support_root::vc::ObligationKind::Requires },
            "assert_by_bit_vector_requires_line_",
        ));
        requires_type_checks.push(quote! {
            if false { let _ = || -> bool { #normalized_requires }; }
        });
    }
    let collection = generate_solver_mode_obligation_collection(
        &normalized_tokens,
        &ast_string,
        quote! { #support_root::vc::ObligationKind::Assert },
        "assert_by_bit_vector_line_",
        "bit_vector",
    );
    let scope_key = quote! {
        format!("assert_by_bit_vector_line_{}_col_{}", line!(), column!())
    };
    let scoped_collection = generate_solver_mode_assert_by_scope_end(
        &normalized_tokens,
        &ast_string,
        quote! { #support_root::vc::SolverMode::BitVector },
    );
    let proof_body = if requires_tokens.is_empty() {
        quote! {
            #collection
        }
    } else {
        quote! {
            #support_root::verify_macro::begin_assert_by_scope(#scope_key);
            #(#requires_collections)*
            let condition_str = #ast_string.to_string();
            #scoped_collection
        }
    };
    quote! {
        {
            #[cfg(trust_mc)]
            {
                let __trust_vc_solver_mode = "bit_vector";
                let __trust_vc_assert_expr = #ast_string;
            }
            #[cfg(test)]
            {
                #(#var_registrations)*
                #proof_body
                if false { let _ = || { #normalized_tokens }; }
                #(#requires_type_checks)*
            }
            #[cfg(not(any(trust_mc, test)))]
            {
                if false { let _ = || { #normalized_tokens }; }
                #(#requires_type_checks)*
            }
        }
    }
}

fn generate_solver_mode_assert_by_scope_end(
    normalized_tokens: &proc_macro2::TokenStream,
    ast_string: &str,
    solver_mode_tokens: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let parsed = parse_expr_with_chains(normalized_tokens).ok();
    let try_builder = parsed.as_ref().and_then(expr_to_try_builder_tokens);

    if let Some(builder) = try_builder {
        quote! {
            if let Some(__trust_vc_expr) = { #builder } {
                #support_root::verify_macro::end_assert_by_scope_expr_with_solver_mode(
                    condition_str,
                    __trust_vc_expr,
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                    #solver_mode_tokens,
                );
            } else {
                #support_root::verify_macro::end_assert_by_scope_with_solver_mode(
                    condition_str,
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                    #solver_mode_tokens,
                );
            }
        }
    } else {
        quote! {
            #support_root::verify_macro::end_assert_by_scope_with_solver_mode(
                #ast_string.to_string(),
                Some(format!("{}:{}:{}", file!(), line!(), column!())),
                #solver_mode_tokens,
            );
        }
    }
}

/// Expands `assert_by_compute!(condition)`.
pub(crate) fn expand_assert_by_compute(
    tokens: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let parsed_input = match trust_vc_core::parse_solver_mode_assert(tokens.clone()) {
        Ok(parsed) => parsed,
        Err(err) => return err.to_compile_error(),
    };
    if parsed_input.body.is_some() {
        // Fail-closed: the compiled proc-macro (test-mode) path does not lower
        // scoped proof blocks yet; only the source-level vc_extraction path
        // does (#2778). Rejecting at compile time prevents silently dropping
        // the block's proof obligations.
        return syn::Error::new(
            proc_macro2::Span::call_site(),
            "`{ .. }` proof blocks are not supported by the compiled macro path; \
             use the source-level verifier (cargo trust-vc check)",
        )
        .to_compile_error();
    }
    if !parsed_input.requires.is_empty() {
        return syn::Error::new(
            proc_macro2::Span::call_site(),
            "`requires` clauses are not supported by assert_by_compute!",
        )
        .to_compile_error();
    }
    let condition_tokens = parsed_input.condition_tokens();
    let normalized_tokens = match normalize_expr_tokens(&condition_tokens) {
        Ok(tokens) => tokens,
        Err(err) => return err.to_compile_error(),
    };
    let ast_string = canonical_expr_ast_string(&normalized_tokens);
    let var_registrations = generate_compute_variable_registrations(&normalized_tokens);
    let collection = generate_solver_mode_obligation_collection(
        &normalized_tokens,
        &ast_string,
        quote! { #support_root::vc::ObligationKind::Assert },
        "assert_by_compute_line_",
        "compute",
    );
    quote! {
        {
            #[cfg(trust_mc)]
            {
                let __trust_vc_solver_mode = "compute";
                let __trust_vc_assert_expr = #ast_string;
            }
            #[cfg(test)]
            {
                #var_registrations
                #collection
                if false { let _ = || { #normalized_tokens }; }
            }
            #[cfg(not(any(trust_mc, test)))]
            {
                if false { let _ = || { #normalized_tokens }; }
            }
        }
    }
}

fn generate_compute_variable_registrations(
    normalized_tokens: &proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    match parse_expr_with_chains(normalized_tokens) {
        Ok(syn::Expr::Block(block)) => {
            generate_variable_registrations_for_names(&free_block_variable_idents(&block.block))
        }
        _ => generate_variable_registrations(normalized_tokens),
    }
}

fn generate_variable_registrations_for_names(names: &[String]) -> proc_macro2::TokenStream {
    if names.is_empty() {
        return proc_macro2::TokenStream::new();
    }

    let support_root = trust_vc_core::macro_support_root();
    let registrations = names.iter().map(|name| {
        let ident = proc_macro2::Ident::new(name, proc_macro2::Span::call_site());
        let name_str = name.as_str();
        quote! {
            #support_root::verify_macro::collect_variable_runtime(#name_str, &#ident);
        }
    });

    quote! { #(#registrations)* }
}

fn free_block_variable_idents(block: &syn::Block) -> Vec<String> {
    let mut visitor = BlockFreeVarVisitor::new();
    visitor.visit_block(block);
    visitor.free.into_iter().collect()
}

struct BlockFreeVarVisitor {
    scopes: Vec<BTreeSet<String>>,
    free: BTreeSet<String>,
}

impl BlockFreeVarVisitor {
    fn new() -> Self {
        Self {
            scopes: vec![BTreeSet::new()],
            free: BTreeSet::new(),
        }
    }

    fn is_bound(&self, name: &str) -> bool {
        self.scopes.iter().rev().any(|scope| scope.contains(name))
    }

    fn bind_pat(&mut self, pat: &syn::Pat) {
        struct BindingVisitor {
            names: Vec<String>,
        }

        impl<'ast> Visit<'ast> for BindingVisitor {
            fn visit_pat_ident(&mut self, pat_ident: &'ast syn::PatIdent) {
                self.names.push(pat_ident.ident.to_string());
                visit::visit_pat_ident(self, pat_ident);
            }
        }

        let mut visitor = BindingVisitor { names: Vec::new() };
        visitor.visit_pat(pat);
        if let Some(scope) = self.scopes.last_mut() {
            scope.extend(visitor.names);
        }
    }

    fn with_scope(&mut self, f: impl FnOnce(&mut Self)) {
        self.scopes.push(BTreeSet::new());
        f(self);
        self.scopes.pop();
    }
}

impl<'ast> Visit<'ast> for BlockFreeVarVisitor {
    fn visit_block(&mut self, block: &'ast syn::Block) {
        self.with_scope(|visitor| {
            for stmt in &block.stmts {
                visitor.visit_stmt(stmt);
            }
        });
    }

    fn visit_local(&mut self, local: &'ast syn::Local) {
        if let Some(init) = &local.init {
            self.visit_expr(&init.expr);
            if let Some((_, diverge)) = &init.diverge {
                self.visit_expr(diverge);
            }
        }
        self.bind_pat(&local.pat);
    }

    fn visit_expr_path(&mut self, expr: &'ast syn::ExprPath) {
        if expr.qself.is_none() && expr.path.segments.len() == 1 {
            let name = expr.path.segments[0].ident.to_string();
            if !self.is_bound(&name) && is_runtime_variable_ident(&name) {
                self.free.insert(name);
            }
        }
    }

    fn visit_expr_call(&mut self, expr: &'ast syn::ExprCall) {
        for arg in &expr.args {
            self.visit_expr(arg);
        }
    }

    fn visit_expr_method_call(&mut self, expr: &'ast syn::ExprMethodCall) {
        self.visit_expr(&expr.receiver);
        for arg in &expr.args {
            self.visit_expr(arg);
        }
    }

    fn visit_expr_closure(&mut self, expr: &'ast syn::ExprClosure) {
        self.with_scope(|visitor| {
            for input in &expr.inputs {
                visitor.bind_pat(input);
            }
            visitor.visit_expr(&expr.body);
        });
    }

    fn visit_expr_for_loop(&mut self, expr: &'ast syn::ExprForLoop) {
        self.visit_expr(&expr.expr);
        self.with_scope(|visitor| {
            visitor.bind_pat(&expr.pat);
            visitor.visit_block(&expr.body);
        });
    }

    fn visit_expr_while(&mut self, expr: &'ast syn::ExprWhile) {
        if let syn::Expr::Let(expr_let) = &*expr.cond {
            self.visit_expr(&expr_let.expr);
            self.with_scope(|visitor| {
                visitor.bind_pat(&expr_let.pat);
                visitor.visit_block(&expr.body);
            });
        } else {
            self.visit_expr(&expr.cond);
            self.visit_block(&expr.body);
        }
    }

    fn visit_expr_if(&mut self, expr: &'ast syn::ExprIf) {
        if let syn::Expr::Let(expr_let) = &*expr.cond {
            self.visit_expr(&expr_let.expr);
            self.with_scope(|visitor| {
                visitor.bind_pat(&expr_let.pat);
                visitor.visit_block(&expr.then_branch);
            });
        } else {
            self.visit_expr(&expr.cond);
            self.visit_block(&expr.then_branch);
        }

        if let Some((_, else_branch)) = &expr.else_branch {
            self.visit_expr(else_branch);
        }
    }

    fn visit_expr_match(&mut self, expr: &'ast syn::ExprMatch) {
        self.visit_expr(&expr.expr);
        for arm in &expr.arms {
            self.with_scope(|visitor| {
                visitor.bind_pat(&arm.pat);
                if let Some((_, guard)) = &arm.guard {
                    visitor.visit_expr(guard);
                }
                visitor.visit_expr(&arm.body);
            });
        }
    }
}

fn is_runtime_variable_ident(name: &str) -> bool {
    !matches!(
        name,
        "true"
            | "false"
            | "self"
            | "Self"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "bool"
            | "char"
            | "str"
    )
}

#[cfg(test)]
mod assert_by_compute_tests {
    use quote::quote;

    use super::expand_assert_by_compute;

    #[test]
    fn block_local_lets_do_not_emit_outer_variable_registrations() {
        let expanded = expand_assert_by_compute(quote!({
            let x: i32 = 4;
            let r1: i32 = x + 1;
            let x: i32 = 5;
            let r2: i32 = x + 1;
            r1 == r2
        }))
        .to_string();

        assert!(
            !expanded.contains("collect_variable_runtime"),
            "block-local let names must not be registered before the block: {expanded}"
        );
        assert!(
            expanded.contains("collect_solver_mode_obligation"),
            "block expressions should still collect a compute obligation: {expanded}"
        );
    }

    #[test]
    fn block_free_variables_still_emit_runtime_registrations() {
        let expanded = expand_assert_by_compute(quote!({
            let y: i32 = outer + 3;
            y == expected
        }))
        .to_string();

        assert!(
            expanded.contains("collect_variable_runtime (\"outer\""),
            "free outer variable should be registered before compute collection: {expanded}"
        );
        assert!(
            expanded.contains("collect_variable_runtime (\"expected\""),
            "free expected variable should be registered before compute collection: {expanded}"
        );
        assert!(
            !expanded.contains("collect_variable_runtime (\"y\""),
            "block-local let variable must not be registered before the block: {expanded}"
        );
    }

    #[test]
    fn bitwise_constants_use_typed_compute_collection() {
        let expanded =
            expand_assert_by_compute(quote!((0b1010u8 & 0b1100u8) == 0b1000u8)).to_string();

        assert!(
            expanded.contains("collect_solver_mode_obligation_expr"),
            "bitwise constant compute should use the typed obligation path: {expanded}"
        );
        assert!(
            expanded.contains("special_arith_inferred"),
            "bitwise operators should lower to typed SpecialArith builders: {expanded}"
        );
    }

    #[test]
    fn compute_only_clause_uses_condition_for_compute_collection() {
        let expanded =
            expand_assert_by_compute(quote!(2u32 + 3u32 == 5u32; compute_only)).to_string();

        assert!(
            expanded.contains("collect_solver_mode_obligation_expr"),
            "compute_only should still collect a typed compute obligation: {expanded}"
        );
        assert!(
            expanded.contains("\"compute\""),
            "compute_only should use compute solver mode: {expanded}"
        );
        assert!(
            !expanded.contains("compute_only"),
            "compute_only is parser syntax and should not be part of the condition: {expanded}"
        );
    }
}

#[cfg(test)]
mod quantifier_expand_tests {
    use quote::quote;

    use super::{expand_exists, expand_forall};

    #[test]
    fn forall_expression_trigger_is_not_reemitted_for_typechecking() {
        let expanded = expand_forall(quote! { |x: i32| #[trigger] f(x) && x > 0 }).to_string();

        assert!(
            expanded.contains("let _forall_closure = | x : i32 | f (x) && x > 0 ;"),
            "expression trigger attrs must not be re-emitted into stable Rust typecheck closure: {expanded}"
        );
        assert!(
            expanded.contains("Some") && expanded.contains("fn_call") && expanded.contains("\"f\""),
            "typed quantifier path should still preserve trigger metadata: {expanded}"
        );
    }

    #[test]
    fn exists_expression_trigger_is_not_reemitted_for_typechecking() {
        let expanded = expand_exists(quote! { |x: i32| #[trigger] f(x) && x > 0 }).to_string();

        assert!(
            expanded.contains("let _exists_closure = | x : i32 | f (x) && x > 0 ;"),
            "expression trigger attrs must not be re-emitted into stable Rust typecheck closure: {expanded}"
        );
        assert!(
            expanded.contains("Some") && expanded.contains("fn_call") && expanded.contains("\"f\""),
            "typed quantifier path should still preserve trigger metadata: {expanded}"
        );
    }
}

// Loop-related expansions extracted to macro_expand_ext_loops.rs (#2621).
pub(crate) use crate::macro_expand_ext_loops::{
    expand_arbitrary, expand_decreases_to, expand_invariant, expand_invariant_except_break,
    expand_loop_decreases, expand_loop_ensures,
};
