// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use quote::quote;
use syn::parse::Parser;

use super::{
    canonical_expr_ast_string, cite_reference_string, generate_obligation_collection,
    normalize_expr_tokens, split_macro_expr_and_tail,
};

/// Expands `assume!(expr)`.
pub(crate) fn expand_assume(expr: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let normalized_expr = match normalize_expr_tokens(&expr) {
        Ok(expr) => expr,
        Err(err) => return err.to_compile_error(),
    };
    let ast_string = canonical_expr_ast_string(&normalized_expr);
    let collection = generate_obligation_collection(
        &normalized_expr,
        &ast_string,
        quote! { #support_root::vc::ObligationKind::Assume },
        "assume_line_",
    );

    quote! {
        #[cfg(test)]
        {
            #collection
        }
        { let _ = || { #normalized_expr }; }
    }
}

/// Expands a `cite` contract clause / `cite!(expr)` / `cite!(expr, "ref")`.
///
/// A cited fact is an explicitly *trusted* assumption with provenance: it is
/// added to the assumption base as an `Assume` obligation — which the solver
/// treats as a trusted axiom — and tagged with its citation reference (woven
/// into the obligation name so the provenance is surfaced).
///
/// SOUNDNESS: this mirrors `assume!` / the `Axiom` trust path. The cited fact
/// is *assumed*, never *asserted/proven*; there is no runtime check and no
/// `Assert`/`Requires`/`Ensures` obligation, so `cite` can never cause an
/// obligation to be reported as proven on the strength of the citation alone.
pub(crate) fn expand_cite(
    expr: proc_macro2::TokenStream,
    reference: Option<String>,
) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let normalized_expr = match normalize_expr_tokens(&expr) {
        Ok(expr) => expr,
        Err(err) => return err.to_compile_error(),
    };
    let ast_string = canonical_expr_ast_string(&normalized_expr);
    // Weave the citation into the obligation name so the trust provenance is
    // visible wherever the assumed obligation is reported.
    let name_prefix = match &reference {
        Some(reference) => format!("cite[{reference}]_line_"),
        None => "cite_line_".to_string(),
    };
    let collection = generate_obligation_collection(
        &normalized_expr,
        &ast_string,
        quote! { #support_root::vc::ObligationKind::Assume },
        &name_prefix,
    );

    quote! {
        #[cfg(test)]
        {
            #collection
        }
        // A cited fact is trusted, not checked: assumed at runtime like assume!.
        { let _ = || { #normalized_expr }; }
    }
}

/// Parses `cite!(expr)` / `cite!(expr, "reference")` argument tokens and
/// delegates to [`expand_cite`]. The reference may be a string literal or a
/// path to an external proof/lemma/source.
pub(crate) fn expand_cite_tokens(tokens: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let args = match syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated
        .parse2(tokens)
    {
        Ok(args) => args,
        Err(err) => return err.to_compile_error(),
    };
    let mut iter = args.iter();
    let Some(fact) = iter.next() else {
        return syn::Error::new(
            proc_macro2::Span::call_site(),
            "cite!() requires a cited fact expression: cite!(expr) or cite!(expr, \"reference\")",
        )
        .to_compile_error();
    };
    let reference = match iter.next() {
        Some(reference_expr) => match cite_reference_string(reference_expr) {
            Ok(reference) => Some(reference),
            Err(err) => return err.to_compile_error(),
        },
        None => None,
    };
    if iter.next().is_some() {
        return syn::Error::new(
            proc_macro2::Span::call_site(),
            "cite!() takes a cited fact and an optional citation reference: \
             cite!(expr) or cite!(expr, \"reference\")",
        )
        .to_compile_error();
    }
    expand_cite(quote!(#fact), reference)
}

/// Expands `assert!(expr)`.
///
/// Tries the typed `TrustVcExpr` path first (Phase 5 Step 3b). Falls back to
/// string-based `collect_typed_obligation` for unsupported expression forms.
///
/// Special-cases `ext_eq!`/`ext_ne!` macro invocations: each argument is
/// stringified independently and lowered at runtime via
/// `collect_ext_eq_obligation`, bypassing the whole-macro stringification
/// round-trip that breaks turbofish generics. Part of #2658.
pub(crate) fn expand_assert(
    expr: proc_macro2::TokenStream,
    parsed_expr: &syn::Expr,
) -> proc_macro2::TokenStream {
    // Detect ext_eq!/ext_ne! and use the specialized collection path.
    if let Some(ext_eq_collection) = try_expand_ext_eq_collection(parsed_expr) {
        let normalized_expr = quote!(#parsed_expr);
        return quote! {
            #[cfg(test)]
            {
                #ext_eq_collection
            }
            #[cfg(not(test))]
            {
                assert!(#normalized_expr, "trust_vc assertion failed: {}", stringify!(#expr));
            }
        };
    }

    let support_root = trust_vc_core::macro_support_root();
    let normalized_expr = quote!(#parsed_expr);
    let ast_string = normalized_expr.to_string();
    let collection = generate_obligation_collection(
        &normalized_expr,
        &ast_string,
        quote! { #support_root::vc::ObligationKind::Assert },
        "assert_line_",
    );

    quote! {
        #[cfg(test)]
        {
            #collection
        }
        #[cfg(not(test))]
        {
            assert!(#normalized_expr, "trust_vc assertion failed: {}", stringify!(#expr));
        }
    }
}

/// Expands `assert_seqs_equal!(lhs == rhs)`.
pub(crate) fn expand_assert_seqs_equal(
    input: &trust_vc_core::AssertSeqsEqualInput,
) -> proc_macro2::TokenStream {
    let lhs = &input.lhs;
    let rhs = &input.rhs;
    let normalized_expr = quote!(#lhs == #rhs);
    let ext_eq_collection = expand_ext_eq_collection(lhs, rhs, true);

    quote! {
        #[cfg(test)]
        {
            #ext_eq_collection
        }
        #[cfg(not(test))]
        {
            assert!(
                #normalized_expr,
                "trust_vc assertion failed: assert_seqs_equal!({})",
                stringify!(#normalized_expr)
            );
        }
    }
}

/// Detects `ext_eq!(lhs, rhs)` or `ext_ne!(lhs, rhs)` inside an assert
/// and generates a `collect_ext_eq_obligation` call with individually-
/// stringified arguments. Returns `None` for non-ext_eq expressions.
fn try_expand_ext_eq_collection(parsed_expr: &syn::Expr) -> Option<proc_macro2::TokenStream> {
    let mac = match parsed_expr {
        syn::Expr::Macro(mac) => mac,
        _ => return None,
    };

    let trailing = mac.mac.path.segments.last()?.ident.to_string();
    let is_eq = match trailing.as_str() {
        "ext_eq" => true,
        "ext_ne" => false,
        _ => return None,
    };

    let args = syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated
        .parse2(mac.mac.tokens.clone())
        .ok()?;
    let mut iter = args.into_iter();
    let lhs = iter.next()?;
    let rhs = iter.next()?;
    if iter.next().is_some() {
        return None; // exactly 2 args required
    }

    Some(expand_ext_eq_collection(&lhs, &rhs, is_eq))
}

fn expand_ext_eq_collection(
    lhs: &syn::Expr,
    rhs: &syn::Expr,
    is_eq: bool,
) -> proc_macro2::TokenStream {
    let lhs_str = quote!(#lhs).to_string();
    let rhs_str = quote!(#rhs).to_string();

    let support_root = trust_vc_core::macro_support_root();

    quote! {
        #support_root::verify_macro::collect_ext_eq_obligation(
            #support_root::vc::ObligationKind::Assert,
            format!("assert_line_{}_col_{}", line!(), column!()),
            #lhs_str.to_string(),
            #rhs_str.to_string(),
            #is_eq,
            Some(format!("{}:{}:{}", file!(), line!(), column!())),
        );
    }
}

/// Expands `requires!(expr)`.
pub(crate) fn expand_requires(expr: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let normalized_expr = match normalize_expr_tokens(&expr) {
        Ok(expr) => expr,
        Err(err) => return err.to_compile_error(),
    };
    let ast_string = canonical_expr_ast_string(&normalized_expr);
    let collection = generate_obligation_collection(
        &normalized_expr,
        &ast_string,
        quote! { #support_root::vc::ObligationKind::Requires },
        "requires_line_",
    );

    quote! {
        #[cfg(test)]
        {
            #collection
        }
        #[cfg(all(not(test), not(trust_vc_driver)))]
        {
            assert!(#normalized_expr, "trust_vc precondition failed: {}", stringify!(#expr));
        }
        // Surface bridge: under `--cfg trust_vc_driver` emit a BARE marker call
        // (statement level, not block-wrapped) so the rustc-driver front end sees
        // a direct `requires(..)` FnDef call and lowers the REAL precondition.
        // Mutually exclusive with the syn (`test`) and runtime (`not(test)`) arms.
        #[cfg(trust_vc_driver)]
        ::trust_vc_core::__driver_markers::requires(#normalized_expr);
    }
}

/// Expands `recommends!(expr)` — soft precondition (warning on violation).
/// Part of #2483.
pub(crate) fn expand_recommends(expr: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let normalized_expr = match normalize_expr_tokens(&expr) {
        Ok(expr) => expr,
        Err(err) => return err.to_compile_error(),
    };
    let ast_string = canonical_expr_ast_string(&normalized_expr);
    let collection = generate_obligation_collection(
        &normalized_expr,
        &ast_string,
        quote! { #support_root::vc::ObligationKind::Recommends },
        "recommends_line_",
    );

    quote! {
        #[cfg(test)]
        {
            #collection
        }
        #[cfg(not(test))]
        {
            // Recommends is advisory — no runtime assert. Debug-only check.
            debug_assert!(
                #normalized_expr,
                "trust_vc recommends condition failed: {}",
                stringify!(#expr)
            );
        }
    }
}

/// Expands `ghost_requires!(expr)`.
///
/// Ghost precondition — verified but not checked at runtime (ghost types may
/// not exist at runtime). In trust_vc test mode, collected as an Assume obligation
/// so the encoder can use it for reasoning. Fixes #2525.
pub(crate) fn expand_ghost_requires(expr: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let (condition_tokens, tail_tokens) = split_macro_expr_and_tail(expr);
    let normalized_expr = match normalize_expr_tokens(&condition_tokens) {
        Ok(expr) => expr,
        Err(err) => return err.to_compile_error(),
    };
    let ast_string = canonical_expr_ast_string(&normalized_expr);
    let collection = generate_obligation_collection(
        &normalized_expr,
        &ast_string,
        quote! { #support_root::vc::ObligationKind::Assume },
        "ghost_requires_line_",
    );

    if let Some(tail_tokens) = tail_tokens {
        quote! {
            #[cfg(trust_mc)]
            ::trust_mc::assume!(#normalized_expr, #tail_tokens);
            #[cfg(all(test, not(trust_mc)))]
            {
                #collection
            }
        }
    } else {
        quote! {
            #[cfg(trust_mc)]
            ::trust_mc::assume!(#normalized_expr);
            #[cfg(all(test, not(trust_mc)))]
            {
                #collection
            }
        }
    }
}

/// Expands `ghost_ensures!(expr)`.
///
/// Ghost postcondition — verified but not checked at runtime (ghost types may
/// not exist at runtime). In trust_vc test mode, collected as an Ensures obligation
/// so the encoder asserts it. Fixes #2525.
pub(crate) fn expand_ghost_ensures(expr: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let (condition_tokens, tail_tokens) = split_macro_expr_and_tail(expr);
    let normalized_expr = match normalize_expr_tokens(&condition_tokens) {
        Ok(expr) => expr,
        Err(err) => return err.to_compile_error(),
    };
    let ast_string = canonical_expr_ast_string(&normalized_expr);
    let collection = generate_obligation_collection(
        &normalized_expr,
        &ast_string,
        quote! { #support_root::vc::ObligationKind::Ensures },
        "ghost_ensures_line_",
    );

    if let Some(tail_tokens) = tail_tokens {
        quote! {
            #[cfg(trust_mc)]
            ::trust_mc::assert!(#normalized_expr, #tail_tokens);
            #[cfg(all(test, not(trust_mc)))]
            {
                #collection
            }
        }
    } else {
        quote! {
            #[cfg(trust_mc)]
            ::trust_mc::assert!(#normalized_expr);
            #[cfg(all(test, not(trust_mc)))]
            {
                #collection
            }
        }
    }
}

/// Expands `ensures!(expr)`.
///
/// Delegates to `postcondition_lowering::lower_postconditions` for analysis
/// and emission, then wraps the result in test/non-test branches.
pub(crate) fn expand_ensures(expr: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let lowered = match crate::postcondition_lowering::lower_postconditions(vec![expr.clone()]) {
        Ok(l) => l,
        Err(err) => return err.to_compile_error(),
    };

    let old_registrations = lowered.emit_test_old_registrations(
        crate::postcondition_lowering::TestOldRegistrationMode::SymbolicOnly,
    );
    let obligations = lowered.emit_test_obligations();
    let runtime_asserts = lowered.emit_runtime_asserts();
    // Surface bridge: bare, statement-level `ensures(..)` marker(s) under
    // `--cfg trust_vc_driver`, mutually exclusive with the syn/runtime arms.
    let driver_markers = lowered.emit_driver_markers();

    quote! {
        #[cfg(test)]
        {
            #(#old_registrations)*
            #(#obligations)*
        }
        #[cfg(all(not(test), not(trust_vc_driver)))]
        {
            #(#runtime_asserts)*
        }
        #(#driver_markers)*
    }
}

/// Expands `proof_block! { ... }`.
pub(crate) fn expand_proof_block(tokens: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    quote! {
        #[cfg(trust_mc)]
        {
            #tokens
        }
        #[cfg(not(trust_mc))]
        {
            let _ = || {
                #tokens
            };
        }
    }
}

/// Expands `old!(expr)`.
///
/// Fail-closed: only simple identifiers (`old!(x)`) and dereferences (`old!(*x)`)
/// are supported. Complex expressions produce a compile error. See #1836.
#[allow(clippy::indexing_slicing)] // invariant: `tokens[0]`/`tokens[1]` bounded by `match tokens.len()` arms (1 or 2)
pub(crate) fn expand_old(expr: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let tokens: Vec<proc_macro2::TokenTree> = expr.clone().into_iter().collect();
    let is_simple = match tokens.len() {
        1 => matches!(tokens[0], proc_macro2::TokenTree::Ident(_)),
        2 => {
            matches!(tokens[0], proc_macro2::TokenTree::Punct(ref p) if p.as_char() == '*')
                && matches!(tokens[1], proc_macro2::TokenTree::Ident(_))
        }
        _ => false,
    };
    if is_simple {
        quote! { { #expr } }
    } else {
        let expr_str = expr.to_string();
        quote! {
            compile_error!(concat!(
                "old!() only supports simple identifiers (old!(x) or old!(*x)); ",
                "complex expressions like old!(",
                #expr_str,
                ") are not yet supported \u{2014} see #1836"
            ))
        }
    }
}

fn track_let_binding_parts(local: &syn::Local) -> Option<(String, Option<&syn::Type>)> {
    match &local.pat {
        syn::Pat::Ident(pat_ident) => Some((pat_ident.ident.to_string(), None)),
        syn::Pat::Type(pat_type) => match pat_type.pat.as_ref() {
            syn::Pat::Ident(pat_ident) => {
                Some((pat_ident.ident.to_string(), Some(pat_type.ty.as_ref())))
            }
            _ => None,
        },
        _ => None,
    }
}

fn track_let_type_string(ty: &syn::Type) -> String {
    quote!(#ty).to_string().replace(' ', "")
}

fn is_track_let_arbitrary_expr(expr: &syn::Expr) -> bool {
    matches!(
        expr,
        syn::Expr::Macro(expr_macro)
            if expr_macro
                .mac
                .path
                .segments
                .last()
                .is_some_and(|segment| segment.ident == "arbitrary")
    )
}

fn is_track_let_encodable_expr(expr: &syn::Expr) -> bool {
    match expr {
        syn::Expr::Lit(_) => true,
        syn::Expr::Path(path) => path.path.get_ident().is_some(),
        syn::Expr::Binary(binary) => {
            is_track_let_encodable_expr(&binary.left) && is_track_let_encodable_expr(&binary.right)
        }
        syn::Expr::Unary(unary) => {
            !matches!(unary.op, syn::UnOp::Deref(_)) && is_track_let_encodable_expr(&unary.expr)
        }
        syn::Expr::Paren(paren) => is_track_let_encodable_expr(&paren.expr),
        syn::Expr::Cast(cast) => is_track_let_encodable_expr(&cast.expr),
        _ => false,
    }
}

fn expand_track_let_capture(local: &syn::Local) -> Option<proc_macro2::TokenStream> {
    let init = local.init.as_ref()?;
    let (var_name, ty) = track_let_binding_parts(local)?;
    let var_ident = syn::Ident::new(&var_name, proc_macro2::Span::call_site());
    let support_root = trust_vc_core::macro_support_root();

    let variable_registration = if let Some(ty) = ty {
        let ty = track_let_type_string(ty);
        quote! {
            #support_root::verify_macro::collect_variable(#var_name.to_string(), #ty.to_string());
        }
    } else {
        quote! {
            #support_root::verify_macro::collect_variable_runtime(#var_name, &#var_ident);
        }
    };

    let value_registration = if is_track_let_arbitrary_expr(&init.expr) {
        quote! {}
    } else if is_track_let_encodable_expr(&init.expr) {
        let init_expr = {
            let expr = &init.expr;
            quote!(#expr).to_string()
        };
        quote! {
            #support_root::verify_macro::collect_let_binding(
                #var_name.to_string(),
                #init_expr.to_string(),
            );
        }
    } else {
        quote! {
            #support_root::collect_let_binding_runtime_value_from_ref(#var_name, &#var_ident);
        }
    };

    Some(quote! {
        #[cfg(test)]
        {
            #variable_registration
            #value_registration
        }
    })
}

/// Expands `track_let! { let y: T = expr; ... }`.
pub(crate) fn expand_track_let(tokens: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let block: syn::Block = match syn::parse2(quote!({ #tokens })) {
        Ok(block) => block,
        Err(err) => return err.to_compile_error(),
    };

    let transformed_stmts = block.stmts.iter().flat_map(|stmt| {
        let stmt_tokens = quote! { #stmt };
        let capture_tokens = match stmt {
            syn::Stmt::Local(local) => expand_track_let_capture(local),
            _ => None,
        };
        std::iter::once(stmt_tokens).chain(capture_tokens)
    });

    quote! {
        {
            #(#transformed_stmts)*
        }
    }
}
