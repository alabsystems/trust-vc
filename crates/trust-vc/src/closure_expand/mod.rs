// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closure contract expansion for `trust_vc::closure!`.
//!
//! Parses the custom closure-with-contracts syntax and rewrites it into a
//! standard Rust closure that uses the existing obligation collection pipeline.
//!
//! Design: designs/2026-03-18-1943-closure-contract-mvp.md
//! Issue: #1943

mod parse;
mod rename;

use proc_macro2::{Ident, TokenStream};
use quote::quote;

use self::parse::ClosureContract;
use self::rename::rename_idents;
use crate::macro_expand;
use crate::postcondition_lowering;

fn trust_vc_type_string(ty: &syn::Type) -> String {
    quote!(#ty).to_string().replace(' ', "")
}

/// Derive a stable, per-invocation suffix for this closure's helper symbols.
///
/// SOUNDNESS (#791): every `trust_vc::closure!` used to rename its parameters
/// and result to the *same* hardcoded symbols `__trust_vc_closure_arg{i}` /
/// `__trust_vc_closure_result`. In the default `VerificationMode::BodyLevel` a
/// closure `requires(P)` is classified as a flat, unscoped global assumption
/// over those shared symbols, so one closure's precondition constrained the
/// `arg{i}` / `result` referenced by a *sibling* closure's obligations (and by
/// outer/post-call code), discharging false postconditions.
///
/// We give each distinct closure its own symbol namespace by hashing the full
/// macro input. The hash is deterministic (`DefaultHasher` is keyed by zeros,
/// not randomized), so identical closures (same params/contract/body) share a
/// namespace harmlessly while any textual difference yields a fresh one. The
/// suffix is applied uniformly to the param symbols, the result symbol, the
/// body-assumption binding and the ensures rewrite, so within a single closure
/// the `result == body(args)` relation and the ensures predicate stay over the
/// same (now-unique) symbols — only cross-closure aliasing is broken.
pub(crate) fn closure_symbol_suffix(input: &TokenStream) -> String {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    input.to_string().hash(&mut hasher);
    format!("_c{:x}", hasher.finish())
}

pub(crate) fn expand_closure(input: TokenStream) -> TokenStream {
    // Per-closure-unique symbol suffix (#791) — computed from the raw input
    // before `syn::parse2` consumes it.
    let suffix = closure_symbol_suffix(&input);
    let arg_symbol = |i: usize| format!("__trust_vc_closure_arg{}{}", i, suffix);
    let result_symbol = format!("__trust_vc_closure_result{}", suffix);
    let result_ident = Ident::new(&result_symbol, proc_macro2::Span::call_site());

    let contract: ClosureContract = match syn::parse2(input) {
        Ok(c) => c,
        Err(err) => return err.to_compile_error(),
    };
    let support_root = trust_vc_core::macro_support_root();

    // Validate: at least requires or ensures must be present.
    if contract.requires.is_none() && contract.ensures.is_none() {
        return syn::Error::new(
            proc_macro2::Span::call_site(),
            "trust_vc::closure! requires at least a requires(...) or ensures(...) clause",
        )
        .to_compile_error();
    }

    // Build rename map: user param names → __trust_vc_closure_argN<suffix>
    // The per-closure suffix (#791) keeps each closure's param symbols in their
    // own namespace so a sibling's requires cannot constrain them.
    let renames: Vec<(String, String)> = contract
        .params
        .iter()
        .enumerate()
        .map(|(i, p)| (p.name.to_string(), arg_symbol(i)))
        .collect();

    // ── Output closure parameter declarations ────────────────────────
    let param_decls: Vec<_> = contract
        .params
        .iter()
        .enumerate()
        .map(|(i, p)| {
            let arg_name = Ident::new(&arg_symbol(i), p.name.span());
            let ty = &p.ty;
            if p.is_mut {
                quote! { mut #arg_name: #ty }
            } else {
                quote! { #arg_name: #ty }
            }
        })
        .collect();

    // ── Variable registrations (#[cfg(test)]) ────────────────────────
    let var_registrations: Vec<_> = contract
        .params
        .iter()
        .enumerate()
        .map(|(i, p)| {
            let arg_name_str = arg_symbol(i);
            let display_name = p.name.to_string();
            let ty = &p.ty;
            let ty_str = trust_vc_type_string(ty);
            quote! {
                #support_root::verify_macro::collect_variable(
                    #arg_name_str.to_string(),
                    #ty_str.to_string(),
                );
                #support_root::register_counterexample_display(
                    #arg_name_str.to_string(),
                    #display_name.to_string(),
                    true,
                );
            }
        })
        .collect();

    // ── Requires expansion ───────────────────────────────────────────
    let requires_expansion = if let Some(ref req_tokens) = contract.requires {
        let renamed = rename_idents(req_tokens.clone(), &renames);
        macro_expand::expand_requires(renamed)
    } else {
        quote! {}
    };

    // ── Body with renamed idents ─────────────────────────────────────
    let body = &contract.body;
    let body_tokens = quote!(#body);
    let renamed_body = rename_idents(body_tokens.clone(), &renames);

    // ── Body assumption: <result_symbol> == body_expr ──────────────────
    // The verifier needs to know the body semantics. We emit an Assume
    // obligation: `<result_symbol> == <renamed_body>`. Both the result symbol
    // and the args inside the body carry this closure's #791 suffix, so the
    // binding stays within this closure's namespace.
    // Only generated when ensures is present — without ensures there's nothing
    // to assert, and the result symbol wouldn't be registered.
    let body_assumption = if contract.ensures.is_some() {
        let body_assumption_expr = quote! {
            #result_ident == #renamed_body
        };
        macro_expand::expand_assume(body_assumption_expr)
    } else {
        quote! {}
    };

    // ── Postcondition lowering via shared module ────────────────────
    // Ensures expressions are renamed then lowered through the shared
    // module so old!() bindings land before the body (fixes latent
    // ordering risk documented in #2464 design §6).
    let pre_body_old_bindings: Vec<TokenStream>;
    let pre_body_test_old_regs: Vec<TokenStream>;
    let post_body_ensures: TokenStream;

    if let Some(ref ens) = contract.ensures {
        let result_name_str = ens.result_name.to_string();
        let mut full_renames = renames.clone();
        full_renames.push((result_name_str.clone(), result_symbol.clone()));
        let renamed_ensures = rename_idents(ens.ensures_expr_tokens(), &full_renames);

        let lowered = match postcondition_lowering::lower_postconditions(vec![renamed_ensures]) {
            Ok(l) => l,
            Err(err) => return err.to_compile_error(),
        };

        pre_body_old_bindings = lowered.emit_runtime_old_bindings();
        pre_body_test_old_regs = lowered.emit_test_old_registrations(
            postcondition_lowering::TestOldRegistrationMode::RegisterRuntimeValues,
        );
        let test_obligations = lowered.emit_test_obligations();
        let runtime_asserts = lowered.emit_runtime_asserts();

        // Result type annotation for the binding (optional).
        let result_ty_annotation = if let Some(ref ty) = ens.result_ty {
            quote! { : #ty }
        } else {
            quote! {}
        };

        // Register result type for the verifier. The registered symbol carries
        // this closure's #791 suffix so it cannot collide with a sibling's.
        let result_registration = if let Some(ref ty) = ens.result_ty {
            let ty_str = trust_vc_type_string(ty);
            quote! {
                #[cfg(test)]
                {
                    #support_root::verify_macro::collect_variable(
                        #result_symbol.to_string(),
                        #ty_str.to_string(),
                    );
                    #support_root::register_counterexample_display(
                        #result_symbol.to_string(),
                        #result_name_str.to_string(),
                        true,
                    );
                }
            }
        } else {
            quote! {
                #[cfg(test)]
                {
                    #support_root::verify_macro::collect_variable_runtime(
                        #result_symbol,
                        &#result_ident,
                    );
                    #support_root::register_counterexample_display(
                        #result_symbol.to_string(),
                        #result_name_str.to_string(),
                        true,
                    );
                }
            }
        };

        post_body_ensures = quote! {
            #result_registration
            #[cfg(test)]
            {
                let #result_ident #result_ty_annotation = #result_ident;
                #(#test_obligations)*
            }
            #[cfg(not(test))]
            {
                let #result_ident #result_ty_annotation = #result_ident;
                #(#runtime_asserts)*
            }
        };
    } else {
        pre_body_old_bindings = Vec::new();
        pre_body_test_old_regs = Vec::new();
        post_body_ensures = quote! {};
    }

    // ── Return type annotation ───────────────────────────────────────
    let return_ty_annotation = if let Some(ref ty) = contract.return_ty {
        quote! { -> #ty }
    } else {
        quote! {}
    };

    // ── Move keyword ─────────────────────────────────────────────────
    let move_kw = if contract.is_move {
        quote! { move }
    } else {
        quote! {}
    };

    // ── Assemble the output closure ──────────────────────────────────
    quote! {
        #move_kw |#(#param_decls),*| #return_ty_annotation {
            #[cfg(test)]
            {
                #(#var_registrations)*
                #(#pre_body_test_old_regs)*
            }

            #requires_expansion

            #(#pre_body_old_bindings)*

            let #result_ident = { #renamed_body };

            #body_assumption

            #post_body_ensures

            #result_ident
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::quote;

    #[test]
    fn test_expand_closure_method_name_preserved() {
        let input = quote! {
            |len: i32| -> i32
            requires(len > 0)
            ensures(|res: i32| res == len)
            { vec.len() as i32 }
        };
        let result = expand_closure(input).to_string();
        assert!(
            result.contains(". len"),
            "method call .len() should be preserved in expanded closure, got: {result}"
        );
    }

    #[test]
    fn test_expand_closure_mut_parameter_preserved() {
        let input = quote! {
            |mut x: i32| -> i32
            ensures(|res: i32| res == x)
            { x += 1; x }
        };
        let suffix = closure_symbol_suffix(&input);
        let result = expand_closure(input).to_string();
        let expected = format!("| mut __trust_vc_closure_arg0{suffix} : i32 |");
        assert!(
            result.contains(&expected),
            "mut parameter should be preserved in expanded closure, got: {result}"
        );
    }

    #[test]
    fn test_expand_closure_old_bindings_before_body() {
        let input = quote! {
            |x: i32| -> i32
            ensures(|res: i32| res == old!(x) + 1)
            { x + 1 }
        };
        let suffix = closure_symbol_suffix(&input);
        let result = expand_closure(input).to_string();

        // Runtime old binding should appear before the body assignment.
        let old_bind_pos = result
            .find("let __trust_vc_old_")
            .expect("should have runtime old binding");
        let body_pos = result
            .find(&format!("let __trust_vc_closure_result{suffix} ="))
            .expect("should have body assignment");
        assert!(
            old_bind_pos < body_pos,
            "old!() binding must appear before body, got: {result}"
        );
    }

    #[test]
    fn test_expand_closure_old_test_registration_before_body() {
        let input = quote! {
            |x: i32| -> i32
            ensures(|res: i32| res == old!(x) + 1)
            { x + 1 }
        };
        let suffix = closure_symbol_suffix(&input);
        let result = expand_closure(input).to_string();

        assert!(
            result.contains("collect_old_value"),
            "test path should register old value, got: {result}"
        );

        // Test old registration should be in the pre-body cfg(test) block.
        let old_reg_pos = result
            .find("collect_old_value")
            .expect("should have old registration");
        let body_pos = result
            .find(&format!("let __trust_vc_closure_result{suffix} ="))
            .expect("should have body assignment");
        assert!(
            old_reg_pos < body_pos,
            "old!() test registration must appear before body, got: {result}"
        );
    }

    #[test]
    fn test_expand_closure_old_deref_in_ensures() {
        let input = quote! {
            |x: i32| -> i32
            ensures(|res: i32| res == old!(*x) + 1)
            { x + 1 }
        };
        let result = expand_closure(input).to_string();

        assert!(
            result.contains("let __trust_vc_old_"),
            "should have old deref binding, got: {result}"
        );
        assert!(
            result.contains("* __trust_vc_closure_arg0"),
            "deref binding should dereference the renamed param, got: {result}"
        );
    }

    #[test]
    fn test_expand_closure_ensures_without_old_no_bindings() {
        let input = quote! {
            |x: i32| -> i32
            ensures(|res: i32| res > 0)
            { x + 1 }
        };
        let result = expand_closure(input).to_string();

        assert!(
            !result.contains("__trust_vc_old_"),
            "ensures without old!() should not generate old bindings, got: {result}"
        );
    }

    #[test]
    fn test_expand_closure_option_and_then_contract_precondition() {
        let input = quote! {
            |x: u32| -> Option<u32>
            requires(x < 1000u32)
            ensures(|r: Option<u32>| r == Option::<u32>::Some(x + 1u32))
            { Option::<u32>::Some(x + 1u32) }
        };
        let suffix = closure_symbol_suffix(&input);
        let result = expand_closure(input).to_string();
        let arg0 = format!("__trust_vc_closure_arg0{suffix}");
        let res = format!("__trust_vc_closure_result{suffix}");

        assert!(
            result.contains(&format!("{arg0} < 1000u32")),
            "requires clause should rename the closure parameter, got: {result}"
        );
        assert!(
            result.contains(&format!("{res} == Option :: < u32 > :: Some")),
            "ensures clause should reference the renamed result, got: {result}"
        );
        assert!(
            result.contains(&format!("{arg0} + 1u32")),
            "body and ensures should preserve the parameter relation, got: {result}"
        );
        assert!(
            result.contains("\"Option<u32>\""),
            "generic result type registration should normalize Rust token spacing, got: {result}"
        );
    }

    #[test]
    fn test_expand_closure_zero_arg_option_fallback_contract() {
        let input = quote! {
            || -> u32
            requires(true)
            ensures(|r: u32| r == 99u32)
            { 99u32 }
        };
        let suffix = closure_symbol_suffix(&input);
        let result = expand_closure(input).to_string();

        assert!(
            result.contains(&format!("__trust_vc_closure_result{suffix} == 99u32")),
            "zero-arg fallback body assumption should preserve the result value, got: {result}"
        );
        assert!(
            result.contains("\"u32\""),
            "zero-arg fallback result type should be registered, got: {result}"
        );
        assert!(
            !result.contains("__trust_vc_closure_arg0"),
            "zero-arg fallback closure should not synthesize any parameter variables, got: {result}"
        );
    }
}
