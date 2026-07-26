// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Desugar ARGUMENT-position `impl Trait` (APIT) into an equivalent synthetic
//! generic type parameter, BEFORE signature/bound extraction.
//!
//! `fn f(x: impl Tr) { .. }` is exactly Rust sugar for
//! `fn f<__TrustVcAPIT0: Tr>(x: __TrustVcAPIT0) { .. }` — an anonymous universal
//! generic. Rewriting it here lets the caller reuse the fully-working
//! generic-trait-bound resolution path (`trait_bounds_from_signature` +
//! `register_trait_bound_methods_for_bounds`) with ZERO changes to resolution
//! logic: `x.spec_method()` resolves against the abstract trait postcondition
//! axiom exactly as it does for `fn f<T: Tr>(x: T)`.
//!
//! SOUNDNESS: this is a behavior-preserving syntactic normalization — it emits
//! no axioms and changes no encoding. It desugars to the SAME generic path that
//! is already sound (a lying consequence of the trait contract fails closed).
//! Only TOP-LEVEL argument `impl Trait` is rewritten; RETURN-position
//! `-> impl Trait` (an existential, not a universal) is deliberately left
//! untouched, as is `impl Trait` nested inside a composite argument type — both
//! keep their existing fail-closed handling.

/// Rewrites every top-level argument-position `impl Trait` in `func`'s signature
/// into a fresh synthetic generic type parameter carrying the same bounds.
/// Returns `Some(rewritten)` when at least one such parameter was desugared, or
/// `None` when the signature contains no argument-position `impl Trait` (so the
/// caller keeps the original borrow, matching the `?`/Self-substitution passes).
pub(crate) fn desugar_impl_trait_args(func: &syn::ItemFn) -> Option<syn::ItemFn> {
    let has_apit = func.sig.inputs.iter().any(|arg| {
        matches!(arg, syn::FnArg::Typed(pat_type) if matches!(&*pat_type.ty, syn::Type::ImplTrait(_)))
    });
    if !has_apit {
        return None;
    }

    let mut owned = func.clone();
    let mut synthesized: Vec<syn::TypeParam> = Vec::new();

    for arg in owned.sig.inputs.iter_mut() {
        let syn::FnArg::Typed(pat_type) = arg else {
            continue;
        };
        let syn::Type::ImplTrait(impl_trait) = &*pat_type.ty else {
            continue;
        };

        let ident = syn::Ident::new(
            &format!("__TrustVcAPIT{}", synthesized.len()),
            proc_macro2::Span::call_site(),
        );

        // Carry the APIT's bounds onto the synthetic type parameter verbatim
        // (trait bounds feed resolution; lifetime / `?Sized` bounds are ignored
        // downstream exactly as they are for a written generic param).
        let type_param = syn::TypeParam {
            attrs: Vec::new(),
            ident: ident.clone(),
            colon_token: Some(syn::token::Colon::default()),
            bounds: impl_trait.bounds.clone(),
            eq_token: None,
            default: None,
        };
        synthesized.push(type_param);

        // Replace the parameter's type with a bare path naming the synthetic
        // param, so it lowers to `TypeParam(ident)` — the receiver shape the
        // generic-bound method resolver keys on.
        *pat_type.ty = syn::parse_quote!(#ident);
    }

    if synthesized.is_empty() {
        return None;
    }

    for type_param in synthesized {
        owned
            .sig
            .generics
            .params
            .push(syn::GenericParam::Type(type_param));
    }

    Some(owned)
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::ToTokens;

    fn desugar_str(src: &str) -> String {
        let func: syn::ItemFn = syn::parse_str(src).expect("parse");
        let rewritten = desugar_impl_trait_args(&func).expect("should desugar");
        rewritten.sig.to_token_stream().to_string()
    }

    #[test]
    fn single_apit_becomes_generic_param() {
        let out = desugar_str("fn f(x: impl Tr) {}");
        assert!(out.contains("__TrustVcAPIT0"), "got: {out}");
        assert!(
            out.contains(": Tr") || out.contains(": Tr"),
            "bound carried: {out}"
        );
        // The parameter type is now the synthetic ident, not `impl Tr`.
        assert!(
            !out.contains("impl Tr"),
            "impl Trait removed from arg: {out}"
        );
    }

    #[test]
    fn two_apits_get_distinct_params() {
        let out = desugar_str("fn f(x: impl A, y: impl B) {}");
        assert!(out.contains("__TrustVcAPIT0"), "got: {out}");
        assert!(out.contains("__TrustVcAPIT1"), "got: {out}");
    }

    #[test]
    fn no_apit_returns_none() {
        let func: syn::ItemFn = syn::parse_str("fn f(x: u64) -> u64 { x }").expect("parse");
        assert!(desugar_impl_trait_args(&func).is_none());
    }

    #[test]
    fn return_position_impl_trait_is_left_untouched() {
        // `-> impl Tr` is existential, not universal — it must NOT be desugared.
        let func: syn::ItemFn = syn::parse_str("fn f() -> impl Tr { todo!() }").expect("parse");
        assert!(
            desugar_impl_trait_args(&func).is_none(),
            "return-position impl Trait must not trigger the APIT desugar"
        );
    }

    #[test]
    fn multi_bound_apit_carries_all_trait_bounds() {
        let out = desugar_str("fn f(x: impl A + B) {}");
        assert!(
            out.contains(": A + B") || (out.contains("A") && out.contains("B")),
            "got: {out}"
        );
    }
}
