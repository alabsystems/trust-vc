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
//!
//! REFERENCE-WRAPPED APIT (`&impl Tr`, `&mut impl Tr`, `&(impl A + B)`) is
//! rewritten too, replacing only the referent: `fn f(x: &impl Tr)` is exactly
//! Rust sugar for `fn f<A: Tr>(x: &A)`, and the reference is PRESERVED so the
//! argument keeps its original type shape. This is deliberately restricted to
//! `&`/`&mut`/parenthesis wrappers, which are transparent to receiver
//! resolution: `&T` and `&mut T` receivers both resolve through the same
//! generic-bound method path as a bare `T` (empirically confirmed in both
//! directions — see
//! `trust-vc/tests/apit_reference_trait_bound_dispatch.rs`). Every OTHER composite (tuple, slice,
//! `Vec<impl Tr>`, …) is left alone: those receiver shapes are not known to
//! resolve, so they keep their existing fail-closed handling rather than being
//! normalized into a path that has not been measured.

/// Rewrites every top-level argument-position `impl Trait` in `func`'s signature
/// into a fresh synthetic generic type parameter carrying the same bounds.
/// Returns `Some(rewritten)` when at least one such parameter was desugared, or
/// `None` when the signature contains no argument-position `impl Trait` (so the
/// caller keeps the original borrow, matching the `?`/Self-substitution passes).
pub(crate) fn desugar_impl_trait_args(func: &syn::ItemFn) -> Option<syn::ItemFn> {
    let has_apit =
        func.sig.inputs.iter().any(
            |arg| matches!(arg, syn::FnArg::Typed(pat_type) if apit_slot(&pat_type.ty).is_some()),
        );
    if !has_apit {
        return None;
    }

    let mut owned = func.clone();
    let mut synthesized: Vec<syn::TypeParam> = Vec::new();

    for arg in owned.sig.inputs.iter_mut() {
        let syn::FnArg::Typed(pat_type) = arg else {
            continue;
        };
        // Locate the APIT slot — the parameter type itself, or the referent of
        // a `&` / `&mut` / parenthesis wrapper chain around it. Anything else
        // yields `None` and is left untouched.
        let Some(slot) = apit_slot_mut(&mut pat_type.ty) else {
            continue;
        };
        // `slot` may be the `impl Trait` itself or a parenthesized wrapper of
        // it; `apit_slot` sees through the parens to read the bounds.
        let Some(bounds) = apit_slot(slot).map(|impl_trait| impl_trait.bounds.clone()) else {
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
            bounds,
            eq_token: None,
            default: None,
        };
        synthesized.push(type_param);

        // Replace ONLY the APIT slot with a bare path naming the synthetic
        // param, so it lowers to `TypeParam(ident)` — the receiver shape the
        // generic-bound method resolver keys on. Any enclosing `&` / `&mut`
        // survives verbatim, keeping the parameter's type shape intact.
        *slot = syn::parse_quote!(#ident);
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

/// Returns the `impl Trait` slot inside `ty`, looking through — and ONLY
/// through — `&` / `&mut` / parenthesis wrappers.
///
/// `impl Tr`, `&impl Tr`, `&mut impl Tr` and `&(impl A + B)` all yield the
/// inner `Type::ImplTrait`. A tuple, slice, array, `Vec<impl Tr>`, boxed or
/// path-generic position yields `None`: those receiver shapes are not known to
/// resolve through the generic-bound method path, so normalizing them would be
/// a guess rather than a measured re-route.
fn apit_slot(ty: &syn::Type) -> Option<&syn::TypeImplTrait> {
    match ty {
        syn::Type::ImplTrait(impl_trait) => Some(impl_trait),
        syn::Type::Reference(reference) => apit_slot(&reference.elem),
        syn::Type::Paren(paren) => apit_slot(&paren.elem),
        _ => None,
    }
}

/// Mutable twin of [`apit_slot`]: returns the `&mut syn::Type` holding the
/// `impl Trait`, so the caller can overwrite exactly that slot and leave every
/// enclosing `&` / `&mut` / paren in place.
///
/// Kept structurally identical to [`apit_slot`] so the "is there one?" scan and
/// the "rewrite it" walk cannot disagree about which shapes are in scope.
fn apit_slot_mut(ty: &mut syn::Type) -> Option<&mut syn::Type> {
    // Parentheses are semantically transparent, so the PAREN NODE ITSELF is the
    // slot: `&(impl A + B)` must become `&__TrustVcAPIT0`, not `&(__TrustVcAPIT0)`.
    // The latter renders as the type string `&(__TrustVcAPIT0)`, which matches no
    // declared type-param name and silently falls back to `Opaque` — a
    // desugar that looks applied but resolves nothing.
    if is_apit_modulo_parens(ty) {
        return Some(ty);
    }
    match ty {
        syn::Type::Reference(reference) => apit_slot_mut(&mut reference.elem),
        _ => None,
    }
}

/// True when `ty` IS the argument-position `impl Trait`, ignoring any number of
/// enclosing parentheses.
fn is_apit_modulo_parens(ty: &syn::Type) -> bool {
    match ty {
        syn::Type::ImplTrait(_) => true,
        syn::Type::Paren(paren) => is_apit_modulo_parens(&paren.elem),
        _ => false,
    }
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

    #[test]
    fn shared_reference_apit_keeps_the_reference() {
        let out = desugar_str("fn f(x: &impl Tr) {}");
        assert!(out.contains("__TrustVcAPIT0"), "got: {out}");
        assert!(!out.contains("impl Tr"), "APIT removed: {out}");
        // The `&` must SURVIVE — rewriting `&impl Tr` to a bare `T` would
        // change the parameter's type, not just normalize its sugar.
        assert!(
            out.replace(' ', "").contains("x:&__TrustVcAPIT0"),
            "reference preserved: {out}"
        );
    }

    #[test]
    fn mutable_reference_apit_keeps_the_mutability() {
        let out = desugar_str("fn f(x: &mut impl Tr) {}");
        assert!(
            out.replace(' ', "").contains("x:&mut__TrustVcAPIT0"),
            "`&mut` preserved: {out}"
        );
    }

    #[test]
    fn parenthesized_multi_bound_reference_apit_desugars() {
        let out = desugar_str("fn f(x: &(impl A + B)) {}");
        assert!(out.contains("__TrustVcAPIT0"), "got: {out}");
        assert!(out.contains('A') && out.contains('B'), "bounds kept: {out}");
        assert!(!out.contains("impl A"), "APIT removed: {out}");
    }

    #[test]
    fn reference_and_bare_apits_get_distinct_params() {
        let out = desugar_str("fn f(x: &impl A, y: impl B, z: &mut impl C) {}");
        for expected in ["__TrustVcAPIT0", "__TrustVcAPIT1", "__TrustVcAPIT2"] {
            assert!(out.contains(expected), "missing {expected} in: {out}");
        }
    }

    /// NARROWNESS PIN for the reference-wrapper widening.
    ///
    /// Only `&` / `&mut` / paren wrappers look through to the APIT. Every other
    /// composite must still return `None`, so those shapes keep their existing
    /// fail-closed handling instead of being normalized into a receiver path
    /// that has never been measured.
    #[test]
    fn composite_wrapped_apit_is_not_desugared() {
        for src in [
            "fn f(x: Vec<impl Tr>) {}",
            "fn f(x: (impl A, u64)) {}",
            "fn f(x: [impl Tr; 4]) {}",
            "fn f(x: Box<impl Tr>) {}",
            "fn f(x: &[impl Tr]) {}",
            "fn f(x: &Vec<impl Tr>) {}",
        ] {
            let func: syn::ItemFn = syn::parse_str(src).expect("parse");
            assert!(
                desugar_impl_trait_args(&func).is_none(),
                "composite-wrapped APIT must stay fail-closed: {src}"
            );
        }
    }

    /// `-> &impl Tr` is still an existential in return position; looking through
    /// references must not have leaked the desugar into the return type.
    #[test]
    fn reference_return_position_impl_trait_is_left_untouched() {
        let func: syn::ItemFn =
            syn::parse_str("fn f() -> &'static impl Tr { todo!() }").expect("parse");
        assert!(
            desugar_impl_trait_args(&func).is_none(),
            "return-position `&impl Tr` must not trigger the APIT desugar"
        );
    }
}
