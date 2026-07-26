//! Attribute proc-macro entrypoint helpers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use proc_macro::TokenStream;
use syn::{parse_macro_input, Attribute, Item, ItemFn, ItemImpl, ItemTrait};

/// Returns a `compile_error!` if `attr` is non-empty, indicating the user
/// passed unexpected arguments to an attribute that accepts none.
///
/// Fixes #1837: 8 proc macros silently discarded attribute arguments.
pub(crate) fn reject_unexpected_args(macro_name: &str, attr: &TokenStream) -> Option<TokenStream> {
    if !attr.is_empty() {
        let msg = format!(
            "#[trust_vc::{}] does not accept arguments — remove the parenthesized content",
            macro_name
        );
        Some(TokenStream::from(
            syn::Error::new(proc_macro2::Span::call_site(), msg).to_compile_error(),
        ))
    } else {
        None
    }
}

pub(crate) fn proof(attr: TokenStream, item: TokenStream) -> TokenStream {
    if let Some(err) = reject_unexpected_args("proof", &attr) {
        return err;
    }
    let result = match trust_vc_core::parse_item_fn_with_tracked_info(
        proc_macro2::TokenStream::from(item),
    ) {
        Ok(result) => result,
        Err(err) => return TokenStream::from(err.to_compile_error()),
    };
    // Apply range loop inference fold pass: wraps `for i in lo..hi` loops
    // with auto-generated invariant + metadata registration. Part of #2502.
    let mut item_fn = result.item_fn;
    item_fn.block = Box::new(crate::loop_infer::fold_with_range_inference(&item_fn.block));
    let expanded = trust_vc_core::expand_proof_with_tracked(item_fn, &result.tracked_params);
    TokenStream::from(expanded)
}

pub(crate) fn decreases(attr: TokenStream, item: TokenStream) -> TokenStream {
    if attr.is_empty() {
        let error = syn::Error::new(
            proc_macro2::Span::call_site(),
            "#[trust_vc::decreases] requires at least one measure expression",
        )
        .to_compile_error();
        return TokenStream::from(error);
    }
    let input = parse_macro_input!(item as ItemFn);
    let attr_tokens = proc_macro2::TokenStream::from(attr);
    let expanded = trust_vc_core::expand_decreases_with_clauses(input, attr_tokens);
    TokenStream::from(expanded)
}

pub(crate) fn broadcast(attr: TokenStream, item: TokenStream) -> TokenStream {
    if let Some(err) = reject_unexpected_args("broadcast", &attr) {
        return err;
    }
    let input =
        match trust_vc_core::parse_item_fn_allow_tracked(proc_macro2::TokenStream::from(item)) {
            Ok(input) => input,
            Err(err) => return TokenStream::from(err.to_compile_error()),
        };
    let expanded = trust_vc_core::expand_broadcast(input);
    TokenStream::from(expanded)
}

fn take_named_attr(attrs: &mut Vec<Attribute>, name: &str) -> bool {
    let original_len = attrs.len();
    attrs.retain(|attr| {
        attr.path()
            .segments
            .last()
            .is_none_or(|segment| segment.ident != name)
    });
    attrs.len() != original_len
}

pub(crate) fn broadcast_group_impl(
    attr: proc_macro2::TokenStream,
    item: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    if attr.is_empty() {
        let error = syn::Error::new(
            proc_macro2::Span::call_site(),
            "#[trust_vc::broadcast_group] requires a group name",
        )
        .to_compile_error();
        return error;
    }

    let group_ident: syn::Ident = match syn::parse2(attr.clone()) {
        Ok(ident) => ident,
        Err(err) => {
            let error = syn::Error::new(
                proc_macro2::Span::call_site(),
                format!(
                    "#[trust_vc::broadcast_group(...)] expects a single identifier group name: {}",
                    err
                ),
            )
            .to_compile_error();
            return error;
        }
    };

    let mut input: ItemFn = match syn::parse2(item) {
        Ok(input) => input,
        Err(err) => return err.to_compile_error(),
    };
    if !take_named_attr(&mut input.attrs, "broadcast") {
        let error = syn::Error::new(
            proc_macro2::Span::call_site(),
            "#[trust_vc::broadcast_group(...)] must wrap a #[trust_vc::broadcast] function and appear above #[trust_vc::broadcast]",
        )
        .to_compile_error();
        return error;
    }

    let group_name = group_ident.to_string();
    let fn_name = input.sig.ident.to_string();
    let expanded = trust_vc_core::expand_broadcast_with_group(input, Some(group_name.clone()));
    let support_root = trust_vc_core::macro_support_root();
    quote::quote! {
        #expanded
        #support_root::inventory::submit! {
            #support_root::BroadcastFnGroupDef {
                function: #fn_name,
                group: #group_name,
            }
        }
    }
}

pub(crate) fn broadcast_group(attr: TokenStream, item: TokenStream) -> TokenStream {
    TokenStream::from(broadcast_group_impl(attr.into(), item.into()))
}

pub(crate) fn trigger(attr: TokenStream, item: TokenStream) -> TokenStream {
    if attr.is_empty() {
        let error = syn::Error::new(
            proc_macro2::Span::call_site(),
            "#[trust_vc::trigger] requires a trigger pattern expression",
        )
        .to_compile_error();
        return TokenStream::from(error);
    }
    let input = parse_macro_input!(item as ItemFn);
    let pattern = proc_macro2::TokenStream::from(attr);
    let expanded = trust_vc_core::expand_trigger_with_group(input, pattern);
    TokenStream::from(expanded)
}

pub(crate) fn auto_trigger(attr: TokenStream, item: TokenStream) -> TokenStream {
    if let Some(err) = reject_unexpected_args("auto_trigger", &attr) {
        return err;
    }
    let input = parse_macro_input!(item as ItemFn);
    let expanded = trust_vc_core::expand_auto_trigger(input);
    TokenStream::from(expanded)
}

pub(crate) fn all_triggers(attr: TokenStream, item: TokenStream) -> TokenStream {
    if let Some(err) = reject_unexpected_args("all_triggers", &attr) {
        return err;
    }
    let input = parse_macro_input!(item as ItemFn);
    let expanded = trust_vc_core::expand_all_triggers(input);
    TokenStream::from(expanded)
}

pub(crate) fn spec(attr: TokenStream, item: TokenStream) -> TokenStream {
    if let Some(err) = reject_unexpected_args("spec", &attr) {
        return err;
    }
    let input = parse_macro_input!(item as ItemFn);
    let expanded = trust_vc_core::expand_spec(input);
    TokenStream::from(expanded)
}

pub(crate) fn trait_spec(attr: TokenStream, item: TokenStream) -> TokenStream {
    if let Some(err) = reject_unexpected_args("trait_spec", &attr) {
        return err;
    }
    let input = parse_macro_input!(item as ItemTrait);
    let expanded = trust_vc_core::expand_trait_spec(input);
    TokenStream::from(expanded)
}

pub(crate) fn trait_impl(attr: TokenStream, item: TokenStream) -> TokenStream {
    if let Some(err) = reject_unexpected_args("trait_impl", &attr) {
        return err;
    }
    let input = parse_macro_input!(item as ItemImpl);
    let expanded = trust_vc_core::expand_trait_impl(input);
    TokenStream::from(expanded)
}

pub(crate) fn spec_mode(attr: TokenStream, item: TokenStream) -> TokenStream {
    if let Some(err) = reject_unexpected_args("spec_mode", &attr) {
        return err;
    }
    let input = parse_macro_input!(item as ItemFn);
    let expanded = trust_vc_core::expand_spec_mode(input);
    TokenStream::from(expanded)
}

pub(crate) fn memoize(attr: TokenStream, item: TokenStream) -> TokenStream {
    if let Some(err) = reject_unexpected_args("memoize", &attr) {
        return err;
    }
    let input = parse_macro_input!(item as ItemFn);
    let expanded = trust_vc_core::expand_memoize(input);
    TokenStream::from(expanded)
}

pub(crate) fn opens_invariants(attr: TokenStream, item: TokenStream) -> TokenStream {
    if attr.is_empty() {
        let error = syn::Error::new(
            proc_macro2::Span::call_site(),
            "#[trust_vc::opens_invariants] requires a specification: any, none, or invariant names",
        )
        .to_compile_error();
        return TokenStream::from(error);
    }
    let input = parse_macro_input!(item as ItemFn);
    let attr_tokens = proc_macro2::TokenStream::from(attr);
    let expanded = trust_vc_core::expand_opens_invariants(input, attr_tokens);
    TokenStream::from(expanded)
}

pub(crate) fn verifier(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}

pub(crate) fn via_fn(attr: TokenStream, item: TokenStream) -> TokenStream {
    if let Some(err) = reject_unexpected_args("via_fn", &attr) {
        return err;
    }
    let input =
        match trust_vc_core::parse_item_fn_allow_tracked(proc_macro2::TokenStream::from(item)) {
            Ok(input) => input,
            Err(err) => return TokenStream::from(err.to_compile_error()),
        };
    let expanded = trust_vc_core::expand_via_fn(input);
    TokenStream::from(expanded)
}

pub(crate) fn returns(attr: TokenStream, item: TokenStream) -> TokenStream {
    if attr.is_empty() {
        let error = syn::Error::new(
            proc_macro2::Span::call_site(),
            "#[trust_vc::returns] requires a name for the return value",
        )
        .to_compile_error();
        return TokenStream::from(error);
    }
    let input = parse_macro_input!(item as ItemFn);
    let attr_tokens = proc_macro2::TokenStream::from(attr);
    let expanded = trust_vc_core::expand_returns(input, attr_tokens);
    TokenStream::from(expanded)
}

pub(crate) fn external_body(attr: TokenStream, item: TokenStream) -> TokenStream {
    if let Some(err) = reject_unexpected_args("external_body", &attr) {
        return err;
    }
    let input = parse_macro_input!(item as ItemFn);
    let expanded = trust_vc_core::expand_external_body(input);
    TokenStream::from(expanded)
}

pub(crate) fn external_impl(
    attr: proc_macro2::TokenStream,
    item: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    if !attr.is_empty() {
        let msg =
            "#[trust_vc::external] does not accept arguments - remove the parenthesized content";
        return syn::Error::new(proc_macro2::Span::call_site(), msg).to_compile_error();
    }

    match syn::parse2::<Item>(item) {
        Ok(Item::Fn(input)) => trust_vc_core::expand_external_body(input),
        Ok(Item::Impl(input)) => quote::quote! { #input },
        Ok(other) => syn::Error::new_spanned(other, "expected `fn` or `impl`").to_compile_error(),
        Err(err) => err.to_compile_error(),
    }
}

pub(crate) fn external(attr: TokenStream, item: TokenStream) -> TokenStream {
    TokenStream::from(external_impl(attr.into(), item.into()))
}

pub(crate) fn inline(attr: TokenStream, item: TokenStream) -> TokenStream {
    if let Some(err) = reject_unexpected_args("inline", &attr) {
        return err;
    }
    item
}

pub(crate) fn allow_in_spec(attr: TokenStream, item: TokenStream) -> TokenStream {
    if let Some(err) = reject_unexpected_args("allow_in_spec", &attr) {
        return err;
    }
    item
}

pub(crate) fn when_used_as_spec(attr: TokenStream, item: TokenStream) -> TokenStream {
    if attr.is_empty() {
        let error = syn::Error::new(
            proc_macro2::Span::call_site(),
            "#[trust_vc::when_used_as_spec] requires a target spec function path",
        )
        .to_compile_error();
        return TokenStream::from(error);
    }
    if let Err(err) = syn::parse::<syn::Path>(attr.clone()) {
        return TokenStream::from(err.to_compile_error());
    }
    item
}

pub(crate) fn contract(attr: TokenStream, item: TokenStream) -> TokenStream {
    if attr.is_empty() {
        let error = syn::Error::new(
            proc_macro2::Span::call_site(),
            "#[trust_vc::contract] requires at least one clause (requires, ensures, returns, decreases, or cite)",
        )
        .to_compile_error();
        return TokenStream::from(error);
    }
    let input = parse_macro_input!(item as ItemFn);
    let attr_tokens = proc_macro2::TokenStream::from(attr);
    let expanded = crate::contract_expand::expand_contract(attr_tokens, input);
    TokenStream::from(expanded)
}

#[cfg(test)]
mod tests {
    use super::{broadcast_group_impl, external_impl};
    use quote::quote;

    #[test]
    fn test_broadcast_group_rejects_non_identifier_names() {
        let expanded = broadcast_group_impl(
            quote!(alpha beta),
            quote! {
                #[trust_vc::broadcast]
                fn lemma(x: u64) {
                    trust_vc::ensures!(x == x);
                }
            },
        )
        .to_string();

        assert!(
            expanded.contains("compile_error !"),
            "broadcast_group should fail closed on non-identifier names, got: {expanded}"
        );
        assert!(
            expanded.contains("expects a single identifier group name"),
            "broadcast_group diagnostic should explain the identifier-only contract, got: {expanded}"
        );
    }

    #[test]
    fn test_broadcast_group_valid_identifier_emits_manifest_entry() {
        let expanded = broadcast_group_impl(
            quote!(alpha_only),
            quote! {
                #[trust_vc::broadcast]
                fn lemma(x: u64) {
                    trust_vc::ensures!(x == x);
                }
            },
        )
        .to_string();

        assert!(
            expanded.contains("BroadcastFnGroupDef"),
            "broadcast_group should emit a manifest entry for valid identifiers, got: {expanded}"
        );
        assert!(
            !expanded.contains("compile_error !"),
            "broadcast_group should accept valid identifier names, got: {expanded}"
        );
    }

    #[test]
    fn test_external_function_uses_external_body_marker() {
        let expanded = external_impl(
            quote!(),
            quote! {
                fn trusted_helper(x: u64) -> u64 {
                    x + 1
                }
            },
        )
        .to_string();

        assert!(
            expanded.contains("__trust_vc_external_body"),
            "external functions should still be registered as trusted bodies, got: {expanded}"
        );
    }

    #[test]
    fn test_external_impl_is_trusted_pass_through() {
        let expanded = external_impl(
            quote!(),
            quote! {
                impl core::fmt::Debug for Err {
                    fn fmt(
                        &self,
                        f: &mut core::fmt::Formatter<'_>,
                    ) -> core::fmt::Result {
                        core::fmt::Debug::fmt(&self.error_code, f)
                    }
                }
            },
        )
        .to_string();

        assert!(
            expanded.contains("impl core :: fmt :: Debug for Err"),
            "external impls should be emitted unchanged, got: {expanded}"
        );
        assert!(
            !expanded.contains("__trust_vc_external_body"),
            "external impls should not masquerade as function bodies, got: {expanded}"
        );
        assert!(
            !expanded.contains("compile_error !"),
            "external impls should be accepted, got: {expanded}"
        );
    }

    #[test]
    fn test_external_rejects_other_items() {
        let expanded = external_impl(
            quote!(),
            quote! {
                struct NotExternal;
            },
        )
        .to_string();

        assert!(
            expanded.contains("compile_error !"),
            "external should fail closed for unsupported item kinds, got: {expanded}"
        );
        assert!(
            expanded.contains("expected `fn` or `impl`"),
            "external diagnostic should explain accepted item kinds, got: {expanded}"
        );
    }
}
