//! Helpers for parsing proof-style `tracked` parameter syntax.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Verus-style proof signatures allow `tracked x: T` parameter modifiers that
//! stable Rust does not parse directly. TrustVc currently implements the MVP
//! behavior by stripping the `tracked` marker before handing the item/source to
//! `syn`, while leaving the underlying Rust move semantics to enforce
//! single-use behavior for non-`Copy` proof values.

use proc_macro2::{Delimiter, Group, TokenStream, TokenTree};
use quote::quote;
use syn::parse::{Parse, ParseStream};
use syn::Token;

/// Result of parsing a function item with tracked parameter metadata.
pub struct TrackedParseResult {
    pub item_fn: syn::ItemFn,
    pub tracked_params: Vec<String>,
}

impl std::fmt::Debug for TrackedParseResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TrackedParseResult")
            .field("item_fn", &self.item_fn.sig.ident.to_string())
            .field("tracked_params", &self.tracked_params)
            .finish()
    }
}

/// Parses a function item after normalizing Verus-style `tracked` parameters.
#[doc(hidden)]
pub fn parse_item_fn_allow_tracked(tokens: TokenStream) -> Result<syn::ItemFn, syn::Error> {
    syn::parse2(normalize_verus_source_tokens(tokens))
}

/// Parses a function item and extracts the names of `tracked`-annotated parameters.
///
/// Returns both the parsed `ItemFn` (with `tracked` stripped) and the names of
/// parameters that were annotated with `tracked`. Part of #2427 Slice 3.
#[doc(hidden)]
pub fn parse_item_fn_with_tracked_info(
    tokens: TokenStream,
) -> Result<TrackedParseResult, syn::Error> {
    let tracked_params = extract_tracked_param_names(&tokens);
    let item_fn = syn::parse2(normalize_verus_source_tokens(tokens))?;
    Ok(TrackedParseResult {
        item_fn,
        tracked_params,
    })
}

/// Parses a Rust source file after normalizing Verus-style `tracked` parameters.
///
/// **File path only.** Unlike [`parse_item_fn_allow_tracked`] (the proc-macro
/// path, which must emit compilable Rust and therefore STRIPS the marker), the
/// file path never re-emits the AST as code — it only verifies it. So here
/// `tracked x: T` is rewritten to the equivalent proof-mode PARAMETER ATTRIBUTE
/// `#[trust_vc::proof] x: T` rather than dropped.
///
/// This is not an invention: in Verus, `tracked x: T` in the `verus!` surface
/// desugars to exactly `#[verifier::proof] x: T` (see `rust_to_vir_func.rs`
/// `get_var_mode`, which reads the parameter's mode off that attribute), and
/// upstream `assert_forall_by.rs` itself uses BOTH spellings. Preserving it is
/// what lets [`crate::proof_var_mode`] see proof-mode variables at all; before
/// this, the marker was erased and every proof-mode variable looked like an
/// ordinary spec/exec one.
#[doc(hidden)]
pub fn parse_file_allow_tracked(source: &str) -> Result<syn::File, syn::Error> {
    let tokens: TokenStream = source
        .parse()
        .map_err(|err| syn::Error::new(proc_macro2::Span::call_site(), err))?;
    let mut file: syn::File = syn::parse2(normalize_verus_file_tokens(tokens))?;
    unwrap_trust_vc_cfg_attrs_in_file(&mut file);
    // Runs AFTER cfg_attr unwrapping so a `#[cfg_attr(.., trust_vc::spec)]`
    // bodyless declaration is recognized as a spec fn too.
    mark_bodyless_spec_fns_uninterp(&mut file.items);
    Ok(file)
}

/// List of trust_vc attribute idents whose presence inside a `cfg_attr` causes
/// that `cfg_attr` to be unwrapped during source-level verification. Mirrors the
/// scanner's `TRUST_VC_ATTRS` so discovery and extraction agree.
const TRUST_VC_CFG_ATTR_NAMES: &[&str] = &[
    "requires",
    "ensures",
    "proof",
    "spec",
    "decreases",
    "opaque",
    "inline",
    "rlimit",
    "external",
    "external_body",
    "broadcast",
    "trigger",
    "trait_spec",
    "trait_impl",
    "contract",
];

/// Rewrites every attribute list in the file, replacing a
/// `#[cfg_attr(<pred>, <attr>...)]` whose inner attribute is a trust_vc attribute
/// with that inner attribute applied directly.
///
/// `cargo trust_vc check` verifies from *source* (never compiling the crate), so
/// a contract gated behind a never-set cfg — e.g.
/// `#[cfg_attr(trust_vc, trust_vc::contract(...))]` on the literal solver
/// function — is inert in the real build yet must still be seen here. Unwrapping
/// the `cfg_attr` (independent of its predicate) lets the proof attach to the
/// real function without pulling a `trust_vc` dependency into the normal build.
/// Only `cfg_attr`s carrying a trust_vc attribute are touched; all other
/// `cfg_attr`s (e.g. `cfg_attr(feature = "x", derive(..))`) are left untouched.
fn unwrap_trust_vc_cfg_attrs_in_file(file: &mut syn::File) {
    use syn::visit_mut::VisitMut;
    CfgAttrUnwrapper.visit_file_mut(file);
}

struct CfgAttrUnwrapper;

impl CfgAttrUnwrapper {
    fn rewrite_attrs(attrs: &mut Vec<syn::Attribute>) {
        let original = std::mem::take(attrs);
        let mut rewritten = Vec::with_capacity(original.len());
        for attr in original {
            if let Some(inner_attrs) = unwrap_trust_vc_cfg_attr(&attr) {
                rewritten.extend(inner_attrs);
            } else {
                rewritten.push(attr);
            }
        }
        *attrs = rewritten;
    }
}

/// If `attr` is `#[cfg_attr(<pred>, <attr>...)]` and at least one inner attribute
/// is a trust_vc attribute, return the inner attributes as standalone
/// `#[...]` attributes; otherwise return `None` (leave the attribute unchanged).
fn unwrap_trust_vc_cfg_attr(attr: &syn::Attribute) -> Option<Vec<syn::Attribute>> {
    let is_cfg_attr = attr
        .path()
        .segments
        .last()
        .is_some_and(|segment| segment.ident == "cfg_attr");
    if !is_cfg_attr {
        return None;
    }
    let syn::Meta::List(meta_list) = &attr.meta else {
        return None;
    };
    let parsed = meta_list
        .parse_args_with(syn::punctuated::Punctuated::<syn::Meta, syn::Token![,]>::parse_terminated)
        .ok()?;
    // First element is the cfg predicate; the rest are attributes to apply.
    let inner_metas: Vec<syn::Meta> = parsed.into_iter().skip(1).collect();
    let has_trust_vc = inner_metas.iter().any(|meta| {
        meta.path()
            .segments
            .last()
            .map(|segment| segment.ident.to_string())
            .is_some_and(|name| TRUST_VC_CFG_ATTR_NAMES.contains(&name.as_str()))
    });
    if !has_trust_vc {
        return None;
    }
    Some(
        inner_metas
            .into_iter()
            .map(|meta| syn::Attribute {
                pound_token: attr.pound_token,
                style: attr.style,
                bracket_token: attr.bracket_token,
                meta,
            })
            .collect(),
    )
}

impl syn::visit_mut::VisitMut for CfgAttrUnwrapper {
    fn visit_item_fn_mut(&mut self, node: &mut syn::ItemFn) {
        Self::rewrite_attrs(&mut node.attrs);
        syn::visit_mut::visit_item_fn_mut(self, node);
    }

    fn visit_impl_item_fn_mut(&mut self, node: &mut syn::ImplItemFn) {
        Self::rewrite_attrs(&mut node.attrs);
        syn::visit_mut::visit_impl_item_fn_mut(self, node);
    }

    fn visit_trait_item_fn_mut(&mut self, node: &mut syn::TraitItemFn) {
        Self::rewrite_attrs(&mut node.attrs);
        syn::visit_mut::visit_trait_item_fn_mut(self, node);
    }
}

/// What to do with a `tracked` parameter modifier during normalization.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TrackedParam {
    /// Drop the marker (proc-macro path: the result is re-emitted as Rust, and a
    /// proc-macro attribute in parameter position does not compile).
    Strip,
    /// Rewrite `tracked x: T` to `#[trust_vc::proof] x: T` (file path: the AST is
    /// only verified, never re-emitted, and the mode must survive).
    MarkProof,
}

fn normalize_verus_source_tokens(tokens: TokenStream) -> TokenStream {
    normalize_bare_assert_forall_by_tokens(normalize_tracked_param_tokens(
        tokens,
        TrackedParam::Strip,
    ))
}

fn normalize_verus_file_tokens(tokens: TokenStream) -> TokenStream {
    normalize_bare_assert_forall_by_tokens(normalize_tracked_param_tokens(
        tokens,
        TrackedParam::MarkProof,
    ))
}

/// A BODYLESS function declaration: `#[trust_vc::spec] fn f(x: int) -> bool;`.
///
/// Not valid Rust, so `syn` hands it back as `Item::Verbatim`.
struct BodylessFn {
    attrs: Vec<syn::Attribute>,
    vis: syn::Visibility,
    sig: syn::Signature,
}

impl Parse for BodylessFn {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let attrs = input.call(syn::Attribute::parse_outer)?;
        let vis: syn::Visibility = input.parse()?;
        let sig: syn::Signature = input.parse()?;
        input.parse::<Token![;]>()?;
        if !input.is_empty() {
            return Err(input.error("expected end of bodyless function declaration"));
        }
        Ok(Self { attrs, vis, sig })
    }
}

/// Rewrites every BODYLESS spec function into an `Item::Fn` carrying an explicit
/// `#[trust_vc::uninterp]` marker and an empty body.
///
/// Verus declares an uninterpreted spec function with no body at all:
/// ```text
/// uninterp spec fn f(x: int) -> bool;
/// ```
/// whose trust-vc spelling is `#[trust_vc::spec] fn f(x: int) -> bool;`. A
/// bodyless free function is not valid Rust, so `syn` yields `Item::Verbatim` —
/// and every consumer matches on `Item::Fn`. So until now such a declaration was
/// **silently dropped**: the symbol simply vanished, taking any call to it down
/// with an error that named neither the function nor the missing surface. That
/// silent drop is the bug this closes; the `uninterp` surface is what it buys.
///
/// The empty block is never read. `SpecFunctionDef::from_item_fn` keys off the
/// marker and builds NO defining axiom, and `apply_to_context` declares the
/// symbol and returns before any axiom could be emitted — so the function is
/// strictly uninterpreted no matter what is revealed. The marker exists because
/// "has no body" must stay observable to a consumer that only ever sees an
/// `ItemFn` with a (synthesized, empty) block.
///
/// FILE path only: the proc-macro path re-emits its input as Rust, where a
/// bodyless fn does not compile in the first place.
fn mark_bodyless_spec_fns_uninterp(items: &mut Vec<syn::Item>) {
    for item in items.iter_mut() {
        if let syn::Item::Mod(module) = item {
            if let Some((_, inner)) = &mut module.content {
                mark_bodyless_spec_fns_uninterp(inner);
            }
            continue;
        }
        let syn::Item::Verbatim(tokens) = item else {
            continue;
        };
        let Ok(mut bodyless) = syn::parse2::<BodylessFn>(tokens.clone()) else {
            continue;
        };
        // Only a SPEC function may be bodyless. A bodyless exec/proof fn is left
        // as `Verbatim` (i.e. still rejected downstream) rather than quietly
        // becoming an uninterpreted symbol.
        if !crate::spec_function_catalog::has_spec_attr(&bodyless.attrs) {
            continue;
        }
        if !crate::spec_function_catalog::has_uninterp_attr(&bodyless.attrs) {
            bodyless
                .attrs
                .push(syn::parse_quote!(#[trust_vc::uninterp]));
        }
        *item = syn::Item::Fn(syn::ItemFn {
            attrs: bodyless.attrs,
            vis: bodyless.vis,
            sig: bodyless.sig,
            block: Box::new(syn::parse_quote!({})),
        });
    }
}

#[allow(clippy::indexing_slicing)] // invariant: rewrite candidates return bounded next indexes
fn normalize_bare_assert_forall_by_tokens(tokens: TokenStream) -> TokenStream {
    let input: Vec<TokenTree> = tokens.into_iter().collect();
    let mut output = TokenStream::new();
    let mut index = 0;

    while index < input.len() {
        if let Some((rewritten, next_index)) = rewrite_bare_assert_forall_by(&input, index) {
            output.extend(rewritten);
            index = next_index;
            continue;
        }

        match &input[index] {
            TokenTree::Group(group) => {
                let delimiter = group.delimiter();
                let stream = if is_macro_body_group(&input, index) {
                    group.stream()
                } else {
                    normalize_bare_assert_forall_by_tokens(group.stream())
                };
                let mut rebuilt = Group::new(delimiter, stream);
                rebuilt.set_span(group.span());
                output.extend(std::iter::once(TokenTree::Group(rebuilt)));
            }
            other => output.extend(std::iter::once(other.clone())),
        }
        index += 1;
    }

    output
}

fn is_macro_body_group(input: &[TokenTree], index: usize) -> bool {
    matches!(
        index.checked_sub(1).and_then(|prev| input.get(prev)),
        Some(TokenTree::Punct(punct)) if punct.as_char() == '!'
    ) || matches!(
        (
            index.checked_sub(2).and_then(|prev| input.get(prev)),
            index.checked_sub(1).and_then(|prev| input.get(prev)),
        ),
        (Some(TokenTree::Punct(punct)), Some(TokenTree::Ident(_))) if punct.as_char() == '!'
    )
}

fn rewrite_bare_assert_forall_by(
    input: &[TokenTree],
    start: usize,
) -> Option<(TokenStream, usize)> {
    if !matches!(input.get(start), Some(TokenTree::Ident(ident)) if ident == "assert")
        || !matches!(input.get(start + 1), Some(TokenTree::Ident(ident)) if ident == "forall")
        || !matches!(input.get(start + 2), Some(TokenTree::Punct(punct)) if punct.as_char() == '|')
    {
        return None;
    }

    let closing_binder = find_next_pipe(input, start + 3)?;
    let by_index = find_by_block(input, closing_binder + 1)?;
    let proof_block_index = by_index + 1;
    let statement_end = proof_block_index + 1;
    let next_index = if matches!(input.get(statement_end), Some(TokenTree::Punct(punct)) if punct.as_char() == ';')
    {
        statement_end + 1
    } else {
        statement_end
    };

    let assertion_tokens = input[start..statement_end]
        .iter()
        .cloned()
        .collect::<TokenStream>();
    Some((
        quote! {
            trust_vc::assert_forall_by!(#assertion_tokens);
        },
        next_index,
    ))
}

fn find_next_pipe(input: &[TokenTree], start: usize) -> Option<usize> {
    input
        .iter()
        .enumerate()
        .skip(start)
        .find_map(|(index, token)| match token {
            TokenTree::Punct(punct) if punct.as_char() == '|' => Some(index),
            _ => None,
        })
}

fn find_by_block(input: &[TokenTree], start: usize) -> Option<usize> {
    input
        .windows(2)
        .enumerate()
        .skip(start)
        .find_map(|(index, pair)| {
            let is_by = matches!(&pair[0], TokenTree::Ident(ident) if ident == "by");
            let is_block = matches!(&pair[1], TokenTree::Group(group) if group.delimiter() == Delimiter::Brace);
            (is_by && is_block).then_some(index)
        })
}

fn normalize_tracked_param_tokens(tokens: TokenStream, tracked: TrackedParam) -> TokenStream {
    let mut output = TokenStream::new();
    let mut awaiting_fn_params = false;

    for token in tokens {
        match token {
            TokenTree::Ident(ident) if ident == "fn" => {
                awaiting_fn_params = true;
                output.extend(std::iter::once(TokenTree::Ident(ident)));
            }
            TokenTree::Group(group) => {
                let delimiter = group.delimiter();
                let span = group.span();
                let stream = if awaiting_fn_params && delimiter == Delimiter::Parenthesis {
                    awaiting_fn_params = false;
                    normalize_param_group(group.stream(), tracked)
                } else {
                    normalize_tracked_param_tokens(group.stream(), tracked)
                };
                let mut rebuilt = Group::new(delimiter, stream);
                rebuilt.set_span(span);
                output.extend(std::iter::once(TokenTree::Group(rebuilt)));
            }
            other => output.extend(std::iter::once(other)),
        }
    }

    output
}

#[allow(clippy::indexing_slicing)] // invariant: token indexing is bounded by `while index < input.len()` and the tracked-shape guards
fn normalize_param_group(tokens: TokenStream, tracked: TrackedParam) -> TokenStream {
    let input: Vec<TokenTree> = tokens.into_iter().collect();
    let mut output = TokenStream::new();
    let mut at_param_start = true;
    let mut index = 0;

    while index < input.len() {
        if at_param_start && matches_tracked_modifier(&input[index..]) {
            if tracked == TrackedParam::MarkProof {
                // `tracked x: T` == Verus `#[verifier::proof] x: T`.
                output.extend(quote! { #[trust_vc::proof] });
            }
            index += 1;
            continue;
        }

        match &input[index] {
            TokenTree::Group(group) => {
                let mut rebuilt = Group::new(
                    group.delimiter(),
                    normalize_tracked_param_tokens(group.stream(), tracked),
                );
                rebuilt.set_span(group.span());
                output.extend(std::iter::once(TokenTree::Group(rebuilt)));
            }
            other => output.extend(std::iter::once(other.clone())),
        }

        at_param_start = matches!(&input[index], TokenTree::Punct(punct) if punct.as_char() == ',');
        index += 1;
    }

    output
}

fn matches_tracked_modifier(tokens: &[TokenTree]) -> bool {
    if !matches!(tokens.first(), Some(TokenTree::Ident(ident)) if ident == "tracked") {
        return false;
    }

    matches_simple_name(tokens, 1)
        || matches_keyword_name(tokens, 1, "mut")
        || matches_keyword_name(tokens, 1, "ref")
        || matches_ref_mut_name(tokens, 1)
}

fn matches_simple_name(tokens: &[TokenTree], start: usize) -> bool {
    matches!(tokens.get(start), Some(TokenTree::Ident(_))) && matches_colon(tokens.get(start + 1))
}

fn matches_keyword_name(tokens: &[TokenTree], start: usize, keyword: &str) -> bool {
    matches!(tokens.get(start), Some(TokenTree::Ident(ident)) if ident == keyword)
        && matches!(tokens.get(start + 1), Some(TokenTree::Ident(_)))
        && matches_colon(tokens.get(start + 2))
}

fn matches_ref_mut_name(tokens: &[TokenTree], start: usize) -> bool {
    matches!(tokens.get(start), Some(TokenTree::Ident(ident)) if ident == "ref")
        && matches!(tokens.get(start + 1), Some(TokenTree::Ident(ident)) if ident == "mut")
        && matches!(tokens.get(start + 2), Some(TokenTree::Ident(_)))
        && matches_colon(tokens.get(start + 3))
}

fn matches_colon(token: Option<&TokenTree>) -> bool {
    matches!(token, Some(TokenTree::Punct(punct)) if punct.as_char() == ':')
}

/// Extracts the names of parameters annotated with `tracked` from a raw token
/// stream representing a function item. Does not modify the tokens.
///
/// For `fn lemma(tracked x: T, y: U, tracked mut z: V)`, returns `["x", "z"]`.
fn extract_tracked_param_names(tokens: &TokenStream) -> Vec<String> {
    let mut names = Vec::new();
    let mut awaiting_fn_params = false;

    for token in tokens.clone() {
        match token {
            TokenTree::Ident(ref ident) if ident == "fn" => {
                awaiting_fn_params = true;
            }
            TokenTree::Group(ref group)
                if awaiting_fn_params && group.delimiter() == Delimiter::Parenthesis =>
            {
                awaiting_fn_params = false;
                extract_tracked_names_from_params(group.stream(), &mut names);
            }
            _ => {}
        }
    }

    names
}

#[allow(clippy::indexing_slicing)] // invariant: token indexing is bounded by `while index < input.len()` and `matches_tracked_modifier(...)`
fn extract_tracked_names_from_params(tokens: TokenStream, names: &mut Vec<String>) {
    let input: Vec<TokenTree> = tokens.into_iter().collect();
    let mut at_param_start = true;
    let mut index = 0;

    while index < input.len() {
        if at_param_start && matches_tracked_modifier(&input[index..]) {
            // Extract the param name after the tracked modifier.
            // Patterns: `tracked name :`, `tracked mut name :`, `tracked ref name :`,
            //           `tracked ref mut name :`
            let name_offset = if matches!(input.get(index + 1), Some(TokenTree::Ident(id)) if id == "ref")
            {
                if matches!(input.get(index + 2), Some(TokenTree::Ident(id)) if id == "mut") {
                    3 // tracked ref mut name
                } else {
                    2 // tracked ref name
                }
            } else if matches!(input.get(index + 1), Some(TokenTree::Ident(id)) if id == "mut") {
                2 // tracked mut name
            } else {
                1 // tracked name
            };

            if let Some(TokenTree::Ident(name_ident)) = input.get(index + name_offset) {
                names.push(name_ident.to_string());
            }
        }

        at_param_start = matches!(&input[index], TokenTree::Punct(punct) if punct.as_char() == ',');
        index += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::{parse_file_allow_tracked, parse_item_fn_allow_tracked};

    #[test]
    fn parse_item_fn_strips_tracked_param_modifier() {
        let item = parse_item_fn_allow_tracked(quote::quote! {
            fn lemma(tracked token: Resource) {}
        })
        .expect("tracked proof syntax should parse");

        let syn::FnArg::Typed(param) = &item.sig.inputs[0] else {
            panic!("expected typed parameter");
        };
        let syn::Pat::Ident(binding) = &*param.pat else {
            panic!("expected ident pattern");
        };

        let ty = &param.ty;
        assert_eq!(binding.ident.to_string(), "token");
        assert_eq!(quote::quote!(#ty).to_string(), "Resource");
    }

    #[test]
    fn parse_item_fn_strips_tracked_mut_param_modifier() {
        let item = parse_item_fn_allow_tracked(quote::quote! {
            fn lemma(tracked mut token: Resource) {}
        })
        .expect("tracked mut proof syntax should parse");

        let syn::FnArg::Typed(param) = &item.sig.inputs[0] else {
            panic!("expected typed parameter");
        };
        let syn::Pat::Ident(binding) = &*param.pat else {
            panic!("expected ident pattern");
        };

        assert!(binding.mutability.is_some(), "mut binding should survive");
        assert_eq!(binding.ident.to_string(), "token");
    }

    #[test]
    fn parse_file_allows_tracked_param_inside_module() {
        let file = parse_file_allow_tracked(
            r#"
            mod proofs {
                #[trust_vc::proof]
                fn lemma(tracked token: Resource) {}
            }
            "#,
        )
        .expect("tracked syntax should not break module parsing");

        assert_eq!(file.items.len(), 1);
    }

    #[test]
    fn parse_file_rewrites_bare_assert_forall_by_statement() {
        let file = parse_file_allow_tracked(
            r#"
            fn proof() {
                assert forall |k: u32| k + 0u32 == k by {
                    trust_vc::assume!(k + 0u32 == k);
                };
            }
            "#,
        )
        .expect("bare Verus assert-forall-by statements should parse");

        let syn::Item::Fn(func) = &file.items[0] else {
            panic!("expected function item");
        };
        let syn::Stmt::Macro(stmt) = &func.block.stmts[0] else {
            panic!("expected rewritten macro statement");
        };

        let path = &stmt.mac.path;
        assert_eq!(
            quote::quote!(#path).to_string(),
            "trust_vc :: assert_forall_by"
        );
        assert!(
            stmt.mac.tokens.to_string().starts_with("assert forall"),
            "macro input should preserve the Verus source token shape"
        );
    }

    #[test]
    fn parse_file_rewrites_nested_bare_assert_forall_by_statement() {
        parse_file_allow_tracked(
            r#"
            fn proof() {
                let _ = ({
                    assert forall |k: u32| k + 0u32 == k by {};
                    0u32
                });
            }
            "#,
        )
        .expect("bare assert-forall-by statements should normalize inside nested groups");
    }

    #[test]
    fn parse_file_does_not_rewrite_macro_invocation_or_transcriber_bodies() {
        let file = parse_file_allow_tracked(
            r#"
            macro_rules! raw_verus_tokens {
                () => {
                    assert forall |k: u32| k == k by {};
                };
            }

            fn proof() {
                raw_verus_tokens!({
                    assert forall |k: u32| k == k by {};
                });
            }
            "#,
        )
        .expect("macro bodies are token trees and should not be normalized as function statements");

        let rendered = quote::quote!(#file).to_string();
        assert!(
            rendered.contains("macro_rules ! raw_verus_tokens"),
            "macro_rules! definition should remain present"
        );
        assert!(
            rendered.contains("raw_verus_tokens !"),
            "macro invocation should remain present"
        );
        assert!(
            !rendered.contains("trust_vc :: assert_forall_by"),
            "macro token bodies should not be rewritten by source normalization"
        );
    }

    #[test]
    fn parse_item_fn_preserves_parameter_named_tracked() {
        let item = parse_item_fn_allow_tracked(quote::quote! {
            fn lemma(tracked: bool) {}
        })
        .expect("plain Rust parameter named tracked should keep parsing");

        let syn::FnArg::Typed(param) = &item.sig.inputs[0] else {
            panic!("expected typed parameter");
        };
        let syn::Pat::Ident(binding) = &*param.pat else {
            panic!("expected ident pattern");
        };

        assert_eq!(binding.ident.to_string(), "tracked");
    }

    // --- extract_tracked_param_names tests (Part of #2427 Slice 3) ---

    use super::{extract_tracked_param_names, parse_item_fn_with_tracked_info};

    #[test]
    fn extract_tracked_single_param() {
        let tokens = quote::quote! { fn lemma(tracked token: Resource) {} };
        let names = extract_tracked_param_names(&tokens);
        assert_eq!(names, vec!["token"]);
    }

    #[test]
    fn extract_tracked_mut_param() {
        let tokens = quote::quote! { fn lemma(tracked mut token: Resource) {} };
        let names = extract_tracked_param_names(&tokens);
        assert_eq!(names, vec!["token"]);
    }

    #[test]
    fn extract_tracked_mixed_params() {
        let tokens = quote::quote! {
            fn lemma(tracked x: T, y: U, tracked mut z: V) {}
        };
        let names = extract_tracked_param_names(&tokens);
        assert_eq!(names, vec!["x", "z"]);
    }

    #[test]
    fn extract_tracked_no_tracked_params() {
        let tokens = quote::quote! { fn lemma(x: T, y: U) {} };
        let names = extract_tracked_param_names(&tokens);
        assert!(names.is_empty());
    }

    #[test]
    fn extract_tracked_param_named_tracked_not_extracted() {
        let tokens = quote::quote! { fn lemma(tracked: bool) {} };
        let names = extract_tracked_param_names(&tokens);
        assert!(
            names.is_empty(),
            "parameter named 'tracked' is not a tracked modifier"
        );
    }

    #[test]
    fn parse_with_tracked_info_returns_both() {
        let tokens = quote::quote! {
            fn lemma(tracked token: Resource, x: i32) {}
        };
        let result =
            parse_item_fn_with_tracked_info(tokens).expect("should parse with tracked info");
        assert_eq!(result.tracked_params, vec!["token"]);
        assert_eq!(result.item_fn.sig.ident.to_string(), "lemma");
        assert_eq!(result.item_fn.sig.inputs.len(), 2);
    }
}
