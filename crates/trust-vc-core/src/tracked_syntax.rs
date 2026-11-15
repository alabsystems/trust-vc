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
    // D1a `state_machine!` expansion runs BEFORE every other rewrite, so the
    // generated attributes are already canonical and the user's macro tokens
    // never pass through alias or cfg_attr rewriting. It never fails (a
    // refusal becomes a poison marker) and is an exact no-op for a file with
    // no item-position invocation. See `crate::state_machine_dsl`.
    crate::state_machine_dsl::expand_file(&mut file);
    // Runs FIRST, and here rather than in any one consumer: a contract reached
    // through `use trust_vc::ensures as promises` must look canonical to the
    // scanner AND to the extractor, or the two disagree — the scanner drops the
    // function (silent, exit 0) or, worse, discovers it with no visible clause
    // and it verifies vacuously. Resolving at the shared parse entry means the
    // lanes cannot diverge. See `crate::contract_attr_alias`.
    let _alias_report = crate::contract_attr_alias::resolve_contract_attr_aliases(&mut file);
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
///
/// The predicate is not evaluated, so an unwrapped attribute may be absent from
/// the build. A postcondition read as present is still sound: the body is
/// checked against it, and a caller only relies on what that check shows. A
/// precondition or a mode is not ([`presence_cannot_be_assumed`]), so a
/// `cfg_attr` that carries one is also kept in place, and the `cfg` refusal
/// (`vc_extraction::refuse_unevaluated_cfg`) refuses a `Verified` answer for
/// the function and for every function that reaches it.
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
                let keep = inner_attrs.iter().any(presence_cannot_be_assumed);
                rewritten.extend(inner_attrs);
                if keep {
                    rewritten.push(attr);
                }
            } else {
                rewritten.push(attr);
            }
        }
        *attrs = rewritten;
    }
}

/// Whether reading `attr` as present when the build leaves it out can make a
/// `Verified` answer false.
///
/// * `requires`, and a `contract` with a `requires` clause: the body is checked
///   under a precondition the function the build runs does not have.
/// * `spec` and `proof`: the lane reads the body as ghost code, with no
///   overflow obligation, and reads a call of it from exec code without one
///   either, while a build that leaves the mode out runs the body as an
///   ordinary exec function (`#[cfg_attr(any(), trust_vc::spec)] fn inc(x:
///   u64) -> u64 { x + 1u64 }` overflows when an exec caller passes
///   `u64::MAX`).
fn presence_cannot_be_assumed(attr: &syn::Attribute) -> bool {
    let Some(name) = attr
        .path()
        .segments
        .last()
        .map(|segment| segment.ident.to_string())
    else {
        return false;
    };
    match name.as_str() {
        "requires" | "spec" | "proof" => true,
        "contract" => match &attr.meta {
            syn::Meta::List(list) => tokens_name(list.tokens.clone(), "requires"),
            _ => false,
        },
        _ => false,
    }
}

/// The name of the first function in `file` that carries a `cfg_attr` kept by
/// the unwrapping: one that gates a precondition or a mode
/// ([`presence_cannot_be_assumed`]). The file-level trait conformance context
/// has no per-function `cfg` reach, so it is refused on this.
pub(crate) fn first_cfg_gated_precondition_or_mode(file: &syn::File) -> Option<String> {
    struct Finder(Option<String>);
    impl Finder {
        fn check(&mut self, attrs: &[syn::Attribute], ident: &syn::Ident) {
            let gated = attrs.iter().any(|attr| {
                unwrap_trust_vc_cfg_attr(attr)
                    .is_some_and(|inner| inner.iter().any(presence_cannot_be_assumed))
            });
            if gated && self.0.is_none() {
                self.0 = Some(ident.to_string());
            }
        }
    }
    impl<'ast> syn::visit::Visit<'ast> for Finder {
        fn visit_item_fn(&mut self, node: &'ast syn::ItemFn) {
            self.check(&node.attrs, &node.sig.ident);
            syn::visit::visit_item_fn(self, node);
        }
        fn visit_impl_item_fn(&mut self, node: &'ast syn::ImplItemFn) {
            self.check(&node.attrs, &node.sig.ident);
            syn::visit::visit_impl_item_fn(self, node);
        }
        fn visit_trait_item_fn(&mut self, node: &'ast syn::TraitItemFn) {
            self.check(&node.attrs, &node.sig.ident);
            syn::visit::visit_trait_item_fn(self, node);
        }
    }
    let mut finder = Finder(None);
    syn::visit::Visit::visit_file(&mut finder, file);
    finder.0
}

/// Whether `tokens` hold the identifier `name` at any group depth.
fn tokens_name(tokens: TokenStream, name: &str) -> bool {
    tokens.into_iter().any(|tree| match tree {
        TokenTree::Ident(ident) => ident == name,
        TokenTree::Group(group) => tokens_name(group.stream(), name),
        _ => false,
    })
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
    normalize_ghost_tracked_local_tokens(normalize_bare_assert_forall_by_tokens(
        normalize_tracked_param_tokens(tokens, TrackedParam::MarkProof),
    ))
}

/// Rewrites a Verus-style ghost/tracked LOCAL declaration into the equivalent
/// mode ATTRIBUTE on the same `let`:
///
/// ```text
/// let ghost   [mut] x ...   ->   #[trust_vc::spec]  let [mut] x ...
/// let tracked [mut] x ...   ->   #[trust_vc::proof] let [mut] x ...
/// ```
///
/// **FILE path only**, and the exact twin of the `tracked x: T` PARAMETER
/// rewrite above: in Verus, `let ghost x` / `let tracked x` are surface sugar
/// for a spec-/proof-mode binding (`vir/src/modes.rs` assigns every `let` a
/// `Mode`), and `#[verifier::spec] let x` / `#[verifier::proof] let x` is the
/// attribute spelling of the same thing — upstream `modes.rs` itself uses BOTH
/// (`#[verifier::spec] let b: bool = ...` in `eq_mode`, `let ghost b = false;`
/// in `initialize_spec_var_in_exec`).
///
/// Why an attribute and not a drop: `let ghost x` does not parse as Rust at
/// all, so before this rewrite EVERY upstream case that declares a ghost or
/// tracked local was a hard `cannot parse source` FileError — it could not be
/// ported, whatever the engine could prove. Dropping the marker instead would
/// be worse than not parsing: the binding would become indistinguishable from
/// an exec local, and [`crate::mode_body`] could not tell a legal ghost
/// mutation inside `proof_block!` from the ILLEGAL mutation of an exec local
/// there (which is erased at runtime — see that module).
///
/// Deliberately narrow, so it can never touch a program that parses today:
/// the rewrite fires ONLY on `let` immediately followed by the bare ident
/// `ghost`/`tracked` and then a binding-name shape (`x` or `mut x`). A
/// local actually *named* `ghost` (`let ghost = 5;`, `let ghost: u32 = 5;`) is
/// left alone, because `=`/`:` is not a binding-name shape.
fn normalize_ghost_tracked_local_tokens(tokens: TokenStream) -> TokenStream {
    let input: Vec<TokenTree> = tokens.into_iter().collect();
    let mut output = TokenStream::new();
    let mut index = 0;

    while index < input.len() {
        if let Some(marker) = ghost_tracked_local_marker(&input, index) {
            // `let` stays; the mode marker token is replaced by the attribute,
            // which syn attaches to the `syn::Local` it precedes.
            match marker {
                LocalMode::Ghost => output.extend(quote! { #[trust_vc::spec] }),
                LocalMode::Tracked => output.extend(quote! { #[trust_vc::proof] }),
            }
            if let Some(let_token) = input.get(index) {
                output.extend(std::iter::once(let_token.clone()));
            }
            // Skip `let` and the consumed `ghost`/`tracked` marker.
            index += 2;
            continue;
        }

        match input.get(index) {
            Some(TokenTree::Group(group)) => {
                let mut rebuilt = Group::new(
                    group.delimiter(),
                    normalize_ghost_tracked_local_tokens(group.stream()),
                );
                rebuilt.set_span(group.span());
                output.extend(std::iter::once(TokenTree::Group(rebuilt)));
            }
            Some(other) => output.extend(std::iter::once(other.clone())),
            None => break,
        }
        index += 1;
    }

    output
}

/// The mode a `let ghost` / `let tracked` local declares.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LocalMode {
    Ghost,
    Tracked,
}

/// Recognizes `let ghost <name-shape>` / `let tracked <name-shape>` starting at
/// `index` (which must point at the `let`). Returns the declared mode, or
/// `None` if this is not a ghost/tracked local declaration.
fn ghost_tracked_local_marker(tokens: &[TokenTree], index: usize) -> Option<LocalMode> {
    if !matches!(tokens.get(index), Some(TokenTree::Ident(ident)) if ident == "let") {
        return None;
    }
    let mode = match tokens.get(index + 1) {
        Some(TokenTree::Ident(ident)) if ident == "ghost" => LocalMode::Ghost,
        Some(TokenTree::Ident(ident)) if ident == "tracked" => LocalMode::Tracked,
        _ => return None,
    };
    if !is_local_binding_name_shape(tokens, index + 2) {
        return None;
    }
    Some(mode)
}

/// Whether `tokens[start..]` begins a plain binding name: `x` or `mut x`.
///
/// Anything else (`=`, `:`, a tuple pattern, end of stream) means the preceding
/// `ghost`/`tracked` ident was the binding name itself, not a mode marker.
fn is_local_binding_name_shape(tokens: &[TokenTree], start: usize) -> bool {
    match tokens.get(start) {
        Some(TokenTree::Ident(ident)) if ident == "mut" => {
            matches!(tokens.get(start + 1), Some(TokenTree::Ident(_)))
        }
        Some(TokenTree::Ident(_)) => true,
        _ => false,
    }
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
fn mark_bodyless_spec_fns_uninterp(items: &mut [syn::Item]) {
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

#[cfg(test)]
mod ghost_tracked_local_tests {
    use super::parse_file_allow_tracked;

    fn body_of(src: &str) -> String {
        let file = parse_file_allow_tracked(src).expect("source should parse");
        let syn::Item::Fn(func) = &file.items[0] else {
            panic!("expected a fn item")
        };
        quote::ToTokens::to_token_stream(&func.block).to_string()
    }

    #[test]
    fn ghost_local_becomes_a_spec_attribute() {
        let body = body_of("fn f(a: u64) { let ghost g: u64 = a; }");
        assert!(
            body.contains("trust_vc :: spec"),
            "`let ghost` must carry the spec mode onto the local: {body}"
        );
    }

    #[test]
    fn tracked_local_becomes_a_proof_attribute() {
        let body = body_of("fn f(a: u64) { let tracked t: u64 = a; }");
        assert!(
            body.contains("trust_vc :: proof"),
            "`let tracked` must carry the proof mode onto the local: {body}"
        );
    }

    #[test]
    fn ghost_mut_and_uninitialized_forms_parse() {
        for src in [
            "fn f(a: u64) { let ghost mut g: u64 = a; }",
            "fn f() { let ghost g: bool; }",
            "fn f() { let tracked mut t: bool; }",
        ] {
            assert!(
                parse_file_allow_tracked(src).is_ok(),
                "should parse after normalization: {src}"
            );
        }
    }

    #[test]
    fn a_local_actually_named_ghost_or_tracked_is_left_alone() {
        // OVER-REJECTION guard. `ghost` and `tracked` are not Rust keywords, so
        // they are legal binding names; the rewrite must fire only on the
        // `let <marker> <name>` shape and never on `let ghost = ..` /
        // `let ghost: T = ..`.
        for src in [
            "fn f() -> u64 { let ghost = 5u64; ghost }",
            "fn f() -> u64 { let tracked: u64 = 7u64; tracked }",
            "fn f() -> u64 { let mut ghost = 5u64; ghost = 6u64; ghost }",
        ] {
            let body = body_of(src);
            assert!(
                !body.contains("trust_vc :: spec") && !body.contains("trust_vc :: proof"),
                "a local NAMED ghost/tracked must not acquire a mode attribute: {body}"
            );
        }
    }

    #[test]
    fn ghost_locals_nested_in_blocks_are_normalized() {
        let body = body_of("fn f(a: u64) { if a > 0 { let ghost g: u64 = a; } }");
        assert!(body.contains("trust_vc :: spec"), "{body}");
    }

    /// The attributes of `fn f` (or of `S::f`) after parsing, one per entry.
    fn attrs_of(src: &str) -> Vec<String> {
        use quote::ToTokens;
        let file = parse_file_allow_tracked(src).expect("fixture parses");
        let attrs = file
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "f" => Some(func.attrs.clone()),
                syn::Item::Impl(imp) => imp.items.iter().find_map(|item| match item {
                    syn::ImplItem::Fn(func) if func.sig.ident == "f" => Some(func.attrs.clone()),
                    _ => None,
                }),
                syn::Item::Trait(tr) => tr.items.iter().find_map(|item| match item {
                    syn::TraitItem::Fn(func) if func.sig.ident == "f" => Some(func.attrs.clone()),
                    _ => None,
                }),
                _ => None,
            })
            .expect("fixture has `f`");
        attrs
            .iter()
            .map(|attr| attr.to_token_stream().to_string())
            .collect()
    }

    #[test]
    fn a_gated_precondition_or_mode_keeps_its_cfg_attr() {
        for (src, unwrapped) in [
            (
                "#[cfg_attr(any(), trust_vc::requires(x > 0u64))] fn f(x: u64) {}",
                "# [trust_vc :: requires (x > 0u64)]",
            ),
            (
                "#[cfg_attr(test, requires(x > 0u64))] fn f(x: u64) {}",
                "# [requires (x > 0u64)]",
            ),
            (
                "#[cfg_attr(trust_vc, trust_vc::contract(requires(x > 0u64), ensures(ret == x), returns(ret)))] fn f(x: u64) -> u64 { x }",
                "# [trust_vc :: contract (requires (x > 0u64) , ensures (ret == x) , returns (ret))]",
            ),
            (
                "#[cfg_attr(trust_vc, trust_vc::ensures(result == x), trust_vc::requires(x > 0u64))] fn f(x: u64) -> u64 { x }",
                "# [trust_vc :: requires (x > 0u64)]",
            ),
            (
                "#[cfg_attr(any(), trust_vc::spec)] fn f(x: u64) -> u64 { x + 1u64 }",
                "# [trust_vc :: spec]",
            ),
            (
                "#[cfg_attr(not(test), trust_vc::proof)] fn f() {}",
                "# [trust_vc :: proof]",
            ),
            (
                "struct S; impl S { #[cfg_attr(any(), trust_vc::requires(x > 0u64))] fn f(&self, x: u64) {} }",
                "# [trust_vc :: requires (x > 0u64)]",
            ),
            (
                "trait T { #[cfg_attr(any(), trust_vc::requires(x > 0u64))] fn f(&self, x: u64); }",
                "# [trust_vc :: requires (x > 0u64)]",
            ),
        ] {
            let attrs = attrs_of(src);
            assert!(attrs.iter().any(|a| a == unwrapped), "{src}: {attrs:?}");
            assert!(
                attrs.iter().any(|a| a.starts_with("# [cfg_attr (")),
                "{src}: the cfg_attr must stay for the cfg refusal: {attrs:?}"
            );
        }
    }

    #[test]
    fn a_gated_postcondition_is_only_unwrapped() {
        for (src, unwrapped) in [
            (
                "#[cfg_attr(any(), trust_vc::ensures(result == x))] fn f(x: u64) -> u64 { x }",
                "# [trust_vc :: ensures (result == x)]",
            ),
            (
                "#[cfg_attr(trust_vc, trust_vc::contract(ensures(ret >= 0), returns(ret)))] fn f() -> i64 { 0 }",
                "# [trust_vc :: contract (ensures (ret >= 0) , returns (ret))]",
            ),
            (
                "#[cfg_attr(any(), trust_vc::decreases(n))] fn f(n: u64) -> u64 { if n == 0 { 0 } else { f(n - 1) } }",
                "# [trust_vc :: decreases (n)]",
            ),
        ] {
            let attrs = attrs_of(src);
            assert_eq!(attrs, vec![unwrapped.to_string()], "{src}");
        }
    }
}
