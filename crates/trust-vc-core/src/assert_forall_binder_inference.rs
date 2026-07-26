// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Binder-type inference for `assert forall|x| …` (untyped binders).
//!
//! Verus lets an `assert forall` binder omit its type and infers it from the
//! binder's USE (upstream `assert_forall_by.rs::test_forallstmt1` contains both
//! `assert forall|x: int| f1(x) > x` and the inference variant
//! `assert forall|x| f1(x) > x` in the SAME test case, so the case cannot
//! reproduce without this).
//!
//! trust-vc's quantifier encoding needs a concrete sort for every bound
//! variable, so this pass runs as a source-level pre-pass over the verified
//! function's body: it rewrites `|x|` into `|x: T|` wherever `T` is forced by
//! the program itself, and otherwise leaves the tokens ALONE so the downstream
//! parser keeps failing closed with "assert_forall_by! binders must be typed".
//!
//! ## Why this is sound
//!
//! The inferred type is never guessed. It is READ OFF the declared parameter
//! type of a spec function the binder is passed to, at the position it is passed
//! in: for `assert forall|x| f1(x) > x` with `spec fn f1(i: int) -> int`, `x`
//! must be `int` or the program would not typecheck in Rust/Verus either. Two
//! properties keep it fail-closed:
//!
//! 1. **Spec functions only.** A quantifier body is a spec-mode context, so a
//!    spec fn is the only thing callable inside it. Restricting resolution to
//!    `#[trust_vc::spec]` items means a local closure or an exec helper that
//!    happens to share a name can never supply a type.
//! 2. **Unanimity or nothing.** Every occurrence of the binder in an argument
//!    position must agree on the type. A binder used at two spec fns with
//!    different parameter types (or used at none) is left untyped, and the
//!    existing typed-binder error fires.
//!
//! Guessing WIDER than the truth (say `nat` where the program means `int`) is
//! the direction that would prove MORE than Verus — a `forall` over a smaller
//! domain is a weaker hypothesis to discharge. That is exactly why the type is
//! taken from the callee's signature rather than inferred from the body's
//! operators.

use std::collections::BTreeMap;

use proc_macro2::{Delimiter, Spacing, TokenStream, TokenTree};
use quote::quote;
use syn::visit_mut::VisitMut;
use syn::{File, Item, ItemFn, Type};

/// Spec-function name -> declared parameter types, in order.
type SpecSignatures = BTreeMap<String, Vec<Type>>;

/// Rewrites untyped `assert forall` binders in `func`'s body using the spec
/// functions declared in `file`. Returns `None` when nothing was inferred (the
/// caller then verifies the original, unmodified function).
pub(crate) fn infer_untyped_assert_forall_binders(file: &File, func: &ItemFn) -> Option<ItemFn> {
    let signatures = collect_spec_signatures(file);
    if signatures.is_empty() {
        return None;
    }

    let mut rewriter = BinderInference {
        signatures,
        changed: false,
    };
    let mut rewritten = func.clone();
    rewriter.visit_item_fn_mut(&mut rewritten);
    rewriter.changed.then_some(rewritten)
}

fn collect_spec_signatures(file: &File) -> SpecSignatures {
    let mut signatures = SpecSignatures::new();
    for item in &file.items {
        let Item::Fn(item_fn) = item else {
            continue;
        };
        // Only SPEC functions participate: a quantifier body is a spec context.
        if !matches!(
            crate::mode_attrs::classify_item_fn(item_fn),
            crate::mode::FunctionMode::Spec
        ) {
            continue;
        }
        let mut params = Vec::new();
        let mut typed = true;
        for input in &item_fn.sig.inputs {
            match input {
                syn::FnArg::Typed(pat_type) => params.push((*pat_type.ty).clone()),
                syn::FnArg::Receiver(_) => {
                    typed = false;
                    break;
                }
            }
        }
        if typed {
            signatures.insert(item_fn.sig.ident.to_string(), params);
        }
    }
    signatures
}

struct BinderInference {
    signatures: SpecSignatures,
    changed: bool,
}

impl VisitMut for BinderInference {
    fn visit_macro_mut(&mut self, mac: &mut syn::Macro) {
        let Some(name) = mac.path.segments.last().map(|seg| seg.ident.to_string()) else {
            return;
        };
        if !matches!(
            name.as_str(),
            "assert" | "trust_vc_assert" | "assert_forall_by"
        ) {
            return;
        }
        if let Some(rewritten) = annotate_binders(mac.tokens.clone(), &self.signatures) {
            mac.tokens = rewritten;
            self.changed = true;
        }
    }

    fn visit_item_mut(&mut self, _: &mut Item) {
        // A nested item has its own scope and its own verification; do not
        // rewrite through it.
    }
}

/// Rewrites `|x| body` / `assert forall |x| body by { .. }` token streams,
/// annotating each untyped binder whose type the body forces. Returns `None` if
/// no binder was annotated.
fn annotate_binders(tokens: TokenStream, signatures: &SpecSignatures) -> Option<TokenStream> {
    let trees: Vec<TokenTree> = tokens.into_iter().collect();

    // Skip the leading `assert` / `forall` keywords of the Verus surface.
    let mut open = 0usize;
    while matches!(trees.get(open), Some(TokenTree::Ident(ident))
        if ident == "assert" || ident == "forall")
    {
        open += 1;
    }
    if !is_punct(trees.get(open)?, '|') {
        return None;
    }
    let close = (open + 1..trees.len()).find(|&idx| is_punct(&trees[idx], '|'))?;

    let binder_segments = split_top_level_commas(&trees[open + 1..close]);
    let body = &trees[close + 1..];

    let mut annotated: Vec<TokenStream> = Vec::new();
    let mut changed = false;
    for segment in &binder_segments {
        if let [TokenTree::Ident(ident)] = segment.as_slice() {
            if let Some(ty) = infer_binder_type(&ident.to_string(), body, signatures) {
                annotated.push(quote!(#ident: #ty));
                changed = true;
                continue;
            }
        }
        annotated.push(segment.iter().cloned().collect());
    }
    if !changed {
        return None;
    }

    let mut out: TokenStream = trees[..=open].iter().cloned().collect();
    for (index, segment) in annotated.iter().enumerate() {
        if index > 0 {
            out.extend(quote!(,));
        }
        out.extend(segment.clone());
    }
    out.extend(trees[close..].iter().cloned());
    Some(out)
}

/// The type every argument-position occurrence of `binder` agrees on, or `None`
/// (no occurrence, an unknown callee, or a disagreement — all fail closed).
fn infer_binder_type(
    binder: &str,
    body: &[TokenTree],
    signatures: &SpecSignatures,
) -> Option<Type> {
    let mut found: Option<Type> = None;
    collect_binder_arg_types(binder, body, signatures, &mut |ty| {
        match &found {
            // Disagreement between two call sites: poison the inference.
            Some(existing) if !types_match(existing, &ty) => found = Some(poison_type()),
            Some(_) => {}
            None => found = Some(ty),
        }
    });
    let ty = found?;
    (!types_match(&ty, &poison_type())).then_some(ty)
}

/// A type that can never be written in source, used as the "conflicting
/// inference" sentinel so a disagreement can never annotate a binder.
fn poison_type() -> Type {
    syn::parse_quote!(__trust_vc_conflicting_binder_type)
}

fn types_match(left: &Type, right: &Type) -> bool {
    use quote::ToTokens;
    left.to_token_stream().to_string() == right.to_token_stream().to_string()
}

/// Walks `trees` for `f( … )` calls on a known spec fn and reports the declared
/// parameter type at each position where `binder` is passed as a BARE argument.
fn collect_binder_arg_types(
    binder: &str,
    trees: &[TokenTree],
    signatures: &SpecSignatures,
    report: &mut impl FnMut(Type),
) {
    for (index, tree) in trees.iter().enumerate() {
        if let TokenTree::Group(group) = tree {
            // Recurse into every group so nested calls are seen too.
            let inner: Vec<TokenTree> = group.stream().into_iter().collect();
            collect_binder_arg_types(binder, &inner, signatures, report);

            if group.delimiter() != Delimiter::Parenthesis || index == 0 {
                continue;
            }
            // A parenthesized group directly after an identifier is a call.
            let TokenTree::Ident(callee) = &trees[index - 1] else {
                continue;
            };
            let Some(params) = signatures.get(&callee.to_string()) else {
                continue;
            };
            let args = split_top_level_commas(&inner);
            for (position, arg) in args.iter().enumerate() {
                // Only a BARE `x` argument pins the binder's type. `x + 1` or
                // `x as int` says nothing about `x`'s own type.
                let [TokenTree::Ident(ident)] = arg.as_slice() else {
                    continue;
                };
                if ident != binder {
                    continue;
                }
                if let Some(ty) = params.get(position) {
                    report(ty.clone());
                }
            }
        }
    }
}

fn split_top_level_commas(trees: &[TokenTree]) -> Vec<Vec<TokenTree>> {
    let mut segments = Vec::new();
    let mut current = Vec::new();
    for tree in trees {
        if is_punct(tree, ',') {
            segments.push(std::mem::take(&mut current));
        } else {
            current.push(tree.clone());
        }
    }
    if !current.is_empty() {
        segments.push(current);
    }
    segments
}

fn is_punct(tree: &TokenTree, ch: char) -> bool {
    matches!(tree, TokenTree::Punct(punct)
        if punct.as_char() == ch && punct.spacing() == Spacing::Alone)
}

#[cfg(test)]
#[path = "assert_forall_binder_inference_tests.rs"]
mod tests;
