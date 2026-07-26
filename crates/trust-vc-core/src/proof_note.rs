// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `#[verifier::proof_note("…")]` / `#[verifier::custom_err("…")]` label
//! parsing (Verus diagnostic-parity foundation, slice 3 FAMILY C).
//!
//! Upstream grounding (pinned Verus `a40d57c`):
//! * `builtin_macros/src/syntax.rs` moves statement-level attrs on
//!   `assert`/`assume` INSIDE onto the argument expression (`:2803`/`:2825`)
//!   and normalizes clause inner attrs `#![…]` onto the clause expression
//!   (`:3710-3724`).
//! * `rust_verify/src/attributes.rs:416-425` parses BOTH `proof_note` and
//!   `custom_err` into `Attr::ProofNote { is_custom_err }`;
//!   `get_proof_note_annotation` (`:1010-1023`) rejects two or more labels of
//!   ANY MIX on one expression with the PRIMARY, translation-time error
//!   "at most one `proof_note` attribute is allowed" — it fires during
//!   HIR→VIR translation, BEFORE verification, regardless of proof outcome.
//! * `rust_verify/src/verifier.rs:96-140` renders a failing obligation that
//!   carries a label: `proof_note` attaches a secondary span label
//!   `note: {text}` to the unchanged primary failure diagnostic;
//!   `custom_err` REPLACES the primary message with the label text.
//!
//! trust-vc mirror: labels are collected at the three attachment positions
//! (statement-level attrs on `assert!`/`assume!` macro statements,
//! expression-level attrs inside the macro token stream, clause-level inner
//! attrs `#![…]` inside `#[trust_vc::requires/ensures(…)]`), pooled per
//! expression/clause, the at-most-one rule enforced as an extraction-time
//! `TrustVcError::Encoding` with the verbatim upstream message, and a single
//! label attached to the emitted [`crate::vc::ProofObligation`] so the
//! verifier can report a labeled FAILING obligation through the Verus error
//! channel (see `VerificationContext::apply_proof_note_verdict`).

use crate::error::{TrustVcError, TrustVcResult};
use proc_macro2::{Delimiter, TokenStream, TokenTree};
use syn::Expr;

/// Verbatim upstream message (rust_verify/src/attributes.rs:1017).
pub const AT_MOST_ONE_PROOF_NOTE: &str = "at most one `proof_note` attribute is allowed";

/// A parsed `proof_note`/`custom_err` label.
///
/// `is_custom_err == false`: Verus attaches "note: {text}" to the primary
/// failure diagnostic. `is_custom_err == true`: Verus replaces the primary
/// failure message with `text`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofNoteLabel {
    /// The user-supplied label text (the string-literal argument).
    pub text: String,
    /// True for `custom_err` (replacement message), false for `proof_note`
    /// (secondary "note: …" label).
    pub is_custom_err: bool,
}

/// Recognizes a proof-note attribute path: exactly two segments, the
/// qualifier `verifier` (upstream spelling) or `trust_vc` (compile-safe
/// spelling for macro-compiled crates), and the name `proof_note` or
/// `custom_err`. Single-segment or otherwise-qualified paths are NOT
/// recognized (a user attribute merely named `proof_note` must not change
/// verdict semantics).
fn proof_note_path_kind(path: &syn::Path) -> Option<bool> {
    if path.leading_colon.is_some() || path.segments.len() != 2 {
        return None;
    }
    let qualifier = path.segments[0].ident.to_string();
    if qualifier != "verifier" && qualifier != "trust_vc" {
        return None;
    }
    match path.segments[1].ident.to_string().as_str() {
        "proof_note" => Some(false),
        "custom_err" => Some(true),
        _ => None,
    }
}

fn malformed_label_error(name: &str) -> TrustVcError {
    TrustVcError::Encoding {
        context: "extract proof_note attributes",
        detail: format!(
            "`{name}` attribute expects exactly one string-literal argument, e.g. \
             `#[verifier::{name}(\"…\")]` — fail-closed so no diagnostic label is silently dropped"
        ),
    }
}

/// Parses one attribute into a label when it is a recognized
/// `proof_note`/`custom_err` attribute. Returns `Ok(None)` for every other
/// attribute (they are NOT this module's concern). A recognized attribute
/// with a malformed argument (anything but a single string literal) is a
/// fail-closed error — silently dropping the label would lose diagnostic
/// metadata the user asked for.
pub fn proof_note_label_from_attribute(
    attr: &syn::Attribute,
) -> TrustVcResult<Option<ProofNoteLabel>> {
    let Some(is_custom_err) = proof_note_path_kind(attr.path()) else {
        return Ok(None);
    };
    let name = if is_custom_err {
        "custom_err"
    } else {
        "proof_note"
    };
    let syn::Meta::List(meta_list) = &attr.meta else {
        return Err(malformed_label_error(name));
    };
    let lit: syn::LitStr =
        syn::parse2(meta_list.tokens.clone()).map_err(|_| malformed_label_error(name))?;
    Ok(Some(ProofNoteLabel {
        text: lit.value(),
        is_custom_err,
    }))
}

/// Collects labels from an attribute list (e.g. statement-level attrs on an
/// `assert!`/`assume!` macro statement). Non-proof-note attributes are
/// ignored — they are never pooled and never rejected here.
pub fn proof_note_labels_from_attrs(
    attrs: &[syn::Attribute],
) -> TrustVcResult<Vec<ProofNoteLabel>> {
    let mut labels = Vec::new();
    for attr in attrs {
        if let Some(label) = proof_note_label_from_attribute(attr)? {
            labels.push(label);
        }
    }
    Ok(labels)
}

/// Mutable access to the attribute list of the expression variants a LEADING
/// attribute can land on. `#[attr] a <= b` parses with the attribute on the
/// leftmost LEAF (`a`), `#[attr] (a <= b)` on the `Paren` — so collection
/// recurses down the leading-position spine only (see
/// [`take_leading_proof_note_labels`]).
fn expr_attrs_mut(expr: &mut Expr) -> Option<&mut Vec<syn::Attribute>> {
    match expr {
        Expr::Binary(e) => Some(&mut e.attrs),
        Expr::Paren(e) => Some(&mut e.attrs),
        Expr::Group(e) => Some(&mut e.attrs),
        Expr::Unary(e) => Some(&mut e.attrs),
        Expr::Lit(e) => Some(&mut e.attrs),
        Expr::Path(e) => Some(&mut e.attrs),
        Expr::Call(e) => Some(&mut e.attrs),
        Expr::MethodCall(e) => Some(&mut e.attrs),
        Expr::Cast(e) => Some(&mut e.attrs),
        Expr::Reference(e) => Some(&mut e.attrs),
        Expr::Index(e) => Some(&mut e.attrs),
        Expr::Field(e) => Some(&mut e.attrs),
        Expr::Macro(e) => Some(&mut e.attrs),
        _ => None,
    }
}

fn take_labels_from_attr_vec(
    attrs: &mut Vec<syn::Attribute>,
    labels: &mut Vec<ProofNoteLabel>,
) -> TrustVcResult<()> {
    let mut error = None;
    attrs.retain(|attr| match proof_note_label_from_attribute(attr) {
        Ok(Some(label)) => {
            labels.push(label);
            false
        }
        Ok(None) => true,
        Err(err) => {
            if error.is_none() {
                error = Some(err);
            }
            true
        }
    });
    match error {
        Some(err) => Err(err),
        None => Ok(()),
    }
}

/// Collects AND STRIPS proof-note labels from the leading-attribute positions
/// of an expression: the node's own attrs, then recursively the
/// leading-position child (a `Binary`'s LEFT operand, a
/// `Paren`/`Group`/`Unary`/`Cast`/`Reference` inner expression). Stripping
/// matters: the condition string rendered from the expression must not carry
/// attribute tokens into the string-based lowering paths.
///
/// A proof-note attribute in a NON-leading position (e.g. on the right
/// operand) is deliberately left in place: it renders into the condition
/// string and fails closed downstream rather than being silently dropped.
pub fn take_leading_proof_note_labels(expr: &mut Expr) -> TrustVcResult<Vec<ProofNoteLabel>> {
    let mut labels = Vec::new();
    let mut cursor: &mut Expr = expr;
    loop {
        if let Some(attrs) = expr_attrs_mut(cursor) {
            take_labels_from_attr_vec(attrs, &mut labels)?;
        }
        cursor = match cursor {
            Expr::Binary(e) => &mut e.left,
            Expr::Paren(e) => &mut e.expr,
            Expr::Group(e) => &mut e.expr,
            Expr::Unary(e) => &mut e.expr,
            Expr::Cast(e) => &mut e.expr,
            Expr::Reference(e) => &mut e.expr,
            _ => break,
        };
    }
    Ok(labels)
}

/// Splits LEADING inner attributes `#![…]` off a contract-clause token stream
/// (`#[trust_vc::requires(#![verifier::proof_note("…")] x == y)]`), returning
/// the recognized proof-note labels and the remaining tokens.
///
/// Mirrors upstream `builtin_macros/src/syntax.rs:3710-3724`, which
/// normalizes clause inner attrs onto the clause expression. Purely additive:
/// this token shape previously ALWAYS failed the clause `Expr` parse
/// ("expected square brackets" — fail-closed), so no legal program changes
/// meaning. A leading inner attribute that is NOT a recognized proof-note
/// attribute is put back verbatim (the clause parse then fails closed exactly
/// as before).
pub fn peel_leading_inner_proof_note_attrs(
    tokens: TokenStream,
) -> TrustVcResult<(Vec<ProofNoteLabel>, TokenStream)> {
    let trees: Vec<TokenTree> = tokens.into_iter().collect();
    let mut labels = Vec::new();
    let mut index = 0;
    while index + 2 < trees.len() {
        let (TokenTree::Punct(pound), TokenTree::Punct(bang), TokenTree::Group(group)) =
            (&trees[index], &trees[index + 1], &trees[index + 2])
        else {
            break;
        };
        if pound.as_char() != '#'
            || bang.as_char() != '!'
            || group.delimiter() != Delimiter::Bracket
        {
            break;
        }
        let Ok(meta) = syn::parse2::<syn::Meta>(group.stream()) else {
            break;
        };
        let Some(is_custom_err) = proof_note_path_kind(meta.path()) else {
            break;
        };
        let syn::Meta::List(meta_list) = &meta else {
            return Err(malformed_label_error(if is_custom_err {
                "custom_err"
            } else {
                "proof_note"
            }));
        };
        let lit: syn::LitStr = syn::parse2(meta_list.tokens.clone()).map_err(|_| {
            malformed_label_error(if is_custom_err {
                "custom_err"
            } else {
                "proof_note"
            })
        })?;
        labels.push(ProofNoteLabel {
            text: lit.value(),
            is_custom_err,
        });
        index += 3;
    }
    let rest: TokenStream = trees.into_iter().skip(index).collect();
    Ok((labels, rest))
}

/// Enforces the upstream at-most-one rule over a pooled label set
/// (`proof_note` and `custom_err` POOL TOGETHER — upstream parses both into
/// `Attr::ProofNote`, so two `custom_err`s yield the same message). Fires at
/// extraction (translation) time, before any solving, exactly as upstream.
pub fn at_most_one_proof_note(
    mut labels: Vec<ProofNoteLabel>,
) -> TrustVcResult<Option<ProofNoteLabel>> {
    if labels.len() > 1 {
        return Err(TrustVcError::Encoding {
            context: "extract proof_note attributes",
            detail: AT_MOST_ONE_PROOF_NOTE.to_string(),
        });
    }
    Ok(labels.pop())
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::quote;

    #[test]
    fn recognizes_verifier_and_trust_vc_spellings_only() {
        let attr: syn::Attribute = syn::parse_quote!(#[verifier::proof_note("x")]);
        assert!(proof_note_label_from_attribute(&attr).unwrap().is_some());
        let attr: syn::Attribute = syn::parse_quote!(#[trust_vc::custom_err("x")]);
        let label = proof_note_label_from_attribute(&attr).unwrap().unwrap();
        assert!(label.is_custom_err);
        // Bare and otherwise-qualified spellings are NOT recognized.
        let attr: syn::Attribute = syn::parse_quote!(#[proof_note("x")]);
        assert!(proof_note_label_from_attribute(&attr).unwrap().is_none());
        let attr: syn::Attribute = syn::parse_quote!(#[other::proof_note("x")]);
        assert!(proof_note_label_from_attribute(&attr).unwrap().is_none());
    }

    #[test]
    fn malformed_argument_fails_closed() {
        let attr: syn::Attribute = syn::parse_quote!(#[verifier::proof_note(42)]);
        assert!(proof_note_label_from_attribute(&attr).is_err());
        let attr: syn::Attribute = syn::parse_quote!(#[verifier::proof_note]);
        assert!(proof_note_label_from_attribute(&attr).is_err());
    }

    #[test]
    fn takes_leading_labels_from_binary_left_leaf_and_paren() {
        // `#[attr] 1 > 2` parses with the attr on the LEFT LITERAL.
        let mut expr: Expr = syn::parse_str("#[verifier::proof_note(\"a\")] 1 > 2").unwrap();
        let labels = take_leading_proof_note_labels(&mut expr).unwrap();
        assert_eq!(labels.len(), 1);
        assert_eq!(labels[0].text, "a");
        assert!(!quote!(#expr).to_string().contains("proof_note"));

        let mut expr: Expr = syn::parse_str("#[verifier::custom_err(\"b\")] (1 > 2)").unwrap();
        let labels = take_leading_proof_note_labels(&mut expr).unwrap();
        assert_eq!(labels.len(), 1);
        assert!(labels[0].is_custom_err);
    }

    #[test]
    fn peels_leading_inner_attrs_and_pools() {
        let tokens = quote! { #![verifier::proof_note("Property 732")] x == y };
        let (labels, rest) = peel_leading_inner_proof_note_attrs(tokens).unwrap();
        assert_eq!(labels.len(), 1);
        assert_eq!(labels[0].text, "Property 732");
        assert_eq!(rest.to_string(), quote! { x == y }.to_string());

        let tokens = quote! {
            #![verifier::proof_note("a")]
            #![verifier::custom_err("b")]
            x == y
        };
        let (labels, _) = peel_leading_inner_proof_note_attrs(tokens).unwrap();
        assert_eq!(labels.len(), 2);
        assert!(at_most_one_proof_note(labels).is_err());
    }

    #[test]
    fn unrecognized_inner_attr_is_left_for_the_fail_closed_parse() {
        let tokens = quote! { #![some::other("x")] x == y };
        let (labels, rest) = peel_leading_inner_proof_note_attrs(tokens).unwrap();
        assert!(labels.is_empty());
        assert!(rest.to_string().contains("other"));
    }
}
