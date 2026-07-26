//! Source-level desugaring of the `matches!(EXPR, PAT [if GUARD])` macro into an
//! equivalent `match` expression.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `matches!(x, PAT)` is exactly `match x { PAT => true, _ => false }` (with an
//! optional `if GUARD` on the pattern arm) — a std macro the extractor otherwise
//! reports as an unsupported macro and fail-closes. Rewriting it to the `match`
//! the encoder already lowers soundly makes it usable in every position:
//! `requires`/`ensures` predicates, `assert!` bodies, and exec code.
//!
//! SOUNDNESS: the rewrite is the macro's exact definitional expansion, so it is
//! behavior-preserving — it can only turn a previously-fail-closed function into
//! a soundly verified or refuted one, never a false verify. syn AST visitors do
//! not descend into macro/attribute token streams, so `matches!` inside an
//! `assert!` body or a contract attribute is handled by re-parsing those streams.

use quote::{quote, ToTokens};
use syn::parse::{Parse, ParseStream};
use syn::visit_mut::VisitMut;
use syn::{Attribute, Expr, Meta, Pat, Stmt};

/// The parsed arguments of `matches!(SCRUTINEE, PAT [if GUARD])`.
struct MatchesInput {
    scrutinee: Expr,
    pat: Pat,
    guard: Option<Expr>,
}
impl Parse for MatchesInput {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        // `Expr` parsing stops at the top-level comma separating scrutinee/pattern.
        let scrutinee: Expr = input.parse()?;
        input.parse::<syn::Token![,]>()?;
        let pat = Pat::parse_multi_with_leading_vert(input)?;
        let guard = if input.peek(syn::Token![if]) {
            input.parse::<syn::Token![if]>()?;
            Some(input.parse()?)
        } else {
            None
        };
        // A trailing comma is permitted by the real macro.
        let _ = input.parse::<Option<syn::Token![,]>>();
        Ok(Self {
            scrutinee,
            pat,
            guard,
        })
    }
}

/// Build `match SCRUTINEE { PAT [if GUARD] => true, _ => false }`.
fn build_match(args: MatchesInput) -> Expr {
    let MatchesInput {
        scrutinee,
        pat,
        guard,
    } = args;
    match guard {
        Some(g) => syn::parse_quote!(match #scrutinee { #pat if #g => true, _ => false }),
        None => syn::parse_quote!(match #scrutinee { #pat => true, _ => false }),
    }
}

/// True iff `mac` is the std `matches!` macro.
fn is_matches_macro(mac: &syn::Macro) -> bool {
    mac.path
        .segments
        .last()
        .is_some_and(|seg| seg.ident == "matches")
        && mac.path.segments.len() == 1
}

struct MatchesRewriter {
    rewrote: bool,
}
impl MatchesRewriter {
    /// Rewrite `matches!` inside a token stream that parses as an `Expr` (an
    /// `assert!` body or a contract-attribute predicate), returning the new
    /// tokens iff a rewrite fired.
    fn rewrite_tokens(
        &self,
        tokens: &proc_macro2::TokenStream,
    ) -> Option<proc_macro2::TokenStream> {
        let mut expr: Expr = syn::parse2(tokens.clone()).ok()?;
        let mut inner = MatchesRewriter { rewrote: false };
        inner.visit_expr_mut(&mut expr);
        inner.rewrote.then(|| quote!(#expr))
    }
}
impl VisitMut for MatchesRewriter {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        syn::visit_mut::visit_expr_mut(self, expr);
        let Expr::Macro(expr_macro) = expr else {
            return;
        };
        if is_matches_macro(&expr_macro.mac) {
            if let Ok(args) = expr_macro.mac.parse_body::<MatchesInput>() {
                *expr = build_match(args);
                self.rewrote = true;
            }
            return;
        }
        // A non-`matches!` macro may still HOLD a `matches!` in its token stream
        // (e.g. `trust_vc::assert!(matches!(x, P))`).
        if let Some(new_tokens) = self.rewrite_tokens(&expr_macro.mac.tokens) {
            expr_macro.mac.tokens = new_tokens;
            self.rewrote = true;
        }
    }

    fn visit_stmt_mut(&mut self, stmt: &mut Stmt) {
        syn::visit_mut::visit_stmt_mut(self, stmt);
        if let Stmt::Macro(stmt_macro) = stmt {
            if !is_matches_macro(&stmt_macro.mac) {
                if let Some(new_tokens) = self.rewrite_tokens(&stmt_macro.mac.tokens) {
                    stmt_macro.mac.tokens = new_tokens;
                    self.rewrote = true;
                }
            }
        }
    }
}

/// Rewrite `matches!` in a function's contract attributes (each carries its
/// predicate as an opaque `Meta::List` token stream).
fn rewrite_contract_attrs(rewriter: &MatchesRewriter, attrs: &mut [Attribute]) -> bool {
    let mut changed = false;
    for attr in attrs.iter_mut() {
        let Meta::List(meta_list) = &mut attr.meta else {
            continue;
        };
        let is_contract = meta_list.path.segments.last().is_some_and(|seg| {
            matches!(
                seg.ident.to_string().as_str(),
                "requires" | "ensures" | "recommends" | "invariant" | "decreases"
            )
        });
        if !is_contract {
            continue;
        }
        if let Some(new_tokens) = rewriter.rewrite_tokens(&meta_list.tokens) {
            meta_list.tokens = new_tokens;
            changed = true;
        }
    }
    changed
}

/// Rewrite every `matches!(..)` in `func` (body, `assert!` bodies, and contract
/// attributes) into its `match` expansion. Returns `Some(rewritten)` iff any
/// `matches!` was rewritten.
pub(crate) fn desugar_matches_macro(func: &syn::ItemFn) -> Option<syn::ItemFn> {
    // Cheap pre-check.
    if !func.block.to_token_stream().to_string().contains("matches")
        && !func
            .attrs
            .iter()
            .any(|a| a.to_token_stream().to_string().contains("matches"))
    {
        return None;
    }
    let mut rewritten = func.clone();
    let mut rewriter = MatchesRewriter { rewrote: false };
    rewriter.visit_item_fn_mut(&mut rewritten);
    let body_changed = rewriter.rewrote;
    let attr_rewriter = MatchesRewriter { rewrote: false };
    let attrs_changed = rewrite_contract_attrs(&attr_rewriter, &mut rewritten.attrs);
    (body_changed || attrs_changed).then_some(rewritten)
}
