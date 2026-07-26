// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Parser for the `assert_forall_by!` macro.
//!
//! Supported source surface:
//! `assert_forall_by!(|x: T, y: U| body, { proof_block })`.
//! `assert!(forall |x: T, y: U| body by { proof_block })`.
//! Future source normalizers may also pass `assert forall ... by { ... }`
//! token streams directly to this parser.

use std::collections::HashSet;

use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::Parser;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::{Block, Expr, ExprClosure, Pat, Token, Type};

mod kw {
    syn::custom_keyword!(assert);
    syn::custom_keyword!(forall);
    syn::custom_keyword!(by);
}

/// One typed variable bound by `assert_forall_by!`.
#[derive(Clone)]
#[must_use]
pub struct AssertForallByBoundVar {
    pub name: String,
    pub ty: Type,
}

/// Parsed `assert_forall_by!(|x: T| body, { proof })` input.
#[derive(Clone)]
#[must_use]
pub struct AssertForallByParsed {
    pub closure: ExprClosure,
    pub proof_block: Block,
    pub bound_vars: Vec<AssertForallByBoundVar>,
    pub trigger_patterns: Vec<Vec<Expr>>,
    /// The ANTECEDENT of the Verus `implies` KEYWORD form
    /// (`assert forall|x| A implies B by { .. }`), if that surface was used.
    ///
    /// Verus keeps `A` in `AssertBy { require, .. }` and `B` in `ensure`, and
    /// the by-block gets to ASSUME `A` (`vir/src/sst_to_air.rs` emits the
    /// require as an assumption of the forall's proof block). The `==>` surface
    /// (`A ==> B`) instead lands wholly in `ensure` with `require == true`, so
    /// its by-block assumes NOTHING — which is exactly what Verus's
    /// "using ==> in `assert forall` does not currently assume the antecedent in
    /// the body" warning is about (`vir/src/well_formed.rs`). The two surfaces
    /// prove the SAME goal, `forall x. A ==> B`; they differ only in what the
    /// by-block may assume, and in whether the warning fires.
    ///
    /// `None` for the `==>` surface and for a plain (non-implication) body.
    pub require: Option<Expr>,
}

struct RawAssertForallByInput {
    closure: ExprClosure,
    proof_block: Block,
    leading_trigger_patterns: Vec<Vec<Expr>>,
    require: Option<Expr>,
}

impl Parse for RawAssertForallByInput {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        if input.peek(kw::assert) || input.peek(kw::forall) {
            return parse_verus_assert_forall_by(input);
        }

        // Take the whole remaining stream and split it at the TOKEN level rather
        // than letting `syn` parse the closure directly. The condition may use
        // Verus boolean connectives (`==>`, `<==`, `<==>`) and chained
        // comparisons, none of which `syn` can parse — they have to be lowered
        // to marker macros by `parse_expr_tokens_with_chains` FIRST. Parsing an
        // `ExprClosure` up front would reject `|x: int| 0 <= x ==> 1 <= f1(x)`
        // with "comparison operators cannot be chained" before the lowering ever
        // ran (upstream assert_forall_by.rs `test_forallstmt2`).
        let rest = input.parse::<TokenStream>()?;
        parse_closure_form_assert_forall_by(rest)
    }
}

/// Parses the `|x: T| condition, { proof_block }` surface at the token level.
///
/// The proof block is the segment after the LAST top-level comma (a Rust
/// expression has no top-level comma of its own, and binder-list commas sit
/// before the closing `|`), so that split is unambiguous. Everything before it
/// is `| binders | condition`, and the condition is lowered through
/// [`crate::chained_comparisons::parse_expr_tokens_with_chains`] so Verus
/// connectives survive.
fn parse_closure_form_assert_forall_by(tokens: TokenStream) -> syn::Result<RawAssertForallByInput> {
    let mut trees: Vec<proc_macro2::TokenTree> = tokens.into_iter().collect();

    // An optional trailing comma is part of the macro surface, not a separator.
    if matches!(trees.last(), Some(token) if is_punct(token, ',')) {
        trees.pop();
    }

    let Some(comma_idx) = trees.iter().rposition(|token| is_punct(token, ',')) else {
        return Err(syn::Error::new(
            proc_macro2::Span::call_site(),
            "assert_forall_by! expects exactly `|x: T| condition, { proof_block }`",
        ));
    };

    // Parse the tail as a `Block` so a non-block proof argument keeps syn's own
    // "expected curly braces" diagnostic.
    let proof_tokens: TokenStream = trees[comma_idx + 1..].iter().cloned().collect();
    let proof_block = syn::parse2::<Block>(proof_tokens)?;

    let head = &trees[..comma_idx];

    // `| binders | condition` — locate the binder-list pipes. If the head is not
    // closure-shaped, defer to syn for the native diagnostic.
    let head_tokens: TokenStream = head.iter().cloned().collect();
    if !matches!(head.first(), Some(token) if is_punct(token, '|')) {
        let closure = syn::parse2::<ExprClosure>(head_tokens)?;
        return Ok(RawAssertForallByInput {
            closure,
            proof_block,
            leading_trigger_patterns: Vec::new(),
            require: None,
        });
    }
    let Some(close_pipe) = head
        .iter()
        .enumerate()
        .skip(1)
        .find(|(_, token)| is_punct(token, '|'))
        .map(|(idx, _)| idx)
    else {
        return Err(syn::Error::new(
            proc_macro2::Span::call_site(),
            "assert_forall_by! expects exactly `|x: T| condition, { proof_block }`",
        ));
    };

    let condition_tokens: TokenStream = head[close_pipe + 1..].iter().cloned().collect();
    let (leading_trigger_patterns, condition_tokens) =
        strip_leading_inner_trigger_attrs(condition_tokens)?;
    let (condition, require) = parse_condition_with_optional_implies(condition_tokens)?;

    let mut closure_tokens: TokenStream = head[..=close_pipe].iter().cloned().collect();
    closure_tokens.extend(quote!(#condition));
    let closure = syn::parse2::<ExprClosure>(closure_tokens)?;

    Ok(RawAssertForallByInput {
        closure,
        proof_block,
        leading_trigger_patterns,
        require,
    })
}

/// Lowers an `assert forall` condition, honouring the Verus `implies` KEYWORD.
///
/// Returns `(goal, require)` where `goal` is always the full implication
/// `A ==> B` (rendered through the `__trust_vc_implies!` marker, exactly as the
/// `==>` surface lowers) and `require` is `Some(A)` only for the `implies`
/// keyword — the surface whose by-block may assume the antecedent.
fn parse_condition_with_optional_implies(
    condition_tokens: TokenStream,
) -> syn::Result<(Expr, Option<Expr>)> {
    let Some((antecedent_tokens, consequent_tokens)) =
        split_at_top_level_implies_keyword(condition_tokens.clone())?
    else {
        let condition =
            crate::chained_comparisons::parse_expr_tokens_with_chains(condition_tokens)?;
        return Ok((condition, None));
    };
    let antecedent = crate::chained_comparisons::parse_expr_tokens_with_chains(antecedent_tokens)?;
    let consequent = crate::chained_comparisons::parse_expr_tokens_with_chains(consequent_tokens)?;
    let marker = syn::Ident::new(
        crate::chained_comparisons::IMPLIES_MARKER_MACRO,
        proc_macro2::Span::call_site(),
    );
    let goal = syn::parse2::<Expr>(quote!(#marker!(#antecedent, #consequent)))?;
    Ok((goal, Some(antecedent)))
}

/// Splits `A implies B` at the TOP-LEVEL `implies` keyword.
///
/// `implies` is Verus's lowest-precedence infix connective, so a top-level
/// occurrence (i.e. one not nested inside a delimiter group) splits the whole
/// condition. Returns `None` when the condition contains no top-level `implies`.
/// A leading/trailing `implies` (missing operand) fails closed.
fn split_at_top_level_implies_keyword(
    tokens: TokenStream,
) -> syn::Result<Option<(TokenStream, TokenStream)>> {
    let trees: Vec<proc_macro2::TokenTree> = tokens.into_iter().collect();
    let positions: Vec<usize> = trees
        .iter()
        .enumerate()
        .filter(|(_, token)| {
            matches!(token, proc_macro2::TokenTree::Ident(ident) if ident == "implies")
        })
        .map(|(index, _)| index)
        .collect();
    let Some(&split) = positions.first() else {
        return Ok(None);
    };
    if positions.len() > 1 {
        return Err(syn::Error::new(
            proc_macro2::Span::call_site(),
            "assert forall supports at most one top-level `implies`",
        ));
    }
    let Some(antecedent) = trees.get(..split).filter(|head| !head.is_empty()) else {
        return Err(syn::Error::new(
            proc_macro2::Span::call_site(),
            "assert forall `implies` requires an antecedent",
        ));
    };
    let Some(consequent) = trees.get(split + 1..).filter(|tail| !tail.is_empty()) else {
        return Err(syn::Error::new(
            proc_macro2::Span::call_site(),
            "assert forall `implies` requires a consequent",
        ));
    };
    Ok(Some((
        antecedent.iter().cloned().collect(),
        consequent.iter().cloned().collect(),
    )))
}

fn parse_verus_assert_forall_by(input: ParseStream<'_>) -> syn::Result<RawAssertForallByInput> {
    if input.peek(kw::assert) {
        input.parse::<kw::assert>()?;
    }
    input.parse::<kw::forall>()?;

    let mut closure_tokens = TokenStream::new();
    let first_pipe = input.parse::<Token![|]>()?;
    closure_tokens.extend(quote!(#first_pipe));

    while !input.peek(Token![|]) {
        if input.is_empty() {
            return Err(input.error("assert forall requires `|x: T| condition by { proof_block }`"));
        }
        let token = input.parse::<proc_macro2::TokenTree>()?;
        closure_tokens.extend(std::iter::once(token));
    }

    let second_pipe = input.parse::<Token![|]>()?;
    closure_tokens.extend(quote!(#second_pipe));

    let condition_tokens = parse_condition_tokens_until_by(input)?;
    let (leading_trigger_patterns, condition_tokens) =
        strip_leading_inner_trigger_attrs(condition_tokens)?;
    // Lower Verus connectives (`==>`, `<==`, `<==>`, and the `implies` KEYWORD)
    // and chained comparisons before `syn` sees the condition — `syn` cannot
    // parse any of them. Upstream assert_forall_by.rs `test_forallstmt2` (the
    // `implies` keyword) / `test_forallstmt_implies` (`==>`).
    let (condition, require) = parse_condition_with_optional_implies(condition_tokens)?;
    input.parse::<kw::by>()?;
    let proof_block = input.parse::<Block>()?;
    if input.peek(Token![;]) {
        input.parse::<Token![;]>()?;
    }
    if !input.is_empty() {
        return Err(input
            .error("assert forall expects exactly `forall |x: T| condition by { proof_block }`"));
    }

    closure_tokens.extend(quote!(#condition));
    let closure = syn::parse2::<ExprClosure>(closure_tokens)?;
    Ok(RawAssertForallByInput {
        closure,
        proof_block,
        leading_trigger_patterns,
        require,
    })
}

fn parse_condition_tokens_until_by(input: ParseStream<'_>) -> syn::Result<TokenStream> {
    let mut condition_tokens = TokenStream::new();
    while !next_is_by_clause(input) {
        if input.is_empty() {
            return Err(input.error("assert forall requires `|x: T| condition by { proof_block }`"));
        }
        let token = input.parse::<proc_macro2::TokenTree>()?;
        condition_tokens.extend(std::iter::once(token));
    }
    Ok(condition_tokens)
}

fn next_is_by_clause(input: ParseStream<'_>) -> bool {
    if !input.peek(kw::by) {
        return false;
    }
    let fork = input.fork();
    fork.parse::<kw::by>().is_ok() && fork.parse::<Block>().is_ok()
}

fn strip_leading_inner_trigger_attrs(
    tokens: TokenStream,
) -> syn::Result<(Vec<Vec<Expr>>, TokenStream)> {
    let mut trigger_patterns = Vec::new();
    let mut iter = tokens.into_iter().peekable();

    loop {
        let Some(first) = iter.peek() else {
            return Ok((trigger_patterns, TokenStream::new()));
        };
        if !is_punct(first, '#') {
            break;
        }

        let mut probe = iter.clone();
        let hash = probe.next();
        let bang = probe.next();
        let group = probe.next();
        let is_inner_attr = matches!(hash.as_ref(), Some(token) if is_punct(token, '#'))
            && matches!(bang.as_ref(), Some(token) if is_punct(token, '!'))
            && matches!(group.as_ref(), Some(proc_macro2::TokenTree::Group(group))
                if group.delimiter() == proc_macro2::Delimiter::Bracket);
        if !is_inner_attr {
            break;
        }

        iter.next();
        iter.next();
        let Some(proc_macro2::TokenTree::Group(group)) = iter.next() else {
            unreachable!("inner attribute shape checked above");
        };
        trigger_patterns.push(parse_inner_trigger_attr(group)?);
    }

    Ok((trigger_patterns, iter.collect()))
}

fn parse_inner_trigger_attr(group: proc_macro2::Group) -> syn::Result<Vec<Expr>> {
    let mut tokens = group.stream().into_iter();
    let Some(proc_macro2::TokenTree::Ident(name)) = tokens.next() else {
        return Err(syn::Error::new(
            group.span(),
            "expected trigger attribute in assert forall",
        ));
    };
    if name != "trigger" {
        return Err(syn::Error::new(
            name.span(),
            "expected trigger attribute in assert forall",
        ));
    }

    let pattern_tokens: TokenStream = tokens.collect();
    if pattern_tokens.is_empty() {
        return Err(syn::Error::new(
            group.span(),
            "trigger attribute requires at least one pattern expression",
        ));
    }

    let parser = Punctuated::<Expr, Token![,]>::parse_terminated;
    let patterns = parser.parse2(pattern_tokens)?;
    if patterns.is_empty() {
        return Err(syn::Error::new(
            group.span(),
            "trigger attribute requires at least one pattern expression",
        ));
    }
    Ok(patterns.into_iter().collect())
}

fn is_punct(token: &proc_macro2::TokenTree, ch: char) -> bool {
    matches!(token, proc_macro2::TokenTree::Punct(punct) if punct.as_char() == ch)
}

/// Parses `assert_forall_by!(|x: T| body, { proof })` and
/// `forall |x: T| body by { proof }`.
pub fn parse_assert_forall_by(tokens: TokenStream) -> syn::Result<AssertForallByParsed> {
    let raw = syn::parse2::<RawAssertForallByInput>(tokens)?;
    let mut seen = HashSet::new();
    let mut bound_vars = Vec::new();

    for input in &raw.closure.inputs {
        let Pat::Type(pat_type) = input else {
            return Err(syn::Error::new_spanned(
                input,
                "assert_forall_by! binders must be typed, e.g. `|x: u32| ...`",
            ));
        };
        let Pat::Ident(ident) = pat_type.pat.as_ref() else {
            return Err(syn::Error::new_spanned(
                &pat_type.pat,
                "assert_forall_by! only supports simple identifier binders",
            ));
        };

        let name = ident.ident.to_string();
        if !seen.insert(name.clone()) {
            return Err(syn::Error::new_spanned(
                &ident.ident,
                "duplicate assert_forall_by! binder",
            ));
        }

        bound_vars.push(AssertForallByBoundVar {
            name,
            ty: (*pat_type.ty).clone(),
        });
    }

    if bound_vars.is_empty() {
        return Err(syn::Error::new_spanned(
            &raw.closure,
            "assert_forall_by! requires at least one typed binder",
        ));
    }

    let mut trigger_patterns = raw.leading_trigger_patterns;
    trigger_patterns.extend(collect_trigger_patterns(&raw.closure.body));

    Ok(AssertForallByParsed {
        trigger_patterns,
        closure: raw.closure,
        proof_block: raw.proof_block,
        bound_vars,
        require: raw.require,
    })
}

fn collect_trigger_patterns(body: &Expr) -> Vec<Vec<Expr>> {
    let mut trigger_exprs = Vec::new();
    collect_trigger_exprs(body, &mut trigger_exprs);
    trigger_exprs
        .into_iter()
        .map(|expr| vec![strip_trigger_attr(expr.clone())])
        .collect()
}

fn collect_trigger_exprs<'a>(expr: &'a Expr, out: &mut Vec<&'a Expr>) {
    struct TriggerCollector<'a, 'out> {
        out: &'out mut Vec<&'a Expr>,
    }

    impl<'ast> syn::visit::Visit<'ast> for TriggerCollector<'ast, '_> {
        fn visit_expr(&mut self, expr: &'ast Expr) {
            if expr_has_trigger_attr(expr) {
                self.out.push(expr);
                return;
            }
            syn::visit::visit_expr(self, expr);
        }
    }

    syn::visit::Visit::visit_expr(&mut TriggerCollector { out }, expr);
}

fn strip_trigger_attr(mut expr: Expr) -> Expr {
    if let Some(attrs) = expr_attrs_mut(&mut expr) {
        attrs.retain(|attr| !attr_path_ends_with(attr, "trigger"));
    }
    expr
}

fn expr_has_trigger_attr(expr: &Expr) -> bool {
    expr_attrs(expr)
        .map(|attrs| {
            attrs
                .iter()
                .any(|attr| attr_path_ends_with(attr, "trigger"))
        })
        .unwrap_or(false)
}

fn expr_attrs(expr: &Expr) -> Option<&[syn::Attribute]> {
    match expr {
        Expr::Array(expr) => Some(&expr.attrs),
        Expr::Assign(expr) => Some(&expr.attrs),
        Expr::Async(expr) => Some(&expr.attrs),
        Expr::Await(expr) => Some(&expr.attrs),
        Expr::Binary(expr) => Some(&expr.attrs),
        Expr::Block(expr) => Some(&expr.attrs),
        Expr::Break(expr) => Some(&expr.attrs),
        Expr::Call(expr) => Some(&expr.attrs),
        Expr::Cast(expr) => Some(&expr.attrs),
        Expr::Closure(expr) => Some(&expr.attrs),
        Expr::Const(expr) => Some(&expr.attrs),
        Expr::Continue(expr) => Some(&expr.attrs),
        Expr::Field(expr) => Some(&expr.attrs),
        Expr::ForLoop(expr) => Some(&expr.attrs),
        Expr::Group(expr) => Some(&expr.attrs),
        Expr::If(expr) => Some(&expr.attrs),
        Expr::Index(expr) => Some(&expr.attrs),
        Expr::Infer(expr) => Some(&expr.attrs),
        Expr::Let(expr) => Some(&expr.attrs),
        Expr::Lit(expr) => Some(&expr.attrs),
        Expr::Loop(expr) => Some(&expr.attrs),
        Expr::Macro(expr) => Some(&expr.attrs),
        Expr::Match(expr) => Some(&expr.attrs),
        Expr::MethodCall(expr) => Some(&expr.attrs),
        Expr::Paren(expr) => Some(&expr.attrs),
        Expr::Path(expr) => Some(&expr.attrs),
        Expr::Range(expr) => Some(&expr.attrs),
        Expr::Reference(expr) => Some(&expr.attrs),
        Expr::Repeat(expr) => Some(&expr.attrs),
        Expr::Return(expr) => Some(&expr.attrs),
        Expr::Struct(expr) => Some(&expr.attrs),
        Expr::Try(expr) => Some(&expr.attrs),
        Expr::TryBlock(expr) => Some(&expr.attrs),
        Expr::Tuple(expr) => Some(&expr.attrs),
        Expr::Unary(expr) => Some(&expr.attrs),
        Expr::Unsafe(expr) => Some(&expr.attrs),
        _ => None,
    }
}

fn expr_attrs_mut(expr: &mut Expr) -> Option<&mut Vec<syn::Attribute>> {
    match expr {
        Expr::Array(expr) => Some(&mut expr.attrs),
        Expr::Assign(expr) => Some(&mut expr.attrs),
        Expr::Async(expr) => Some(&mut expr.attrs),
        Expr::Await(expr) => Some(&mut expr.attrs),
        Expr::Binary(expr) => Some(&mut expr.attrs),
        Expr::Block(expr) => Some(&mut expr.attrs),
        Expr::Break(expr) => Some(&mut expr.attrs),
        Expr::Call(expr) => Some(&mut expr.attrs),
        Expr::Cast(expr) => Some(&mut expr.attrs),
        Expr::Closure(expr) => Some(&mut expr.attrs),
        Expr::Const(expr) => Some(&mut expr.attrs),
        Expr::Continue(expr) => Some(&mut expr.attrs),
        Expr::Field(expr) => Some(&mut expr.attrs),
        Expr::ForLoop(expr) => Some(&mut expr.attrs),
        Expr::Group(expr) => Some(&mut expr.attrs),
        Expr::If(expr) => Some(&mut expr.attrs),
        Expr::Index(expr) => Some(&mut expr.attrs),
        Expr::Infer(expr) => Some(&mut expr.attrs),
        Expr::Let(expr) => Some(&mut expr.attrs),
        Expr::Lit(expr) => Some(&mut expr.attrs),
        Expr::Loop(expr) => Some(&mut expr.attrs),
        Expr::Macro(expr) => Some(&mut expr.attrs),
        Expr::Match(expr) => Some(&mut expr.attrs),
        Expr::MethodCall(expr) => Some(&mut expr.attrs),
        Expr::Paren(expr) => Some(&mut expr.attrs),
        Expr::Path(expr) => Some(&mut expr.attrs),
        Expr::Range(expr) => Some(&mut expr.attrs),
        Expr::Reference(expr) => Some(&mut expr.attrs),
        Expr::Repeat(expr) => Some(&mut expr.attrs),
        Expr::Return(expr) => Some(&mut expr.attrs),
        Expr::Struct(expr) => Some(&mut expr.attrs),
        Expr::Try(expr) => Some(&mut expr.attrs),
        Expr::TryBlock(expr) => Some(&mut expr.attrs),
        Expr::Tuple(expr) => Some(&mut expr.attrs),
        Expr::Unary(expr) => Some(&mut expr.attrs),
        Expr::Unsafe(expr) => Some(&mut expr.attrs),
        _ => None,
    }
}

fn attr_path_ends_with(attr: &syn::Attribute, name: &str) -> bool {
    attr.path()
        .segments
        .last()
        .is_some_and(|segment| segment.ident == name)
}

#[cfg(test)]
mod tests {
    use quote::{quote, ToTokens};

    use super::*;

    #[test]
    fn parses_single_typed_binder() {
        let parsed = parse_assert_forall_by(quote! {
            |k: u32| k + 0 == k,
            { trust_vc::assume!(k + 0 == k); }
        })
        .expect("valid assert_forall_by input should parse");

        assert_eq!(parsed.bound_vars.len(), 1);
        assert_eq!(parsed.bound_vars[0].name, "k");
    }

    #[test]
    fn parses_multiple_typed_binders() {
        let parsed = parse_assert_forall_by(quote! {
            |x: i32, y: i32| x + y == y + x,
            {}
        })
        .expect("valid assert_forall_by input should parse");

        let names = parsed
            .bound_vars
            .iter()
            .map(|var| var.name.as_str())
            .collect::<Vec<_>>();
        assert_eq!(names, vec!["x", "y"]);
    }

    #[test]
    fn parses_verus_style_forall_by() {
        let parsed = parse_assert_forall_by(quote! {
            forall |k: u32| k + 0 == k by {
                trust_vc::assume!(k + 0 == k);
            }
        })
        .expect("Verus-style forall-by input should parse");

        assert_eq!(parsed.bound_vars.len(), 1);
        assert_eq!(parsed.bound_vars[0].name, "k");
        assert!(matches!(parsed.proof_block.stmts.len(), 1));
    }

    #[test]
    fn parses_verus_style_assert_forall_by_tokens() {
        let parsed = parse_assert_forall_by(quote! {
            assert forall |x: i32, y: i32| x + y == y + x by {}
        })
        .expect("Verus-style assert forall-by tokens should parse");

        let names = parsed
            .bound_vars
            .iter()
            .map(|var| var.name.as_str())
            .collect::<Vec<_>>();
        assert_eq!(names, vec!["x", "y"]);
    }

    #[test]
    fn parses_verus_style_inner_trigger_group() {
        let parsed = parse_assert_forall_by(quote! {
            assert forall |k: u32| #![trigger f(k, z)] f(k, z) && g(z, k) by {}
        })
        .expect("Verus-style inner trigger group should parse");

        assert_eq!(parsed.trigger_patterns.len(), 1);
        assert_eq!(parsed.trigger_patterns[0].len(), 1);
        let trigger = parsed.trigger_patterns[0][0].to_token_stream().to_string();
        assert_eq!(trigger, "f (k , z)");
        let body = parsed.closure.body.to_token_stream().to_string();
        assert!(
            !body.contains("# !"),
            "inner trigger attribute should not remain in closure body: {body}"
        );
    }

    #[test]
    fn parses_verus_style_multi_pattern_inner_trigger_group() {
        let parsed = parse_assert_forall_by(quote! {
            assert forall |i: u32, j: u32| #![trigger s[i], s[j]] s[i] != s[j] by {}
        })
        .expect("multi-pattern inner trigger group should parse");

        assert_eq!(parsed.trigger_patterns.len(), 1);
        let triggers = parsed.trigger_patterns[0]
            .iter()
            .map(ToTokens::to_token_stream)
            .map(|tokens| tokens.to_string())
            .collect::<Vec<_>>();
        assert_eq!(triggers, vec!["s [i]", "s [j]"]);
    }

    #[test]
    fn rejects_unsupported_inner_trigger_attribute_fail_closed() {
        let err = match parse_assert_forall_by(quote! {
            assert forall |k: u32| #![autos] f(k) by {}
        }) {
            Ok(_) => panic!("unknown inner quantifier attribute must be rejected"),
            Err(err) => err,
        };

        assert!(err.to_string().contains("expected trigger"));
    }

    #[test]
    fn parses_expression_trigger_patterns() {
        let parsed = parse_assert_forall_by(quote! {
            |k: u32| #[trigger] f(k) && k >= 0u32,
            {}
        })
        .expect("trigger-bearing assert_forall_by input should parse");

        assert_eq!(parsed.trigger_patterns.len(), 1);
        assert_eq!(parsed.trigger_patterns[0].len(), 1);
        let trigger = parsed.trigger_patterns[0][0].to_token_stream().to_string();
        assert_eq!(trigger, "f (k)");
    }

    #[test]
    fn parses_expression_trigger_patterns_inside_blocks() {
        let parsed = parse_assert_forall_by(quote! {
            |k: u32| { #[trigger] f(k) && k >= 0u32 },
            {}
        })
        .expect("block-wrapped trigger-bearing assert_forall_by input should parse");

        assert_eq!(parsed.trigger_patterns.len(), 1);
        assert_eq!(parsed.trigger_patterns[0].len(), 1);
        let trigger = parsed.trigger_patterns[0][0].to_token_stream().to_string();
        assert_eq!(trigger, "f (k)");
    }

    #[test]
    fn rejects_untyped_binder() {
        let err = match parse_assert_forall_by(quote! {
            |k| k == k,
            {}
        }) {
            Ok(_) => panic!("untyped binder must be rejected"),
            Err(err) => err,
        };

        assert!(err.to_string().contains("binders must be typed"));
    }

    #[test]
    fn rejects_non_block_proof() {
        let err = match parse_assert_forall_by(quote! {
            |k: u32| k == k,
            true
        }) {
            Ok(_) => panic!("proof argument must be a block"),
            Err(err) => err,
        };

        assert!(
            err.to_string().contains("expected curly braces"),
            "unexpected error: {err}"
        );
    }
}
