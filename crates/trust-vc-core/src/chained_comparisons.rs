//! Chained comparison normalization.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Rewrites Verus-style chained comparisons (`a <= b < c`) into pairwise
//! boolean conjunctions (`(a <= b) && (b < c)`) at the token-stream level,
//! before `syn` parsing. This is necessary because `syn` rejects chained
//! comparisons outright ("comparison operators cannot be chained").

use proc_macro2::{Delimiter, Spacing, Span, TokenStream, TokenTree};
use quote::quote;

/// Marker produced by the `==>` (and reverse `<==`) rewrite so the IR lowering
/// can rebuild a real `TrustVcExpr::Implies` node. Keeping this as a macro
/// invocation means `syn` parses the surrounding expression normally (the
/// premise/conclusion token sub-streams are left untouched and re-parsed —
/// chain-normalized — at lowering time, mirroring how the engine already
/// encodes implication).
pub(crate) const IMPLIES_MARKER_MACRO: &str = "__trust_vc_implies";

/// Marker produced by the `<==>` (logical equivalence / biconditional) rewrite.
/// Lowered to `(P ==> Q) && (Q ==> P)` — a pure boolean rewrite, so it is sound
/// without introducing any new IR node. Like the implication marker, the two
/// operand sub-streams are re-parsed (chain-normalized) at lowering time.
pub(crate) const IFF_MARKER_MACRO: &str = "__trust_vc_iff";

/// Parse a token stream, normalizing chained comparisons into conjunctions.
pub fn parse_expr_tokens_with_chains(tokens: TokenStream) -> syn::Result<syn::Expr> {
    // Lower Verus "bulleted" prefix disjunctions (`||| e1 ||| e2 …`, upstream
    // basic.rs test_big_or) into parenthesized `(e1) || (e2) || …` FIRST:
    // the bullets bind loosest of all operators (verus-syn parses each bullet
    // operand at `Precedence::Assign`, i.e. below `==>`/`<==>`), so the split
    // must happen before the quantifier and connective passes. The synthesized
    // parens groups are then recursed into by every later pass. See
    // `rewrite_verus_big_or_tokens` for the exact (leading-position-only)
    // trigger shape.
    let tokens = rewrite_verus_big_or_tokens(tokens)?;
    let tokens = rewrite_verus_quantifier_tokens(tokens)?;
    let tokens = rewrite_verus_choose_tuple_tokens(tokens)?;
    let tokens = rewrite_verus_result_variant_tokens(tokens)?;
    // Lower Verus-style boolean connectives `P <==> Q` (equivalence), `P ==> Q`
    // (implication) and `P <== Q` (reverse implication) into marker macros before
    // `syn` parsing. Runs *after* quantifier normalization so that a connective
    // inside a `forall|..|`/`exists|..|` body is already enclosed in the
    // synthesized closure group and is bound by the quantifier rather than split
    // at the outer level.
    let tokens = rewrite_verus_connectives_tokens(tokens)?;
    // Lower the Verus equality operators `a =~= b` (extensional) and `a === b`
    // (strict / spec equality) into the `ext_eq!` / `strict_eq!` call surfaces.
    // `syn` cannot parse either token sequence, so this must run before
    // `syn::parse2`. It runs *after* the connective lowering because `=~=`/`===`
    // bind tighter than `==>`/`<==>` (so the connectives split first, and this
    // pass then descends into the marker operands).
    let tokens = rewrite_verus_eq_operator_tokens(tokens)?;
    match syn::parse2(tokens.clone()) {
        Ok(expr) => Ok(expr),
        Err(err)
            if err
                .to_string()
                .contains("comparison operators cannot be chained") =>
        {
            let rewritten = rewrite_chained_tokens(tokens)?;
            syn::parse2(rewritten)
        }
        Err(err) => Err(err),
    }
}

/// Split a token stream at top-level commas (commas not nested inside any
/// delimiter group). Trailing empty segments are dropped. Used to recover the
/// two raw operand sub-streams of a connective marker macro
/// (`__trust_vc_implies!(P, Q)` / `__trust_vc_iff!(P, Q)`) wherever a
/// syntactic walker needs to see INSIDE the marker (e.g. the spec-function
/// catalog's referenced-call collector) — the operands are raw token streams,
/// not a parseable expression list, precisely because they may themselves
/// contain chains/connectives.
pub(crate) fn split_top_level_comma_operands(tokens: TokenStream) -> Vec<TokenStream> {
    let mut segments = Vec::new();
    let mut current = TokenStream::new();
    for tree in tokens {
        match &tree {
            TokenTree::Punct(punct)
                if punct.as_char() == ',' && punct.spacing() == Spacing::Alone =>
            {
                segments.push(std::mem::take(&mut current));
            }
            _ => current.extend(std::iter::once(tree)),
        }
    }
    if !current.is_empty() {
        segments.push(current);
    }
    segments
}

/// Parse a string expression, normalizing chained comparisons into conjunctions.
pub fn parse_expr_str_with_chains(src: &str) -> syn::Result<syn::Expr> {
    let tokens: TokenStream = src
        .parse()
        .map_err(|e: proc_macro2::LexError| syn::Error::new(Span::call_site(), format!("{e}")))?;
    parse_expr_tokens_with_chains(tokens)
}

fn rewrite_verus_quantifier_tokens(tokens: TokenStream) -> syn::Result<TokenStream> {
    let trees = rewrite_verus_quantifier_groups(tokens.into_iter().collect())?;
    rewrite_verus_quantifier_sequence(trees)
}

/// Rewrite Verus "bulleted" prefix disjunctions into plain disjunctions.
///
/// Upstream (verus-syn `parse_prefix_binop` + builtin_macros `syntax.rs`
/// BigOr lowering), `||| e1 ||| e2 ||| e3` is a prefix-bulleted expression
/// that lowers to the left-associated `((e1) || (e2)) || (e3)`; a bullet is
/// only legal in LEADING (statement/expression-head) position — verus-syn
/// errors with "leading ||| must be inside a block" elsewhere, and its
/// expression parser hard-stops at any non-leading `&&&`/`|||`. This pass
/// mirrors exactly that surface at the token level:
///
/// * A bullet sequence is recognized only when a token sequence (the whole
///   stream, a delimiter group's inner stream, or a `;`-separated statement
///   segment thereof) STARTS with a `|||` triple (three `|` puncts, the first
///   two `Joint` — the same textual-adjacency shape verus-syn's
///   `Token![|||]` requires). `a ||| b` in infix position is left untouched,
///   exactly like upstream (where it is a parse error) — here it keeps its
///   pre-existing plain-Rust reading.
/// * Subsequent top-level `|||` triples inside the sequence separate the
///   bullet operands. Each operand is wrapped in parentheses and the operands
///   are joined with `||`, matching the upstream lowering. Later passes
///   (quantifiers, `==>`/`<==>`, chained comparisons) recurse into the
///   synthesized groups, so bullets bind loosest — upstream precedence.
/// * A top-level `&&&` triple inside a bullet sequence is a mixing error
///   upstream (the bullet-operand parse hard-stops at `&&&` and the leftover
///   tokens fail the enclosing parse); fail closed with an explicit error.
/// * An empty bullet operand (`||| a ||| ||| b`) fails closed.
///
/// The rewrite never fires on token sequences without a LEADING `|||` triple,
/// so no previously-parsing expression changes meaning. (A leading
/// `|||`-triple sequence today parses as a zero-argument closure returning a
/// closure — never a legal spec value, and rejected by the lowering as
/// "standalone closure" — so nothing verifiable flips.)
fn rewrite_verus_big_or_tokens(tokens: TokenStream) -> syn::Result<TokenStream> {
    let trees = rewrite_verus_big_or_groups(tokens.into_iter().collect())?;
    rewrite_verus_big_or_sequence(trees)
}

fn rewrite_verus_big_or_groups(trees: Vec<TokenTree>) -> syn::Result<Vec<TokenTree>> {
    trees
        .into_iter()
        .map(|tt| match tt {
            TokenTree::Group(group) => {
                let inner = rewrite_verus_big_or_tokens(group.stream())?;
                let mut rewritten = proc_macro2::Group::new(group.delimiter(), inner);
                rewritten.set_span(group.span());
                Ok(TokenTree::Group(rewritten))
            }
            other => Ok(other),
        })
        .collect()
}

/// Whether a `|||` bullet (three `|` puncts, first two `Joint` — the textual
/// adjacency `Token![|||]` requires) starts at `index`.
fn big_or_bullet_at(trees: &[TokenTree], index: usize) -> bool {
    let joint_pipe = |offset: usize, need_joint: bool| {
        matches!(
            trees.get(index + offset),
            Some(TokenTree::Punct(p))
                if p.as_char() == '|' && (!need_joint || p.spacing() == Spacing::Joint)
        )
    };
    joint_pipe(0, true) && joint_pipe(1, true) && joint_pipe(2, false)
}

/// Whether a `&&&` bullet (three `&` puncts, first two `Joint`) starts at
/// `index`. Only used for the mixing guard inside a leading-`|||` sequence:
/// this is the exact textual shape verus-syn's `Token![&&&]` matches, and it
/// is distinct from a spaced `a && &b` (whose second `&` is `Alone`).
fn big_and_bullet_at(trees: &[TokenTree], index: usize) -> bool {
    let amp = |offset: usize, need_joint: bool| {
        matches!(
            trees.get(index + offset),
            Some(TokenTree::Punct(p))
                if p.as_char() == '&' && (!need_joint || p.spacing() == Spacing::Joint)
        )
    };
    amp(0, true) && amp(1, true) && amp(2, false)
}

fn rewrite_verus_big_or_sequence(trees: Vec<TokenTree>) -> syn::Result<TokenStream> {
    let mut rewritten = TokenStream::new();
    let mut index = 0;
    let mut segment_start = true;

    while index < trees.len() {
        if segment_start && big_or_bullet_at(&trees, index) {
            // Statement segment: the bullets extend to the next top-level `;`
            // (upstream bullets are statement/clause-leading) or to the end.
            let segment_end = trees[index..]
                .iter()
                .position(|tt| matches!(tt, TokenTree::Punct(p) if p.as_char() == ';'))
                .map(|offset| index + offset)
                .unwrap_or(trees.len());
            let lowered = lower_big_or_segment(&trees[index..segment_end])?;
            rewritten.extend(lowered);
            index = segment_end;
            segment_start = false;
            continue;
        }
        segment_start = matches!(&trees[index], TokenTree::Punct(p) if p.as_char() == ';');
        rewritten.extend(std::iter::once(trees[index].clone()));
        index += 1;
    }

    Ok(rewritten)
}

/// Lower one leading-`|||` bullet segment (`||| e1 ||| e2 …`, no top-level
/// `;`) to `(e1) || (e2) || …`, mirroring the upstream BigOr lowering.
#[allow(clippy::indexing_slicing)] // cursor movement is guarded by big_or_bullet_at
fn lower_big_or_segment(trees: &[TokenTree]) -> syn::Result<TokenStream> {
    debug_assert!(big_or_bullet_at(trees, 0));
    let bullet_span = token_span(&trees[0]);
    let mut operands: Vec<Vec<TokenTree>> = Vec::new();
    let mut current: Vec<TokenTree> = Vec::new();
    let mut index = 3; // consume the leading bullet

    while index < trees.len() {
        if big_or_bullet_at(trees, index) {
            operands.push(std::mem::take(&mut current));
            index += 3;
            continue;
        }
        if big_and_bullet_at(trees, index) {
            return Err(syn::Error::new(
                token_span(&trees[index]),
                "cannot mix `&&&` and `|||` in a bulleted expression; \
                 group the inner bullets in a block",
            ));
        }
        current.push(trees[index].clone());
        index += 1;
    }
    operands.push(current);

    if operands.iter().any(Vec::is_empty) {
        return Err(syn::Error::new(
            bullet_span,
            "`|||` requires an expression after each bullet",
        ));
    }

    let mut lowered = TokenStream::new();
    for (position, operand) in operands.into_iter().enumerate() {
        if position > 0 {
            let mut first = proc_macro2::Punct::new('|', Spacing::Joint);
            first.set_span(bullet_span);
            let mut second = proc_macro2::Punct::new('|', Spacing::Alone);
            second.set_span(bullet_span);
            lowered.extend([TokenTree::Punct(first), TokenTree::Punct(second)]);
        }
        let operand_span = operand.first().map(token_span).unwrap_or(bullet_span);
        let mut group =
            proc_macro2::Group::new(Delimiter::Parenthesis, operand.into_iter().collect());
        group.set_span(operand_span);
        lowered.extend(std::iter::once(TokenTree::Group(group)));
    }
    Ok(lowered)
}

fn rewrite_verus_choose_tuple_tokens(tokens: TokenStream) -> syn::Result<TokenStream> {
    let trees = rewrite_verus_choose_tuple_groups(tokens.into_iter().collect())?;
    Ok(rewrite_verus_choose_tuple_sequence(trees))
}

fn rewrite_verus_choose_tuple_groups(trees: Vec<TokenTree>) -> syn::Result<Vec<TokenTree>> {
    trees
        .into_iter()
        .map(|tt| match tt {
            TokenTree::Group(group) => {
                let inner = rewrite_verus_choose_tuple_tokens(group.stream())?;
                let mut rewritten = proc_macro2::Group::new(group.delimiter(), inner);
                rewritten.set_span(group.span());
                Ok(TokenTree::Group(rewritten))
            }
            other => Ok(other),
        })
        .collect()
}

#[allow(clippy::indexing_slicing)] // cursor movement is guarded by token lookups
fn rewrite_verus_choose_tuple_sequence(trees: Vec<TokenTree>) -> TokenStream {
    let mut rewritten = TokenStream::new();
    let mut index = 0;

    while index < trees.len() {
        if let Some((call_group_index, next_index)) = choose_tuple_call_at(&trees, index) {
            let TokenTree::Ident(ident) = &trees[index] else {
                unreachable!("choose_tuple_call_at only matches an ident start");
            };
            rewritten.extend(std::iter::once(TokenTree::Ident(proc_macro2::Ident::new(
                "choose",
                ident.span(),
            ))));
            rewritten.extend(std::iter::once(trees[call_group_index].clone()));
            index = next_index;
        } else {
            rewritten.extend(std::iter::once(trees[index].clone()));
            index += 1;
        }
    }

    rewritten
}

fn choose_tuple_call_at(trees: &[TokenTree], start: usize) -> Option<(usize, usize)> {
    let TokenTree::Ident(ident) = trees.get(start)? else {
        return None;
    };
    if ident != "choose_tuple" || !is_expression_boundary_before(trees, start) {
        return None;
    }

    let mut cursor = start + 1;
    if matches!(trees.get(cursor), Some(TokenTree::Punct(p)) if p.as_char() == ':')
        && matches!(trees.get(cursor + 1), Some(TokenTree::Punct(p)) if p.as_char() == ':')
        && matches!(trees.get(cursor + 2), Some(TokenTree::Punct(p)) if p.as_char() == '<')
    {
        cursor += 3;
        let mut depth = 1usize;
        while let Some(tree) = trees.get(cursor) {
            if let TokenTree::Punct(punct) = tree {
                match punct.as_char() {
                    '<' => depth += 1,
                    '>' => {
                        depth -= 1;
                        if depth == 0 {
                            cursor += 1;
                            break;
                        }
                    }
                    _ => {}
                }
            }
            cursor += 1;
        }
        if depth != 0 {
            return None;
        }
    }

    match trees.get(cursor) {
        Some(TokenTree::Group(group)) if group.delimiter() == Delimiter::Parenthesis => {
            Some((cursor, cursor + 1))
        }
        _ => None,
    }
}

fn rewrite_verus_quantifier_groups(trees: Vec<TokenTree>) -> syn::Result<Vec<TokenTree>> {
    trees
        .into_iter()
        .map(|tt| match tt {
            TokenTree::Group(group) => {
                let inner = rewrite_verus_quantifier_tokens(group.stream())?;
                let mut rewritten = proc_macro2::Group::new(group.delimiter(), inner);
                rewritten.set_span(group.span());
                Ok(TokenTree::Group(rewritten))
            }
            other => Ok(other),
        })
        .collect()
}

#[allow(clippy::indexing_slicing)] // indices are checked by parser helpers before slicing
fn rewrite_verus_quantifier_sequence(trees: Vec<TokenTree>) -> syn::Result<TokenStream> {
    let mut rewritten = TokenStream::new();
    let mut index = 0;

    while index < trees.len() {
        if is_verus_quantifier_start(&trees, index) {
            let (binder, next_index) = rewrite_verus_quantifier_at(&trees, index)?;
            rewritten.extend(binder);
            index = next_index;
        } else {
            rewritten.extend(std::iter::once(trees[index].clone()));
            index += 1;
        }
    }

    Ok(rewritten)
}

#[allow(clippy::indexing_slicing)] // callers only pass indices within trees
fn rewrite_verus_quantifier_at(
    trees: &[TokenTree],
    start: usize,
) -> syn::Result<(TokenStream, usize)> {
    let TokenTree::Ident(quantifier) = &trees[start] else {
        return Err(syn::Error::new(
            Span::call_site(),
            "internal: expected Verus-style binder identifier",
        ));
    };
    let Some(second_pipe) = find_binder_pipe(trees, start) else {
        return Err(syn::Error::new(
            quantifier.span(),
            "Verus-style binder expression requires `forall|x: T| body`, `exists|x: T| body`, or `choose|x: T| body`",
        ));
    };

    let binder_tokens: TokenStream = trees[start + 2..second_pipe].iter().cloned().collect();

    let body_start = second_pipe + 1;
    let body_end = find_verus_quantifier_body_end(trees, body_start)?;
    if body_start == body_end {
        return Err(syn::Error::new(
            quantifier.span(),
            "Verus-style binder expression requires a body",
        ));
    }

    let body_tokens: TokenStream = trees[body_start..body_end].iter().cloned().collect();
    let body_tokens = rewrite_verus_quantifier_tokens(body_tokens)?;
    // Lower `<==>`/`==>`/`<==` in the body *before* the chained-comparison pass.
    // Otherwise a body like `i >= 0 ==> f(i) >= 0` would let the chain detector
    // span the two `>=` comparisons across the raw connective tokens and corrupt
    // the rewrite.
    let body_tokens = rewrite_verus_connectives_tokens(body_tokens)?;
    // Lower `=~=`/`===` in the body before the chained pass, while the binder is
    // still detached from the body, so a body like `a[i] =~= b[i]` splits at the
    // body's own top level rather than across the synthesized closure's binder.
    let body_tokens = rewrite_verus_eq_operator_tokens(body_tokens)?;
    let body_tokens = rewrite_chained_tokens(body_tokens)?;
    Ok((
        quote! { #quantifier(| #binder_tokens | #body_tokens) },
        body_end,
    ))
}

fn is_verus_quantifier_start(trees: &[TokenTree], index: usize) -> bool {
    let Some(TokenTree::Ident(ident)) = trees.get(index) else {
        return false;
    };
    if !matches!(ident.to_string().as_str(), "forall" | "exists" | "choose") {
        return false;
    }
    if !matches!(trees.get(index + 1), Some(TokenTree::Punct(punct)) if punct.as_char() == '|') {
        return false;
    }
    is_expression_boundary_before(trees, index)
}

fn is_expression_boundary_before(trees: &[TokenTree], index: usize) -> bool {
    if index == 0 {
        return true;
    }
    match &trees[index - 1] {
        TokenTree::Punct(punct) => !matches!(punct.as_char(), '.' | ':' | '\''),
        TokenTree::Ident(_) | TokenTree::Literal(_) | TokenTree::Group(_) => false,
    }
}

fn find_binder_pipe(trees: &[TokenTree], start: usize) -> Option<usize> {
    trees
        .iter()
        .enumerate()
        .skip(start + 2)
        .find_map(|(index, tree)| {
            matches!(tree, TokenTree::Punct(punct) if punct.as_char() == '|').then_some(index)
        })
}

fn find_verus_quantifier_body_end(trees: &[TokenTree], body_start: usize) -> syn::Result<usize> {
    let mut index = body_start;
    while index < trees.len() {
        if is_verus_quantifier_start(trees, index) {
            let (_, nested_end) = rewrite_verus_quantifier_at(trees, index)?;
            index = nested_end;
            continue;
        }
        if matches!(
            &trees[index],
            TokenTree::Punct(punct) if matches!(punct.as_char(), ',' | ';')
        ) {
            return Ok(index);
        }
        index += 1;
    }
    Ok(trees.len())
}

fn rewrite_verus_result_variant_tokens(tokens: TokenStream) -> syn::Result<TokenStream> {
    let trees = rewrite_verus_result_variant_groups(tokens.into_iter().collect())?;
    rewrite_verus_result_variant_sequence(trees)
}

fn rewrite_verus_result_variant_groups(trees: Vec<TokenTree>) -> syn::Result<Vec<TokenTree>> {
    trees
        .into_iter()
        .map(|tt| match tt {
            TokenTree::Group(group) => {
                let inner = rewrite_verus_result_variant_tokens(group.stream())?;
                let mut rewritten = proc_macro2::Group::new(group.delimiter(), inner);
                rewritten.set_span(group.span());
                Ok(TokenTree::Group(rewritten))
            }
            other => Ok(other),
        })
        .collect()
}

#[allow(clippy::indexing_slicing)] // slices are guarded by token pattern checks before use
fn rewrite_verus_result_variant_sequence(trees: Vec<TokenTree>) -> syn::Result<TokenStream> {
    // `->` is a postfix trailer and may be chained or feed another variant
    // operator (`x->A_0->Some_0`, `x->A_0 is Some`).  Lower every projection
    // into an ordinary call first, left-to-right, so each replacement becomes
    // part of the next trailer's receiver.  Rewriting a projection and then
    // recursively processing only its raw suffix loses that receiver and
    // rejects every chained form.
    let trees = rewrite_verus_projection_sequence(trees)?;

    for index in 0..trees.len() {
        if let Some(variant) = verus_notis_operator_variant(&trees, index) {
            // `EXPR !is Variant` — negated variant test. Handled at the `!`
            // position so the receiver excludes the leading `!`.
            let left_start = find_verus_result_left_operand_start(&trees, index, true)?;
            if left_start == index {
                return Err(syn::Error::new(
                    token_span(&trees[index]),
                    "Verus negated variant test `!is` requires a receiver",
                ));
            }
            let prefix = rewrite_verus_result_variant_sequence(trees[..left_start].to_vec())?;
            let receiver: TokenStream = trees[left_start..index].iter().cloned().collect();
            let rest = rewrite_verus_result_variant_sequence(trees[index + 3..].to_vec())?;
            return Ok(quote! {
                #prefix (!(match (#receiver) { #variant { .. } => true, _ => false })) #rest
            });
        }

        if let Some(variant) = verus_is_operator_variant(&trees, index) {
            let left_start = find_verus_result_left_operand_start(&trees, index, true)?;
            if left_start == index {
                return Err(syn::Error::new(
                    token_span(&trees[index]),
                    "Verus variant test `is` requires a receiver before `is`",
                ));
            }
            let prefix = rewrite_verus_result_variant_sequence(trees[..left_start].to_vec())?;
            let receiver: TokenStream = trees[left_start..index].iter().cloned().collect();
            let rest = rewrite_verus_result_variant_sequence(trees[index + 2..].to_vec())?;
            // Resolve every variant test from the receiver's datatype. Spelling
            // alone is not provenance: user datatypes may also define `Ok` and
            // `Err`, so eagerly rewriting those names to Result's `is_ok()` /
            // `is_err()` rejects valid custom variants (or targets the wrong
            // semantic surface). Variant testing binds no fields, so the
            // `{ .. }` rest form works for tuple, struct, and unit variants.
            let test = quote! {
                (match (#receiver) { #variant { .. } => true, _ => false })
            };
            return Ok(quote! { #prefix #test #rest });
        }

        if verus_is_has_operator(&trees, index) {
            // `RECEIVER has ELEM` (collection membership) → `(RECEIVER).contains(ELEM)`.
            let left_start = find_verus_result_left_operand_start(&trees, index, true)?;
            if left_start == index {
                return Err(syn::Error::new(
                    token_span(&trees[index]),
                    "Verus `has` requires a receiver before `has`",
                ));
            }
            let rhs_end = find_verus_has_rhs_end(&trees, index + 1);
            if rhs_end == index + 1 {
                return Err(syn::Error::new(
                    token_span(&trees[index]),
                    "Verus `has` requires an element expression after `has`",
                ));
            }
            let prefix = rewrite_verus_result_variant_sequence(trees[..left_start].to_vec())?;
            let receiver: TokenStream = trees[left_start..index].iter().cloned().collect();
            let elem = rewrite_verus_result_variant_sequence(trees[index + 1..rhs_end].to_vec())?;
            let rest = rewrite_verus_result_variant_sequence(trees[rhs_end..].to_vec())?;
            return Ok(quote! { #prefix ((#receiver).contains(#elem)) #rest });
        }

        if let Some(pat_end) = verus_matches_pattern_span(&trees, index) {
            let left_start = find_verus_result_left_operand_start(&trees, index, true)?;
            if left_start == index {
                return Err(syn::Error::new(
                    token_span(&trees[index]),
                    "Verus `matches` requires a receiver before `matches`",
                ));
            }
            let prefix = rewrite_verus_result_variant_sequence(trees[..left_start].to_vec())?;
            let receiver: TokenStream = trees[left_start..index].iter().cloned().collect();
            let base_pattern: TokenStream = trees[index + 1..pat_end].iter().cloned().collect();
            // A group-less variant (`matches A`) would be read as a const pattern
            // and silently drop its refinement; force the constructor form with a
            // `{ .. }` rest (matches tuple/struct/unit variants), exactly as `is`.
            let pattern = if matches!(trees.get(pat_end - 1), Some(TokenTree::Group(_))) {
                base_pattern
            } else {
                quote! { #base_pattern { .. } }
            };
            if is_verus_implies_arrow_at(&trees, pat_end) {
                // `EXPR matches PAT ==> RHS`: the pattern's bindings scope into
                // the implication RHS (Verus's binding-into-implication). Desugar
                // to `match EXPR { PAT => RHS, _ => true }` (a non-matching
                // receiver makes the implication vacuously true). The RHS is the
                // remainder of the scope (`==>` binds loosest), recursively
                // rewritten; the connective pass later normalizes any `==>`
                // inside it.
                let rhs = rewrite_verus_result_variant_sequence(trees[pat_end + 3..].to_vec())?;
                return Ok(quote! {
                    #prefix (match (#receiver) { #pattern => { #rhs }, _ => true })
                });
            }
            // verus-syn checks `&&&` before `&&`: the first two ampersands of
            // a bullet are also Joint, so reversing this order would consume
            // only two and leak the third as an accidental unary borrow.
            if big_and_bullet_at(&trees, pat_end) {
                // Inside a leading `&&&` expression, verus-syn gives a
                // bullet-leading `matches` expression ownership of all
                // following bullets so its pattern bindings remain in scope:
                // `&&& e matches A(x) &&& p(x)`.  The surrounding raw bullets
                // already lower as conjunctions on the established path; only
                // the binding scope needs this explicit conditional.
                let rhs = rewrite_verus_result_variant_sequence(trees[pat_end + 3..].to_vec())?;
                return Ok(quote! {
                    #prefix (match (#receiver) { #pattern => { #rhs }, _ => false })
                });
            }
            if is_logical_and_at(&trees, pat_end) {
                // `EXPR matches PAT && RHS`: as in verus-syn's
                // `MatchesOpToken::AndAnd`, bindings from PAT scope through
                // the maximal `&&`-precedence RHS.  Lower-precedence `||` and
                // implication operators remain outside the match expression.
                let rhs_end = find_verus_matches_and_rhs_end(&trees, pat_end + 2);
                let rhs =
                    rewrite_verus_result_variant_sequence(trees[pat_end + 2..rhs_end].to_vec())?;
                let rest = rewrite_verus_result_variant_sequence(trees[rhs_end..].to_vec())?;
                return Ok(quote! {
                    #prefix (match (#receiver) { #pattern => { #rhs }, _ => false }) #rest
                });
            }
            // Bare `EXPR matches PAT` boolean test.
            let rest = rewrite_verus_result_variant_sequence(trees[pat_end..].to_vec())?;
            return Ok(quote! {
                #prefix (match (#receiver) { #pattern => true, _ => false }) #rest
            });
        }

        if let Some(field) = verus_general_projection_field(&trees, index) {
            // General `EXPR->FIELD` field projection over any datatype → a marker
            // `__trust_vc_field_proj_{field}(EXPR)` that the lowering resolves to
            // the owning variant's native selector (total-but-unconstrained off
            // its constructor = the sound off-variant value).
            let left_start = find_verus_result_left_operand_start(&trees, index, false)?;
            if left_start == index {
                return Err(syn::Error::new(
                    token_span(&trees[index]),
                    "Verus variant projection `->` requires a receiver",
                ));
            }
            let prefix = rewrite_verus_result_variant_sequence(trees[..left_start].to_vec())?;
            let receiver: TokenStream = trees[left_start..index].iter().cloned().collect();
            let rest = rewrite_verus_result_variant_sequence(trees[index + 3..].to_vec())?;
            let marker = projection_marker_ident(&field, token_span(&trees[index]));
            return Ok(quote! { #prefix ::trust_vc_core::#marker(#receiver) #rest });
        }
    }

    Ok(trees.into_iter().collect())
}

/// Lower all recognized `->` trailers in one flat sequence while retaining the
/// already-lowered receiver for a following trailer/operator.
#[allow(clippy::indexing_slicing)] // all slices are guarded by recognizers
fn rewrite_verus_projection_sequence(mut trees: Vec<TokenTree>) -> syn::Result<Vec<TokenTree>> {
    loop {
        let mut projection = None;
        for index in 0..trees.len() {
            if let Some(field) = verus_general_projection_field(&trees, index) {
                projection = Some((index, field));
                break;
            }
        }

        let Some((index, field)) = projection else {
            return Ok(trees);
        };
        let left_start = find_verus_result_left_operand_start(&trees, index, false)?;
        if left_start == index {
            return Err(syn::Error::new(
                token_span(&trees[index]),
                "Verus variant projection `->` requires a receiver",
            ));
        }

        let receiver: TokenStream = trees[left_start..index].iter().cloned().collect();
        let marker = projection_marker_ident(&field, token_span(&trees[index]));
        let replacement = quote! { ::trust_vc_core::#marker(#receiver) };

        let mut next = Vec::with_capacity(trees.len());
        next.extend_from_slice(&trees[..left_start]);
        next.extend(replacement);
        next.extend_from_slice(&trees[index + 3..]);
        trees = next;
    }
}

/// Encode the source field spelling into an identifier-safe marker suffix.
///
/// A direct concatenation can panic in `Ident::new` for legal raw identifiers
/// (`e->r#type`) and for malformed literal spellings that must instead fail
/// closed during lowering. Hex is injective over the UTF-8 spelling and keeps
/// every synthesized identifier valid. The lowering decodes the suffix before
/// resolving it against datatype metadata.
fn projection_marker_ident(field: &str, span: Span) -> proc_macro2::Ident {
    use std::fmt::Write;

    let mut marker = String::from("__trust_vc_field_proj_x");
    for byte in field.as_bytes() {
        // quality-audit: allow-expect — fmt::Write to a String is infallible
        write!(&mut marker, "{byte:02x}").expect("writing to String cannot fail");
    }
    proc_macro2::Ident::new(&marker, span)
}

/// The field name in a general `EXPR->FIELD` projection (`-` `>` <Ident|Literal>)
/// over any datatype. `FIELD` is a tuple index literal (`e->0`) or a named field
/// (`e->f`). Result's `->Ok_0`/`->Err_0` use this same type-directed path: a
/// custom datatype is allowed to name variants `Ok` or `Err`, so choosing the
/// Result-specific lowering from spelling alone would be incorrect.
fn verus_general_projection_field(trees: &[TokenTree], index: usize) -> Option<String> {
    // Must have a receiver before `->` (index 0 = a leading arrow, not a field
    // projection).
    if index == 0 {
        return None;
    }
    // NOT a closure return-type arrow `|args| -> T`: the token before `->` is the
    // closure's closing `|`. (Field projection's `->` is preceded by an
    // expression: ident / `)` / `]` / literal.)
    if matches!(trees.get(index - 1), Some(TokenTree::Punct(p)) if p.as_char() == '|') {
        return None;
    }
    let TokenTree::Punct(dash) = trees.get(index)? else {
        return None;
    };
    if dash.as_char() != '-' || dash.spacing() != Spacing::Joint {
        return None;
    }
    let TokenTree::Punct(gt) = trees.get(index + 1)? else {
        return None;
    };
    if gt.as_char() != '>' {
        return None;
    }
    let field = match trees.get(index + 2)? {
        TokenTree::Ident(field) => field.to_string(),
        TokenTree::Literal(lit) => lit.to_string(),
        _ => return None,
    };
    // NOT a function-TYPE return arrow `Fn(..) -> T` / `fn(..) -> T`: those have a
    // `)` right before `->` AND a fn-type keyword heading the "receiver".
    if matches!(trees.get(index - 1), Some(TokenTree::Group(g)) if g.delimiter() == proc_macro2::Delimiter::Parenthesis)
    {
        if let Some(TokenTree::Ident(head)) = trees.get(index.wrapping_sub(2)) {
            if matches!(
                head.to_string().as_str(),
                "Fn" | "FnMut" | "FnOnce" | "fn" | "spec_fn"
            ) {
                return None;
            }
        }
    }
    Some(field)
}

/// The variant identifier in an `EXPR is Variant` test. `is` is a Verus
/// contextual keyword (never a Rust operator), so between an operand and a bare
/// identifier in spec position it is unambiguously the variant-test operator.
/// Only the UNQUALIFIED form (`e is Some`, `e is A`) is matched here — a
/// path-qualified variant (`e is Foo::Bar`, i.e. followed by `::`) is left for
/// the normal parser rather than mis-split.
fn verus_is_operator_variant(trees: &[TokenTree], index: usize) -> Option<proc_macro2::Ident> {
    let TokenTree::Ident(is_ident) = trees.get(index)? else {
        return None;
    };
    if is_ident != "is" {
        return None;
    }
    let TokenTree::Ident(variant) = trees.get(index + 1)? else {
        return None;
    };
    // Reject a path-qualified variant (`Foo :: Bar`): don't consume just `Foo`.
    if let Some(TokenTree::Punct(p)) = trees.get(index + 2) {
        if p.as_char() == ':' {
            return None;
        }
    }
    Some(variant.clone())
}

/// Whether `trees[index]` is the `has` membership operator: the bare ident
/// `has` followed by an element expression (not a `.has(...)` method call — that
/// has a `.` before it, which the receiver scan would include, and a Group after,
/// which we require NOT to immediately follow as the whole element).
fn verus_is_has_operator(trees: &[TokenTree], index: usize) -> bool {
    matches!(trees.get(index), Some(TokenTree::Ident(id)) if id == "has")
        && trees.get(index + 1).is_some()
        // Not a method call `x.has(..)`: reject when preceded by `.`.
        && !matches!(trees.get(index.wrapping_sub(1)), Some(TokenTree::Punct(p)) if p.as_char() == '.')
}

/// The exclusive end of a `has` right-hand element expression.
///
/// Verus parses the RHS with `unary_expr`, not as an arbitrary expression.  In
/// particular, `s has x == p` means `(s has x) == p`, while a parenthesized
/// element (`s has (x == p)`) keeps the comparison inside the membership test.
/// Find the longest prefix that `syn` recognizes as a unary/atom expression;
/// this also handles compound atoms such as calls, indexing, `if`, `match`, and
/// closures without trying to duplicate their grammar here.
fn find_verus_has_rhs_end(trees: &[TokenTree], start: usize) -> usize {
    let mut best = None;
    for end in start + 1..=trees.len() {
        if parses_as_verus_unary_operand(&trees[start..end]) {
            best = Some(end);
        }
    }
    if let Some(end) = best {
        return end;
    }

    // Preserve the old fail-closed fallback for a Verus-only atom that plain
    // `syn` cannot recognize.  Ordinary Rust/Verus operator-precedence cases
    // take the exact prefix path above.
    let mut i = start;
    while i < trees.len() {
        if let TokenTree::Punct(p) = &trees[i] {
            match p.as_char() {
                ',' | ';' => return i,
                '&' | '|' if is_logical_pair_starting_at(trees, i) => return i,
                '=' if is_verus_implies_arrow_at(trees, i) => return i,
                // `<==>` iff arrow.
                '<' if matches!(trees.get(i + 1), Some(TokenTree::Punct(q)) if q.as_char() == '=')
                    && is_verus_implies_arrow_at(trees, i + 1) =>
                {
                    return i;
                }
                _ => {}
            }
        }
        i += 1;
    }
    i
}

/// Whether a token slice can be the result of Verus's `unary_expr` parser.
///
/// Plain `syn` has the same atom/prefix/trailer grammar needed here.  The only
/// expression variants it constructs exclusively in its lower-precedence loop
/// are binary operations, assignment, casts, and ranges with a left endpoint;
/// those must remain outside a `has` RHS.  Prefix ranges (`..end`) are atoms in
/// both parsers and therefore remain accepted.
fn parses_as_verus_unary_operand(trees: &[TokenTree]) -> bool {
    parses_as_verus_receiver_operand(trees, false)
}

/// Whether a token slice can be the left receiver of a Verus postfix variant
/// operator. `is`/`has`/`matches` are parsed in the expression-precedence loop
/// immediately after casts, so an already-formed cast may be their receiver.
/// `->` is instead part of `unary_expr`'s trailer loop and must pass
/// `allow_cast = false`.
fn parses_as_verus_receiver_operand(trees: &[TokenTree], allow_cast: bool) -> bool {
    if trees.is_empty() {
        return false;
    }
    let normalized = normalize_verus_unary_operand_for_syn(trees);
    let Ok(expr) = syn::parse2::<syn::Expr>(normalized) else {
        return false;
    };
    match expr {
        syn::Expr::Assign(_) | syn::Expr::Binary(_) => false,
        syn::Expr::Cast(_) => allow_cast,
        syn::Expr::Range(range) => range.start.is_none(),
        _ => true,
    }
}

/// Make Verus postfix trailers parseable by plain `syn` solely for operand
/// boundary discovery.  The returned stream is never emitted:
///
/// * `e->field` is represented as `e.field` (the same postfix extent), and
/// * `e@` drops the postfix view marker.
///
/// The real rewrite still receives and lowers the original tokens.
#[allow(clippy::indexing_slicing)] // every lookahead is guarded below
fn normalize_verus_unary_operand_for_syn(trees: &[TokenTree]) -> TokenStream {
    let mut normalized = TokenStream::new();
    let mut index = 0;
    while index < trees.len() {
        if let TokenTree::Punct(punct) = &trees[index] {
            if punct.as_char() == '@' {
                index += 1;
                continue;
            }
            if punct.as_char() == '-'
                && punct.spacing() == Spacing::Joint
                && matches!(trees.get(index + 1), Some(TokenTree::Punct(next)) if next.as_char() == '>')
                && matches!(
                    trees.get(index + 2),
                    Some(TokenTree::Ident(_) | TokenTree::Literal(_))
                )
            {
                let mut dot = proc_macro2::Punct::new('.', Spacing::Alone);
                dot.set_span(punct.span());
                normalized.extend(std::iter::once(TokenTree::Punct(dot)));
                normalized.extend(std::iter::once(trees[index + 2].clone()));
                index += 3;
                continue;
            }
        }
        normalized.extend(std::iter::once(trees[index].clone()));
        index += 1;
    }
    normalized
}

/// If `trees[index]` starts a `matches PAT` operator, returns the exclusive end
/// index of the pattern. `PAT` is a variant path (`A`, `E::A`) with an optional
/// binding/field group (`A(x)`, `A { x }`) — enough for Verus's variant-matching
/// spec surface; complex patterns fall back to the normal parser.
fn verus_matches_pattern_span(trees: &[TokenTree], index: usize) -> Option<usize> {
    let TokenTree::Ident(kw) = trees.get(index)? else {
        return None;
    };
    if kw != "matches" {
        return None;
    }
    let mut i = index + 1;
    loop {
        match trees.get(i)? {
            TokenTree::Ident(_) => i += 1,
            _ => return None,
        }
        let seg = matches!(trees.get(i), Some(TokenTree::Punct(p)) if p.as_char() == ':')
            && matches!(trees.get(i + 1), Some(TokenTree::Punct(p)) if p.as_char() == ':');
        if seg {
            i += 2;
            continue;
        }
        break;
    }
    if matches!(trees.get(i), Some(TokenTree::Group(_))) {
        i += 1;
    }
    Some(i)
}

/// Whether `trees[index..]` begins the raw `==>` arrow (`=` `=` `>`), used to
/// detect `matches PAT ==> RHS` before the connective pass runs.
fn is_verus_implies_arrow_at(trees: &[TokenTree], index: usize) -> bool {
    matches!(trees.get(index), Some(TokenTree::Punct(p)) if p.as_char() == '=')
        && matches!(trees.get(index + 1), Some(TokenTree::Punct(p)) if p.as_char() == '=')
        && matches!(trees.get(index + 2), Some(TokenTree::Punct(p)) if p.as_char() == '>')
}

fn is_verus_reverse_implies_at(trees: &[TokenTree], index: usize) -> bool {
    matches!(trees.get(index), Some(TokenTree::Punct(p)) if p.as_char() == '<' && p.spacing() == Spacing::Joint)
        && matches!(trees.get(index + 1), Some(TokenTree::Punct(p)) if p.as_char() == '=' && p.spacing() == Spacing::Joint)
        && matches!(trees.get(index + 2), Some(TokenTree::Punct(p)) if p.as_char() == '=')
}

fn is_logical_and_at(trees: &[TokenTree], index: usize) -> bool {
    !big_and_bullet_at(trees, index)
        && matches!(trees.get(index), Some(TokenTree::Punct(p)) if p.as_char() == '&' && p.spacing() == Spacing::Joint)
        && matches!(trees.get(index + 1), Some(TokenTree::Punct(p)) if p.as_char() == '&')
}

/// Exclusive end of the RHS captured by Verus's special
/// `matches PAT && RHS` form.  Its RHS includes operators at `&&` precedence
/// and tighter, but leaves lower-precedence disjunction, implication,
/// assignment/range, and outer bullet/statement boundaries to the caller.
/// Delimiter groups are opaque tokens, so every boundary here is top-level.
fn find_verus_matches_and_rhs_end(trees: &[TokenTree], start: usize) -> usize {
    let mut index = start;
    while index < trees.len() {
        if big_and_bullet_at(trees, index) || big_or_bullet_at(trees, index) {
            return index;
        }
        let TokenTree::Punct(punct) = &trees[index] else {
            index += 1;
            continue;
        };
        match punct.as_char() {
            ',' | ';' => return index,
            '|' if is_logical_pair_starting_at(trees, index) => return index,
            '=' if is_verus_implies_arrow_at(trees, index) => return index,
            '<' if is_verus_reverse_implies_at(trees, index) => return index,
            '=' if !matches!(trees.get(index + 1), Some(TokenTree::Punct(p)) if p.as_char() == '=')
                && !matches!(trees.get(index.wrapping_sub(1)), Some(TokenTree::Punct(p)) if p.as_char() == '=' || p.as_char() == '!' || p.as_char() == '<' || p.as_char() == '>') =>
            {
                return index;
            }
            '.' if matches!(trees.get(index + 1), Some(TokenTree::Punct(p)) if p.as_char() == '.') =>
            {
                return index;
            }
            _ => {}
        }
        index += 1;
    }
    trees.len()
}

/// The variant identifier in an `EXPR !is Variant` negated test (`!` `is` V).
/// Matched at the `!` so the receiver is the operand before the `!`.
fn verus_notis_operator_variant(trees: &[TokenTree], index: usize) -> Option<proc_macro2::Ident> {
    let TokenTree::Punct(bang) = trees.get(index)? else {
        return None;
    };
    if bang.as_char() != '!' {
        return None;
    }
    let TokenTree::Ident(is_ident) = trees.get(index + 1)? else {
        return None;
    };
    if is_ident != "is" {
        return None;
    }
    let TokenTree::Ident(variant) = trees.get(index + 2)? else {
        return None;
    };
    if let Some(TokenTree::Punct(p)) = trees.get(index + 3) {
        if p.as_char() == ':' {
            return None;
        }
    }
    Some(variant.clone())
}

fn find_verus_result_left_operand_start(
    trees: &[TokenTree],
    operator_index: usize,
    allow_cast: bool,
) -> syn::Result<usize> {
    if operator_index == 0 {
        return Err(syn::Error::new(
            Span::call_site(),
            "Verus Result syntax is missing a receiver",
        ));
    }

    // First preserve the punctuation boundaries that are unambiguous in this
    // flat stream.  This floor is important: a leading infix `&&` in a
    // recursively processed suffix is also parseable by Rust as two nested
    // unary references (`& &value`), so asking `syn` alone would accidentally
    // absorb it into the receiver.
    let mut angle_depth = 0usize;
    let mut index = operator_index;
    let mut floor = 0usize;
    while index > 0 {
        index -= 1;
        let TokenTree::Punct(punct) = &trees[index] else {
            continue;
        };
        match punct.as_char() {
            // The `>` of a connective arrow (`==>` / `<==>` — the punct before it
            // is `=`) bounds the left operand of a downstream `is`/`matches`/`has`/
            // `->`. (The projection arrow `->` has `-` before its `>`, so it is
            // NOT a boundary — a projected receiver like `a->b is C` stays whole.)
            '>' if angle_depth == 0
                && is_arrow_suffix(trees, index)
                && matches!(
                    trees.get(index.wrapping_sub(1)),
                    Some(TokenTree::Punct(p)) if p.as_char() == '='
                ) =>
            {
                return Ok(index + 1);
            }
            '>' if !is_arrow_suffix(trees, index) => {
                angle_depth = angle_depth.saturating_add(1);
            }
            '<' if angle_depth > 0 => {
                angle_depth -= 1;
            }
            ',' | ';' if angle_depth == 0 => {
                floor = index + 1;
                break;
            }
            '|' if angle_depth == 0 && !is_logical_pair_member(trees, index) => {
                floor = index + 1;
                break;
            }
            '&' | '|' if angle_depth == 0 => {
                if is_logical_pair_ending_at(trees, index) {
                    floor = index + 1;
                    break;
                }
                if is_logical_pair_starting_at(trees, index) {
                    floor = index + 2;
                    break;
                }
            }
            _ => {}
        }
    }

    // `is`, `matches`, `has`, and `->` all bind more tightly than ordinary
    // binary operators.  Starting no earlier than the floor above, select the
    // longest suffix ending at the operator that is a legal receiver. This
    // catches comparison/arithmetic boundaries that the punctuation scan
    // deliberately does not try to decode (`flag == value is V`, `n + set has
    // x`). The caller admits a trailing cast only for `is`/`has`/`matches`,
    // matching their position immediately after Cast in verus-syn's
    // precedence loop; `->` remains a unary trailer.
    for start in floor..operator_index {
        if parses_as_verus_receiver_operand(&trees[start..operator_index], allow_cast) {
            // `-`, `*`, `&`, and `..` can begin a unary/prefix expression but
            // can also be the infix operator immediately before this receiver.
            // For `mask & value is A`, the suffix `& value` parses as a Rust
            // reference even though verus-syn parses `mask & (value is A)`.
            // If the tokens before such a candidate already form a complete
            // expression, keep looking past the infix token. The same rule
            // preserves genuine RHS prefixes (`mask & &value is A`) because
            // `mask &` is incomplete before the second ampersand.
            if start > floor
                && can_start_prefix_or_end_infix(&trees[start..operator_index])
                && parses_as_complete_expression(&trees[floor..start])
            {
                continue;
            }
            return Ok(start);
        }
    }

    // A Verus-only atom that cannot be mirrored through plain `syn` retains the
    // conservative floor.  Malformed input therefore remains fail-closed.
    Ok(floor)
}

fn can_start_prefix_or_end_infix(trees: &[TokenTree]) -> bool {
    matches!(trees.first(), Some(TokenTree::Punct(p)) if matches!(p.as_char(), '-' | '*' | '&'))
        || matches!(
            (trees.first(), trees.get(1)),
            (Some(TokenTree::Punct(first)), Some(TokenTree::Punct(second)))
                if first.as_char() == '.' && second.as_char() == '.'
        )
}

fn parses_as_complete_expression(trees: &[TokenTree]) -> bool {
    !trees.is_empty()
        && syn::parse2::<syn::Expr>(normalize_verus_unary_operand_for_syn(trees)).is_ok()
}

fn is_logical_pair_member(trees: &[TokenTree], index: usize) -> bool {
    is_logical_pair_ending_at(trees, index) || is_logical_pair_starting_at(trees, index)
}

fn is_logical_pair_ending_at(trees: &[TokenTree], index: usize) -> bool {
    if index == 0 {
        return false;
    }
    let (TokenTree::Punct(prev), TokenTree::Punct(current)) = (&trees[index - 1], &trees[index])
    else {
        return false;
    };
    prev.as_char() == current.as_char()
        && matches!(current.as_char(), '&' | '|')
        && prev.spacing() == Spacing::Joint
}

fn is_logical_pair_starting_at(trees: &[TokenTree], index: usize) -> bool {
    let (Some(TokenTree::Punct(current)), Some(TokenTree::Punct(next))) =
        (trees.get(index), trees.get(index + 1))
    else {
        return false;
    };
    current.as_char() == next.as_char()
        && matches!(current.as_char(), '&' | '|')
        && current.spacing() == Spacing::Joint
}

fn token_span(token: &TokenTree) -> Span {
    match token {
        TokenTree::Group(group) => group.span(),
        TokenTree::Ident(ident) => ident.span(),
        TokenTree::Punct(punct) => punct.span(),
        TokenTree::Literal(literal) => literal.span(),
    }
}

// ---- Verus boolean connective (`<==>`, `==>`, `<==`) lowering ----

/// Lower Verus-style boolean connectives into marker macros, in strict
/// precedence order (loosest first):
///
/// 1. `<==>` (logical equivalence / biconditional) — the loosest connective.
/// 2. `==>` / `<==` (forward / reverse implication) — same precedence level.
///
/// Equivalence is rewritten before implication so that the `==>`-suffix of a
/// `<==>` token (`< = = >`) is never mistaken for a bare `==>`. Each pass only
/// ever consumes connectives at its own top level; the operand sub-streams are
/// re-parsed (and thus re-passed through *all* connective rewrites) at lowering
/// time, so nesting and precedence interleaving are handled uniformly.
///
/// The rewrites are pure boolean: `P <==> Q` becomes `(P ==> Q) && (Q ==> P)`
/// and `P <== Q` becomes `Q ==> P`. No new IR node is introduced and the
/// transformation is sound by construction.
fn rewrite_verus_connectives_tokens(tokens: TokenStream) -> syn::Result<TokenStream> {
    let trees: Vec<TokenTree> = tokens.into_iter().collect();
    // Recurse into every delimiter group first so a connective nested inside
    // parens/brackets/braces (and quantifier-body closures) is lowered relative
    // to that group's own top level.
    let trees = recurse_connective_groups(trees)?;
    // At this top level, split equivalence first (loosest), then implication.
    rewrite_verus_iff_sequence(trees)
}

/// Split a flat (already group-recursed) token sequence at the leftmost
/// top-level `<==>` operator. When no `<==>` is present at this level, falls
/// through to the implication splitter (`==>` / `<==`).
///
/// Each `<==>` operand is itself fully connective-lowered (equivalence *and*
/// implication) *before* being wrapped in the marker, so the marker only ever
/// contains already-lowered sub-markers. That keeps the comma separating the two
/// marker operands from ever being swept into a later implication split.
#[allow(clippy::indexing_slicing)] // split index comes from a guarded scan of `trees`
fn rewrite_verus_iff_sequence(trees: Vec<TokenTree>) -> syn::Result<TokenStream> {
    let Some((op_index, op_span)) = find_first_top_level_iff(&trees) else {
        // No equivalence at this level: lower any forward/reverse implications.
        return rewrite_verus_implies_sequence(trees);
    };

    let lhs_trees = &trees[..op_index];
    if lhs_trees.is_empty() {
        return Err(syn::Error::new(
            op_span,
            "logical equivalence `<==>` requires an operand on its left-hand side",
        ));
    }
    let rhs_trees = &trees[op_index + 4..];
    if rhs_trees.is_empty() {
        return Err(syn::Error::new(
            op_span,
            "logical equivalence `<==>` requires an operand on its right-hand side",
        ));
    }

    // Fully lower the left operand's own connectives (it is to the left of the
    // leftmost `<==>`, so it contains no further top-level `<==>`, but it may
    // contain `==>`/`<==`).
    let lhs = rewrite_verus_implies_sequence(lhs_trees.to_vec())?;
    // Recurse so a chain `a <==> b <==> c` lowers to nested markers. Equivalence
    // is associative as booleans, so the chosen right-associativity is sound.
    let rhs = rewrite_verus_iff_sequence(rhs_trees.to_vec())?;
    Ok(marker_call(IFF_MARKER_MACRO, lhs, rhs, op_span))
}

/// Find the leftmost top-level `<==>` (four puncts: `<` joint, `=` joint,
/// `=` joint, `>`).
#[allow(clippy::indexing_slicing)] // every index is bounds-checked via `get`
fn find_first_top_level_iff(trees: &[TokenTree]) -> Option<(usize, Span)> {
    let mut index = 0;
    while index < trees.len() {
        if let (
            Some(TokenTree::Punct(first)),
            Some(TokenTree::Punct(second)),
            Some(TokenTree::Punct(third)),
            Some(TokenTree::Punct(fourth)),
        ) = (
            trees.get(index),
            trees.get(index + 1),
            trees.get(index + 2),
            trees.get(index + 3),
        ) {
            if first.as_char() == '<'
                && first.spacing() == Spacing::Joint
                && second.as_char() == '='
                && second.spacing() == Spacing::Joint
                && third.as_char() == '='
                && third.spacing() == Spacing::Joint
                && fourth.as_char() == '>'
            {
                return Some((index, first.span()));
            }
        }
        index += 1;
    }
    None
}

/// Split a flat (already group-recursed) token sequence at the leftmost
/// top-level `==>` or `<==` operator into the marker macro
/// `__trust_vc_implies!(premise, conclusion)`.
///
/// `==>` is right-associative (`a ==> b ==> c` means `a ==> (b ==> c)`); `<==`
/// is its mirror (`P <== Q` means `Q ==> P`). Both live at the same precedence
/// level, below `<==>`. Reverse implication is normalized into forward form so
/// that the IR only ever sees `Implies`. Trees are assumed already group-recursed
/// by `rewrite_verus_connectives_tokens`.
#[allow(clippy::indexing_slicing)] // split index comes from a guarded scan of `trees`
fn rewrite_verus_implies_sequence(trees: Vec<TokenTree>) -> syn::Result<TokenStream> {
    let Some(op) = find_first_top_level_implication(&trees) else {
        return Ok(trees.into_iter().collect());
    };
    let op_span = op.span;

    // Diagnostics are phrased relative to the *source* spelling. For `==>` the
    // left-hand side is the premise and the right-hand side is the conclusion;
    // for `<==` (reverse implication) the roles are swapped.
    let (left_role, right_role) = match op.direction {
        ImplicationDirection::Forward => ("premise", "conclusion"),
        ImplicationDirection::Reverse => ("conclusion", "premise"),
    };

    let left_trees = &trees[..op.index];
    if left_trees.is_empty() {
        return Err(syn::Error::new(
            op_span,
            format!(
                "logical implication `==>`/`<==` requires a {} on its left-hand side",
                left_role
            ),
        ));
    }
    let right_trees = &trees[op.index + 3..];
    if right_trees.is_empty() {
        return Err(syn::Error::new(
            op_span,
            format!(
                "logical implication `==>`/`<==` requires a {} on its right-hand side",
                right_role
            ),
        ));
    }

    // The premise/conclusion are emitted as raw token sub-streams; the lowering
    // re-parses each through the chain-aware parser. They are separated by a
    // top-level `,`, which `rewrite_chained_tokens` now treats as a hard
    // boundary, so a later chained pass descending into the marker group (e.g.
    // inside a quantifier body) cannot span a comparison chain across them.
    let left: TokenStream = left_trees.iter().cloned().collect();
    // Recurse the rewrite on the (entire) right-hand side so that a chain of
    // implications associates to the right: `a ==> b ==> c` becomes
    // `__trust_vc_implies!(a, __trust_vc_implies!(b, c))`.
    let right = rewrite_verus_implies_sequence(right_trees.to_vec())?;

    let (premise, conclusion) = match op.direction {
        // `P ==> Q`: premise = left, conclusion = right.
        ImplicationDirection::Forward => (left, right),
        // `P <== Q`: reverse implication is `Q ==> P`, so premise = right,
        // conclusion = left. This is a pure boolean normalization.
        ImplicationDirection::Reverse => (right, left),
    };
    Ok(marker_call(
        IMPLIES_MARKER_MACRO,
        premise,
        conclusion,
        op_span,
    ))
}

/// Direction of an implication operator at its source spelling.
#[derive(Clone, Copy)]
enum ImplicationDirection {
    /// `==>` (forward implication).
    Forward,
    /// `<==` (reverse implication / "explies").
    Reverse,
}

/// A located implication operator: the index of its first punct, its source
/// direction, and the span used for diagnostics.
struct ImplicationOp {
    index: usize,
    direction: ImplicationDirection,
    span: Span,
}

/// Find the leftmost top-level `==>` (three puncts: `=` joint, `=` joint, `>`)
/// or `<==` (three puncts: `<` joint, `=` joint, `=` *non*-`>`-suffixed).
///
/// `=>` (the two-punct fat arrow used by `match`, closures, and `map!`) is left
/// untouched because its first `=` is immediately followed by `>`, not `=`. A
/// `<==` whose final `=` is joined to a trailing `>` is part of a `<==>` and is
/// excluded — those are handled by the equivalence pass that runs first.
#[allow(clippy::indexing_slicing)] // every index is bounds-checked via `get`
fn find_first_top_level_implication(trees: &[TokenTree]) -> Option<ImplicationOp> {
    let mut index = 0;
    while index < trees.len() {
        if let (
            Some(TokenTree::Punct(first)),
            Some(TokenTree::Punct(second)),
            Some(TokenTree::Punct(third)),
        ) = (trees.get(index), trees.get(index + 1), trees.get(index + 2))
        {
            // `==>`
            if first.as_char() == '='
                && first.spacing() == Spacing::Joint
                && second.as_char() == '='
                && second.spacing() == Spacing::Joint
                && third.as_char() == '>'
            {
                return Some(ImplicationOp {
                    index,
                    direction: ImplicationDirection::Forward,
                    span: first.span(),
                });
            }
            // `<==` (and not the `<==>` prefix: any `<==>` is already lowered by
            // the equivalence pass, but guard against a stray `>` joined to the
            // last `=` so we never split a `<==>` here).
            if first.as_char() == '<'
                && first.spacing() == Spacing::Joint
                && second.as_char() == '='
                && second.spacing() == Spacing::Joint
                && third.as_char() == '='
                && !is_joined_to_gt(trees, index + 2)
            {
                return Some(ImplicationOp {
                    index,
                    direction: ImplicationDirection::Reverse,
                    span: first.span(),
                });
            }
        }
        index += 1;
    }
    None
}

/// Whether the punct at `index` is joint and immediately followed by a `>`,
/// i.e. it forms (the tail of) a `<==>` rather than a bare `<==`.
#[allow(clippy::indexing_slicing)] // both indices are bounds-checked via `get`
fn is_joined_to_gt(trees: &[TokenTree], index: usize) -> bool {
    matches!(trees.get(index), Some(TokenTree::Punct(p)) if p.spacing() == Spacing::Joint)
        && matches!(trees.get(index + 1), Some(TokenTree::Punct(n)) if n.as_char() == '>')
}

/// Recurse the connective rewrite into every delimiter group so that connectives
/// nested inside parentheses, brackets, braces (and the closures synthesized for
/// quantifier bodies) are lowered relative to that group's own top level.
fn recurse_connective_groups(trees: Vec<TokenTree>) -> syn::Result<Vec<TokenTree>> {
    trees
        .into_iter()
        .map(|tt| match tt {
            TokenTree::Group(group) => {
                let inner = rewrite_verus_connectives_tokens(group.stream())?;
                let mut rewritten = proc_macro2::Group::new(group.delimiter(), inner);
                rewritten.set_span(group.span());
                Ok(TokenTree::Group(rewritten))
            }
            other => Ok(other),
        })
        .collect()
}

/// Build a two-operand marker macro invocation `marker!(first, second)` with all
/// synthesized tokens carrying `op_span`. The operands are emitted as raw token
/// sub-streams separated by a top-level comma.
fn marker_call(
    marker_name: &str,
    first: TokenStream,
    second: TokenStream,
    op_span: Span,
) -> TokenStream {
    let marker = proc_macro2::Ident::new(marker_name, op_span);
    let bang = {
        let mut punct = proc_macro2::Punct::new('!', Spacing::Alone);
        punct.set_span(op_span);
        punct
    };
    let mut args = TokenStream::new();
    args.extend(first);
    let mut comma = proc_macro2::Punct::new(',', Spacing::Alone);
    comma.set_span(op_span);
    args.extend(std::iter::once(TokenTree::Punct(comma)));
    args.extend(second);
    let mut group = proc_macro2::Group::new(Delimiter::Parenthesis, args);
    group.set_span(op_span);
    quote! { #marker #bang #group }
}

// ---- Verus equality operator (`=~=`, `===`) lowering ----

/// Surface macro that `=~=` lowers to. Verus `=~=` is *extensional* equality.
/// `ext_eq!` already has full IR-lowering (`ir_lowering::dispatch::macros`) and
/// proc-macro try-builder (`expr_codegen`) support keyed on this trailing
/// identifier, where it expands to the true extensional formula (sequence
/// length+indices, set/multiset membership/count, map key+value, spec-fn
/// pointwise). A false extensional claim therefore becomes an unprovable
/// `forall` and fails closed. Reusing the macro means this rewrite adds no new
/// lowering code.
const EXT_EQ_SURFACE_MACRO: &str = "ext_eq";

/// Surface macro that `===` lowers to. Verus `===` is *strict* (`spec_eq`)
/// equality, encoded as a raw solver equality (`__trust_vc_strict_eq`). It
/// deliberately does **not** expand extensionally: mapping `===` to `ext_eq`
/// would be unsound by over-proving (it would prove `a === b` for
/// extensionally-equal but structurally-distinct terms), so the two operators
/// stay distinct. `strict_eq!` is likewise already wired into both lowering
/// paths.
const STRICT_EQ_SURFACE_MACRO: &str = "strict_eq";

/// Lower Verus-style `=~=` (extensional equality) and `===` (strict / spec
/// equality) into the `ext_eq!` / `strict_eq!` call surfaces. `syn` cannot parse
/// either token sequence (`=~=` contains `~`; `===` is three joined `=`), so
/// they must be rewritten at the token level, exactly like the `==>`/`<==>`
/// connectives.
///
/// Both operators bind at *comparison* precedence: tighter than `&&`/`||` and
/// the `==>`/`<==>` connectives (already lowered to markers when this runs),
/// looser than arithmetic. So — unlike the connective splitters, which take the
/// whole level — this splits the stream at the top-level `&&`/`||`/`,`
/// boundaries first (mirroring `rewrite_chained_tokens`) and rewrites the single
/// equality operator within each resulting segment.
fn rewrite_verus_eq_operator_tokens(tokens: TokenStream) -> syn::Result<TokenStream> {
    let trees: Vec<TokenTree> = tokens.into_iter().collect();
    // Recurse into every delimiter group first (parens/brackets/braces and the
    // closures synthesized for quantifier bodies) so an operator nested inside is
    // rewritten relative to that group's own top level.
    let trees = recurse_eq_operator_groups(trees)?;
    rewrite_eq_operator_segments(trees)
}

/// Recurse the equality-operator rewrite into every delimiter group.
fn recurse_eq_operator_groups(trees: Vec<TokenTree>) -> syn::Result<Vec<TokenTree>> {
    trees
        .into_iter()
        .map(|tt| match tt {
            TokenTree::Group(group) => {
                let inner = rewrite_verus_eq_operator_tokens(group.stream())?;
                let mut rewritten = proc_macro2::Group::new(group.delimiter(), inner);
                rewritten.set_span(group.span());
                Ok(TokenTree::Group(rewritten))
            }
            other => Ok(other),
        })
        .collect()
}

/// Split a flat (already group-recursed) token sequence at the top-level
/// `&&`/`||`/`,` boundaries and rewrite the equality operator inside each
/// segment. Those boundaries bind looser than `=~=`/`===`, and an equality
/// operand is a (non-boolean) collection/value expression, so each segment holds
/// at most one such operator.
///
/// Commas are only treated as boundaries at angle-bracket depth zero: a comma
/// inside a turbofish (`Map::<u8, bool>`) separates type arguments, not
/// expressions, and must stay inside its operand. Angle brackets are bare puncts
/// (not delimiter groups), so unlike `(`/`[`/`{` they are not handled by the
/// group recursion and must be tracked here.
#[allow(clippy::indexing_slicing)] // i bounded by `while i < trees.len()`; separators[i-1] guarded by i > 0
fn rewrite_eq_operator_segments(trees: Vec<TokenTree>) -> syn::Result<TokenStream> {
    let mut segments: Vec<Vec<TokenTree>> = Vec::new();
    let mut separators: Vec<Vec<TokenTree>> = Vec::new();
    let mut current: Vec<TokenTree> = Vec::new();
    let mut i = 0;
    let mut angle_depth = 0usize;

    while i < trees.len() {
        if let TokenTree::Punct(p) = &trees[i] {
            // Track turbofish / generic angle-bracket depth.
            if turbofish_opens_at(&trees, i, angle_depth) {
                angle_depth += 1;
            } else if angle_depth > 0 && turbofish_closes_at(&trees, i) {
                angle_depth -= 1;
            } else if angle_depth == 0 {
                if (p.as_char() == '&' || p.as_char() == '|') && p.spacing() == Spacing::Joint {
                    if let Some(TokenTree::Punct(next)) = trees.get(i + 1) {
                        if next.as_char() == p.as_char() {
                            segments.push(std::mem::take(&mut current));
                            separators.push(vec![trees[i].clone(), trees[i + 1].clone()]);
                            i += 2;
                            continue;
                        }
                    }
                }
                if p.as_char() == ',' {
                    segments.push(std::mem::take(&mut current));
                    separators.push(vec![trees[i].clone()]);
                    i += 1;
                    continue;
                }
            }
        }
        current.push(trees[i].clone());
        i += 1;
    }
    segments.push(current);

    let mut result = TokenStream::new();
    for (index, segment) in segments.into_iter().enumerate() {
        if index > 0 {
            let sep: TokenStream = separators[index - 1].iter().cloned().collect();
            result.extend(sep);
        }
        result.extend(process_eq_operator_segment(segment)?);
    }
    Ok(result)
}

/// Rewrite the leftmost top-level `=~=`/`===` in a single segment (no
/// `&&`/`||`/`,`, groups already recursed) into the corresponding marker call.
/// The operand sub-streams are emitted raw and separated by a top-level comma,
/// exactly like the connective markers; the existing `ext_eq!`/`strict_eq!`
/// lowering re-parses them. A chained `a =~= b =~= c` leaves a second raw
/// operator inside an operand, which fails the operand parse closed.
#[allow(clippy::indexing_slicing)] // split index comes from a guarded scan of `trees`
fn process_eq_operator_segment(trees: Vec<TokenTree>) -> syn::Result<TokenStream> {
    let Some(op) = find_first_top_level_eq_operator(&trees) else {
        return Ok(trees.into_iter().collect());
    };

    let lhs_trees = &trees[..op.index];
    if lhs_trees.is_empty() {
        return Err(syn::Error::new(
            op.span,
            format!(
                "`{}` requires an operand on its left-hand side",
                op.spelling()
            ),
        ));
    }
    let rhs_trees = &trees[op.index + 3..];
    if rhs_trees.is_empty() {
        return Err(syn::Error::new(
            op.span,
            format!(
                "`{}` requires an operand on its right-hand side",
                op.spelling()
            ),
        ));
    }

    let lhs: TokenStream = lhs_trees.iter().cloned().collect();
    let rhs: TokenStream = rhs_trees.iter().cloned().collect();
    Ok(marker_call(op.surface_macro(), lhs, rhs, op.span))
}

/// Which Verus equality operator was located in a segment.
#[derive(Clone, Copy)]
enum EqOperatorKind {
    /// `=~=` — extensional equality (lowers to `ext_eq!`).
    Extensional,
    /// `===` — strict / spec equality (lowers to `strict_eq!`).
    Strict,
}

/// A located equality operator: the index of its first punct, its kind, and the
/// span used for diagnostics. Both operators are exactly three puncts wide.
struct EqOperator {
    index: usize,
    kind: EqOperatorKind,
    span: Span,
}

impl EqOperator {
    fn surface_macro(&self) -> &'static str {
        match self.kind {
            EqOperatorKind::Extensional => EXT_EQ_SURFACE_MACRO,
            EqOperatorKind::Strict => STRICT_EQ_SURFACE_MACRO,
        }
    }

    fn spelling(&self) -> &'static str {
        match self.kind {
            EqOperatorKind::Extensional => "=~=",
            EqOperatorKind::Strict => "===",
        }
    }
}

/// Find the leftmost top-level `=~=` (`=` joint, `~` joint, `=`) or `===`
/// (`=` joint, `=` joint, `=`).
///
/// Requiring a *third* `=` plus the leading two puncts being `Joint` is what
/// keeps `==` (two puncts, the second `Alone`) and `==>` (`=` `=` `>`) from ever
/// matching `===`. `=~=` is unambiguous because `~` appears nowhere else in the
/// spec surface.
#[allow(clippy::indexing_slicing)] // every index is bounds-checked via `get`
fn find_first_top_level_eq_operator(trees: &[TokenTree]) -> Option<EqOperator> {
    let mut index = 0;
    while index < trees.len() {
        if let (
            Some(TokenTree::Punct(first)),
            Some(TokenTree::Punct(second)),
            Some(TokenTree::Punct(third)),
        ) = (trees.get(index), trees.get(index + 1), trees.get(index + 2))
        {
            if first.as_char() == '='
                && first.spacing() == Spacing::Joint
                && second.spacing() == Spacing::Joint
                && third.as_char() == '='
            {
                // `=~=` (extensional)
                if second.as_char() == '~' {
                    return Some(EqOperator {
                        index,
                        kind: EqOperatorKind::Extensional,
                        span: first.span(),
                    });
                }
                // `===` (strict / spec equality)
                if second.as_char() == '=' {
                    return Some(EqOperator {
                        index,
                        kind: EqOperatorKind::Strict,
                        span: first.span(),
                    });
                }
            }
        }
        index += 1;
    }
    None
}

/// Whether the punct at `index` opens a turbofish / generic angle-bracket list.
///
/// The outermost `<` only opens when preceded by `::` (a turbofish), so a bare
/// `<` comparison — which never follows `::` — is not miscounted. Once inside an
/// angle list (`angle_depth > 0`) any `<` opens a nested argument list. `<=`,
/// `<==`, and `<<` are excluded.
#[allow(clippy::indexing_slicing)] // index < trees.len() guaranteed by the caller's loop bound
fn turbofish_opens_at(trees: &[TokenTree], index: usize, angle_depth: usize) -> bool {
    let TokenTree::Punct(punct) = &trees[index] else {
        return false;
    };
    if punct.as_char() != '<' {
        return false;
    }
    if matches!(trees.get(index + 1), Some(TokenTree::Punct(next)) if matches!(next.as_char(), '=' | '<'))
    {
        return false;
    }
    if angle_depth > 0 {
        return true;
    }
    matches!(
        index.checked_sub(1).and_then(|prev| trees.get(prev)),
        Some(TokenTree::Punct(prev)) if prev.as_char() == ':'
    )
}

/// Whether the punct at `index` closes a turbofish / generic angle-bracket list.
/// Only meaningful when `angle_depth > 0`. `->`/`=>` arrow suffixes and `>=` are
/// excluded; a `>>` closing two nested lists is consumed one `>` at a time.
#[allow(clippy::indexing_slicing)] // index < trees.len() guaranteed by the caller's loop bound
fn turbofish_closes_at(trees: &[TokenTree], index: usize) -> bool {
    let TokenTree::Punct(punct) = &trees[index] else {
        return false;
    };
    if punct.as_char() != '>' || is_arrow_suffix(trees, index) {
        return false;
    }
    !matches!(trees.get(index + 1), Some(TokenTree::Punct(next)) if next.as_char() == '=')
}

// ---- Token-level chain detection and rewriting ----

#[derive(Clone, Copy, PartialEq)]
enum ChainDirection {
    Ascending,
    Descending,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ExplicitChainOperandType {
    Int,
    Nat,
    Real,
}

struct ComparisonOp {
    index: usize,
    token_count: usize,
    direction: ChainDirection,
    span: Span,
}

/// Check if the `>` at `index` is actually part of `->` or `=>`.
#[allow(clippy::indexing_slicing)] // index > 0 guard before trees[index - 1]
fn is_arrow_suffix(trees: &[TokenTree], index: usize) -> bool {
    if index == 0 {
        return false;
    }
    if let TokenTree::Punct(prev) = &trees[index - 1] {
        if prev.spacing() == Spacing::Joint {
            return matches!(prev.as_char(), '-' | '=');
        }
    }
    false
}

/// Find top-level comparison operators (`<`, `<=`, `>`, `>=`) in a flat
/// token sequence. Skips `<<`, `>>`, `->`, `=>`.
#[allow(clippy::indexing_slicing)] // i bounded by while i < trees.len()
fn find_comparison_ops(trees: &[TokenTree]) -> Vec<ComparisonOp> {
    let mut result = Vec::new();
    let mut i = 0;

    while i < trees.len() {
        if let TokenTree::Punct(p) = &trees[i] {
            match (p.as_char(), p.spacing()) {
                ('<', Spacing::Alone) => {
                    result.push(ComparisonOp {
                        index: i,
                        token_count: 1,
                        direction: ChainDirection::Ascending,
                        span: p.span(),
                    });
                }
                ('<', Spacing::Joint) => {
                    if let Some(TokenTree::Punct(next)) = trees.get(i + 1) {
                        match next.as_char() {
                            '=' => {
                                result.push(ComparisonOp {
                                    index: i,
                                    token_count: 2,
                                    direction: ChainDirection::Ascending,
                                    span: p.span(),
                                });
                                i += 2;
                                continue;
                            }
                            '<' => {
                                // << (shift), skip both
                                i += 2;
                                continue;
                            }
                            _ => {}
                        }
                    }
                }
                ('>', Spacing::Alone) if !is_arrow_suffix(trees, i) => {
                    result.push(ComparisonOp {
                        index: i,
                        token_count: 1,
                        direction: ChainDirection::Descending,
                        span: p.span(),
                    });
                }
                ('>', Spacing::Joint) if !is_arrow_suffix(trees, i) => {
                    if let Some(TokenTree::Punct(next)) = trees.get(i + 1) {
                        match next.as_char() {
                            '=' => {
                                result.push(ComparisonOp {
                                    index: i,
                                    token_count: 2,
                                    direction: ChainDirection::Descending,
                                    span: p.span(),
                                });
                                i += 2;
                                continue;
                            }
                            '>' => {
                                // >> (shift), skip both
                                i += 2;
                                continue;
                            }
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
        }
        i += 1;
    }

    result
}

/// Recursively rewrite chained comparisons inside groups (parens, brackets).
fn rewrite_groups(trees: Vec<TokenTree>) -> syn::Result<Vec<TokenTree>> {
    trees
        .into_iter()
        .map(|tt| match tt {
            TokenTree::Group(g) => {
                let inner = rewrite_chained_tokens(g.stream())?;
                let mut new_g = proc_macro2::Group::new(g.delimiter(), inner);
                new_g.set_span(g.span());
                Ok(TokenTree::Group(new_g))
            }
            other => Ok(other),
        })
        .collect()
}

/// Rewrite a segment (no `&&`/`||`) that may contain a comparison chain.
#[allow(clippy::indexing_slicing)] // ops indices within trees.len(); operand_segments has ops.len()+1 entries
fn process_comparison_segment(trees: Vec<TokenTree>) -> syn::Result<TokenStream> {
    let ops = find_comparison_ops(&trees);

    if ops.len() < 2 {
        return Ok(trees.into_iter().collect());
    }

    // Validate direction uniformity
    let first_dir = ops[0].direction;
    for op in &ops[1..] {
        if op.direction != first_dir {
            return Err(syn::Error::new(
                op.span,
                "chained comparisons must be monotone: use only (<, <=) or only (>, >=)",
            ));
        }
    }

    // Split into operand token segments between comparison operators
    let mut operand_segments: Vec<TokenStream> = Vec::new();
    let mut pos = 0;
    for op in &ops {
        let seg: TokenStream = trees[pos..op.index].iter().cloned().collect();
        operand_segments.push(seg);
        pos = op.index + op.token_count;
    }
    let last_seg: TokenStream = trees[pos..].iter().cloned().collect();
    operand_segments.push(last_seg);

    reject_mixed_explicit_chain_operand_types(&operand_segments)?;

    // Build pairwise conjunction: (seg0 op0 seg1) && (seg1 op1 seg2) && ...
    let mut conjuncts: Vec<TokenStream> = Vec::new();
    for i in 0..ops.len() {
        let left = &operand_segments[i];
        let right = &operand_segments[i + 1];
        let op_tokens: TokenStream = trees[ops[i].index..ops[i].index + ops[i].token_count]
            .iter()
            .cloned()
            .collect();
        conjuncts.push(quote!((#left #op_tokens #right)));
    }

    conjuncts
        .into_iter()
        .reduce(|acc, next| quote!(#acc && #next))
        .ok_or_else(|| {
            syn::Error::new(
                Span::call_site(),
                "internal: empty conjuncts in chained comparison",
            )
        })
}

fn reject_mixed_explicit_chain_operand_types(segments: &[TokenStream]) -> syn::Result<()> {
    let mut chain_type = None;
    for segment in segments {
        let Some(segment_type) = explicit_chain_operand_type(segment.clone()) else {
            continue;
        };
        match chain_type {
            Some(previous) if previous != segment_type => {
                return Err(syn::Error::new(
                    Span::call_site(),
                    "The verifier does not yet support the following Rust feature: chained inequalities require all elements to have the same type",
                ));
            }
            Some(_) => {}
            None => chain_type = Some(segment_type),
        }
    }
    Ok(())
}

fn explicit_chain_operand_type(tokens: TokenStream) -> Option<ExplicitChainOperandType> {
    let trees: Vec<TokenTree> = tokens.into_iter().collect();
    explicit_chain_operand_type_in_trees(&trees)
}

#[allow(clippy::indexing_slicing)] // recursive scans guard lookahead with get()
fn explicit_chain_operand_type_in_trees(trees: &[TokenTree]) -> Option<ExplicitChainOperandType> {
    let mut found = None;
    for (index, tree) in trees.iter().enumerate() {
        let candidate = match tree {
            TokenTree::Literal(literal) => verus_numeric_literal_type(&literal.to_string()),
            TokenTree::Ident(ident) if ident == "as" => {
                trees.get(index + 1).and_then(|next| match next {
                    TokenTree::Ident(ty) => verus_numeric_type_name(&ty.to_string()),
                    _ => None,
                })
            }
            TokenTree::Group(group) => {
                let nested: Vec<TokenTree> = group.stream().into_iter().collect();
                explicit_chain_operand_type_in_trees(&nested)
            }
            _ => None,
        };
        if let Some(candidate) = candidate {
            match found {
                Some(previous) if previous != candidate => return None,
                Some(_) => {}
                None => found = Some(candidate),
            }
        }
    }
    found
}

fn verus_numeric_literal_type(literal: &str) -> Option<ExplicitChainOperandType> {
    ["real", "int", "nat"]
        .into_iter()
        .find_map(|suffix| {
            literal
                .ends_with(suffix)
                .then(|| verus_numeric_type_name(suffix))
        })
        .flatten()
}

fn verus_numeric_type_name(name: &str) -> Option<ExplicitChainOperandType> {
    match name {
        "int" => Some(ExplicitChainOperandType::Int),
        "nat" => Some(ExplicitChainOperandType::Nat),
        "real" => Some(ExplicitChainOperandType::Real),
        _ => None,
    }
}

/// Top-level rewriter: split at `&&`/`||`/`,` boundaries, process each segment,
/// then rejoin with the original separators.
///
/// A comma is a hard boundary: a comparison chain can never span one (commas
/// only delimit call arguments, tuple/array elements, and the operands of the
/// synthesized `__trust_vc_implies!(P, Q)` marker), so splitting there both
/// prevents the chain detector from joining comparisons across a comma and
/// keeps it from corrupting the implication marker's two operands.
#[allow(clippy::indexing_slicing)] // i bounded by while i < trees.len(); separators[i-1] guarded by i > 0
fn rewrite_chained_tokens(tokens: TokenStream) -> syn::Result<TokenStream> {
    let trees: Vec<TokenTree> = tokens.into_iter().collect();

    // Recursively rewrite inside groups first
    let trees = rewrite_groups(trees)?;

    // Split at top-level && and || boundaries
    let mut segments: Vec<Vec<TokenTree>> = Vec::new();
    let mut separators: Vec<Vec<TokenTree>> = Vec::new();
    let mut current: Vec<TokenTree> = Vec::new();
    let mut i = 0;

    while i < trees.len() {
        if let TokenTree::Punct(p) = &trees[i] {
            if (p.as_char() == '&' || p.as_char() == '|') && p.spacing() == Spacing::Joint {
                if let Some(TokenTree::Punct(next)) = trees.get(i + 1) {
                    if next.as_char() == p.as_char() {
                        // Found && or ||
                        segments.push(std::mem::take(&mut current));
                        separators.push(vec![trees[i].clone(), trees[i + 1].clone()]);
                        i += 2;
                        continue;
                    }
                }
            }
            if p.as_char() == ',' {
                // Found a top-level comma boundary.
                segments.push(std::mem::take(&mut current));
                separators.push(vec![trees[i].clone()]);
                i += 1;
                continue;
            }
        }
        current.push(trees[i].clone());
        i += 1;
    }
    segments.push(current);

    // Process each segment independently
    let mut result = TokenStream::new();
    for (i, segment) in segments.into_iter().enumerate() {
        if i > 0 {
            let sep: TokenStream = separators[i - 1].iter().cloned().collect();
            result.extend(sep);
        }
        let processed = process_comparison_segment(segment)?;
        result.extend(processed);
    }

    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::ToTokens;

    fn normalized(src: &str) -> String {
        parse_expr_str_with_chains(src)
            .unwrap()
            .to_token_stream()
            .to_string()
    }

    fn normalized_err(src: &str) -> String {
        match parse_expr_str_with_chains(src) {
            Err(e) => e.to_string(),
            Ok(_) => panic!("expected error for input: {src}"),
        }
    }

    // -----------------------------------------------------------------
    // `|||` bulleted disjunction (upstream basic.rs test_big_or family)
    // -----------------------------------------------------------------

    #[test]
    fn test_big_or_block_two_bullets() {
        // Upstream test_big_or shape: `assert({ ||| true ||| false })`.
        assert_eq!(
            normalized("{ ||| true ||| false }"),
            "{ (true) || (false) }"
        );
    }

    #[test]
    fn test_big_or_three_bullets_left_associated() {
        assert_eq!(normalized("{ ||| a ||| b ||| c }"), "{ (a) || (b) || (c) }");
    }

    #[test]
    fn test_big_or_single_bullet() {
        // verus-syn BigOr allows a single bullet (`exprs.len() >= 1`).
        assert_eq!(normalized("{ ||| a }"), "{ (a) }");
    }

    #[test]
    fn test_big_or_operand_with_implication_binds_loosest() {
        // Bullets bind loosest: each operand may contain `==>` (upstream
        // bullet operands parse at Precedence::Assign, below Imply).
        assert_eq!(
            normalized("{ ||| a ==> b ||| c }"),
            "{ (__trust_vc_implies ! (a , b)) || (c) }"
        );
    }

    #[test]
    fn test_big_or_leading_at_stream_top_level() {
        // Requires/ensures clause token streams have no surrounding block.
        assert_eq!(normalized("||| a ||| b"), "(a) || (b)");
    }

    #[test]
    fn test_big_or_after_statement_boundary() {
        assert_eq!(
            normalized("{ let x = true; ||| x ||| false }"),
            "{ let x = true ; (x) || (false) }"
        );
    }

    #[test]
    fn test_big_or_nested_in_parens_group() {
        assert_eq!(normalized("({ ||| a ||| b })"), "({ (a) || (b) })");
    }

    #[test]
    fn test_big_or_infix_pipes_untouched() {
        // Non-leading `|||` keeps its plain-Rust reading (`a || |closure…`
        // stays whatever it was); the bullet pass must not fire.
        assert_eq!(normalized("a || b"), "a || b");
        assert_eq!(normalized("f(true, false)"), "f (true , false)");
    }

    #[test]
    fn test_big_or_closure_or_chain_not_rewritten() {
        // `x || (|y| y)` written with spaced pipes: the leading token is not a
        // `|||` triple, so the sequence is untouched.
        assert_eq!(normalized("x || (|y| y)"), "x || (| y | y)");
    }

    #[test]
    fn test_big_or_mixing_with_big_and_fails_closed() {
        let err = normalized_err("{ ||| a &&& b }");
        assert!(
            err.contains("cannot mix `&&&` and `|||`"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn test_big_or_empty_bullet_fails_closed() {
        let err = normalized_err("{ ||| a ||| ||| b }");
        assert!(
            err.contains("requires an expression after each bullet"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn test_big_or_quantifier_operand_scopes_binder_to_its_bullet() {
        // `||| forall|i: int| true ||| i == 0`: the binder `i` must NOT leak
        // into the second bullet (upstream basic.rs
        // test_big_and_syntax_vs_forall pins the analogous `&&&` scoping —
        // rustc E0425). The bullet split runs before the quantifier pass, so
        // the quantifier body is confined to the first operand's group.
        let expr = parse_expr_str_with_chains("{ ||| forall|i: int| true ||| i == 0 }")
            .expect("bulleted quantifier operand should parse");
        let rendered = expr.to_token_stream().to_string();
        assert!(
            rendered.contains("|| (i == 0)"),
            "second bullet must sit outside the quantifier closure: {rendered}"
        );
    }

    #[test]
    fn test_ascending_two_chain() {
        assert_eq!(normalized("a < b < c"), "(a < b) && (b < c)");
    }

    #[test]
    fn test_ascending_mixed_ops() {
        let result = normalized("a <= b < c <= d");
        assert!(result.contains("a <= b"), "got: {result}");
        assert!(result.contains("b < c"), "got: {result}");
        assert!(result.contains("c <= d"), "got: {result}");
    }

    #[test]
    fn test_descending_chain() {
        let result = normalized("hi >= mid > lo");
        assert!(result.contains("hi >= mid"), "got: {result}");
        assert!(result.contains("mid > lo"), "got: {result}");
    }

    #[test]
    fn test_same_type_verus_real_suffix_chain() {
        let result = normalized("0real <= 0real < n as real + 1real < n as real + 2real");
        assert!(result.contains("0real <= 0real"), "got: {result}");
        assert!(
            result.contains("0real < n as real + 1real"),
            "got: {result}"
        );
        assert!(
            result.contains("n as real + 1real < n as real + 2real"),
            "got: {result}"
        );
    }

    #[test]
    fn test_mixed_verus_numeric_suffix_chain_rejected() {
        let err = normalized_err("0real <= 1int <= 2real");
        assert!(
            err.contains("chained inequalities require all elements to have the same type"),
            "Expected same-type error, got: {err}"
        );
    }

    #[test]
    fn test_mixed_direction_rejected() {
        let err = normalized_err("a < b > c");
        assert!(
            err.contains("monotone"),
            "Expected monotone error, got: {err}"
        );
    }

    #[test]
    fn test_equality_not_rewritten() {
        // == chaining is out of scope — syn rejects it and we don't intervene.
        let result = parse_expr_str_with_chains("a == b == c");
        assert!(result.is_err(), "a == b == c should still be rejected");
    }

    #[test]
    fn test_single_comparison_unchanged() {
        assert_eq!(normalized("a < b"), "a < b");
    }

    #[test]
    fn test_non_comparison_unchanged() {
        assert_eq!(normalized("a + b"), "a + b");
    }

    #[test]
    fn test_chain_inside_conjunction() {
        let result = normalized("a < b < c && d > 0");
        assert!(result.contains("a < b"), "got: {result}");
        assert!(result.contains("b < c"), "got: {result}");
        assert!(result.contains("d > 0"), "got: {result}");
    }

    #[test]
    fn test_integer_range() {
        assert_eq!(normalized("1 < x < 10"), "(1 < x) && (x < 10)");
    }

    #[test]
    fn test_index_bound() {
        assert_eq!(normalized("0 <= i < n"), "(0 <= i) && (i < n)");
    }

    #[test]
    fn test_verus_forall_normalized() {
        assert_eq!(
            normalized("forall|i: int| i >= 0"),
            "forall (| i : int | i >= 0)"
        );
    }

    #[test]
    fn test_verus_exists_normalized() {
        assert_eq!(
            normalized("exists|i: nat| i == 0"),
            "exists (| i : nat | i == 0)"
        );
    }

    #[test]
    fn test_verus_choose_single_binder_normalized() {
        assert_eq!(
            normalized("choose|i: int| i >= 0"),
            "choose (| i : int | i >= 0)"
        );
    }

    #[test]
    fn test_verus_choose_nested_rhs_normalized() {
        assert_eq!(
            normalized("w == choose|i: i32| i >= 0i32"),
            "w == choose (| i : i32 | i >= 0i32)"
        );
    }

    #[test]
    fn test_verus_choose_nested_rhs_conjunction_normalized() {
        assert_eq!(
            normalized("w == choose|i: i32| i >= 0i32 && i < 10i32"),
            "w == choose (| i : i32 | i >= 0i32 && i < 10i32)"
        );
    }

    #[test]
    fn test_verus_choose_call_arg_stops_at_comma() {
        assert_eq!(
            normalized("f(choose|i: i32| i >= 0i32, y)"),
            "f (choose (| i : i32 | i >= 0i32) , y)"
        );
    }

    #[test]
    fn test_verus_choose_multi_binder_normalized() {
        assert_eq!(
            normalized("choose|i: int, j: int| i <= j"),
            "choose (| i : int , j : int | i <= j)"
        );
    }

    #[test]
    fn test_verus_choose_nested_multi_binder_normalized() {
        assert_eq!(
            normalized("w == choose|i: int, j: int| i <= j"),
            "w == choose (| i : int , j : int | i <= j)"
        );
    }

    #[test]
    fn test_choose_tuple_call_rewrites_to_choose() {
        assert_eq!(
            normalized("choose_tuple::<(nat, nat), _>(|m: nat, n: nat| m <= n)"),
            "choose (| m : nat , n : nat | m <= n)"
        );
    }

    #[test]
    fn test_verus_nested_quantifiers_normalized() {
        assert_eq!(
            normalized("forall|i: int| exists|j: int| i <= j"),
            "forall (| i : int | exists (| j : int | i <= j))"
        );
    }

    #[test]
    fn test_verus_binder_body_chain_normalized() {
        let result = normalized("forall|i: int| 0 <= i < 10");
        assert!(
            result.contains("forall (| i : int |"),
            "expected forall closure, got: {result}"
        );
        assert!(result.contains("0 <= i"), "got: {result}");
        assert!(result.contains("i < 10"), "got: {result}");
    }

    #[test]
    fn test_verus_result_is_ok_normalized() {
        assert_eq!(
            normalized("res is Ok").replace(' ', ""),
            "(match(res){Ok{..}=>true,_=>false})"
        );
    }

    #[test]
    fn test_verus_result_is_err_normalized_in_conjunction() {
        assert_eq!(
            normalized("ready && res is Err").replace(' ', ""),
            "ready&&(match(res){Err{..}=>true,_=>false})"
        );
    }

    #[test]
    fn test_verus_variant_receiver_stops_after_binary_operator() {
        let compact = normalized("flag == res is Ok").replace(' ', "");
        assert_eq!(compact, "flag==(match(res){Ok{..}=>true,_=>false})");

        let bitand = normalized("mask & value is A").replace(' ', "");
        assert_eq!(bitand, "mask&(match(value){A{..}=>true,_=>false})");

        let prefixed_rhs = normalized("mask & &value is A").replace(' ', "");
        assert_eq!(prefixed_rhs, "mask&(match(&value){A{..}=>true,_=>false})");
    }

    #[test]
    fn test_verus_variant_receiver_includes_preceding_cast() {
        let compact = normalized("value as E is A").replace(' ', "");
        assert_eq!(compact, "(match(valueasE){A{..}=>true,_=>false})");
    }

    #[test]
    fn test_verus_projection_receiver_stops_after_binary_operator() {
        let compact = normalized("expected == res->Ok_0").replace(' ', "");
        assert_eq!(
            compact,
            "expected==::trust_vc_core::__trust_vc_field_proj_x4f6b5f30(res)"
        );

        let product = normalized("factor * res->Ok_0").replace(' ', "");
        assert_eq!(
            product,
            "factor*::trust_vc_core::__trust_vc_field_proj_x4f6b5f30(res)"
        );
    }

    #[test]
    fn test_verus_has_uses_unary_rhs_precedence() {
        // Upstream verus-syn constructs ExprHas with `rhs = unary_expr(...)`.
        // Comparisons therefore remain outside membership on either side.
        let rhs = normalized("s has x == flag").replace(' ', "");
        assert_eq!(rhs, "((s).contains(x))==flag");

        let lhs = normalized("flag == s has x").replace(' ', "");
        assert_eq!(lhs, "flag==((s).contains(x))");
    }

    #[test]
    fn test_verus_has_parenthesized_and_unary_elements_stay_inside() {
        let parenthesized = normalized("s has (x == flag)").replace(' ', "");
        assert_eq!(parenthesized, "((s).contains((x==flag)))");

        let unary = normalized("s has -x == flag").replace(' ', "");
        assert_eq!(unary, "((s).contains(-x))==flag");
    }

    #[test]
    fn test_verus_postfix_receivers_stop_after_implication() {
        let membership = normalized("premise ==> s has x").replace(' ', "");
        assert_eq!(membership, "__trust_vc_implies!(premise,((s).contains(x)))");

        let projection = normalized("premise ==> res->Ok_0 == expected").replace(' ', "");
        assert_eq!(
            projection,
            "__trust_vc_implies!(premise,::trust_vc_core::__trust_vc_field_proj_x4f6b5f30(res)==expected)"
        );
    }

    #[test]
    fn test_verus_projection_chains_retain_the_lowered_receiver() {
        let compact = normalized("value->A_0->Some_0 == expected").replace(' ', "");
        assert_eq!(
            compact,
            "::trust_vc_core::__trust_vc_field_proj_x536f6d655f30(\
             ::trust_vc_core::__trust_vc_field_proj_x415f30(value))==expected"
                .replace(' ', "")
        );

        let feeds_variant_test = normalized("value->A_0 is Some").replace(' ', "");
        assert!(
            feeds_variant_test.contains("__trust_vc_field_proj_x415f30(value)"),
            "first projection must remain the `is` receiver: {feeds_variant_test}"
        );
    }

    #[test]
    fn test_verus_matches_binding_scopes_through_and_only() {
        let compact = normalized("value matches A(x) && x == 5 || fallback").replace(' ', "");
        assert_eq!(compact, "(match(value){A(x)=>{x==5},_=>false})||fallback");

        let reverse_implies =
            normalized("value matches A(x) && x == 5 <== fallback").replace(' ', "");
        assert!(
            reverse_implies
                .contains("__trust_vc_implies!(fallback,(match(value){A(x)=>{x==5},_=>false}))"),
            "reverse implication must remain outside the pattern-binding scope: {reverse_implies}"
        );
    }

    #[test]
    fn test_verus_matches_binding_scopes_through_big_and_tail() {
        let compact = normalized("{ &&& value matches A(x) &&& x == 5 }").replace(' ', "");
        assert_eq!(
            compact, "{&&&(match(value){A(x)=>{x==5},_=>false})}",
            "the following `&&&` bullet must be consumed whole inside the pattern scope"
        );
    }

    #[test]
    fn test_rust_method_named_has_is_not_rewritten() {
        assert_eq!(normalized("holder.has(x)"), "holder . has (x)");
    }

    #[test]
    fn test_verus_result_err_projection_normalized() {
        assert_eq!(
            normalized("res->Err_0 == expected"),
            ":: trust_vc_core :: __trust_vc_field_proj_x4572725f30 (res) == expected"
        );
    }

    #[test]
    fn test_verus_result_projection_after_local_binding_normalized() {
        let result = normalized(
            "{ let res = Result::<i8, i32>::Err(-1i32); res is Err && res->Err_0 == -1i32 }",
        );
        assert!(
            result
                .replace(' ', "")
                .contains("match(res){Err{..}=>true,_=>false}"),
            "got: {result}"
        );
        assert!(
            result.contains(":: trust_vc_core :: __trust_vc_field_proj_x4572725f30 (res)"),
            "got: {result}"
        );
    }

    #[test]
    fn test_implies_basic_lowers_to_marker() {
        // `a ==> b` => `__trust_vc_implies !(a, b)`.
        let result = normalized("a ==> b");
        let compact = result.replace(' ', "");
        assert!(
            compact.contains("__trust_vc_implies!(a,b)"),
            "got: {result}"
        );
    }

    #[test]
    fn test_implies_lowest_precedence_over_and_or() {
        // Implication binds looser than `&&`/`||`, so the whole conjunction is
        // the premise and the whole disjunction is the conclusion.
        let result = normalized("p && q ==> r || s");
        let compact = result.replace(' ', "");
        assert!(
            compact.contains("__trust_vc_implies!(p&&q,r||s)"),
            "got: {result}"
        );
    }

    #[test]
    fn test_implies_right_associative() {
        // `a ==> b ==> c` parses as `a ==> (b ==> c)`.
        let result = normalized("a ==> b ==> c");
        let compact = result.replace(' ', "");
        assert!(
            compact.contains("__trust_vc_implies!(a,__trust_vc_implies!(b,c))"),
            "got: {result}"
        );
    }

    #[test]
    fn test_implies_premise_chain_is_normalized_at_lowering() {
        // The premise carries a comparison chain. The `==>` rewrite keeps the
        // chain as raw tokens inside the marker; the chain is normalized when
        // the lowering re-parses the operand. Here we only assert the marker
        // wraps the full chain as the premise.
        let result = normalized("0 <= i < n ==> q");
        let compact = result.replace(' ', "");
        assert!(
            compact.contains("__trust_vc_implies!(0<=i<n,q)"),
            "got: {result}"
        );
    }

    #[test]
    fn test_implies_inside_quantifier_body_is_bound_by_quantifier() {
        // `==>` inside a `forall|..|` body must stay inside the synthesized
        // closure (bound by the quantifier), not split the quantifier itself.
        let result = normalized("forall|i: int| i >= 0 ==> f(i) >= 0");
        let compact = result.replace(' ', "");
        assert!(
            compact.starts_with("forall(|i:int|"),
            "quantifier must wrap the implication, got: {result}"
        );
        assert!(
            compact.contains("__trust_vc_implies!(i>=0,f(i)>=0)"),
            "got: {result}"
        );
    }

    #[test]
    fn test_implies_in_parens_recurses_into_group() {
        let result = normalized("(a ==> b) && c");
        let compact = result.replace(' ', "");
        assert!(
            compact.contains("(__trust_vc_implies!(a,b))&&c"),
            "got: {result}"
        );
    }

    #[test]
    fn test_fat_arrow_is_not_treated_as_implies() {
        // `=>` (match/closure/map! fat arrow) must be left alone: it is a
        // two-punct operator (`=` then `>`), not the three-punct `==>`.
        let result = normalized("map![1u8 => 2u8]");
        assert!(
            !result.contains("__trust_vc_implies"),
            "fat arrow must not be rewritten as implication, got: {result}"
        );
    }

    #[test]
    fn test_implies_missing_conclusion_is_rejected() {
        let err = normalized_err("a ==> ");
        assert!(
            err.contains("conclusion"),
            "expected missing-conclusion diagnostic, got: {err}"
        );
    }

    #[test]
    fn test_explies_basic_normalizes_to_reverse_implies() {
        // `a <== b` is reverse implication: `b ==> a`. The marker keeps forward
        // form, so premise = b (the RHS), conclusion = a (the LHS).
        let result = normalized("a <== b");
        let compact = result.replace(' ', "");
        assert!(
            compact.contains("__trust_vc_implies!(b,a)"),
            "got: {result}"
        );
    }

    #[test]
    fn test_explies_lowest_precedence_over_and_or() {
        // `<==` binds looser than `&&`/`||`. `p && q <== r || s` is
        // `(r || s) ==> (p && q)`.
        let result = normalized("p && q <== r || s");
        let compact = result.replace(' ', "");
        assert!(
            compact.contains("__trust_vc_implies!(r||s,p&&q)"),
            "got: {result}"
        );
    }

    #[test]
    fn test_explies_in_parens_recurses_into_group() {
        let result = normalized("(a <== b) && c");
        let compact = result.replace(' ', "");
        assert!(
            compact.contains("(__trust_vc_implies!(b,a))&&c"),
            "got: {result}"
        );
    }

    #[test]
    fn test_iff_basic_lowers_to_marker() {
        // `a <==> b` => `__trust_vc_iff!(a, b)`.
        let result = normalized("a <==> b");
        let compact = result.replace(' ', "");
        assert!(compact.contains("__trust_vc_iff!(a,b)"), "got: {result}");
        // The `<==>` suffix must not also be mistaken for a bare `==>`.
        assert!(
            !compact.contains("__trust_vc_implies"),
            "equivalence must not produce an implication marker, got: {result}"
        );
    }

    #[test]
    fn test_iff_is_looser_than_implies() {
        // `<==>` is looser than `==>`: `a ==> b <==> c` is `(a ==> b) <==> c`.
        let result = normalized("a ==> b <==> c");
        let compact = result.replace(' ', "");
        assert!(
            compact.contains("__trust_vc_iff!(__trust_vc_implies!(a,b),c)"),
            "got: {result}"
        );
    }

    #[test]
    fn test_iff_with_comparison_operands_lowers_cleanly() {
        // Mirrors the upstream `test_eq_ineq2` shape: comparison operands on
        // both sides of `<==>` survive into the marker for later normalization.
        let result = normalized("a < b <==> (a as i64) < b");
        let compact = result.replace(' ', "");
        assert!(
            compact.contains("__trust_vc_iff!(a<b,(aasi64)<b)"),
            "got: {result}"
        );
        assert!(
            !compact.contains("__trust_vc_implies"),
            "equivalence must not emit an implication marker, got: {result}"
        );
    }

    #[test]
    fn test_iff_in_parens_recurses_into_group() {
        let result = normalized("(a <==> b) && c");
        let compact = result.replace(' ', "");
        assert!(
            compact.contains("(__trust_vc_iff!(a,b))&&c"),
            "got: {result}"
        );
    }

    #[test]
    fn test_iff_missing_rhs_is_rejected() {
        let err = normalized_err("a <==> ");
        assert!(
            err.contains("equivalence"),
            "expected equivalence diagnostic, got: {err}"
        );
    }

    #[test]
    fn test_le_is_not_treated_as_explies() {
        // `<=` (two-punct comparison) must not be confused with `<==`.
        let result = normalized("a <= b");
        assert!(
            !result.contains("__trust_vc_implies") && !result.contains("__trust_vc_iff"),
            "comparison `<=` must not be rewritten as a connective, got: {result}"
        );
    }

    #[test]
    fn test_nested_macro_with_turbofish_generics_is_not_rewritten() {
        let expr = parse_expr_str_with_chains(
            "trust_vc::ext_eq!(trust_vc_types::Seq::<i32>::empty().push(10), trust_vc_types::Seq::<i32>::empty().push(20))",
        )
        .unwrap();
        let syn::Expr::Macro(mac) = expr else {
            panic!("expected nested macro expression");
        };
        assert_eq!(
            mac.mac
                .path
                .segments
                .last()
                .expect("macro path segment")
                .ident,
            "ext_eq"
        );
        let tokens = mac.mac.tokens.to_string();
        assert!(tokens.contains("Seq"), "got: {tokens}");
        assert!(!tokens.contains("&&"), "unexpected rewrite: {tokens}");
    }

    #[test]
    fn test_nested_macro_with_map_generics_is_not_rewritten() {
        let expr = parse_expr_str_with_chains(
            "trust_vc::ext_eq!(trust_vc_types::Map::<u64, i32>::empty().insert(1, 10), trust_vc_types::Map::<u64, i32>::empty().insert(1, 20))",
        )
        .unwrap();
        let syn::Expr::Macro(mac) = expr else {
            panic!("expected nested macro expression");
        };
        let tokens = mac.mac.tokens.to_string();
        assert!(tokens.contains("Map"), "got: {tokens}");
        assert!(!tokens.contains("&&"), "unexpected rewrite: {tokens}");
    }

    // ---- Verus equality operators (`=~=`, `===`) ----

    #[test]
    fn test_ext_eq_operator_parses_without_error() {
        // The whole point: `=~=` used to be rejected by `syn` outright. It must
        // now parse (lowering to `ext_eq!`). This mirrors `sets.rs` `test1`'s
        // `pos1 =~= pos2`.
        assert!(
            parse_expr_str_with_chains("pos1 =~= pos2").is_ok(),
            "`=~=` must parse"
        );
    }

    #[test]
    fn test_ext_eq_operator_lowers_to_ext_eq_macro() {
        let result = normalized("a =~= b");
        let compact = result.replace(' ', "");
        assert!(compact.contains("ext_eq!(a,b)"), "got: {result}");
        // Must be the extensional surface, never the raw/strict one.
        assert!(
            !compact.contains("strict_eq!"),
            "`=~=` must lower to ext_eq, not strict_eq, got: {result}"
        );
    }

    #[test]
    fn test_strict_eq_operator_lowers_to_strict_eq_macro() {
        let result = normalized("a === b");
        let compact = result.replace(' ', "");
        assert!(compact.contains("strict_eq!(a,b)"), "got: {result}");
        // Strict equality must NOT be promoted to the extensional surface
        // (that would be unsound over-proving).
        assert!(
            !compact.contains("ext_eq!"),
            "`===` must lower to strict_eq, not ext_eq, got: {result}"
        );
    }

    #[test]
    fn test_plain_eq_is_not_treated_as_strict_eq() {
        // `==` (two `=`, spec equality) must survive untouched into `syn`.
        let result = normalized("a == b");
        assert!(
            !result.contains("strict_eq") && !result.contains("ext_eq"),
            "`==` must not be rewritten to an equality marker, got: {result}"
        );
    }

    #[test]
    fn test_implies_arrow_is_not_treated_as_strict_eq() {
        // `==>` (`=` `=` `>`) must lower to the implication marker, never the
        // `===` strict-equality marker.
        let result = normalized("a ==> b");
        let compact = result.replace(' ', "");
        assert!(
            compact.contains("__trust_vc_implies!(a,b)"),
            "got: {result}"
        );
        assert!(!compact.contains("strict_eq"), "got: {result}");
    }

    #[test]
    fn test_ext_eq_operator_binds_tighter_than_and() {
        // `a =~= b && c =~= d` is `(a =~= b) && (c =~= d)`: each equality lives
        // inside its own `&&` segment.
        let result = normalized("a =~= b && c =~= d");
        let compact = result.replace(' ', "");
        assert!(
            compact.contains("ext_eq!(a,b)&&ext_eq!(c,d)"),
            "got: {result}"
        );
    }

    #[test]
    fn test_ext_eq_operator_binds_tighter_than_implies() {
        // `a =~= b ==> c` is `(a =~= b) ==> c`: the connective splits first
        // (it is looser), then this pass rewrites the premise's `=~=`.
        let result = normalized("a =~= b ==> c");
        let compact = result.replace(' ', "");
        assert!(
            compact.contains("__trust_vc_implies!(ext_eq!(a,b),c)"),
            "got: {result}"
        );
    }

    #[test]
    fn test_ext_eq_operator_in_parens_recurses_into_group() {
        let result = normalized("(a =~= b) && c");
        let compact = result.replace(' ', "");
        assert!(compact.contains("(ext_eq!(a,b))&&c"), "got: {result}");
    }

    #[test]
    fn test_ext_eq_operator_inside_quantifier_body_is_bound_by_quantifier() {
        // `=~=` inside a `forall|..|` body must stay inside the synthesized
        // closure, with the binder excluded from the left operand.
        let result = normalized("forall|i: int| a[i] =~= b[i]");
        let compact = result.replace(' ', "");
        assert!(
            compact.starts_with("forall(|i:int|"),
            "quantifier must wrap the equality, got: {result}"
        );
        assert!(compact.contains("ext_eq!(a[i],b[i])"), "got: {result}");
    }

    #[test]
    fn test_ext_eq_operator_missing_rhs_is_rejected() {
        let err = normalized_err("a =~= ");
        assert!(
            err.contains("right-hand side"),
            "expected missing-rhs diagnostic, got: {err}"
        );
    }

    #[test]
    fn test_ext_eq_operator_preserves_turbofish_commas() {
        // A turbofish comma (`Map::<u8, bool>`) lives at the same token level as
        // the operator (angle brackets are not delimiter groups), yet it must not
        // be treated as an operand boundary — both type args stay in the operand.
        let result = normalized("Map::<u8, bool>::empty() =~= Map::<u8, bool>::empty()");
        let compact = result.replace(' ', "");
        assert!(
            compact.contains("ext_eq!(Map::<u8,bool>::empty(),Map::<u8,bool>::empty())"),
            "turbofish commas must be preserved inside operands, got: {result}"
        );
    }

    #[test]
    fn test_ext_eq_operator_in_call_arg_splits_at_real_comma() {
        // A real (depth-0) comma separating call arguments *is* a boundary, so
        // only the first argument's `=~=` is rewritten.
        let result = normalized("f(a =~= b, c)");
        let compact = result.replace(' ', "");
        assert!(compact.contains("f(ext_eq!(a,b),c)"), "got: {result}");
    }
}
