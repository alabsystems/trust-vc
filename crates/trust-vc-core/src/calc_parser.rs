// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Parser for `calc!` calculational proof blocks.
//!
//! Parses the calc syntax into a structured representation of expressions,
//! operators, and proof blocks that the proc-macro crate desugars into
//! sequential `assert_by!` calls.
//!
//! Part of #2413.

use proc_macro2::{Punct, Spacing, TokenStream, TokenTree};
use quote::quote;
use syn::parse::discouraged::Speculative;
use syn::parse::{Parse, ParseStream};
use syn::{Expr, Token};

/// Supported calc! operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CalcOp {
    Eq, // ==
    Lt, // <
    Le, // <=
    Gt, // >
    Ge, // >=
    // Logical connectives (Verus calc relations). Transitive in their own right
    // (`a ==> b`, `b ==> c` ⊢ `a ==> c`; likewise `<==>`), and NEVER mixable with
    // the ordering relations above.
    Implies, // ==>
    Iff,     // <==>
}

impl CalcOp {
    /// Returns the token representation for code generation. For the logical
    /// connectives this reproduces the exact `==>` / `<==>` source form, which
    /// the assertion path rewrites to `__trust_vc_implies!` / `__trust_vc_iff!`
    /// (see `chained_comparisons::rewrite_verus_connectives_tokens`).
    pub fn to_tokens(self) -> TokenStream {
        match self {
            CalcOp::Eq => quote! { == },
            CalcOp::Lt => quote! { < },
            CalcOp::Le => quote! { <= },
            CalcOp::Gt => quote! { > },
            CalcOp::Ge => quote! { >= },
            // Build `==>` / `<==>` with EXPLICIT Joint spacing on every leading
            // punct. `quote! { ==> }` emits `=`(Joint) `=`(Alone) `>`, and the
            // connective rewriter (`chained_comparisons::is_arrow_suffix`)
            // requires the `=` immediately before `>` to be Joint — otherwise
            // the arrow is not recognized and the condition fails to lower.
            CalcOp::Implies => [
                TokenTree::Punct(Punct::new('=', Spacing::Joint)),
                TokenTree::Punct(Punct::new('=', Spacing::Joint)),
                TokenTree::Punct(Punct::new('>', Spacing::Alone)),
            ]
            .into_iter()
            .collect(),
            CalcOp::Iff => [
                TokenTree::Punct(Punct::new('<', Spacing::Joint)),
                TokenTree::Punct(Punct::new('=', Spacing::Joint)),
                TokenTree::Punct(Punct::new('=', Spacing::Joint)),
                TokenTree::Punct(Punct::new('>', Spacing::Alone)),
            ]
            .into_iter()
            .collect(),
        }
    }

    /// Returns the source spelling used in diagnostics.
    pub fn as_str(self) -> &'static str {
        match self {
            CalcOp::Eq => "==",
            CalcOp::Lt => "<",
            CalcOp::Le => "<=",
            CalcOp::Gt => ">",
            CalcOp::Ge => ">=",
            CalcOp::Implies => "==>",
            CalcOp::Iff => "<==>",
        }
    }

    /// Returns true if this operator goes in the "less-than" direction.
    fn is_ascending(self) -> bool {
        matches!(self, CalcOp::Lt | CalcOp::Le)
    }

    /// Returns true if this operator goes in the "greater-than" direction.
    fn is_descending(self) -> bool {
        matches!(self, CalcOp::Gt | CalcOp::Ge)
    }

    /// Returns true for the logical connectives (`==>`, `<==>`). These form
    /// their own transitivity group and are never compatible with the ordering
    /// relations.
    fn is_logical(self) -> bool {
        matches!(self, CalcOp::Implies | CalcOp::Iff)
    }
}

/// A parsed calc! block.
pub struct CalcBlock {
    /// Optional Verus-style overall relation header, e.g. `(<=)`.
    pub overall_op_hint: Option<CalcOp>,
    /// The chain of expressions (n+1 expressions for n steps).
    pub expressions: Vec<Expr>,
    /// The chain of operators (n operators for n steps).
    pub operators: Vec<CalcOp>,
    /// The chain of proof blocks (n blocks for n steps).
    pub proof_blocks: Vec<TokenStream>,
}

/// Computes the overall transitive operator from a chain.
///
/// Returns `None` if the chain contains incompatible operators
/// (e.g., `<=` mixed with `>=`).
pub fn transitive_op(ops: &[CalcOp]) -> Option<CalcOp> {
    if ops.is_empty() {
        return None;
    }
    if let [op] = ops {
        return Some(*op);
    }

    // Logical connectives form their own transitivity group: `<==>` is to `==>`
    // as `==` is to `<=` — an all-`<==>` chain concludes `<==>`, any `==>` step
    // weakens the overall relation to `==>`. Mixing a logical connective with an
    // ordering relation is incompatible (fail-closed to `None`).
    let has_logical = ops.iter().any(|op| op.is_logical());
    if has_logical {
        if !ops.iter().all(|op| op.is_logical()) {
            return None;
        }
        if ops.iter().all(|op| matches!(op, CalcOp::Iff)) {
            return Some(CalcOp::Iff);
        }
        return Some(CalcOp::Implies);
    }

    let has_ascending = ops.iter().any(|op| op.is_ascending());
    let has_descending = ops.iter().any(|op| op.is_descending());

    // Incompatible: mixing ascending and descending directions.
    if has_ascending && has_descending {
        return None;
    }

    let has_strict = ops.iter().any(|op| matches!(op, CalcOp::Lt | CalcOp::Gt));
    let has_eq = ops.iter().any(|op| matches!(op, CalcOp::Eq));

    if has_descending {
        // All descending (Gt, Ge, Eq)
        if has_strict {
            Some(CalcOp::Gt)
        } else if !has_eq {
            Some(CalcOp::Ge)
        } else {
            // Ge or Eq only → Ge overall (Eq + Ge = Ge)
            if ops.iter().any(|op| matches!(op, CalcOp::Ge)) {
                Some(CalcOp::Ge)
            } else {
                Some(CalcOp::Eq) // all Eq
            }
        }
    } else if has_ascending {
        // All ascending (Lt, Le, Eq)
        if has_strict {
            Some(CalcOp::Lt)
        } else if !has_eq {
            Some(CalcOp::Le)
        } else {
            // Le or Eq only → Le overall (Eq + Le = Le)
            if ops.iter().any(|op| matches!(op, CalcOp::Le)) {
                Some(CalcOp::Le)
            } else {
                Some(CalcOp::Eq) // all Eq
            }
        }
    } else {
        // No ascending, no descending → only Eq
        Some(CalcOp::Eq)
    }
}

/// Parses `calc! { expr; op { block } expr; ... }` into a CalcBlock.
pub fn parse_calc(tokens: TokenStream) -> syn::Result<CalcBlock> {
    syn::parse2::<CalcBlockParser>(tokens).map(|p| p.block)
}

/// Internal parser wrapper.
struct CalcBlockParser {
    block: CalcBlock,
}

impl Parse for CalcBlockParser {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let mut expressions = Vec::new();
        let mut operators = Vec::new();
        let mut proof_blocks = Vec::new();
        let overall_op_hint = parse_optional_parenthesized_calc_op(input)?;

        // Parse first expression + semicolon
        let first_expr: Expr = input.parse()?;
        input.parse::<Token![;]>()?;
        expressions.push(first_expr);

        // Loop: parse operator, optional { block }, expression + semicolon.
        // When a Verus-style header is present, later steps may omit the
        // operator and inherit the header relation:
        // `calc! { (==) a; { proof } b; { proof } c; }`.
        while !input.is_empty() {
            let op = parse_calc_step_op(input, overall_op_hint)?;
            operators.push(op);

            // Optional proof block: if next token is `{`, parse as a block
            let proof = if input.peek(syn::token::Brace) {
                let content;
                syn::braced!(content in input);
                content.parse::<TokenStream>()?
            } else {
                TokenStream::new()
            };
            proof_blocks.push(proof);

            let expr: Expr = input.parse()?;
            input.parse::<Token![;]>()?;
            expressions.push(expr);
        }

        if operators.is_empty() {
            return Err(syn::Error::new(
                proc_macro2::Span::call_site(),
                "calc! requires at least one step (two expressions with an operator)",
            ));
        }

        if let Some(overall_op) = overall_op_hint {
            validate_ops_against_header(overall_op, &operators)?;
        } else if operators.len() > 1 && transitive_op(&operators).is_none() {
            return Err(incompatible_ops_error());
        }

        Ok(CalcBlockParser {
            block: CalcBlock {
                overall_op_hint,
                expressions,
                operators,
                proof_blocks,
            },
        })
    }
}

fn parse_optional_parenthesized_calc_op(input: ParseStream<'_>) -> syn::Result<Option<CalcOp>> {
    let fork = input.fork();
    let Some(op) = parse_parenthesized_calc_op(&fork)? else {
        return Ok(None);
    };
    input.advance_to(&fork);
    Ok(Some(op))
}

fn parse_calc_op_or_parenthesized(input: ParseStream<'_>) -> syn::Result<CalcOp> {
    if let Some(op) = parse_parenthesized_calc_op(input)? {
        return Ok(op);
    }
    parse_calc_op(input)
}

fn parse_calc_step_op(
    input: ParseStream<'_>,
    overall_op_hint: Option<CalcOp>,
) -> syn::Result<CalcOp> {
    let fork = input.fork();
    if let Ok(op) = parse_calc_op_or_parenthesized(&fork) {
        input.advance_to(&fork);
        return Ok(op);
    }

    overall_op_hint.ok_or_else(|| input.error("expected a calc operator: ==, <, <=, >, >="))
}

fn parse_parenthesized_calc_op(input: ParseStream<'_>) -> syn::Result<Option<CalcOp>> {
    if !input.peek(syn::token::Paren) {
        return Ok(None);
    }
    let fork = input.fork();
    let content;
    syn::parenthesized!(content in fork);
    let Ok(op) = parse_calc_op(&content) else {
        return Ok(None);
    };
    if !content.is_empty() {
        return Ok(None);
    }
    input.advance_to(&fork);
    Ok(Some(op))
}

fn validate_ops_against_header(header: CalcOp, ops: &[CalcOp]) -> syn::Result<()> {
    for op in ops {
        if !calc_op_compatible_with_header(header, *op) {
            return Err(syn::Error::new(
                proc_macro2::Span::call_site(),
                format!(
                    "inconsistent relation `{}` with `{}`",
                    op.as_str(),
                    header.as_str()
                ),
            ));
        }
    }
    Ok(())
}

fn calc_op_compatible_with_header(header: CalcOp, op: CalcOp) -> bool {
    match header {
        CalcOp::Eq => op == CalcOp::Eq,
        CalcOp::Le | CalcOp::Lt => matches!(op, CalcOp::Eq | CalcOp::Le | CalcOp::Lt),
        CalcOp::Ge | CalcOp::Gt => matches!(op, CalcOp::Eq | CalcOp::Ge | CalcOp::Gt),
        // A `==>` chain admits both `==>` and (stronger) `<==>` steps; a `<==>`
        // chain admits only `<==>` steps. Neither mixes with ordering relations.
        CalcOp::Implies => matches!(op, CalcOp::Implies | CalcOp::Iff),
        CalcOp::Iff => op == CalcOp::Iff,
    }
}

fn incompatible_ops_error() -> syn::Error {
    syn::Error::new(
        proc_macro2::Span::call_site(),
        "calc! operators are incompatible: cannot mix ascending (<, <=) with descending (>, >=)",
    )
}

/// Peeks the raw punct sequence for a logical connective without consuming.
///
/// `syn`'s `peek2` does not skip a compound punct token (e.g. it cannot look
/// PAST `==`), so multi-punct connectives must be recognized on the raw cursor:
/// `==>` is `=`(Joint) `=`(Joint) `>`, and `<==>` is `<`(Joint) `=`(Joint)
/// `=`(Joint) `>` — the same spacing contract `chained_comparisons` keys on.
fn peek_arrow_op(input: ParseStream<'_>) -> Option<CalcOp> {
    // Read up to four leading punct chars. In calc OPERATOR position the char
    // sequence is unambiguous — `= = >` is always `==>` and `< = = >` is always
    // `<==>` (no valid calc expression begins with `>`), so match on chars only.
    // Punct SPACING is unreliable here: `quote!` emits `==>` as `=`(Joint)
    // `=`(Alone) `>`, unlike contiguous source, so a Joint contract would miss it.
    let mut chars: Vec<char> = Vec::new();
    let mut cursor = input.cursor();
    while chars.len() < 4 {
        match cursor.punct() {
            Some((punct, next)) => {
                chars.push(punct.as_char());
                cursor = next;
            }
            None => break,
        }
    }
    if chars.len() >= 4 && chars[..4] == ['<', '=', '=', '>'] {
        Some(CalcOp::Iff)
    } else if chars.len() >= 3 && chars[..3] == ['=', '=', '>'] {
        Some(CalcOp::Implies)
    } else {
        None
    }
}

/// Consumes exactly `n` leading punct tokens, regardless of their Joint/Alone
/// spacing (`syn`'s `Token!` matchers are spacing-sensitive, which is unreliable
/// for `quote!`-emitted connectives — see `peek_arrow_op`).
fn consume_leading_puncts(input: ParseStream<'_>, n: usize) -> syn::Result<()> {
    input.step(|cursor| {
        let mut rest = *cursor;
        for _ in 0..n {
            match rest.punct() {
                Some((_, next)) => rest = next,
                None => return Err(cursor.error("expected calc connective punctuation")),
            }
        }
        Ok(((), rest))
    })
}

/// Parses a calc operator token (`==`, `<`, `<=`, `>`, `>=`, `==>`, `<==>`).
///
/// The logical connectives are matched FIRST (longest match) on the raw cursor
/// and consumed by punct count, so they are not mis-read as the prefix `<=` /
/// `==` operators.
fn parse_calc_op(input: ParseStream<'_>) -> syn::Result<CalcOp> {
    match peek_arrow_op(input) {
        Some(CalcOp::Iff) => {
            consume_leading_puncts(input, 4)?;
            return Ok(CalcOp::Iff);
        }
        Some(CalcOp::Implies) => {
            consume_leading_puncts(input, 3)?;
            return Ok(CalcOp::Implies);
        }
        _ => {}
    }

    if input.peek(Token![==]) {
        input.parse::<Token![==]>()?;
        Ok(CalcOp::Eq)
    } else if input.peek(Token![<=]) {
        input.parse::<Token![<=]>()?;
        Ok(CalcOp::Le)
    } else if input.peek(Token![>=]) {
        input.parse::<Token![>=]>()?;
        Ok(CalcOp::Ge)
    } else if input.peek(Token![<]) {
        input.parse::<Token![<]>()?;
        Ok(CalcOp::Lt)
    } else if input.peek(Token![>]) {
        input.parse::<Token![>]>()?;
        Ok(CalcOp::Gt)
    } else {
        Err(input.error("expected a calc operator: ==, <, <=, >, >=, ==>, <==>"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // === transitive_op unit tests ===

    #[test]
    fn test_transitive_op_all_eq() {
        assert_eq!(transitive_op(&[CalcOp::Eq, CalcOp::Eq]), Some(CalcOp::Eq));
    }

    #[test]
    fn test_transitive_op_eq_le() {
        assert_eq!(transitive_op(&[CalcOp::Eq, CalcOp::Le]), Some(CalcOp::Le));
    }

    #[test]
    fn test_transitive_op_le_eq() {
        assert_eq!(transitive_op(&[CalcOp::Le, CalcOp::Eq]), Some(CalcOp::Le));
    }

    #[test]
    fn test_transitive_op_lt_le() {
        assert_eq!(transitive_op(&[CalcOp::Lt, CalcOp::Le]), Some(CalcOp::Lt));
    }

    #[test]
    fn test_transitive_op_le_lt() {
        assert_eq!(transitive_op(&[CalcOp::Le, CalcOp::Lt]), Some(CalcOp::Lt));
    }

    #[test]
    fn test_transitive_op_eq_lt() {
        assert_eq!(transitive_op(&[CalcOp::Eq, CalcOp::Lt]), Some(CalcOp::Lt));
    }

    #[test]
    fn test_transitive_op_all_le() {
        assert_eq!(
            transitive_op(&[CalcOp::Le, CalcOp::Le, CalcOp::Le]),
            Some(CalcOp::Le)
        );
    }

    #[test]
    fn test_transitive_op_all_ge() {
        assert_eq!(transitive_op(&[CalcOp::Ge, CalcOp::Ge]), Some(CalcOp::Ge));
    }

    #[test]
    fn test_transitive_op_gt_ge() {
        assert_eq!(transitive_op(&[CalcOp::Gt, CalcOp::Ge]), Some(CalcOp::Gt));
    }

    #[test]
    fn test_transitive_op_eq_ge() {
        assert_eq!(transitive_op(&[CalcOp::Eq, CalcOp::Ge]), Some(CalcOp::Ge));
    }

    #[test]
    fn test_transitive_op_incompatible_le_ge() {
        assert_eq!(transitive_op(&[CalcOp::Le, CalcOp::Ge]), None);
    }

    #[test]
    fn test_transitive_op_incompatible_lt_gt() {
        assert_eq!(transitive_op(&[CalcOp::Lt, CalcOp::Gt]), None);
    }

    #[test]
    fn test_transitive_op_incompatible_le_gt() {
        assert_eq!(transitive_op(&[CalcOp::Le, CalcOp::Gt]), None);
    }

    #[test]
    fn test_transitive_op_single() {
        assert_eq!(transitive_op(&[CalcOp::Le]), Some(CalcOp::Le));
        assert_eq!(transitive_op(&[CalcOp::Eq]), Some(CalcOp::Eq));
        assert_eq!(transitive_op(&[CalcOp::Gt]), Some(CalcOp::Gt));
    }

    #[test]
    fn test_transitive_op_empty() {
        assert_eq!(transitive_op(&[]), None);
    }

    // === logical connective (==> / <==>) tests ===

    #[test]
    fn test_transitive_op_all_implies() {
        assert_eq!(
            transitive_op(&[CalcOp::Implies, CalcOp::Implies]),
            Some(CalcOp::Implies)
        );
    }

    #[test]
    fn test_transitive_op_all_iff() {
        assert_eq!(
            transitive_op(&[CalcOp::Iff, CalcOp::Iff]),
            Some(CalcOp::Iff)
        );
    }

    #[test]
    fn test_transitive_op_iff_implies_weakens_to_implies() {
        assert_eq!(
            transitive_op(&[CalcOp::Iff, CalcOp::Implies]),
            Some(CalcOp::Implies)
        );
        assert_eq!(
            transitive_op(&[CalcOp::Implies, CalcOp::Iff]),
            Some(CalcOp::Implies)
        );
    }

    #[test]
    fn test_transitive_op_logical_mixed_with_ordering_is_incompatible() {
        assert_eq!(transitive_op(&[CalcOp::Implies, CalcOp::Le]), None);
        assert_eq!(transitive_op(&[CalcOp::Eq, CalcOp::Iff]), None);
        assert_eq!(transitive_op(&[CalcOp::Iff, CalcOp::Lt]), None);
    }

    #[test]
    fn test_parse_implies_step() {
        let block = parse_calc(quote! { a; ==> {} b; }).unwrap();
        assert_eq!(block.operators, vec![CalcOp::Implies]);
        assert_eq!(block.expressions.len(), 2);
    }

    #[test]
    fn test_parse_iff_step() {
        let block = parse_calc(quote! { a; <==> {} b; }).unwrap();
        assert_eq!(block.operators, vec![CalcOp::Iff]);
        assert_eq!(block.expressions.len(), 2);
    }

    #[test]
    fn test_parse_implies_chain_with_header() {
        let block = parse_calc(quote! { (==>) a; ==> {} b; <==> {} c; }).unwrap();
        assert_eq!(block.overall_op_hint, Some(CalcOp::Implies));
        assert_eq!(block.operators, vec![CalcOp::Implies, CalcOp::Iff]);
    }

    #[test]
    fn test_parse_implies_still_distinguishes_eq_and_le() {
        // `==` and `<=` must NOT be swallowed by the `==>` / `<==>` matchers.
        assert_eq!(
            parse_calc(quote! { a; == {} b; }).unwrap().operators,
            vec![CalcOp::Eq]
        );
        assert_eq!(
            parse_calc(quote! { a; <= {} b; }).unwrap().operators,
            vec![CalcOp::Le]
        );
    }

    #[test]
    fn test_parse_logical_mixed_with_ordering_rejected() {
        let err = parse_calc(quote! { a; ==> {} b; <= {} c; })
            .err()
            .expect("mixing ==> with <= must be rejected")
            .to_string();
        assert!(err.contains("incompatible"), "got: {err}");
    }

    // === parse_calc tests ===

    #[test]
    fn test_parse_single_step_eq() {
        let tokens = quote! { a; == {} b; };
        let block = parse_calc(tokens).unwrap();
        assert_eq!(block.overall_op_hint, None);
        assert_eq!(block.expressions.len(), 2);
        assert_eq!(block.operators.len(), 1);
        assert_eq!(block.operators[0], CalcOp::Eq);
        assert_eq!(block.proof_blocks.len(), 1);
    }

    #[test]
    fn test_parse_verus_style_header_and_parenthesized_steps() {
        let tokens = quote! {
            (<=)
            2i32;
            (==) {} 3i32 - 1i32;
            (<) {} 5i32;
        };
        let block = parse_calc(tokens).unwrap();
        assert_eq!(block.overall_op_hint, Some(CalcOp::Le));
        assert_eq!(block.expressions.len(), 3);
        assert_eq!(block.operators, vec![CalcOp::Eq, CalcOp::Lt]);
        assert_eq!(block.proof_blocks.len(), 2);
    }

    #[test]
    fn test_parse_verus_style_header_defaults_omitted_step_ops() {
        let tokens = quote! {
            (==)
            a;
            { trust_vc::assert!(trust_vc::ext_eq!(a, b.add(c))); } b.add(c);
            { trust_vc::assert!(trust_vc::ext_eq!(b.add(c), d)); } d;
        };
        let block = parse_calc(tokens).unwrap();
        assert_eq!(block.overall_op_hint, Some(CalcOp::Eq));
        assert_eq!(block.expressions.len(), 3);
        assert_eq!(block.operators, vec![CalcOp::Eq, CalcOp::Eq]);
        assert_eq!(block.proof_blocks.len(), 2);
        assert!(block.proof_blocks[0].to_string().contains("ext_eq"));
    }

    #[test]
    fn test_parse_verus_style_header_allows_mixed_explicit_and_omitted_steps() {
        let tokens = quote! {
            (<=)
            2i32;
            (==) {} 3i32 - 1i32;
            {} 5i32;
        };
        let block = parse_calc(tokens).unwrap();
        assert_eq!(block.overall_op_hint, Some(CalcOp::Le));
        assert_eq!(block.operators, vec![CalcOp::Eq, CalcOp::Le]);
    }

    #[test]
    fn test_parse_without_header_rejects_omitted_step_op() {
        let tokens = quote! {
            a;
            { helper(); } b;
        };
        let err_msg = parse_calc(tokens)
            .err()
            .expect("omitted step operator without a header should be rejected")
            .to_string();
        assert!(
            err_msg.contains("expected a calc operator"),
            "error should explain missing operator, got: {}",
            err_msg
        );
    }

    #[test]
    fn test_parse_verus_style_header_rejects_inconsistent_step() {
        let tokens = quote! {
            (<=)
            2i32;
            (==) {} 3i32 - 1i32;
            (>) {} 1i32;
            (<=) {} 5i32;
        };
        let err_msg = parse_calc(tokens)
            .err()
            .expect("inconsistent header relation should be rejected")
            .to_string();
        assert!(
            err_msg.contains("inconsistent relation `>` with `<=`"),
            "error should match the Verus calc diagnostic, got: {}",
            err_msg
        );
    }

    #[test]
    fn test_parse_verus_style_header_rejects_inconsistent_explicit_step_with_omitted_tail() {
        let tokens = quote! {
            (<=)
            2i32;
            (==) {} 3i32 - 1i32;
            (>) {} 1i32;
            {} 5i32;
        };
        let err_msg = parse_calc(tokens)
            .err()
            .expect("inconsistent explicit relation should be rejected")
            .to_string();
        assert!(
            err_msg.contains("inconsistent relation `>` with `<=`"),
            "error should match the Verus calc diagnostic, got: {}",
            err_msg
        );
    }

    #[test]
    fn test_parse_two_step_mixed() {
        let tokens = quote! { a; == {} b; <= {} c; };
        let block = parse_calc(tokens).unwrap();
        assert_eq!(block.expressions.len(), 3);
        assert_eq!(block.operators.len(), 2);
        assert_eq!(block.operators[0], CalcOp::Eq);
        assert_eq!(block.operators[1], CalcOp::Le);
        assert_eq!(block.proof_blocks.len(), 2);
    }

    #[test]
    fn test_parse_with_nonempty_proof_block() {
        let tokens = quote! { a; == { helper_lemma(); } b; };
        let block = parse_calc(tokens).unwrap();
        assert_eq!(block.operators[0], CalcOp::Eq);
        let proof_str = block.proof_blocks[0].to_string();
        assert!(
            proof_str.contains("helper_lemma"),
            "proof block should contain helper_lemma, got: {}",
            proof_str
        );
    }

    #[test]
    fn test_parse_incompatible_operators_rejected() {
        let tokens = quote! { a; <= {} b; >= {} c; };
        let err_msg = parse_calc(tokens)
            .err()
            .expect("incompatible operators should be rejected")
            .to_string();
        assert!(
            err_msg.contains("incompatible"),
            "error should mention incompatible, got: {}",
            err_msg
        );
    }

    #[test]
    fn test_parse_single_expression_rejected() {
        let tokens = quote! { a; };
        let err_msg = parse_calc(tokens)
            .err()
            .expect("single expression should be rejected")
            .to_string();
        assert!(
            err_msg.contains("at least"),
            "error should explain minimum step requirement, got: {}",
            err_msg
        );
    }

    #[test]
    fn test_parse_all_operators() {
        for (tok, expected) in [
            (quote! { a; < {} b; }, CalcOp::Lt),
            (quote! { a; <= {} b; }, CalcOp::Le),
            (quote! { a; > {} b; }, CalcOp::Gt),
            (quote! { a; >= {} b; }, CalcOp::Ge),
            (quote! { a; == {} b; }, CalcOp::Eq),
        ] {
            let block = parse_calc(tok).unwrap();
            assert_eq!(block.operators[0], expected);
        }
    }

    #[test]
    fn test_parse_complex_expressions() {
        let tokens = quote! { x + 1; == {} y * 2; <= {} z - 3; };
        let block = parse_calc(tokens).unwrap();
        assert_eq!(block.expressions.len(), 3);
        assert_eq!(block.operators[0], CalcOp::Eq);
        assert_eq!(block.operators[1], CalcOp::Le);
    }

    #[test]
    fn test_parse_three_step_chain() {
        let tokens = quote! { a; <= {} b; <= {} c; <= {} d; };
        let block = parse_calc(tokens).unwrap();
        assert_eq!(block.expressions.len(), 4);
        assert_eq!(block.operators.len(), 3);
        assert!(block.operators.iter().all(|op| *op == CalcOp::Le));
    }
}
