// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Parser for solver-mode assertion macros.
//!
//! Supports the TrustVc spelling of Verus-style scoped requires:
//! `assert_by_bit_vector!(condition; requires req1, req2)`.
//! Also accepts `assert_by_compute!(condition; compute_only)` as a bounded
//! Verus `by(compute_only)` compatibility spelling, and an optional trailing
//! proof-block clause mirroring the Verus
//! `assert(..) by(nonlinear_arith) requires .. { proof-body }` surface:
//! `assert_by_nonlinear!(condition; requires req1, req2; { stmts })`.

use proc_macro2::{TokenStream, TokenTree};
use quote::quote;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::{Expr, Ident, Result, Token};

/// Parsed solver-mode assertion input.
#[derive(Clone)]
#[non_exhaustive]
pub struct SolverModeAssertInput {
    pub condition: Expr,
    pub requires: Vec<Expr>,
    pub compute_only: bool,
    /// Optional Verus-style scoped proof block (`{ stmts }` after the final
    /// top-level `;`). `None` when the clause is absent; `Some` (possibly
    /// empty) when written.
    pub body: Option<syn::Block>,
}

impl SolverModeAssertInput {
    /// Returns the condition as tokens.
    pub fn condition_tokens(&self) -> TokenStream {
        let condition = &self.condition;
        quote!(#condition)
    }

    /// Returns each scoped requires expression as tokens.
    pub fn requires_tokens(&self) -> Vec<TokenStream> {
        self.requires
            .iter()
            .map(|requires| quote!(#requires))
            .collect()
    }
}

/// The optional clause that may follow the condition after a top-level `;`.
struct SolverModeAssertClause {
    requires: Vec<Expr>,
    compute_only: bool,
}

impl Parse for SolverModeAssertClause {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let mut requires = Vec::new();
        let mut compute_only = false;
        let keyword: Ident = input.parse()?;
        if keyword == "compute_only" {
            compute_only = true;
            if !input.is_empty() {
                return Err(input.error("unexpected tokens after `compute_only`"));
            }
        } else if keyword == "requires" {
            let parsed: Punctuated<Expr, Token![,]> = Punctuated::parse_terminated(input)?;
            if parsed.is_empty() {
                return Err(input.error("expected at least one scoped requires expression"));
            }
            requires.extend(parsed);
        } else {
            return Err(syn::Error::new_spanned(
                keyword,
                "expected `requires` or `compute_only` after `;`",
            ));
        }
        Ok(Self {
            requires,
            compute_only,
        })
    }
}

/// Splits the macro tokens at every top-level `;` (one not nested inside
/// `()`/`[]`/`{}`, which `proc_macro2` already groups for us) into segments:
/// the condition, then any `requires`/`compute_only` clause, then any
/// trailing `{ proof-body }` clause. The Verus condition is a single
/// expression that never contains a top-level `;`, so the split is
/// unambiguous; `;`s inside a proof block are inside a brace group and never
/// split.
fn split_top_level_segments(tokens: TokenStream) -> Vec<TokenStream> {
    let mut segments = vec![TokenStream::new()];
    for tt in tokens {
        if let TokenTree::Punct(punct) = &tt {
            if punct.as_char() == ';' {
                segments.push(TokenStream::new());
                continue;
            }
        }
        segments
            .last_mut()
            .expect("segments is never empty")
            .extend(std::iter::once(tt));
    }
    segments
}

/// Whether the segment is exactly one braced group (a `{ .. }` proof block).
fn segment_is_brace_block(segment: &TokenStream) -> bool {
    let mut iter = segment.clone().into_iter();
    matches!(
        (iter.next(), iter.next()),
        (
            Some(TokenTree::Group(group)),
            None
        ) if group.delimiter() == proc_macro2::Delimiter::Brace
    )
}

/// Parses `condition`, `condition; requires req1, req2`,
/// `condition; requires req1, req2; { stmts }`, or `condition; { stmts }`.
///
/// The condition is normalized through the shared chained-comparison and
/// Verus-`==>` implication rewriter (the same path `assert!` uses) so that
/// solver-mode asserts accept the full Verus boolean surface (`P ==> Q`,
/// `a <= b < c`) rather than only `syn`-native expressions.
pub fn parse_solver_mode_assert(tokens: TokenStream) -> Result<SolverModeAssertInput> {
    let mut segments = split_top_level_segments(tokens).into_iter();
    let condition_tokens = segments.next().unwrap_or_default();
    let condition = crate::chained_comparisons::parse_expr_tokens_with_chains(condition_tokens)?;
    let mut requires = Vec::new();
    let mut compute_only = false;
    let mut body: Option<syn::Block> = None;
    let mut saw_clause = false;
    for segment in segments {
        if body.is_some() {
            return Err(syn::Error::new_spanned(
                segment,
                "the `{ .. }` proof block must be the final clause",
            ));
        }
        if segment_is_brace_block(&segment) {
            body = Some(syn::parse2(segment)?);
            continue;
        }
        if saw_clause {
            return Err(syn::Error::new_spanned(
                segment,
                "at most one `requires`/`compute_only` clause is supported",
            ));
        }
        let clause: SolverModeAssertClause = syn::parse2(segment)?;
        requires = clause.requires;
        compute_only = clause.compute_only;
        saw_clause = true;
    }
    Ok(SolverModeAssertInput {
        condition,
        requires,
        compute_only,
        body,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::quote;

    #[test]
    fn parses_plain_condition() {
        let parsed = parse_solver_mode_assert(quote!(x & 1 == 0)).unwrap();
        assert_eq!(parsed.condition_tokens().to_string(), "x & 1 == 0");
        assert!(parsed.requires.is_empty());
    }

    #[test]
    fn parses_scoped_requires() {
        let parsed =
            parse_solver_mode_assert(quote!(x << 1 == 0x200u32; requires x == 0x100u32, y != 0))
                .unwrap();
        assert_eq!(parsed.requires.len(), 2);
        assert!(!parsed.compute_only);
        assert_eq!(parsed.requires_tokens()[0].to_string(), "x == 0x100u32");
        assert_eq!(parsed.requires_tokens()[1].to_string(), "y != 0");
    }

    #[test]
    fn parses_compute_only_clause() {
        let parsed = parse_solver_mode_assert(quote!(fib(10) == 55; compute_only)).unwrap();
        assert_eq!(parsed.condition_tokens().to_string(), "fib (10) == 55");
        assert!(parsed.requires.is_empty());
        assert!(parsed.compute_only);
    }

    #[test]
    fn rejects_wrong_clause_keyword() {
        let err = match parse_solver_mode_assert(quote!(x == x; assume x == 1)) {
            Ok(_) => panic!("expected wrong clause keyword to be rejected"),
            Err(err) => err,
        };
        assert!(
            err.to_string().contains("expected `requires`"),
            "diagnostic should mention requires, got: {err}"
        );
    }

    #[test]
    fn rejects_tokens_after_compute_only() {
        let err = match parse_solver_mode_assert(quote!(x == x; compute_only, y == y)) {
            Ok(_) => panic!("expected trailing compute_only tokens to be rejected"),
            Err(err) => err,
        };
        assert!(
            err.to_string().contains("unexpected tokens"),
            "diagnostic should reject trailing tokens, got: {err}"
        );
    }
}
