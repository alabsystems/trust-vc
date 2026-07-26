// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Parser for Verus-style `assert_seqs_equal!(lhs == rhs)`.

use proc_macro2::TokenStream;
use quote::quote;
use syn::{BinOp, Expr};

/// Parsed `assert_seqs_equal!(lhs == rhs)` input.
#[derive(Clone)]
#[non_exhaustive]
pub struct AssertSeqsEqualInput {
    pub lhs: Expr,
    pub rhs: Expr,
}

impl std::fmt::Debug for AssertSeqsEqualInput {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AssertSeqsEqualInput")
            .field("lhs", &self.lhs_tokens().to_string())
            .field("rhs", &self.rhs_tokens().to_string())
            .finish()
    }
}

impl AssertSeqsEqualInput {
    /// Returns the left-hand side as tokens.
    pub fn lhs_tokens(&self) -> TokenStream {
        let lhs = &self.lhs;
        quote!(#lhs)
    }

    /// Returns the right-hand side as tokens.
    pub fn rhs_tokens(&self) -> TokenStream {
        let rhs = &self.rhs;
        quote!(#rhs)
    }
}

/// Parses `assert_seqs_equal!(lhs == rhs)`.
pub fn parse_assert_seqs_equal(tokens: TokenStream) -> syn::Result<AssertSeqsEqualInput> {
    let expr = crate::chained_comparisons::parse_expr_tokens_with_chains(tokens)?;
    let Expr::Binary(binary) = expr else {
        return Err(syn::Error::new_spanned(
            expr,
            "assert_seqs_equal! expects binary syntax: assert_seqs_equal!(lhs == rhs)",
        ));
    };

    if !matches!(binary.op, BinOp::Eq(_)) {
        return Err(syn::Error::new_spanned(
            binary.op,
            "assert_seqs_equal! expects `==`: assert_seqs_equal!(lhs == rhs)",
        ));
    }

    Ok(AssertSeqsEqualInput {
        lhs: *binary.left,
        rhs: *binary.right,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::quote;

    #[test]
    fn parses_binary_eq() {
        let parsed = parse_assert_seqs_equal(quote!(s1 == s2)).unwrap();

        assert_eq!(parsed.lhs_tokens().to_string(), "s1");
        assert_eq!(parsed.rhs_tokens().to_string(), "s2");
    }

    #[test]
    fn preserves_complex_seq_sides() {
        let parsed = parse_assert_seqs_equal(quote!(
            Seq::<i32>::empty().push(1i32) == Seq::<i32>::empty().push(1i32)
        ))
        .unwrap();

        assert_eq!(
            parsed.lhs_tokens().to_string(),
            "Seq :: < i32 > :: empty () . push (1i32)"
        );
        assert_eq!(
            parsed.rhs_tokens().to_string(),
            "Seq :: < i32 > :: empty () . push (1i32)"
        );
    }

    #[test]
    fn rejects_comma_arguments() {
        let err = match parse_assert_seqs_equal(quote!(s1, s2)) {
            Ok(_) => panic!("expected comma arguments to be rejected"),
            Err(err) => err,
        };

        assert!(
            err.to_string().contains("unexpected token")
                || err.to_string().contains("expects binary syntax"),
            "comma arguments must be rejected, got: {err}"
        );
    }

    #[test]
    fn rejects_non_eq_binary_operator() {
        let err = match parse_assert_seqs_equal(quote!(s1 != s2)) {
            Ok(_) => panic!("expected non-eq binary operator to be rejected"),
            Err(err) => err,
        };

        assert!(
            err.to_string().contains("expects `==`"),
            "diagnostic should mention ==, got: {err}"
        );
    }
}
