//! Parser for `decreases_to!` macro arguments.
//!
//! Parses the `lhs1, lhs2, ... => rhs1, rhs2, ...` syntax.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use proc_macro::TokenStream;

/// Parse the `lhs1, lhs2, ... => rhs1, rhs2, ...` syntax for decreases_to!
#[allow(clippy::indexing_slicing)] // invariant: `tokens[i]`/`tokens[i+1]` bounded by `while i < tokens.len()` and `i + 1 < tokens.len()`; slices bounded by computed `arrow_pos`
pub(crate) fn parse_decreases_to_args(
    input: TokenStream,
) -> syn::Result<(Vec<proc_macro2::TokenStream>, Vec<proc_macro2::TokenStream>)> {
    let tokens: Vec<proc_macro2::TokenTree> =
        proc_macro2::TokenStream::from(input).into_iter().collect();

    // Find the `=>` separator
    let mut arrow_pos = None;
    let mut i = 0;
    while i < tokens.len() {
        if let proc_macro2::TokenTree::Punct(p) = &tokens[i] {
            if p.as_char() == '=' && i + 1 < tokens.len() {
                if let proc_macro2::TokenTree::Punct(p2) = &tokens[i + 1] {
                    if p2.as_char() == '>' {
                        arrow_pos = Some(i);
                        break;
                    }
                }
            }
        }
        i += 1;
    }

    let arrow_pos = arrow_pos.ok_or_else(|| {
        syn::Error::new(
            proc_macro2::Span::call_site(),
            "decreases_to! requires `=>` separator between LHS and RHS",
        )
    })?;

    let lhs_tokens: proc_macro2::TokenStream = tokens[..arrow_pos].iter().cloned().collect();
    let rhs_tokens: proc_macro2::TokenStream = tokens[arrow_pos + 2..].iter().cloned().collect();

    let lhs_exprs = split_by_comma(lhs_tokens);
    let rhs_exprs = split_by_comma(rhs_tokens);

    if lhs_exprs.len() != rhs_exprs.len() {
        return Err(syn::Error::new(
            proc_macro2::Span::call_site(),
            format!(
                "decreases_to! requires equal number of LHS and RHS expressions (got {} and {})",
                lhs_exprs.len(),
                rhs_exprs.len(),
            ),
        ));
    }

    Ok((lhs_exprs, rhs_exprs))
}

/// Split a token stream by top-level commas into individual expressions.
fn split_by_comma(tokens: proc_macro2::TokenStream) -> Vec<proc_macro2::TokenStream> {
    let mut exprs = Vec::new();
    let mut current: Vec<proc_macro2::TokenTree> = Vec::new();

    for tt in tokens {
        if let proc_macro2::TokenTree::Punct(ref p) = tt {
            if p.as_char() == ',' {
                if !current.is_empty() {
                    exprs.push(current.drain(..).collect());
                }
                continue;
            }
        }
        current.push(tt);
    }
    if !current.is_empty() {
        exprs.push(current.into_iter().collect());
    }

    exprs
}
