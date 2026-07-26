//! Solver-family proc-macro entrypoint helpers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use proc_macro::TokenStream;
use quote::quote;
use syn::parse::Parser;

use crate::{decreases_to_parser, macro_expand_ext};

pub(crate) fn forall(input: TokenStream) -> TokenStream {
    let closure = proc_macro2::TokenStream::from(input);
    TokenStream::from(macro_expand_ext::expand_forall(closure))
}

pub(crate) fn exists(input: TokenStream) -> TokenStream {
    let closure = proc_macro2::TokenStream::from(input);
    TokenStream::from(macro_expand_ext::expand_exists(closure))
}

pub(crate) fn decreases_to(input: TokenStream) -> TokenStream {
    let input_clone = input.clone();
    let tokens = proc_macro2::TokenStream::from(input);

    let (lhs_exprs, rhs_exprs) = match decreases_to_parser::parse_decreases_to_args(input_clone) {
        Ok(result) => result,
        Err(err) => return err.to_compile_error().into(),
    };

    TokenStream::from(macro_expand_ext::expand_decreases_to(
        tokens, &lhs_exprs, &rhs_exprs,
    ))
}

pub(crate) fn assert_by_nonlinear(input: TokenStream) -> TokenStream {
    let tokens = proc_macro2::TokenStream::from(input);
    TokenStream::from(macro_expand_ext::expand_assert_by_nonlinear(tokens))
}

pub(crate) fn assert_by_bit_vector(input: TokenStream) -> TokenStream {
    let tokens = proc_macro2::TokenStream::from(input);
    TokenStream::from(macro_expand_ext::expand_assert_by_bit_vector(tokens))
}

pub(crate) fn assert_by_compute(input: TokenStream) -> TokenStream {
    let tokens = proc_macro2::TokenStream::from(input);
    TokenStream::from(macro_expand_ext::expand_assert_by_compute(tokens))
}

pub(crate) fn invariant(input: TokenStream) -> TokenStream {
    let tokens = proc_macro2::TokenStream::from(input);
    TokenStream::from(macro_expand_ext::expand_invariant(tokens))
}

pub(crate) fn invariant_except_break(input: TokenStream) -> TokenStream {
    let tokens = proc_macro2::TokenStream::from(input);
    TokenStream::from(macro_expand_ext::expand_invariant_except_break(tokens))
}

pub(crate) fn loop_ensures(input: TokenStream) -> TokenStream {
    let tokens = proc_macro2::TokenStream::from(input);
    TokenStream::from(macro_expand_ext::expand_loop_ensures(tokens))
}

pub(crate) fn loop_decreases(input: TokenStream) -> TokenStream {
    let tokens = proc_macro2::TokenStream::from(input);
    TokenStream::from(macro_expand_ext::expand_loop_decreases(tokens))
}

pub(crate) fn choose(input: TokenStream) -> TokenStream {
    let closure = proc_macro2::TokenStream::from(input);
    TokenStream::from(macro_expand_ext::expand_choose(closure))
}

pub(crate) fn arbitrary(input: TokenStream) -> TokenStream {
    let ty_tokens = proc_macro2::TokenStream::from(input);
    TokenStream::from(macro_expand_ext::expand_arbitrary(ty_tokens))
}

pub(crate) fn ext_eq(input: TokenStream) -> TokenStream {
    let (lhs, rhs) = match parse_two_expr_args("ext_eq", input) {
        Ok(args) => args,
        Err(err) => return TokenStream::from(err.to_compile_error()),
    };

    let lhs_tokens = quote!(#lhs);
    let rhs_tokens = quote!(#rhs);
    TokenStream::from(trust_vc_core::expand_ext_eq(lhs_tokens, rhs_tokens))
}

pub(crate) fn ext_ne(input: TokenStream) -> TokenStream {
    let (lhs, rhs) = match parse_two_expr_args("ext_ne", input) {
        Ok(args) => args,
        Err(err) => return TokenStream::from(err.to_compile_error()),
    };

    let lhs_tokens = quote!(#lhs);
    let rhs_tokens = quote!(#rhs);
    TokenStream::from(trust_vc_core::expand_ext_ne(lhs_tokens, rhs_tokens))
}

pub(crate) fn strict_eq(input: TokenStream) -> TokenStream {
    let (lhs, rhs) = match parse_two_expr_args("strict_eq", input) {
        Ok(args) => args,
        Err(err) => return TokenStream::from(err.to_compile_error()),
    };

    let lhs_tokens = quote!(#lhs);
    let rhs_tokens = quote!(#rhs);
    TokenStream::from(trust_vc_core::expand_strict_eq(lhs_tokens, rhs_tokens))
}

pub(crate) fn equal(input: TokenStream) -> TokenStream {
    let (lhs, rhs) = match parse_two_expr_args("equal", input) {
        Ok(args) => args,
        Err(err) => return TokenStream::from(err.to_compile_error()),
    };

    let lhs_tokens = quote!(#lhs);
    let rhs_tokens = quote!(#rhs);
    TokenStream::from(trust_vc_core::expand_strict_eq(lhs_tokens, rhs_tokens))
}

pub(crate) fn assert_seqs_equal(input: TokenStream) -> TokenStream {
    let tokens = proc_macro2::TokenStream::from(input);
    let parsed = match trust_vc_core::parse_assert_seqs_equal(tokens) {
        Ok(parsed) => parsed,
        Err(err) => return TokenStream::from(err.to_compile_error()),
    };

    TokenStream::from(crate::macro_expand::expand_assert_seqs_equal(&parsed))
}

fn parse_two_expr_args(
    macro_name: &str,
    input: TokenStream,
) -> Result<(syn::Expr, syn::Expr), syn::Error> {
    let parser = syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated;
    let args = parser.parse(input)?;

    if args.len() != 2 {
        return Err(syn::Error::new(
            proc_macro2::Span::call_site(),
            format!("{macro_name}! requires exactly two arguments: {macro_name}!(a, b)"),
        ));
    }

    let mut iter = args.into_iter();
    let (Some(lhs), Some(rhs)) = (iter.next(), iter.next()) else {
        return Err(syn::Error::new(
            proc_macro2::Span::call_site(),
            format!("{macro_name}! requires exactly two arguments: {macro_name}!(a, b)"),
        ));
    };

    Ok((lhs, rhs))
}
