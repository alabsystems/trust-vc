// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Parsing for `trust_vc::closure!` contract syntax.
//!
//! Handles the custom `|params| requires(...) ensures(...) body` syntax.

use proc_macro2::{Ident, TokenStream};
use syn::parse::{Parse, ParseStream};
use syn::{Token, Type};

pub(super) struct ClosureParam {
    pub(super) is_mut: bool,
    pub(super) name: Ident,
    pub(super) ty: Type,
}

pub(super) struct EnsuresClause {
    pub(super) result_name: Ident,
    pub(super) result_ty: Option<Type>,
    pub(super) expr: TokenStream,
}

pub(super) struct ClosureContract {
    pub(super) is_move: bool,
    pub(super) params: Vec<ClosureParam>,
    pub(super) return_ty: Option<Type>,
    pub(super) requires: Option<TokenStream>,
    pub(super) ensures: Option<EnsuresClause>,
    pub(super) body: syn::Expr,
}

impl Parse for ClosureContract {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let is_move = input.peek(Token![move]);
        if is_move {
            input.parse::<Token![move]>()?;
        }

        // `|param1: Ty1, ..., paramN: TyN|`
        input.parse::<Token![|]>()?;
        let mut params = Vec::new();
        while !input.peek(Token![|]) {
            if !params.is_empty() {
                input.parse::<Token![,]>()?;
                if input.peek(Token![|]) {
                    break;
                }
            }
            let is_mut = if input.peek(Token![mut]) {
                input.parse::<Token![mut]>()?;
                true
            } else {
                false
            };
            let name: Ident = input.parse()?;
            input.parse::<Token![:]>()?;
            let ty: Type = input.parse()?;
            params.push(ClosureParam { is_mut, name, ty });
        }
        input.parse::<Token![|]>()?;

        // Optional `-> RetTy`
        let return_ty = if input.peek(Token![->]) {
            input.parse::<Token![->]>()?;
            Some(input.parse::<Type>()?)
        } else {
            None
        };

        // Optional `requires(expr)`
        let requires = parse_clause(input, "requires")?;

        // Optional `ensures(|res[: Ty]| expr)`
        let ensures = parse_ensures_clause(input)?;

        let body: syn::Expr = input.parse()?;

        Ok(ClosureContract {
            is_move,
            params,
            return_ty,
            requires,
            ensures,
            body,
        })
    }
}

/// Parse a named clause like `requires(expr)`.
fn parse_clause(input: ParseStream<'_>, name: &str) -> syn::Result<Option<TokenStream>> {
    if input.peek(syn::Ident) {
        let fork = input.fork();
        let ident: Ident = fork.parse()?;
        if ident == name {
            input.parse::<Ident>()?;
            let content;
            syn::parenthesized!(content in input);
            return Ok(Some(content.parse::<TokenStream>()?));
        }
    }
    Ok(None)
}

/// Parse `ensures(|res[: Ty]| expr)`.
fn parse_ensures_clause(input: ParseStream<'_>) -> syn::Result<Option<EnsuresClause>> {
    if input.peek(syn::Ident) {
        let fork = input.fork();
        let ident: Ident = fork.parse()?;
        if ident == "ensures" {
            input.parse::<Ident>()?;
            let content;
            syn::parenthesized!(content in input);
            content.parse::<Token![|]>()?;
            let result_name: Ident = content.parse()?;
            let result_ty = if content.peek(Token![:]) {
                content.parse::<Token![:]>()?;
                Some(content.parse::<Type>()?)
            } else {
                None
            };
            content.parse::<Token![|]>()?;
            let expr = content.parse::<TokenStream>()?;
            return Ok(Some(EnsuresClause {
                result_name,
                result_ty,
                expr,
            }));
        }
    }
    Ok(None)
}

impl EnsuresClause {
    pub(super) fn ensures_expr_tokens(&self) -> TokenStream {
        self.expr.clone()
    }
}
