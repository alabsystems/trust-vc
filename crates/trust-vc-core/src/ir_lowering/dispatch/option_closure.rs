//! Core-private `trust_vc::closure!` argument parsing for Option methods.
//!
//! This intentionally supports only closure arguments consumed by
//! `Option::{unwrap_or_else, ok_or_else, and_then}`. It mirrors the proc-macro
//! syntax enough to fail closed on unsupported contract clauses without
//! exposing a new public parser.

use proc_macro2::TokenStream;
use syn::parse::{Parse, ParseStream};
use syn::{Expr, Ident, Token, Type};

use super::super::{LoweringError, TypeEnv};
use crate::ir::TrustVcType;

pub(super) enum OptionClosureArg<'a> {
    Plain(&'a syn::ExprClosure),
    TrustVc(Box<TrustVcClosureContract>),
}

pub(super) fn parse_option_closure_arg<'a>(
    expr: &'a syn::Expr,
    method: &str,
) -> Result<OptionClosureArg<'a>, LoweringError> {
    match expr {
        syn::Expr::Closure(closure) => Ok(OptionClosureArg::Plain(closure)),
        syn::Expr::Macro(mac) if is_trust_vc_closure_macro(mac) => {
            let contract: TrustVcClosureContract =
                syn::parse2(mac.mac.tokens.clone()).map_err(|err| {
                    LoweringError::UnsupportedMethod(format!(
                        "Option::{method} trust_vc::closure! argument is malformed: {err}"
                    ))
                })?;
            if !contract.has_contract_clause() {
                return Err(LoweringError::UnsupportedMethod(
                    "trust_vc::closure! requires at least a requires(...) or ensures(...) clause; \
                     contract-free trust_vc::closure! is not supported as an Option closure"
                        .into(),
                ));
            }
            if !matches!(method, "ok_or_else" | "unwrap_or_else" | "and_then") {
                return Err(LoweringError::UnsupportedMethod(format!(
                    "Option::{method} trust_vc::closure! contract clauses are not yet \
                         supported in Option lowering; refusing to ignore requires/ensures"
                )));
            }
            Ok(OptionClosureArg::TrustVc(Box::new(contract)))
        }
        _ => Err(LoweringError::UnsupportedMethod(format!(
            "Option::{method} expects a closure argument"
        ))),
    }
}

impl OptionClosureArg<'_> {
    pub(super) fn input_len(&self) -> usize {
        match self {
            Self::Plain(closure) => closure.inputs.len(),
            Self::TrustVc(contract) => contract.params.len(),
        }
    }

    pub(super) fn body(&self) -> &syn::Expr {
        match self {
            Self::Plain(closure) => &closure.body,
            Self::TrustVc(contract) => &contract.body,
        }
    }

    pub(super) fn output_type(&self) -> Option<&syn::Type> {
        match self {
            Self::Plain(closure) => match &closure.output {
                syn::ReturnType::Default => None,
                syn::ReturnType::Type(_, ty) => Some(ty),
            },
            Self::TrustVc(contract) => contract.return_ty.as_ref(),
        }
    }

    pub(super) fn unary_typed_ident(
        &self,
        method: &str,
        env: &TypeEnv,
    ) -> Result<(String, TrustVcType), LoweringError> {
        if self.input_len() != 1 {
            return Err(LoweringError::UnsupportedMethod(format!(
                "Option::{method} expects a unary closure, got {} parameters",
                self.input_len()
            )));
        }

        match self {
            Self::TrustVc(contract) => {
                let input = contract.params.first().ok_or_else(|| {
                    LoweringError::UnsupportedMethod(format!(
                        "Option::{method} expects a unary closure, got 0 parameters"
                    ))
                })?;
                Ok((input.name.to_string(), env.resolve_syn_type(&input.ty)?))
            }
            Self::Plain(closure) => {
                let input = closure.inputs.first().ok_or_else(|| {
                    LoweringError::UnsupportedMethod(format!(
                        "Option::{method} expects a unary closure, got 0 parameters"
                    ))
                })?;
                let syn::Pat::Type(typed) = input else {
                    return Err(LoweringError::InvalidType(format!(
                        "Option::{method} closure parameter requires an explicit type annotation"
                    )));
                };
                let syn::Pat::Ident(ident) = typed.pat.as_ref() else {
                    return Err(LoweringError::UnsupportedPattern(format!(
                        "Option::{method} closure parameter must be a simple identifier"
                    )));
                };
                Ok((ident.ident.to_string(), env.resolve_syn_type(&typed.ty)?))
            }
        }
    }
}

pub(super) struct TrustVcClosureContract {
    params: Vec<TrustVcClosureParam>,
    return_ty: Option<Type>,
    requires: Option<TokenStream>,
    ensures: Option<TrustVcEnsuresClause>,
    body: Expr,
}

struct TrustVcClosureParam {
    name: Ident,
    ty: Type,
}

struct TrustVcEnsuresClause {
    _result_name: Ident,
    _result_ty: Option<Type>,
    _expr: TokenStream,
}

impl TrustVcClosureContract {
    fn has_contract_clause(&self) -> bool {
        self.requires.is_some() || self.ensures.is_some()
    }
}

impl Parse for TrustVcClosureContract {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        if input.peek(Token![move]) {
            input.parse::<Token![move]>()?;
        }

        let mut params = Vec::new();
        input.parse::<Token![|]>()?;
        while !input.peek(Token![|]) {
            if !params.is_empty() {
                input.parse::<Token![,]>()?;
                if input.peek(Token![|]) {
                    break;
                }
            }
            if input.peek(Token![mut]) {
                input.parse::<Token![mut]>()?;
            }
            let name = input.parse::<Ident>()?;
            input.parse::<Token![:]>()?;
            let ty = input.parse::<Type>()?;
            params.push(TrustVcClosureParam { name, ty });
        }
        input.parse::<Token![|]>()?;

        let return_ty = if input.peek(Token![->]) {
            input.parse::<Token![->]>()?;
            Some(input.parse::<Type>()?)
        } else {
            None
        };

        let requires = parse_clause(input, "requires")?;
        let ensures = parse_ensures_clause(input)?;
        let body = input.parse::<syn::Expr>()?;

        Ok(Self {
            params,
            return_ty,
            requires,
            ensures,
            body,
        })
    }
}

fn is_trust_vc_closure_macro(mac: &syn::ExprMacro) -> bool {
    let path = &mac.mac.path;
    let mut segments = path.segments.iter();
    matches!(
        (segments.next(), segments.next(), segments.next()),
        (Some(first), Some(second), None) if first.ident == "trust_vc" && second.ident == "closure"
    )
}

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

fn parse_ensures_clause(input: ParseStream<'_>) -> syn::Result<Option<TrustVcEnsuresClause>> {
    if input.peek(syn::Ident) {
        let fork = input.fork();
        let ident: Ident = fork.parse()?;
        if ident == "ensures" {
            input.parse::<Ident>()?;
            let content;
            syn::parenthesized!(content in input);
            content.parse::<Token![|]>()?;
            let _result_name: Ident = content.parse()?;
            let _result_ty = if content.peek(Token![:]) {
                content.parse::<Token![:]>()?;
                Some(content.parse::<Type>()?)
            } else {
                None
            };
            content.parse::<Token![|]>()?;
            let expr = content.parse::<TokenStream>()?;
            return Ok(Some(TrustVcEnsuresClause {
                _result_name,
                _result_ty,
                _expr: expr,
            }));
        }
    }
    Ok(None)
}
