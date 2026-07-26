// trust-vc-oracle — Source parser for FunctionSignature extraction
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

mod text;

use quote::ToTokens;
use syn::spanned::Spanned;
use syn::{FnArg, ImplItem, Item, ReturnType, TraitItem};

use crate::engine::FunctionSignature;
use crate::OracleError;

use self::text::SourceMap;

/// Parse all function signatures from a Rust source string.
///
/// Walks free functions, `impl` methods, `trait` methods, and inline modules.
/// On parse failure this returns an empty vector.
#[must_use]
pub fn parse_functions(source: &str) -> Vec<FunctionSignature> {
    try_parse_functions(source).unwrap_or_default()
}

/// Parse all function signatures, returning an error on invalid syntax.
pub fn try_parse_functions(source: &str) -> Result<Vec<FunctionSignature>, OracleError> {
    let file = syn::parse_file(source).map_err(|error| OracleError::SourceParse {
        message: error.to_string(),
    })?;

    let source_map = SourceMap::new(source);
    let mut functions = Vec::new();
    collect_functions(&source_map, &file.items, &mut functions);
    Ok(functions)
}

/// Parse a single function by name from Rust source.
///
/// Returns the first function whose name matches `name`.
#[must_use]
pub fn parse_function_by_name(source: &str, name: &str) -> Option<FunctionSignature> {
    parse_functions(source)
        .into_iter()
        .find(|signature| signature.name == name)
}

fn collect_functions(
    source_map: &SourceMap<'_>,
    items: &[Item],
    functions: &mut Vec<FunctionSignature>,
) {
    for item in items {
        match item {
            Item::Fn(item_fn) => {
                functions.push(build_signature(source_map, item, &item_fn.sig));
            }
            Item::Impl(item_impl) => {
                for impl_item in &item_impl.items {
                    if let ImplItem::Fn(method) = impl_item {
                        functions.push(build_signature(source_map, method, &method.sig));
                    }
                }
            }
            Item::Trait(item_trait) => {
                for trait_item in &item_trait.items {
                    if let TraitItem::Fn(method) = trait_item {
                        functions.push(build_signature(source_map, method, &method.sig));
                    }
                }
            }
            Item::Mod(module) => {
                if let Some((_, items)) = &module.content {
                    collect_functions(source_map, items, functions);
                }
            }
            _ => {}
        }
    }
}

fn build_signature<T>(
    source_map: &SourceMap<'_>,
    item: &T,
    signature: &syn::Signature,
) -> FunctionSignature
where
    T: ToTokens + Spanned + ?Sized,
{
    let item_range = source_map.range_for(item);
    let source = item_range
        .as_ref()
        .map(|range| source_map.slice(range).to_owned())
        .unwrap_or_else(|| quote::quote!(#item).to_string());

    let params = signature
        .inputs
        .iter()
        .map(|arg| match arg {
            FnArg::Receiver(receiver) => ("self".to_owned(), node_text(source_map, receiver)),
            FnArg::Typed(param) => (
                node_text(source_map, param.pat.as_ref()),
                node_text(source_map, param.ty.as_ref()),
            ),
        })
        .collect();

    let return_type = match &signature.output {
        ReturnType::Default => None,
        ReturnType::Type(_, ty) => Some(node_text(source_map, ty.as_ref())),
    };

    FunctionSignature {
        name: signature.ident.to_string(),
        params,
        return_type,
        source,
        generics: signature
            .generics
            .params
            .iter()
            .map(|param| node_text(source_map, param))
            .collect(),
        where_clause: signature
            .generics
            .where_clause
            .as_ref()
            .map(|where_clause| {
                where_clause
                    .predicates
                    .iter()
                    .map(|predicate| node_text(source_map, predicate))
                    .collect()
            })
            .unwrap_or_default(),
        is_async: signature.asyncness.is_some(),
        is_const: signature.constness.is_some(),
        is_unsafe: signature.unsafety.is_some(),
        span_start: source_map.byte_offset(signature.span().start()),
        span_len: item_range.as_ref().map(|range| range.len()),
    }
}

fn node_text<T>(source_map: &SourceMap<'_>, node: &T) -> String
where
    T: ToTokens + Spanned + ?Sized,
{
    source_map
        .range_for(node)
        .map(|range| source_map.slice(&range).trim().to_owned())
        .filter(|text| !text.is_empty())
        .unwrap_or_else(|| quote::quote!(#node).to_string())
}

#[cfg(test)]
mod tests;
