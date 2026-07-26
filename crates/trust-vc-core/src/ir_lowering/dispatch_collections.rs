//! Collection-specific expression lowering helpers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Part of #2526.

use crate::ir::TrustVcType;
use crate::ir_expr::{CollectionOp, TrustVcExpr};
use crate::ir_lowering::operators::coerce_unsuffixed_literal;

#[path = "dispatch/collections/constructors.rs"]
mod constructors;
#[path = "dispatch/collections/typing.rs"]
mod typing;

pub(super) use constructors::{coerce_literal_to_receiver_type, lower_collection_constructor};
pub(super) use typing::{
    infer_collection_op_type, invalid_collection_receiver_error, unsupported_collection_op_error,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum CollectionSurface {
    DirectCollection,
    ViewOnly(TrustVcType),
    None,
}

/// Extract the root variable name from a receiver expression.
///
/// Recursively follows MethodCall chains so chained expressions like
/// `s.remove(5).contains(3)` resolve to `Some("s")`. Parity with
/// `AstExpressionParser::extract_receiver_name` in `expressions.rs`.
/// Fixes #2067: IR lowering returned `None` for chained receivers,
/// causing `contains()` to fail with "unknown collection type".
#[allow(clippy::indexing_slicing)] // segments[0] guarded by segments.len() == 1
pub(super) fn extract_receiver_name(expr: &syn::Expr) -> Option<String> {
    let mut current = expr;
    loop {
        match current {
            syn::Expr::Path(path) => {
                return (path.path.segments.len() == 1)
                    .then(|| path.path.segments[0].ident.to_string());
            }
            syn::Expr::MethodCall(method_call) => current = &method_call.receiver,
            syn::Expr::Paren(paren) => current = &paren.expr,
            _ => return None,
        }
    }
}

pub(super) fn lowered_receiver_name(expr: &TrustVcExpr) -> Option<String> {
    match expr {
        TrustVcExpr::Var { name, .. } => Some(name.clone()),
        TrustVcExpr::FnCall { name, args, .. } if args.is_empty() => Some(name.clone()),
        TrustVcExpr::CollectionOp {
            receiver_name,
            receiver,
            ..
        } => receiver_name
            .clone()
            .or_else(|| lowered_receiver_name(receiver)),
        TrustVcExpr::Index { .. } => None,
        TrustVcExpr::Cast { expr, .. } => lowered_receiver_name(expr),
        _ => None,
    }
}

pub(super) fn match_collection_op(m: &str, receiver_ty: &TrustVcType) -> Option<CollectionOp> {
    Some(match m {
        "len" => CollectionOp::Len,
        "is_empty" => CollectionOp::IsEmpty,
        "push" => CollectionOp::Push,
        "push_back" => match receiver_ty {
            TrustVcType::Seq(_) => CollectionOp::Push,
            _ => return None,
        },
        "add" => match receiver_ty {
            TrustVcType::Seq(_) => CollectionOp::Add,
            TrustVcType::Multiset(_) => CollectionOp::Union,
            _ => return None,
        },
        "first" => CollectionOp::First,
        "last" => CollectionOp::Last,
        "update" => CollectionOp::Update,
        "set" => match receiver_ty {
            TrustVcType::Seq(_) => CollectionOp::Update,
            _ => return None,
        },
        "drop_last" => CollectionOp::DropLast,
        "pop_back" => match receiver_ty {
            TrustVcType::Seq(_) => CollectionOp::DropLast,
            _ => return None,
        },
        "drop_first" => CollectionOp::DropFirst,
        "take" => CollectionOp::Take,
        "skip" => CollectionOp::Skip,
        "subrange" => CollectionOp::Subrange,
        "subsequence" => match receiver_ty {
            TrustVcType::Seq(_) => CollectionOp::Subrange,
            _ => return None,
        },
        "concat" => CollectionOp::Concat,
        "view" => CollectionOp::View,
        "map_values" => match receiver_ty {
            TrustVcType::Map(_, _) => CollectionOp::MapMapValues,
            _ => CollectionOp::SeqMapValues,
        },
        "map" => match receiver_ty {
            TrustVcType::Set(_) => CollectionOp::SetMap,
            _ => CollectionOp::SeqMap,
        },
        "filter" => match receiver_ty {
            TrustVcType::Set(_) => CollectionOp::SetFilter,
            TrustVcType::Seq(_) => CollectionOp::SeqFilter,
            _ => return None,
        },
        "flat_map" => match receiver_ty {
            TrustVcType::Seq(_) => CollectionOp::SeqFlatMap,
            _ => return None,
        },
        "fold_left" => match receiver_ty {
            TrustVcType::Seq(_) => CollectionOp::SeqFoldLeft,
            _ => return None,
        },
        "fold_right" => match receiver_ty {
            TrustVcType::Seq(_) => CollectionOp::SeqFoldRight,
            _ => return None,
        },
        "reverse" => match receiver_ty {
            TrustVcType::Seq(_) => CollectionOp::Reverse,
            _ => return None,
        },
        "no_duplicates" => match receiver_ty {
            TrustVcType::Seq(_) => CollectionOp::NoDuplicates,
            _ => return None,
        },
        "to_set" => match receiver_ty {
            TrustVcType::Seq(_) => CollectionOp::ToSet,
            _ => return None,
        },
        "to_multiset" => match receiver_ty {
            TrustVcType::Seq(_) => CollectionOp::ToMultiset,
            _ => return None,
        },
        "fold" => match receiver_ty {
            TrustVcType::Set(_) => CollectionOp::SetFold,
            _ => return None,
        },
        "mk_map" => CollectionOp::SetMkMap,
        "filter_keys" => CollectionOp::MapFilterKeys,
        "map_entries" => CollectionOp::MapMapEntries,
        "contains" => match receiver_ty {
            TrustVcType::Map(_, _) => CollectionOp::ContainsKey,
            _ => CollectionOp::Contains,
        },
        "insert" => CollectionOp::Insert,
        "remove" => CollectionOp::Remove,
        "union" => CollectionOp::Union,
        "intersect" => CollectionOp::Intersect,
        "intersection" => match receiver_ty {
            TrustVcType::Set(_) => CollectionOp::Intersect,
            _ => return None,
        },
        "difference" => CollectionOp::Difference,
        "sub" => match receiver_ty {
            TrustVcType::Multiset(_) => CollectionOp::Difference,
            _ => return None,
        },
        "subset" | "subset_of" => CollectionOp::Subset,
        "is_subset" => match receiver_ty {
            TrustVcType::Set(_) | TrustVcType::Multiset(_) => CollectionOp::Subset,
            _ => return None,
        },
        "superset" => CollectionOp::Superset,
        "is_superset" => match receiver_ty {
            TrustVcType::Set(_) => CollectionOp::Superset,
            _ => return None,
        },
        "finite" => match receiver_ty {
            TrustVcType::Set(_) => CollectionOp::Finite,
            _ => return None,
        },
        "count" => CollectionOp::Count,
        "choose" => match receiver_ty {
            TrustVcType::Set(_) | TrustVcType::Multiset(_) => CollectionOp::Choose,
            _ => return None,
        },
        "get" | "index" => CollectionOp::Get,
        "lookup" => match receiver_ty {
            TrustVcType::Map(_, _) => CollectionOp::Get,
            _ => return None,
        },
        "contains_key" => CollectionOp::ContainsKey,
        "contains_value" => match receiver_ty {
            TrustVcType::Map(_, _) => CollectionOp::ContainsValue,
            _ => return None,
        },
        "dom" => CollectionOp::Dom,
        _ => return None,
    })
}

pub(super) fn coerce_collection_literal_args(
    op: &CollectionOp,
    receiver_ty: &TrustVcType,
    args: Vec<TrustVcExpr>,
) -> Vec<TrustVcExpr> {
    let Some(key_ty) = multiset_key_literal_hint(op, receiver_ty) else {
        return args;
    };

    args.into_iter()
        .map(|arg| coerce_unsuffixed_literal(arg, key_ty))
        .collect()
}

fn multiset_key_literal_hint<'a>(
    op: &CollectionOp,
    receiver_ty: &'a TrustVcType,
) -> Option<&'a TrustVcType> {
    if !matches!(
        op,
        CollectionOp::Contains | CollectionOp::Count | CollectionOp::Insert | CollectionOp::Remove
    ) {
        return None;
    }
    match receiver_ty {
        TrustVcType::Multiset(elem_ty) => Some(elem_ty.as_ref()),
        _ => None,
    }
}

pub(super) fn collection_surface(receiver_ty: &TrustVcType) -> CollectionSurface {
    match receiver_ty {
        TrustVcType::Seq(_)
        | TrustVcType::Array(_, _)
        | TrustVcType::Set(_)
        | TrustVcType::Multiset(_)
        | TrustVcType::Map(_, _) => CollectionSurface::DirectCollection,
        TrustVcType::String | TrustVcType::StrSlice => receiver_ty
            .view_collection_type()
            .map(CollectionSurface::ViewOnly)
            .unwrap_or(CollectionSurface::None),
        _ => CollectionSurface::None,
    }
}

pub(super) fn collection_op_supported(receiver_ty: &TrustVcType, op: &CollectionOp) -> bool {
    match receiver_ty {
        TrustVcType::Multiset(_) => matches!(
            op,
            CollectionOp::Len
                | CollectionOp::IsEmpty
                | CollectionOp::Contains
                | CollectionOp::Count
                | CollectionOp::Choose
                | CollectionOp::Insert
                | CollectionOp::Remove
                | CollectionOp::Union
                | CollectionOp::Intersect
                | CollectionOp::Difference
                | CollectionOp::Subset
        ),
        TrustVcType::Array(_, _) => matches!(
            op,
            CollectionOp::Len
                | CollectionOp::IsEmpty
                | CollectionOp::Contains
                | CollectionOp::First
                | CollectionOp::Last
                | CollectionOp::Get
                | CollectionOp::Update
                | CollectionOp::View
        ),
        TrustVcType::Seq(_) | TrustVcType::Set(_) | TrustVcType::Map(_, _) => true,
        _ => false,
    }
}
