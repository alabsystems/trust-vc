//! Collection typing and diagnostics helpers for IR lowering.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Part of #2526.

use crate::ir::TrustVcType;
use crate::ir_expr::{CollectionOp, TrustVcExpr};
use crate::ir_lowering::{infer_expr_type, LoweringError};

pub(in crate::ir_lowering::dispatch) fn infer_collection_op_type(
    op: &CollectionOp,
    receiver_ty: &TrustVcType,
    args: &[TrustVcExpr],
) -> Result<TrustVcType, LoweringError> {
    match op {
        CollectionOp::Len => Ok(TrustVcType::Uint {
            width: crate::ir::pointer_width(),
        }),
        CollectionOp::IsEmpty
        | CollectionOp::Contains
        | CollectionOp::ContainsKey
        | CollectionOp::ContainsValue
        | CollectionOp::NoDuplicates
        | CollectionOp::Finite => Ok(TrustVcType::Bool),
        CollectionOp::Subset | CollectionOp::Superset => {
            if let TrustVcType::Multiset(elem_ty) = receiver_ty {
                require_matching_multiset_arg(op, elem_ty, args)?;
            }
            Ok(TrustVcType::Bool)
        }
        CollectionOp::Count => Ok(TrustVcType::Nat),
        CollectionOp::Choose => match receiver_ty {
            TrustVcType::Set(elem) => {
                if !args.is_empty() {
                    return Err(LoweringError::TypeInference(format!(
                        "Set::choose requires 0 arguments, got {}",
                        args.len()
                    )));
                }
                Ok(*elem.clone())
            }
            TrustVcType::Multiset(elem) => {
                if !args.is_empty() {
                    return Err(LoweringError::TypeInference(format!(
                        "Multiset::choose requires 0 arguments, got {}",
                        args.len()
                    )));
                }
                Ok(*elem.clone())
            }
            _ => Err(LoweringError::TypeInference(format!(
                "choose requires Set or Multiset receiver, got '{}'",
                receiver_ty.to_type_string()
            ))),
        },
        CollectionOp::First | CollectionOp::Last | CollectionOp::Get => match receiver_ty {
            TrustVcType::Seq(elem) | TrustVcType::Array(elem, _) => Ok(*elem.clone()),
            TrustVcType::Map(_, val) => Ok(*val.clone()),
            _ => Err(LoweringError::TypeInference(format!(
                "collection operation '{}' requires Seq/Map/array receiver, got '{}'",
                collection_op_name(op),
                receiver_ty.to_type_string()
            ))),
        },
        CollectionOp::Reverse => match receiver_ty {
            TrustVcType::Seq(_) => Ok(receiver_ty.clone()),
            _ => Err(LoweringError::TypeInference(format!(
                "Seq::reverse requires Seq receiver, got '{}'",
                receiver_ty.to_type_string()
            ))),
        },
        CollectionOp::ToSet => match receiver_ty {
            TrustVcType::Seq(elem_ty) => Ok(TrustVcType::Set(elem_ty.clone())),
            _ => Err(LoweringError::TypeInference(format!(
                "Seq::to_set requires Seq receiver, got '{}'",
                receiver_ty.to_type_string()
            ))),
        },
        CollectionOp::ToMultiset => match receiver_ty {
            TrustVcType::Seq(elem_ty) => Ok(TrustVcType::Multiset(elem_ty.clone())),
            _ => Err(LoweringError::TypeInference(format!(
                "Seq::to_multiset requires Seq receiver, got '{}'",
                receiver_ty.to_type_string()
            ))),
        },
        CollectionOp::Push
        | CollectionOp::Add
        | CollectionOp::Update
        | CollectionOp::DropLast
        | CollectionOp::DropFirst
        | CollectionOp::Take
        | CollectionOp::Skip
        | CollectionOp::Subrange
        | CollectionOp::Concat
        | CollectionOp::Insert
        | CollectionOp::Remove => Ok(receiver_ty.clone()),
        CollectionOp::View => Ok(receiver_ty
            .view_collection_type()
            .unwrap_or_else(|| receiver_ty.clone())),
        CollectionOp::Union | CollectionOp::Intersect | CollectionOp::Difference => {
            if let TrustVcType::Multiset(elem_ty) = receiver_ty {
                require_matching_multiset_arg(op, elem_ty, args)?;
            }
            Ok(receiver_ty.clone())
        }
        CollectionOp::SeqMapValues => match receiver_ty {
            TrustVcType::Seq(elem_ty) => {
                let (params, ret_ty) = extract_spec_fn_signature(args, "map_values")?;
                if params.as_slice() != [elem_ty.as_ref().clone()] {
                    return Err(LoweringError::TypeInference(format!(
                        "collection operation 'map_values' requires SpecFn<{}, Ret>, got '{}'",
                        elem_ty.to_type_string(),
                        args.first()
                            .map(infer_expr_type)
                            .unwrap_or_else(|| TrustVcType::Opaque("<missing>".to_string()))
                            .to_type_string()
                    )));
                }
                Ok(TrustVcType::Seq(Box::new(ret_ty)))
            }
            _ => Err(LoweringError::TypeInference(format!(
                "collection operation '{}' requires Seq receiver, got '{}'",
                collection_op_name(op),
                receiver_ty.to_type_string()
            ))),
        },
        CollectionOp::SeqMap => match receiver_ty {
            TrustVcType::Seq(elem_ty) => {
                let (params, ret_ty) = extract_spec_fn_signature(args, "map")?;
                let pw = crate::ir::pointer_width();
                let expected = vec![TrustVcType::Uint { width: pw }, elem_ty.as_ref().clone()];
                if params != expected {
                    return Err(LoweringError::TypeInference(format!(
                        "Seq::map requires SpecFn<(usize, {}), Ret>, got '{}'",
                        elem_ty.to_type_string(),
                        args.first()
                            .map(infer_expr_type)
                            .unwrap_or_else(|| TrustVcType::Opaque("<missing>".to_string()))
                            .to_type_string()
                    )));
                }
                Ok(TrustVcType::Seq(Box::new(ret_ty)))
            }
            _ => Err(LoweringError::TypeInference(format!(
                "Seq::map requires Seq receiver, got '{}'",
                receiver_ty.to_type_string()
            ))),
        },
        CollectionOp::SeqFilter => match receiver_ty {
            TrustVcType::Seq(elem_ty) => {
                let (params, ret_ty) = extract_spec_fn_signature(args, "filter")?;
                if params.as_slice() != [elem_ty.as_ref().clone()] || ret_ty != TrustVcType::Bool {
                    return Err(LoweringError::TypeInference(format!(
                        "Seq::filter requires SpecFn<{}, bool>, got '{}'",
                        elem_ty.to_type_string(),
                        args.first()
                            .map(infer_expr_type)
                            .unwrap_or_else(|| TrustVcType::Opaque("<missing>".to_string()))
                            .to_type_string()
                    )));
                }
                Ok(receiver_ty.clone())
            }
            _ => Err(LoweringError::TypeInference(format!(
                "Seq::filter requires Seq receiver, got '{}'",
                receiver_ty.to_type_string()
            ))),
        },
        CollectionOp::SeqFlatMap => match receiver_ty {
            TrustVcType::Seq(elem_ty) => {
                let (params, ret_ty) = extract_spec_fn_signature(args, "flat_map")?;
                if params.as_slice() != [elem_ty.as_ref().clone()] {
                    return Err(LoweringError::TypeInference(format!(
                        "Seq::flat_map requires SpecFn<{}, Seq<Ret>>, got '{}'",
                        elem_ty.to_type_string(),
                        args.first()
                            .map(infer_expr_type)
                            .unwrap_or_else(|| TrustVcType::Opaque("<missing>".to_string()))
                            .to_type_string()
                    )));
                }
                match ret_ty {
                    TrustVcType::Seq(flat_elem_ty) => Ok(TrustVcType::Seq(flat_elem_ty)),
                    other => Err(LoweringError::TypeInference(format!(
                        "Seq::flat_map requires SpecFn<{}, Seq<Ret>>, got '{}'",
                        elem_ty.to_type_string(),
                        TrustVcType::SpecFn(params, Box::new(other)).to_type_string()
                    ))),
                }
            }
            _ => Err(LoweringError::TypeInference(format!(
                "Seq::flat_map requires Seq receiver, got '{}'",
                receiver_ty.to_type_string()
            ))),
        },
        CollectionOp::SeqFoldLeft => infer_seq_fold_type(receiver_ty, args, true),
        CollectionOp::SeqFoldRight => infer_seq_fold_type(receiver_ty, args, false),
        CollectionOp::SetFilter => match receiver_ty {
            TrustVcType::Set(elem_ty) => {
                let (params, ret_ty) = extract_spec_fn_signature(args, "filter")?;
                if params.as_slice() != [elem_ty.as_ref().clone()] || ret_ty != TrustVcType::Bool {
                    return Err(LoweringError::TypeInference(format!(
                        "Set::filter requires SpecFn<{}, bool>, got '{}'",
                        elem_ty.to_type_string(),
                        args.first()
                            .map(infer_expr_type)
                            .unwrap_or_else(|| TrustVcType::Opaque("<missing>".to_string()))
                            .to_type_string()
                    )));
                }
                Ok(receiver_ty.clone())
            }
            _ => Err(LoweringError::TypeInference(format!(
                "Set::filter requires Set receiver, got '{}'",
                receiver_ty.to_type_string()
            ))),
        },
        CollectionOp::SetMap => match receiver_ty {
            TrustVcType::Set(elem_ty) => {
                let (params, ret_ty) = extract_spec_fn_signature(args, "map")?;
                if params.as_slice() != [elem_ty.as_ref().clone()] {
                    return Err(LoweringError::TypeInference(format!(
                        "Set::map requires SpecFn<{}, Ret>, got '{}'",
                        elem_ty.to_type_string(),
                        args.first()
                            .map(infer_expr_type)
                            .unwrap_or_else(|| TrustVcType::Opaque("<missing>".to_string()))
                            .to_type_string()
                    )));
                }
                Ok(TrustVcType::Set(Box::new(ret_ty)))
            }
            _ => Err(LoweringError::TypeInference(format!(
                "Set::map requires Set receiver, got '{}'",
                receiver_ty.to_type_string()
            ))),
        },
        CollectionOp::SetMkMap => match receiver_ty {
            TrustVcType::Set(elem_ty) => {
                let (params, ret_ty) = extract_spec_fn_signature(args, "mk_map")?;
                if params.as_slice() != [elem_ty.as_ref().clone()] {
                    return Err(LoweringError::TypeInference(format!(
                        "Set::mk_map requires SpecFn<{}, Ret>, got '{}'",
                        elem_ty.to_type_string(),
                        args.first()
                            .map(infer_expr_type)
                            .unwrap_or_else(|| TrustVcType::Opaque("<missing>".to_string()))
                            .to_type_string()
                    )));
                }
                Ok(TrustVcType::Map(elem_ty.clone(), Box::new(ret_ty)))
            }
            _ => Err(LoweringError::TypeInference(format!(
                "Set::mk_map requires Set receiver, got '{}'",
                receiver_ty.to_type_string()
            ))),
        },
        CollectionOp::SetFold => infer_set_fold_type(receiver_ty, args),
        CollectionOp::MapMapValues => match receiver_ty {
            TrustVcType::Map(key, val) => {
                let (params, ret_ty) = extract_spec_fn_signature(args, "map_values")?;
                if params.as_slice() != [val.as_ref().clone()] {
                    return Err(LoweringError::TypeInference(format!(
                        "Map::map_values requires SpecFn<{}, Ret>, got '{}'",
                        val.to_type_string(),
                        args.first()
                            .map(infer_expr_type)
                            .unwrap_or_else(|| TrustVcType::Opaque("<missing>".to_string()))
                            .to_type_string()
                    )));
                }
                Ok(TrustVcType::Map(key.clone(), Box::new(ret_ty)))
            }
            _ => Err(LoweringError::TypeInference(format!(
                "Map::map_values requires Map receiver, got '{}'",
                receiver_ty.to_type_string()
            ))),
        },
        CollectionOp::MapMapEntries => match receiver_ty {
            TrustVcType::Map(key, val) => {
                let (params, ret_ty) = extract_spec_fn_signature(args, "map_entries")?;
                let expected = vec![key.as_ref().clone(), val.as_ref().clone()];
                if params != expected {
                    return Err(LoweringError::TypeInference(format!(
                        "Map::map_entries requires SpecFn<({}, {}), Ret>, got '{}'",
                        key.to_type_string(),
                        val.to_type_string(),
                        args.first()
                            .map(infer_expr_type)
                            .unwrap_or_else(|| TrustVcType::Opaque("<missing>".to_string()))
                            .to_type_string()
                    )));
                }
                Ok(TrustVcType::Map(key.clone(), Box::new(ret_ty)))
            }
            _ => Err(LoweringError::TypeInference(format!(
                "Map::map_entries requires Map receiver, got '{}'",
                receiver_ty.to_type_string()
            ))),
        },
        CollectionOp::MapFilterKeys => match receiver_ty {
            TrustVcType::Map(key, _) => {
                let (params, ret_ty) = extract_spec_fn_signature(args, "filter_keys")?;
                if params.as_slice() != [key.as_ref().clone()] || ret_ty != TrustVcType::Bool {
                    return Err(LoweringError::TypeInference(format!(
                        "Map::filter_keys requires SpecFn<{}, bool>, got '{}'",
                        key.to_type_string(),
                        args.first()
                            .map(infer_expr_type)
                            .unwrap_or_else(|| TrustVcType::Opaque("<missing>".to_string()))
                            .to_type_string()
                    )));
                }
                Ok(receiver_ty.clone())
            }
            _ => Err(LoweringError::TypeInference(format!(
                "Map::filter_keys requires Map receiver, got '{}'",
                receiver_ty.to_type_string()
            ))),
        },
        CollectionOp::Dom => match receiver_ty {
            TrustVcType::Map(key, _) => Ok(TrustVcType::Set(key.clone())),
            _ => Ok(receiver_ty.clone()),
        },
    }
}

pub(in crate::ir_lowering::dispatch) fn invalid_collection_receiver_error(
    op: &CollectionOp,
    receiver_ty: &TrustVcType,
) -> LoweringError {
    match op {
        CollectionOp::Get | CollectionOp::First | CollectionOp::Last => {
            LoweringError::TypeInference(format!(
                "collection operation '{}' requires Seq/Map/array receiver, got '{}'",
                collection_op_name(op),
                receiver_ty.to_type_string()
            ))
        }
        _ => LoweringError::TypeInference(format!(
            "collection operation '{}' requires a collection receiver, got '{}'",
            collection_op_name(op),
            receiver_ty.to_type_string()
        )),
    }
}

pub(in crate::ir_lowering::dispatch) fn unsupported_collection_op_error(
    op: &CollectionOp,
    receiver_ty: &TrustVcType,
) -> LoweringError {
    LoweringError::TypeInference(format!(
        "collection operation '{}' is not yet supported for '{}'",
        collection_op_name(op),
        receiver_ty.to_type_string()
    ))
}

fn collection_op_name(op: &CollectionOp) -> &'static str {
    match op {
        CollectionOp::Len => "len",
        CollectionOp::IsEmpty => "is_empty",
        CollectionOp::Push => "push",
        CollectionOp::Add => "add",
        CollectionOp::First => "first",
        CollectionOp::Last => "last",
        CollectionOp::Update => "update",
        CollectionOp::DropLast => "drop_last",
        CollectionOp::DropFirst => "drop_first",
        CollectionOp::Take => "take",
        CollectionOp::Skip => "skip",
        CollectionOp::Subrange => "subrange",
        CollectionOp::Concat => "concat",
        CollectionOp::View => "view",
        CollectionOp::SeqMapValues => "map_values",
        CollectionOp::SeqMap => "map",
        CollectionOp::SeqFilter => "filter",
        CollectionOp::SeqFlatMap => "flat_map",
        CollectionOp::SeqFoldLeft => "fold_left",
        CollectionOp::SeqFoldRight => "fold_right",
        CollectionOp::Reverse => "reverse",
        CollectionOp::NoDuplicates => "no_duplicates",
        CollectionOp::ToSet => "to_set",
        CollectionOp::ToMultiset => "to_multiset",
        CollectionOp::SetFilter => "filter",
        CollectionOp::SetMap => "map",
        CollectionOp::SetMkMap => "mk_map",
        CollectionOp::SetFold => "fold",
        CollectionOp::MapMapValues => "map_values",
        CollectionOp::MapMapEntries => "map_entries",
        CollectionOp::MapFilterKeys => "filter_keys",
        CollectionOp::Contains => "contains",
        CollectionOp::Insert => "insert",
        CollectionOp::Remove => "remove",
        CollectionOp::Union => "union",
        CollectionOp::Intersect => "intersect",
        CollectionOp::Difference => "difference",
        CollectionOp::Subset => "subset",
        CollectionOp::Superset => "superset",
        CollectionOp::Finite => "finite",
        CollectionOp::Count => "count",
        CollectionOp::Choose => "choose",
        CollectionOp::Get => "get",
        CollectionOp::ContainsKey => "contains_key",
        CollectionOp::ContainsValue => "contains_value",
        CollectionOp::Dom => "dom",
    }
}

fn require_matching_multiset_arg(
    op: &CollectionOp,
    elem_ty: &TrustVcType,
    args: &[TrustVcExpr],
) -> Result<(), LoweringError> {
    let [arg] = args else {
        return Err(LoweringError::TypeInference(format!(
            "Multiset operation '{}' requires exactly 1 argument, got {}",
            collection_op_name(op),
            args.len()
        )));
    };
    let expected = TrustVcType::Multiset(Box::new(elem_ty.clone()));
    let actual = infer_expr_type(arg);
    if actual == expected {
        return Ok(());
    }
    Err(LoweringError::TypeInference(format!(
        "Multiset operation '{}' requires argument '{}', got '{}'",
        collection_op_name(op),
        expected.to_type_string(),
        actual.to_type_string()
    )))
}

#[allow(clippy::indexing_slicing)] // args[0] guarded by args.len() != 1
fn extract_spec_fn_signature(
    args: &[TrustVcExpr],
    method: &str,
) -> Result<(Vec<TrustVcType>, TrustVcType), LoweringError> {
    if args.len() != 1 {
        return Err(LoweringError::TypeInference(format!(
            "collection operation '{}' expects 1 SpecFn argument, got {}",
            method,
            args.len()
        )));
    }

    match infer_expr_type(&args[0]) {
        TrustVcType::SpecFn(params, ret) => Ok((params, *ret)),
        other => Err(LoweringError::TypeInference(format!(
            "collection operation '{}' requires a SpecFn argument, got '{}'",
            method,
            other.to_type_string()
        ))),
    }
}

#[allow(clippy::indexing_slicing)] // args[0]/args[1] guarded by args.len() != 2
fn infer_seq_fold_type(
    receiver_ty: &TrustVcType,
    args: &[TrustVcExpr],
    left_to_right: bool,
) -> Result<TrustVcType, LoweringError> {
    let method = if left_to_right {
        "Seq::fold_left"
    } else {
        "Seq::fold_right"
    };
    let TrustVcType::Seq(elem_ty) = receiver_ty else {
        return Err(LoweringError::TypeInference(format!(
            "{method} requires Seq receiver, got '{}'",
            receiver_ty.to_type_string()
        )));
    };
    if args.len() != 2 {
        return Err(LoweringError::TypeInference(format!(
            "{method} expects 2 arguments (init, SpecFn), got {}",
            args.len()
        )));
    }

    let acc_ty = infer_expr_type(&args[0]);
    let (params, ret_ty) = extract_spec_fn_signature(
        std::slice::from_ref(&args[1]),
        if left_to_right {
            "fold_left"
        } else {
            "fold_right"
        },
    )?;
    let expected = if left_to_right {
        vec![acc_ty.clone(), elem_ty.as_ref().clone()]
    } else {
        vec![elem_ty.as_ref().clone(), acc_ty.clone()]
    };
    if params != expected || ret_ty != acc_ty {
        let expected_sig = if left_to_right {
            format!(
                "SpecFn<({}, {}), {}>",
                acc_ty.to_type_string(),
                elem_ty.to_type_string(),
                acc_ty.to_type_string()
            )
        } else {
            format!(
                "SpecFn<({}, {}), {}>",
                elem_ty.to_type_string(),
                acc_ty.to_type_string(),
                acc_ty.to_type_string()
            )
        };
        return Err(LoweringError::TypeInference(format!(
            "{method} requires initial accumulator plus {expected_sig}, got '{}'",
            infer_expr_type(&args[1]).to_type_string()
        )));
    }

    Ok(acc_ty)
}

#[allow(clippy::indexing_slicing)] // args[0]/args[1] guarded by args.len() != 2
fn infer_set_fold_type(
    receiver_ty: &TrustVcType,
    args: &[TrustVcExpr],
) -> Result<TrustVcType, LoweringError> {
    let TrustVcType::Set(elem_ty) = receiver_ty else {
        return Err(LoweringError::TypeInference(format!(
            "Set::fold requires Set receiver, got '{}'",
            receiver_ty.to_type_string()
        )));
    };
    if args.len() != 2 {
        return Err(LoweringError::TypeInference(format!(
            "Set::fold expects 2 arguments (init, SpecFn), got {}",
            args.len()
        )));
    }

    let acc_ty = infer_expr_type(&args[0]);
    let (params, ret_ty) = extract_spec_fn_signature(std::slice::from_ref(&args[1]), "fold")?;
    let expected = vec![acc_ty.clone(), elem_ty.as_ref().clone()];
    if params != expected || ret_ty != acc_ty {
        return Err(LoweringError::TypeInference(format!(
            "Set::fold requires initial accumulator plus SpecFn<({}, {}), {}>, got '{}'",
            acc_ty.to_type_string(),
            elem_ty.to_type_string(),
            acc_ty.to_type_string(),
            infer_expr_type(&args[1]).to_type_string()
        )));
    }

    Ok(acc_ty)
}
