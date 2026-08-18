// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ir::{pointer_width, CollectionOp, TrustVcType};

fn seq_i32_ty() -> TrustVcType {
    TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }))
}

fn seq_var(name: &str) -> TrustVcExpr {
    crate::ir_builder::var(name, seq_i32_ty())
}

#[test]
fn test_build_ext_eq_expr_seq_expands_to_len_and_forall() {
    let lhs = seq_var("lhs");
    let rhs = seq_var("rhs");
    let index_ty = TrustVcType::Uint {
        width: pointer_width(),
    };
    let index_name = "__trust_vc_ext_seq_idx".to_string();
    let index_var = crate::ir_builder::var(&index_name, index_ty.clone());
    let lhs_len = crate::ir_builder::collection_op(
        CollectionOp::Len,
        lhs.clone(),
        Some("lhs"),
        vec![],
        index_ty.clone(),
    );
    let rhs_len = crate::ir_builder::collection_op(
        CollectionOp::Len,
        rhs.clone(),
        Some("rhs"),
        vec![],
        index_ty.clone(),
    );
    let lhs_at = crate::ir_builder::collection_op(
        CollectionOp::Get,
        lhs,
        Some("lhs"),
        vec![index_var.clone()],
        TrustVcType::Int { width: 32 },
    );
    let rhs_at = crate::ir_builder::collection_op(
        CollectionOp::Get,
        rhs,
        Some("rhs"),
        vec![index_var.clone()],
        TrustVcType::Int { width: 32 },
    );
    let expected = crate::ir_builder::and(
        crate::ir_builder::eq(lhs_len.clone(), rhs_len),
        crate::ir_builder::forall(
            vec![(index_name, index_ty)],
            crate::ir_builder::implies(
                crate::ir_builder::lt(index_var, lhs_len),
                crate::ir_builder::eq(lhs_at, rhs_at),
            ),
            None,
        ),
    );

    assert_eq!(build_ext_eq_expr(seq_var("lhs"), seq_var("rhs")), expected);
}

#[test]
fn test_build_ext_eq_expr_string_normalizes_to_view() {
    let lhs = crate::ir_builder::var("lhs", TrustVcType::String);
    let rhs = crate::ir_builder::var("rhs", TrustVcType::String);
    let view_ty = TrustVcType::String
        .view_collection_type()
        .expect("string view type");

    let result = build_ext_eq_expr(lhs, rhs);
    match result {
        TrustVcExpr::Logic {
            op: crate::ir::LogicOp::And,
            left,
            ..
        } => match *left {
            TrustVcExpr::Compare { left, right, .. } => {
                for len_expr in [left, right] {
                    match *len_expr {
                        TrustVcExpr::CollectionOp {
                            op: CollectionOp::Len,
                            receiver,
                            ty,
                            ..
                        } => {
                            assert_eq!(
                                ty,
                                TrustVcType::Uint {
                                    width: pointer_width()
                                }
                            );
                            match *receiver {
                                TrustVcExpr::CollectionOp {
                                    op: CollectionOp::View,
                                    ty: receiver_ty,
                                    ..
                                } => {
                                    assert_eq!(receiver_ty, view_ty);
                                }
                                other => panic!("expected string view receiver, got {other:?}"),
                            }
                        }
                        other => panic!("expected len comparison, got {other:?}"),
                    }
                }
            }
            other => panic!("expected len equality on left conjunct, got {other:?}"),
        },
        other => panic!("expected seq-style extensional equality, got {other:?}"),
    }
}

#[test]
fn test_build_ext_eq_expr_mismatched_types_falls_back_to_plain_eq() {
    let lhs = crate::ir_builder::var("lhs", seq_i32_ty());
    let rhs = crate::ir_builder::var(
        "rhs",
        TrustVcType::Set(Box::new(TrustVcType::Int { width: 32 })),
    );

    assert_eq!(
        build_ext_eq_expr(lhs.clone(), rhs.clone()),
        crate::ir_builder::eq(lhs, rhs)
    );
}

fn set_i32_ty() -> TrustVcType {
    TrustVcType::Set(Box::new(TrustVcType::Int { width: 32 }))
}

fn set_var(name: &str) -> TrustVcExpr {
    crate::ir_builder::var(name, set_i32_ty())
}

fn multiset_i32_ty() -> TrustVcType {
    TrustVcType::Multiset(Box::new(TrustVcType::Int { width: 32 }))
}

fn multiset_var(name: &str) -> TrustVcExpr {
    crate::ir_builder::var(name, multiset_i32_ty())
}

fn multiset_empty() -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: format!(
            "{}Multiset_i32_empty",
            crate::ir_lowering::COLLECTION_CONSTRUCTOR_PREFIX
        ),
        args: vec![],
        return_ty: multiset_i32_ty(),
    }
}

fn multiset_insert(receiver: TrustVcExpr, elem: TrustVcExpr) -> TrustVcExpr {
    crate::ir_builder::collection_op(
        CollectionOp::Insert,
        receiver,
        None,
        vec![elem],
        multiset_i32_ty(),
    )
}

fn map_i32_bool_ty() -> TrustVcType {
    TrustVcType::Map(
        Box::new(TrustVcType::Int { width: 32 }),
        Box::new(TrustVcType::Bool),
    )
}

fn map_var(name: &str) -> TrustVcExpr {
    crate::ir_builder::var(name, map_i32_bool_ty())
}

fn spec_fn_i32_i32_ty() -> TrustVcType {
    TrustVcType::SpecFn(
        vec![TrustVcType::Int { width: 32 }],
        Box::new(TrustVcType::Int { width: 32 }),
    )
}

fn spec_closure(param_name: &str, body: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::SpecClosure {
        params: vec![(param_name.to_string(), TrustVcType::Int { width: 32 })],
        body: Box::new(body),
        ty: spec_fn_i32_i32_ty(),
    }
}

fn i32_var(name: &str) -> TrustVcExpr {
    crate::ir_builder::var(name, TrustVcType::Int { width: 32 })
}

fn i32_add(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    crate::ir_builder::add(left, right, TrustVcType::Int { width: 32 })
}

fn assert_forall_bound_name(expr: TrustVcExpr, expected_name: &str) -> Box<TrustVcExpr> {
    match expr {
        TrustVcExpr::Quantifier {
            kind: crate::ir_expr::QuantifierKind::Forall,
            bound_vars,
            body,
            ..
        } => {
            assert_eq!(bound_vars.len(), 1);
            assert_eq!(bound_vars[0].0, expected_name);
            body
        }
        other => panic!("expected forall expression, got {other:?}"),
    }
}

#[test]
fn test_build_ext_eq_expr_set_expands_to_forall_contains() {
    let lhs = set_var("lhs");
    let rhs = set_var("rhs");
    let elem_ty = TrustVcType::Int { width: 32 };
    let elem_name = "__trust_vc_ext_set_elem".to_string();
    let elem_var = crate::ir_builder::var(&elem_name, elem_ty.clone());

    let lhs_has = crate::ir_builder::collection_op(
        CollectionOp::Contains,
        lhs.clone(),
        Some("lhs"),
        vec![elem_var.clone()],
        TrustVcType::Bool,
    );
    let rhs_has = crate::ir_builder::collection_op(
        CollectionOp::Contains,
        rhs.clone(),
        Some("rhs"),
        vec![elem_var],
        TrustVcType::Bool,
    );

    let expected = crate::ir_builder::forall(
        vec![(elem_name, elem_ty)],
        crate::ir_builder::eq(lhs_has, rhs_has),
        None,
    );

    assert_eq!(build_ext_eq_expr(set_var("lhs"), set_var("rhs")), expected);
}

#[test]
fn test_build_ext_eq_expr_multiset_expands_to_forall_count_eq() {
    let lhs = multiset_var("lhs");
    let rhs = multiset_var("rhs");
    let elem_ty = TrustVcType::Int { width: 32 };
    let elem_name = "__trust_vc_ext_multiset_elem".to_string();
    let elem_var = crate::ir_builder::var(&elem_name, elem_ty.clone());
    let count_ty = TrustVcType::Nat;

    let lhs_count = crate::ir_builder::collection_op(
        CollectionOp::Count,
        lhs.clone(),
        Some("lhs"),
        vec![elem_var.clone()],
        count_ty.clone(),
    );
    let rhs_count = crate::ir_builder::collection_op(
        CollectionOp::Count,
        rhs.clone(),
        Some("rhs"),
        vec![elem_var],
        count_ty,
    );

    let expected = crate::ir_builder::forall(
        vec![(elem_name, elem_ty)],
        crate::ir_builder::eq(lhs_count, rhs_count),
        None,
    );

    assert_eq!(
        build_ext_eq_expr(multiset_var("lhs"), multiset_var("rhs")),
        expected
    );
}

#[test]
fn test_finite_multiset_ext_eq_deduplicates_support_but_preserves_duplicate_counts() {
    let a = i32_var("a");
    let b = i32_var("b");
    let lhs = multiset_insert(
        multiset_insert(multiset_insert(multiset_empty(), a.clone()), a.clone()),
        b.clone(),
    );
    let rhs = multiset_insert(
        multiset_insert(multiset_insert(multiset_empty(), b), a.clone()),
        a,
    );

    let result = build_ext_eq_expr(lhs, rhs);
    assert!(
        !matches!(result, TrustVcExpr::Quantifier { .. }),
        "finite empty-rooted multiset equality must use exact ground support"
    );
    let rendered = format!("{result:?}");
    assert_eq!(
        rendered.matches("op: Count").count(),
        4,
        "two structurally unique support keys require exactly two count comparisons"
    );
}

#[test]
fn test_finite_multiset_ext_eq_duplicate_mismatch_remains_discriminating() {
    let a = i32_var("a");
    let lhs = multiset_insert(multiset_insert(multiset_empty(), a.clone()), a.clone());
    let rhs = multiset_insert(multiset_empty(), a);

    let result = build_ext_eq_expr(lhs, rhs);
    assert!(
        !matches!(result, TrustVcExpr::BoolLit(true)),
        "different finite multiplicities must retain a real count equality obligation"
    );
    assert!(format!("{result:?}").contains("Count"));
}

#[test]
fn test_multiset_ext_eq_symbolic_base_preserves_quantified_fallback() {
    let a = i32_var("a");
    let lhs = multiset_insert(multiset_var("lhs"), a.clone());
    let rhs = multiset_insert(multiset_var("rhs"), a);

    assert!(matches!(
        build_ext_eq_expr(lhs, rhs),
        TrustVcExpr::Quantifier {
            kind: crate::ir_expr::QuantifierKind::Forall,
            ..
        }
    ));
}

#[test]
fn test_multiset_ext_eq_over_finite_cap_preserves_quantified_fallback() {
    let mut lhs = multiset_empty();
    let mut rhs = multiset_empty();
    for i in 0..=MULTISET_EXT_EQ_FINITE_SUPPORT_CAP / 2 {
        let elem = crate::ir_builder::int_lit(i as i128, TrustVcType::Int { width: 32 });
        lhs = multiset_insert(lhs, elem.clone());
        rhs = multiset_insert(rhs, elem);
    }

    assert!(matches!(
        build_ext_eq_expr(lhs, rhs),
        TrustVcExpr::Quantifier {
            kind: crate::ir_expr::QuantifierKind::Forall,
            ..
        }
    ));
}

#[test]
fn test_multiset_ext_eq_single_chain_over_cap_preserves_quantified_fallback() {
    let mut lhs = multiset_empty();
    for i in 0..=MULTISET_EXT_EQ_FINITE_SUPPORT_CAP {
        let elem = crate::ir_builder::int_lit(i as i128, TrustVcType::Int { width: 32 });
        lhs = multiset_insert(lhs, elem);
    }

    assert!(matches!(
        build_ext_eq_expr(lhs, multiset_empty()),
        TrustVcExpr::Quantifier {
            kind: crate::ir_expr::QuantifierKind::Forall,
            ..
        }
    ));
}

#[test]
fn test_multiset_ext_eq_malformed_cross_element_insert_fails_closed_to_forall() {
    let malformed_key = crate::ir_builder::var("wide", TrustVcType::Uint { width: 64 });
    let lhs = multiset_insert(multiset_empty(), malformed_key);
    let rhs = multiset_empty();

    assert!(matches!(
        build_ext_eq_expr(lhs, rhs),
        TrustVcExpr::Quantifier {
            kind: crate::ir_expr::QuantifierKind::Forall,
            ..
        }
    ));
}

#[test]
fn test_multiset_ext_eq_malformed_cross_element_constructor_fails_closed_to_forall() {
    let malformed_empty = TrustVcExpr::FnCall {
        name: format!(
            "{}Multiset_u64_empty",
            crate::ir_lowering::COLLECTION_CONSTRUCTOR_PREFIX
        ),
        args: vec![],
        return_ty: TrustVcType::Multiset(Box::new(TrustVcType::Uint { width: 64 })),
    };
    // Forge an outer i32 Multiset result around the wrong receiver. The public
    // lowering path never creates this shape; finite support must still reject
    // it rather than manufacturing a cross-sort count comparison.
    let lhs = multiset_insert(malformed_empty, i32_var("a"));
    let rhs = multiset_empty();

    assert!(matches!(
        build_ext_eq_expr(lhs, rhs),
        TrustVcExpr::Quantifier {
            kind: crate::ir_expr::QuantifierKind::Forall,
            ..
        }
    ));
}

#[test]
fn test_build_ext_eq_expr_map_expands_to_key_membership_and_value_eq() {
    let lhs = map_var("lhs");
    let rhs = map_var("rhs");
    let key_ty = TrustVcType::Int { width: 32 };
    let value_ty = TrustVcType::Bool;
    let key_name = "__trust_vc_ext_map_key".to_string();
    let key_var = crate::ir_builder::var(&key_name, key_ty.clone());

    let lhs_has = crate::ir_builder::collection_op(
        CollectionOp::ContainsKey,
        lhs.clone(),
        Some("lhs"),
        vec![key_var.clone()],
        TrustVcType::Bool,
    );
    let rhs_has = crate::ir_builder::collection_op(
        CollectionOp::ContainsKey,
        rhs.clone(),
        Some("rhs"),
        vec![key_var.clone()],
        TrustVcType::Bool,
    );
    let lhs_value = crate::ir_builder::collection_op(
        CollectionOp::Get,
        lhs,
        Some(MAP_EXTENSIONAL_SELECT_RECEIVER),
        vec![key_var.clone()],
        value_ty.clone(),
    );
    let rhs_value = crate::ir_builder::collection_op(
        CollectionOp::Get,
        rhs,
        Some(MAP_EXTENSIONAL_SELECT_RECEIVER),
        vec![key_var],
        value_ty,
    );

    let expected = crate::ir_builder::forall(
        vec![(key_name, key_ty)],
        crate::ir_builder::and(
            crate::ir_builder::eq(lhs_has.clone(), rhs_has),
            crate::ir_builder::implies(lhs_has, crate::ir_builder::eq(lhs_value, rhs_value)),
        ),
        None,
    );

    assert_eq!(build_ext_eq_expr(map_var("lhs"), map_var("rhs")), expected);
}

#[test]
fn test_build_ext_eq_expr_spec_fn_closures_expands_to_forall_body_eq() {
    let lhs = spec_closure(
        "i",
        crate::ir_builder::add(
            crate::ir_builder::var("i", TrustVcType::Int { width: 32 }),
            crate::ir_builder::int_lit(1, TrustVcType::Int { width: 32 }),
            TrustVcType::Int { width: 32 },
        ),
    );
    let rhs = spec_closure(
        "j",
        crate::ir_builder::add(
            crate::ir_builder::int_lit(1, TrustVcType::Int { width: 32 }),
            crate::ir_builder::var("j", TrustVcType::Int { width: 32 }),
            TrustVcType::Int { width: 32 },
        ),
    );

    let bound_name = "__trust_vc_ext_spec_arg0".to_string();
    let bound_ty = TrustVcType::Int { width: 32 };
    let bound = crate::ir_builder::var(&bound_name, bound_ty.clone());
    let expected = crate::ir_builder::forall(
        vec![(bound_name, bound_ty.clone())],
        crate::ir_builder::eq(
            crate::ir_builder::add(
                bound.clone(),
                crate::ir_builder::int_lit(1, bound_ty.clone()),
                bound_ty.clone(),
            ),
            crate::ir_builder::add(
                crate::ir_builder::int_lit(1, bound_ty.clone()),
                bound,
                bound_ty,
            ),
        ),
        None,
    );

    assert_eq!(build_ext_eq_expr(lhs, rhs), expected);
}

#[test]
fn test_build_ext_eq_expr_spec_fn_math_int_closures_expands_to_forall_body_eq() {
    let lhs = TrustVcExpr::SpecClosure {
        params: vec![("i".to_string(), TrustVcType::MathInt)],
        body: Box::new(crate::ir_builder::add(
            crate::ir_builder::var("i", TrustVcType::MathInt),
            crate::ir_builder::int_lit(1, TrustVcType::MathInt),
            TrustVcType::MathInt,
        )),
        ty: TrustVcType::SpecFn(vec![TrustVcType::MathInt], Box::new(TrustVcType::MathInt)),
    };
    let rhs = TrustVcExpr::SpecClosure {
        params: vec![("j".to_string(), TrustVcType::MathInt)],
        body: Box::new(crate::ir_builder::add(
            crate::ir_builder::int_lit(1, TrustVcType::MathInt),
            crate::ir_builder::var("j", TrustVcType::MathInt),
            TrustVcType::MathInt,
        )),
        ty: TrustVcType::SpecFn(vec![TrustVcType::MathInt], Box::new(TrustVcType::MathInt)),
    };

    let bound_name = "__trust_vc_ext_spec_arg0".to_string();
    let bound = crate::ir_builder::var(&bound_name, TrustVcType::MathInt);
    let expected = crate::ir_builder::forall(
        vec![(bound_name, TrustVcType::MathInt)],
        crate::ir_builder::eq(
            crate::ir_builder::add(
                bound.clone(),
                crate::ir_builder::int_lit(1, TrustVcType::MathInt),
                TrustVcType::MathInt,
            ),
            crate::ir_builder::add(
                crate::ir_builder::int_lit(1, TrustVcType::MathInt),
                bound,
                TrustVcType::MathInt,
            ),
        ),
        None,
    );

    assert_eq!(build_ext_eq_expr(lhs, rhs), expected);
}

#[test]
fn test_build_ext_eq_expr_spec_fn_closures_freshens_bound_name_against_free_vars() {
    let free_name = "__trust_vc_ext_spec_arg0";
    let int_ty = TrustVcType::Int { width: 32 };
    let free_var = crate::ir_builder::var(free_name, int_ty.clone());
    let lhs = spec_closure(
        "i",
        crate::ir_builder::add(
            crate::ir_builder::var("i", int_ty.clone()),
            free_var.clone(),
            int_ty.clone(),
        ),
    );
    let rhs = spec_closure(
        "j",
        crate::ir_builder::add(
            crate::ir_builder::var("j", int_ty.clone()),
            free_var,
            int_ty,
        ),
    );

    let body = assert_forall_bound_name(build_ext_eq_expr(lhs, rhs), "__trust_vc_ext_spec_arg0_1");
    assert!(
        crate::ir_expr_traversal::free_root_names(&body).contains(free_name),
        "free variable named like the default generated binder must not be captured"
    );
}

#[test]
fn test_build_ext_eq_expr_spec_fn_calls_normalizes_apply_arguments() {
    let int_ty = TrustVcType::Int { width: 32 };
    let spec_fn_ty = spec_fn_i32_i32_ty();
    let f = crate::ir_builder::var("f", spec_fn_ty.clone());

    let lhs = spec_closure(
        "n",
        crate::ir_builder::spec_fn_apply(
            f.clone(),
            std::slice::from_ref(&int_ty),
            vec![i32_add(i32_add(i32_var("n"), i32_var("k2")), i32_var("k1"))],
            int_ty.clone(),
        ),
    );
    let rhs = spec_closure(
        "n",
        crate::ir_builder::spec_fn_apply(
            f.clone(),
            std::slice::from_ref(&int_ty),
            vec![i32_add(i32_var("n"), i32_add(i32_var("k1"), i32_var("k2")))],
            int_ty.clone(),
        ),
    );

    let body = assert_forall_bound_name(build_ext_eq_expr(lhs, rhs), "__trust_vc_ext_spec_arg0");
    let TrustVcExpr::Compare { left, right, .. } = *body else {
        panic!("expected equality over SpecFn application calls");
    };
    let (
        TrustVcExpr::FnCall {
            args: left_args, ..
        },
        TrustVcExpr::FnCall {
            args: right_args, ..
        },
    ) = (*left, *right)
    else {
        panic!("expected SpecFn application calls on both equality sides");
    };

    assert_eq!(left_args.len(), 2);
    assert_eq!(right_args.len(), 2);
    assert_eq!(left_args[0], f);
    assert_eq!(right_args[0], f);
    assert_eq!(
        left_args[1], right_args[1],
        "arithmetic-equivalent internal SpecFn application arguments must canonicalize"
    );
}

#[test]
fn test_spec_fn_apply_argument_normalization_requires_exact_internal_shape() {
    let int_ty = TrustVcType::Int { width: 32 };
    let source_call = TrustVcExpr::FnCall {
        // A source function may legally share the reserved-looking prefix.
        // Prefix spelling alone must not grant internal-call provenance.
        name: format!("{}user", crate::ir_builder::SPEC_FN_APPLY_PREFIX),
        args: vec![
            i32_var("ordinary_first_arg"),
            i32_add(i32_add(i32_var("n"), i32_var("k2")), i32_var("k1")),
        ],
        return_ty: int_ty,
    };

    assert_eq!(
        normalize_spec_fn_apply_args(source_call.clone()),
        source_call,
        "a source call with an internal-looking prefix must remain byte-for-byte IR-identical",
    );
}

#[test]
fn test_build_ext_eq_expr_seq_freshens_index_name_against_free_operands() {
    let result = build_ext_eq_expr(seq_var("__trust_vc_ext_seq_idx"), seq_var("rhs"));

    let body = match result {
        TrustVcExpr::Logic {
            op: crate::ir_expr::LogicOp::And,
            right,
            ..
        } => assert_forall_bound_name(*right, "__trust_vc_ext_seq_idx_1"),
        other => panic!("expected seq extensional equality formula, got {other:?}"),
    };
    assert!(
        crate::ir_expr_traversal::free_root_names(&body).contains("__trust_vc_ext_seq_idx"),
        "the operand variable must remain free in the generated formula"
    );
}

#[test]
fn test_build_ext_ne_expr_wraps_ext_eq_in_not() {
    let lhs = seq_var("lhs");
    let rhs = seq_var("rhs");
    assert_eq!(
        build_ext_ne_expr(lhs.clone(), rhs.clone()),
        crate::ir_builder::not(build_ext_eq_expr(lhs, rhs))
    );
}
