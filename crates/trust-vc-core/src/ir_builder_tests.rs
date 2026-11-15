//! Unit tests for ir_builder.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_builder_bool_lit() {
    assert_eq!(bool_lit(true), TrustVcExpr::BoolLit(true));
    assert_eq!(bool_lit(false), TrustVcExpr::BoolLit(false));
}

#[test]
fn test_builder_unit_lit() {
    assert_eq!(unit_lit(), TrustVcExpr::UnitLit);
}

#[test]
fn test_builder_int_lit_typed() {
    let expr = int_lit(42, TrustVcType::Int { width: 32 });
    assert_eq!(
        expr,
        TrustVcExpr::IntLit {
            value: 42,
            ty: TrustVcType::Int { width: 32 }
        }
    );
}

#[test]
fn test_builder_var() {
    let expr = var("x", TrustVcType::Int { width: 32 });
    assert_eq!(
        expr,
        TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Int { width: 32 }
        }
    );
}

#[test]
fn test_builder_compare_gt() {
    let left = var("x", TrustVcType::Int { width: 32 });
    let right = i32_lit(0);
    let expr = gt(left.clone(), right.clone());
    assert_eq!(
        expr,
        TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(left),
            right: Box::new(right),
        }
    );
}

#[test]
fn test_builder_arith_add() {
    let ty = TrustVcType::Int { width: 32 };
    let left = var("x", ty.clone());
    let right = i32_lit(1);
    let expr = add(left.clone(), right.clone(), ty.clone());
    assert_eq!(
        expr,
        TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(left),
            right: Box::new(right),
            ty,
        }
    );
}

#[test]
fn test_builder_arith_inferred_seq_add_operator() {
    let seq_ty = TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }));
    let left = var("s", seq_ty.clone());
    let right = var("t", seq_ty.clone());
    let expr = arith_inferred(ArithOp::Add, left.clone(), right.clone());

    assert_eq!(
        expr,
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Add,
            receiver: Box::new(left),
            receiver_name: Some("s".to_string()),
            args: vec![right],
            ty: seq_ty,
        }
    );
}

#[test]
fn test_builder_special_arith_inferred_bool_xor_as_inequality() {
    let left = var("a", TrustVcType::Bool);
    let right = var("b", TrustVcType::Bool);
    let expr = special_arith_inferred(SpecialArithOp::BitXor, left.clone(), right.clone());

    assert_eq!(
        expr,
        TrustVcExpr::Compare {
            op: CompareOp::Ne,
            left: Box::new(left),
            right: Box::new(right),
        }
    );
}

#[test]
fn test_builder_logic_and() {
    let a = bool_lit(true);
    let b = bool_lit(false);
    let expr = and(a.clone(), b.clone());
    assert_eq!(
        expr,
        TrustVcExpr::Logic {
            op: LogicOp::And,
            left: Box::new(a),
            right: Box::new(b),
        }
    );
}

#[test]
fn test_builder_implies() {
    let p = bool_lit(true);
    let q = bool_lit(false);
    let expr = implies(p.clone(), q.clone());
    assert_eq!(
        expr,
        TrustVcExpr::Implies {
            premise: Box::new(p),
            conclusion: Box::new(q),
        }
    );
}

#[test]
fn test_builder_forall() {
    let body = gt(var("i", TrustVcType::Int { width: 32 }), i32_lit(0));
    let expr = forall(
        vec![("i".to_string(), TrustVcType::Int { width: 32 })],
        body.clone(),
        None,
    );
    assert_eq!(
        expr,
        TrustVcExpr::Quantifier {
            kind: QuantifierKind::Forall,
            bound_vars: vec![("i".to_string(), TrustVcType::Int { width: 32 })],
            body: Box::new(body),
            triggers: None,
            trigger_inference_mode: None,
        }
    );
}

#[test]
fn test_builder_composite_expression() {
    // Build: x + 1 > 0
    let ty = TrustVcType::Int { width: 32 };
    let expr = gt(add(var("x", ty.clone()), i32_lit(1), ty), i32_lit(0));
    // Just verify it constructs without panic and is a Compare
    assert!(matches!(
        expr,
        TrustVcExpr::Compare {
            op: CompareOp::Gt,
            ..
        }
    ));
}

#[test]
fn test_builder_fn_call() {
    let expr = fn_call("f", vec![i32_lit(5)], TrustVcType::Int { width: 32 });
    assert_eq!(
        expr,
        TrustVcExpr::FnCall {
            name: "f".to_string(),
            args: vec![i32_lit(5)],
            return_ty: TrustVcType::Int { width: 32 },
        }
    );
}

fn named_datatype(name: &str) -> TrustVcType {
    TrustVcType::Datatype {
        name: name.to_string(),
        variants: Vec::new(),
    }
}

#[test]
fn closure_uf_symbols_are_injective_over_type_spelling_and_argument_boundaries() {
    let ret = TrustVcType::Nat;

    // The former punctuation-to-underscore encoding mapped both spellings to
    // `a__B`, even though they are distinct nominal types.
    assert_ne!(
        spec_fn_apply_symbol(&[named_datatype("a::B")], &ret),
        spec_fn_apply_symbol(&[named_datatype("a__B")], &ret),
    );

    // Joining sanitized components with `_` also lost argument boundaries.
    assert_ne!(
        call_requires_symbol(&[named_datatype("A_B"), named_datatype("C")]),
        call_requires_symbol(&[named_datatype("A"), named_datatype("B_C")]),
    );
    assert_ne!(
        call_ensures_symbol(&[named_datatype("A_B"), named_datatype("C")], &ret),
        call_ensures_symbol(&[named_datatype("A"), named_datatype("B_C")], &ret),
    );

    // Presentation strings are not type identities: all of these spell `T`,
    // and the distinction must survive below recursive constructors too.
    let type_param = TrustVcType::TypeParam("T".to_string());
    let datatype = named_datatype("T");
    let opaque = TrustVcType::Opaque("T".to_string());
    assert_ne!(
        spec_fn_apply_symbol(std::slice::from_ref(&type_param), &ret),
        spec_fn_apply_symbol(std::slice::from_ref(&datatype), &ret),
    );
    assert_ne!(
        spec_fn_apply_symbol(std::slice::from_ref(&datatype), &ret),
        spec_fn_apply_symbol(&[opaque], &ret),
    );
    assert_ne!(
        call_requires_symbol(&[TrustVcType::Seq(Box::new(type_param))]),
        call_requires_symbol(&[TrustVcType::Seq(Box::new(datatype))]),
    );
}

#[test]
fn closure_uf_symbol_encoding_is_stable_for_int_to_nat() {
    assert_eq!(
        spec_fn_apply_symbol(&[TrustVcType::MathInt], &TrustVcType::Nat),
        "__trust_vc_spec_fn_apply_x696e74_to_x6e6174",
    );
}
