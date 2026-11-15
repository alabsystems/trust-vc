//! Coverage tests for `eval.rs` compute-mode helpers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! These regressions cover the remaining private helper branches in
//! `try_reduce_to_int` and `try_compute_eval` without touching the production
//! file, keeping the PROVER slice test-only.

use super::*;

use crate::ir::{
    ArithOp, CollectionOp, CompareOp, DatatypeVariant, LogicOp, QuantifierKind, SpecialArithOp,
    TrustVcExpr, TrustVcType,
};
use crate::ir_expr::{MatchArm, MatchPattern};

fn i32_lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value,
        ty: i32_ty(),
    }
}

fn math_int_lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value,
        ty: TrustVcType::MathInt,
    }
}

fn nat_lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value,
        ty: TrustVcType::Nat,
    }
}

fn u8_ty() -> TrustVcType {
    TrustVcType::Uint { width: 8 }
}

fn i8_ty() -> TrustVcType {
    TrustVcType::Int { width: 8 }
}

fn char_ty() -> TrustVcType {
    TrustVcType::Char
}

fn u32_ty() -> TrustVcType {
    TrustVcType::Uint { width: 32 }
}

fn usize_ty() -> TrustVcType {
    TrustVcType::Uint {
        width: crate::ir::pointer_width(),
    }
}

fn u8_lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit { value, ty: u8_ty() }
}

fn i8_lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit { value, ty: i8_ty() }
}

fn char_lit(value: char) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value: i128::from(u32::from(value)),
        ty: char_ty(),
    }
}

fn u32_lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value,
        ty: u32_ty(),
    }
}

fn usize_lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value,
        ty: usize_ty(),
    }
}

fn i32_var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: i32_ty(),
    }
}

fn bool_var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: crate::ir::TrustVcType::Bool,
    }
}

fn seq_ty(elem_ty: TrustVcType) -> TrustVcType {
    TrustVcType::Seq(Box::new(elem_ty))
}

fn seq_empty(elem_ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: format!(
            "{}eval_compute_seq_empty",
            crate::ir_lowering::COLLECTION_CONSTRUCTOR_PREFIX
        ),
        args: vec![],
        return_ty: seq_ty(elem_ty),
    }
}

fn seq_var(name: &str, elem_ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: seq_ty(elem_ty),
    }
}

fn seq_push(receiver: TrustVcExpr, value: TrustVcExpr, elem_ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::CollectionOp {
        op: CollectionOp::Push,
        receiver: Box::new(receiver),
        receiver_name: None,
        args: vec![value],
        ty: seq_ty(elem_ty),
    }
}

fn seq_from_values(elem_ty: TrustVcType, values: Vec<TrustVcExpr>) -> TrustVcExpr {
    values
        .into_iter()
        .fold(seq_empty(elem_ty.clone()), |receiver, value| {
            seq_push(receiver, value, elem_ty.clone())
        })
}

fn seq_len(receiver: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::CollectionOp {
        op: CollectionOp::Len,
        receiver: Box::new(receiver),
        receiver_name: None,
        args: vec![],
        ty: usize_ty(),
    }
}

fn seq_get(receiver: TrustVcExpr, index: TrustVcExpr, elem_ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::CollectionOp {
        op: CollectionOp::Get,
        receiver: Box::new(receiver),
        receiver_name: None,
        args: vec![index],
        ty: elem_ty,
    }
}

fn seq_contains(receiver: TrustVcExpr, value: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::CollectionOp {
        op: CollectionOp::Contains,
        receiver: Box::new(receiver),
        receiver_name: None,
        args: vec![value],
        ty: TrustVcType::Bool,
    }
}

fn seq_is_empty(receiver: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::CollectionOp {
        op: CollectionOp::IsEmpty,
        receiver: Box::new(receiver),
        receiver_name: None,
        args: vec![],
        ty: TrustVcType::Bool,
    }
}

fn seq_last(receiver: TrustVcExpr, elem_ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::CollectionOp {
        op: CollectionOp::Last,
        receiver: Box::new(receiver),
        receiver_name: None,
        args: vec![],
        ty: elem_ty,
    }
}

fn seq_update(
    receiver: TrustVcExpr,
    index: TrustVcExpr,
    value: TrustVcExpr,
    elem_ty: TrustVcType,
) -> TrustVcExpr {
    TrustVcExpr::CollectionOp {
        op: CollectionOp::Update,
        receiver: Box::new(receiver),
        receiver_name: None,
        args: vec![index, value],
        ty: seq_ty(elem_ty),
    }
}

fn seq_add(receiver: TrustVcExpr, other: TrustVcExpr, elem_ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::CollectionOp {
        op: CollectionOp::Add,
        receiver: Box::new(receiver),
        receiver_name: None,
        args: vec![other],
        ty: seq_ty(elem_ty),
    }
}

fn seq_subrange(
    receiver: TrustVcExpr,
    start: TrustVcExpr,
    end: TrustVcExpr,
    elem_ty: TrustVcType,
) -> TrustVcExpr {
    TrustVcExpr::CollectionOp {
        op: CollectionOp::Subrange,
        receiver: Box::new(receiver),
        receiver_name: None,
        args: vec![start, end],
        ty: seq_ty(elem_ty),
    }
}

fn seq_view(receiver: TrustVcExpr, elem_ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::CollectionOp {
        op: CollectionOp::View,
        receiver: Box::new(receiver),
        receiver_name: None,
        args: vec![],
        ty: seq_ty(elem_ty),
    }
}

fn seq_index(receiver: TrustVcExpr, index: TrustVcExpr, elem_ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Index {
        receiver: Box::new(receiver),
        index: Box::new(index),
        receiver_name: None,
        elem_ty,
    }
}

fn datatype_ty(name: &str, fields: Vec<(&str, TrustVcType)>) -> TrustVcType {
    TrustVcType::Datatype {
        name: name.to_string(),
        variants: vec![DatatypeVariant::new(
            name,
            fields
                .into_iter()
                .map(|(field_name, field_ty)| (field_name.to_string(), field_ty))
                .collect(),
        )],
    }
}

fn enum_ty(name: &str, variants: Vec<(&str, Vec<(&str, TrustVcType)>)>) -> TrustVcType {
    TrustVcType::Datatype {
        name: name.to_string(),
        variants: variants
            .into_iter()
            .map(|(variant, fields)| {
                DatatypeVariant::new(
                    variant,
                    fields
                        .into_iter()
                        .map(|(field_name, field_ty)| (field_name.to_string(), field_ty))
                        .collect(),
                )
            })
            .collect(),
    }
}

fn option_bool_ty() -> TrustVcType {
    enum_ty(
        "Option<bool>",
        vec![("Some", vec![("0", TrustVcType::Bool)]), ("None", vec![])],
    )
}

fn datatype_ctor(ty: TrustVcType, variant: &str, args: Vec<TrustVcExpr>) -> TrustVcExpr {
    let TrustVcType::Datatype { name, .. } = &ty else {
        panic!("datatype_ctor helper requires a datatype type");
    };
    TrustVcExpr::FnCall {
        name: crate::encoder::datatype::variant_symbol_name(name, variant),
        args,
        return_ty: ty,
    }
}

fn datatype_selector(
    receiver: TrustVcExpr,
    receiver_ty: &TrustVcType,
    variant: &str,
    field_name: &str,
    field_index: usize,
    field_ty: TrustVcType,
) -> TrustVcExpr {
    let TrustVcType::Datatype { name, .. } = receiver_ty else {
        panic!("datatype_selector helper requires a datatype type");
    };
    TrustVcExpr::FnCall {
        name: crate::encoder::datatype::selector_symbol_name(
            name,
            variant,
            field_name,
            field_index,
        ),
        args: vec![receiver],
        return_ty: field_ty,
    }
}

fn datatype_tester(receiver: TrustVcExpr, receiver_ty: &TrustVcType, variant: &str) -> TrustVcExpr {
    let TrustVcType::Datatype { name, .. } = receiver_ty else {
        panic!("datatype_tester helper requires a datatype type");
    };
    TrustVcExpr::FnCall {
        name: crate::encoder::datatype::tester_symbol_name(name, variant),
        args: vec![receiver],
        return_ty: TrustVcType::Bool,
    }
}

fn i32_arith(op: ArithOp, left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    arith(op, left, right, i32_ty())
}

fn arith(op: ArithOp, left: TrustVcExpr, right: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Arith {
        op,
        left: Box::new(left),
        right: Box::new(right),
        ty,
    }
}

fn special_arith(
    op: SpecialArithOp,
    left: TrustVcExpr,
    right: TrustVcExpr,
    ty: TrustVcType,
) -> TrustVcExpr {
    TrustVcExpr::SpecialArith {
        op,
        left: Box::new(left),
        right: Box::new(right),
        ty,
    }
}

fn compare(op: CompareOp, left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op,
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn logic(op: LogicOp, left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Logic {
        op,
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn quantifier(kind: QuantifierKind, name: &str, ty: TrustVcType, body: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Quantifier {
        kind,
        bound_vars: vec![(name.to_string(), ty)],
        body: Box::new(body),
        triggers: None,
        trigger_inference_mode: None,
    }
}

fn i32_let(name: &str, value: TrustVcExpr, body: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Let {
        name: name.to_string(),
        ty: i32_ty(),
        value: Box::new(value),
        body: Box::new(body),
    }
}

fn cast(expr: TrustVcExpr, from_ty: TrustVcType, to_ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Cast {
        expr: Box::new(expr),
        from_ty,
        to_ty,
    }
}

#[test]
fn test_try_reduce_to_int_handles_remaining_arithmetic_variants() {
    // (((10 - 4) * -3) / 2) % 5 = -4 under i128 semantics.
    // This covers the Sub/Mul/Div/Rem/Neg branches that the existing
    // Ite regression in eval.rs does not exercise directly.
    let expr = i32_arith(
        ArithOp::Rem,
        i32_arith(
            ArithOp::Div,
            i32_arith(
                ArithOp::Mul,
                i32_arith(ArithOp::Sub, i32_lit(10), i32_lit(4)),
                TrustVcExpr::Neg(Box::new(i32_lit(3))),
            ),
            i32_lit(2),
        ),
        i32_lit(5),
    );

    assert_eq!(
        AYEncoder::try_reduce_to_int(&expr),
        Some(-4),
        "remaining arithmetic variants should reduce with checked i128 semantics"
    );
}

#[test]
fn test_try_reduce_to_int_uses_euclidean_division_for_math_int() {
    for (op, left, right, expected) in [
        (ArithOp::Div, 8, 3, 2),
        (ArithOp::Div, 8, -3, -2),
        (ArithOp::Div, -8, 3, -3),
        (ArithOp::Div, -8, -3, 3),
        (ArithOp::Div, 1, 2, 0),
        (ArithOp::Div, 1, -2, 0),
        (ArithOp::Div, -1, 2, -1),
        (ArithOp::Div, -1, -2, 1),
        (ArithOp::Rem, 8, 3, 2),
        (ArithOp::Rem, 8, -3, 2),
        (ArithOp::Rem, -8, 3, 1),
        (ArithOp::Rem, -8, -3, 1),
        (ArithOp::Rem, 1, 2, 1),
        (ArithOp::Rem, 1, -2, 1),
        (ArithOp::Rem, -1, 2, 1),
        (ArithOp::Rem, -1, -2, 1),
    ] {
        let expr = arith(
            op,
            math_int_lit(left),
            math_int_lit(right),
            TrustVcType::MathInt,
        );
        assert_eq!(
            AYEncoder::try_reduce_to_int(&expr),
            Some(expected),
            "MathInt {:?} should follow Verus Euclidean semantics for {left} and {right}",
            op
        );
    }
}

#[test]
fn test_try_compute_eval_distinguishes_truncating_and_euclidean_math_int_division() {
    let euclidean_div = arith(
        ArithOp::Div,
        math_int_lit(-8),
        math_int_lit(3),
        TrustVcType::MathInt,
    );
    let euclidean_rem = arith(
        ArithOp::Rem,
        math_int_lit(-8),
        math_int_lit(3),
        TrustVcType::MathInt,
    );

    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            euclidean_div.clone(),
            math_int_lit(-3)
        )),
        Some(true),
        "MathInt -8 / 3 should compute to the Euclidean quotient"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, euclidean_div, math_int_lit(-2))),
        Some(false),
        "MathInt division must not use Rust truncating quotient semantics"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, euclidean_rem, math_int_lit(1))),
        Some(true),
        "MathInt -8 % 3 should compute to the non-negative Euclidean remainder"
    );
}

#[test]
fn test_try_reduce_to_int_returns_none_for_unevaluable_cases() {
    let div_by_zero = i32_arith(ArithOp::Div, i32_lit(1), i32_lit(0));
    let rem_by_zero = i32_arith(ArithOp::Rem, i32_lit(1), i32_lit(0));
    let symbolic_guard = TrustVcExpr::Ite {
        cond: Box::new(bool_var("cond")),
        then_branch: Box::new(i32_lit(1)),
        else_branch: Box::new(i32_lit(2)),
        ty: i32_ty(),
    };

    assert_eq!(
        AYEncoder::try_reduce_to_int(&div_by_zero),
        None,
        "division by zero must fail closed instead of folding"
    );
    assert_eq!(
        AYEncoder::try_reduce_to_int(&rem_by_zero),
        None,
        "remainder by zero must fail closed instead of folding"
    );
    assert_eq!(
        AYEncoder::try_reduce_to_int(&symbolic_guard),
        None,
        "Ite should not reduce when its guard is not computable"
    );
}

#[test]
fn test_try_reduce_to_int_returns_none_on_i128_overflow() {
    // i128::MIN.checked_neg() overflows because i128::MAX < |i128::MIN|.
    let neg_overflow = TrustVcExpr::Neg(Box::new(i32_lit(i128::MIN)));
    assert_eq!(
        AYEncoder::try_reduce_to_int(&neg_overflow),
        None,
        "negating i128::MIN must return None instead of wrapping"
    );

    // i128::MAX + 1 overflows.
    let add_overflow = i32_arith(ArithOp::Add, i32_lit(i128::MAX), i32_lit(1));
    assert_eq!(
        AYEncoder::try_reduce_to_int(&add_overflow),
        None,
        "i128::MAX + 1 must return None instead of wrapping"
    );

    // i128::MIN - 1 overflows.
    let sub_overflow = i32_arith(ArithOp::Sub, i32_lit(i128::MIN), i32_lit(1));
    assert_eq!(
        AYEncoder::try_reduce_to_int(&sub_overflow),
        None,
        "i128::MIN - 1 must return None instead of wrapping"
    );

    // i128::MAX * 2 overflows.
    let mul_overflow = i32_arith(ArithOp::Mul, i32_lit(i128::MAX), i32_lit(2));
    assert_eq!(
        AYEncoder::try_reduce_to_int(&mul_overflow),
        None,
        "i128::MAX * 2 must return None instead of wrapping"
    );

    // i128::MIN / -1 overflows (result would be i128::MAX + 1).
    let div_overflow = i32_arith(ArithOp::Div, i32_lit(i128::MIN), i32_lit(-1));
    assert_eq!(
        AYEncoder::try_reduce_to_int(&div_overflow),
        None,
        "i128::MIN / -1 must return None instead of wrapping"
    );
}

#[test]
fn test_try_reduce_to_int_fails_closed_on_typed_arithmetic_overflow() {
    let unsigned_underflow = arith(ArithOp::Sub, u8_lit(10), u8_lit(20), u8_ty());
    let signed_div_overflow = arith(ArithOp::Div, i8_lit(-128), i8_lit(-1), i8_ty());
    let nat_underflow = arith(ArithOp::Sub, nat_lit(0), nat_lit(1), TrustVcType::Nat);

    assert_eq!(
        AYEncoder::try_reduce_to_int(&unsigned_underflow),
        None,
        "u8 subtraction that would leave the type range must fail closed"
    );
    assert_eq!(
        AYEncoder::try_reduce_to_int(&signed_div_overflow),
        None,
        "i8::MIN / -1 must fail closed even though it fits in i128"
    );
    // A difference of two `nat`s is an `int` (§5b rule 6: Verus types `nat -
    // nat` as `int`), so `0 - 1` is exactly -1; it is binding it at `nat`
    // that is refused (tests/integer_typing_nat_bindings.rs).
    assert_eq!(
        AYEncoder::try_reduce_to_int(&nat_underflow),
        Some(-1),
        "a nat difference is the int it denotes"
    );
}

#[test]
fn test_try_compute_eval_discriminates_compare_ops() {
    // Exercise arithmetic reduction on both sides while also making each
    // operator distinguishable from close relatives like Eq/Le/Ge.
    for (op, left, right, expected) in [
        (CompareOp::Eq, i32_lit(3), i32_lit(3), true),
        (CompareOp::Eq, i32_lit(3), i32_lit(2), false),
        (CompareOp::Ne, i32_lit(3), i32_lit(2), true),
        (CompareOp::Ne, i32_lit(3), i32_lit(3), false),
        (CompareOp::Lt, i32_lit(2), i32_lit(3), true),
        (CompareOp::Lt, i32_lit(3), i32_lit(3), false),
        (CompareOp::Le, i32_lit(3), i32_lit(3), true),
        (CompareOp::Le, i32_lit(4), i32_lit(3), false),
        (CompareOp::Gt, i32_lit(4), i32_lit(3), true),
        (CompareOp::Gt, i32_lit(3), i32_lit(3), false),
        (CompareOp::Ge, i32_lit(3), i32_lit(3), true),
        (CompareOp::Ge, i32_lit(2), i32_lit(3), false),
    ] {
        let expr = compare(
            op,
            i32_arith(ArithOp::Add, left, i32_lit(1)),
            i32_arith(ArithOp::Add, right, i32_lit(1)),
        );
        assert_eq!(
            AYEncoder::try_compute_eval(&expr),
            Some(expected),
            "comparison op {:?} should evaluate after arithmetic reduction",
            op
        );
    }
}

#[test]
fn test_try_compute_eval_structural_equality_for_unreduced_pure_exprs() {
    let pure_call = TrustVcExpr::FnCall {
        name: "pure_id".to_string(),
        args: vec![i32_lit(5), i32_var("x")],
        return_ty: i32_ty(),
    };
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            pure_call.clone(),
            pure_call.clone()
        )),
        Some(true),
        "identical unreduced pure calls should use structural equality"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Ne,
            pure_call.clone(),
            pure_call.clone()
        )),
        Some(false),
        "identical unreduced pure calls should compute as not unequal"
    );
}

#[test]
fn test_try_compute_eval_structural_equality_skips_floats() {
    let f64_ty = TrustVcType::Float { width: 64 };
    let float_var = TrustVcExpr::Var {
        name: "x".to_string(),
        ty: f64_ty.clone(),
    };
    let point_ty = TrustVcType::Datatype {
        name: "P".to_string(),
        variants: vec![DatatypeVariant::new(
            "P",
            vec![("f".to_string(), f64_ty.clone())],
        )],
    };
    let field_read = TrustVcExpr::FnCall {
        name: "P_f".to_string(),
        args: vec![TrustVcExpr::Var {
            name: "p".to_string(),
            ty: point_ty.clone(),
        }],
        return_ty: f64_ty,
    };
    let point_var = TrustVcExpr::Var {
        name: "p".to_string(),
        ty: point_ty,
    };
    let cast_of_var = TrustVcExpr::Cast {
        expr: Box::new(float_var.clone()),
        from_ty: TrustVcType::Float { width: 64 },
        to_ty: TrustVcType::Float { width: 32 },
    };
    for operand in [float_var, field_read, point_var, cast_of_var] {
        for op in [CompareOp::Eq, CompareOp::Ne] {
            assert_eq!(
                AYEncoder::try_compute_eval(&compare(op, operand.clone(), operand.clone())),
                None,
                "`{operand:?}` compared with itself holds a float: IEEE `NaN == NaN` is \
                 false, so reflexivity must not decide it"
            );
        }
    }

    // `0.0f32` lowers to a conversion of an integer, which is never NaN.
    let zero = TrustVcExpr::Cast {
        expr: Box::new(i32_lit(0)),
        from_ty: i32_ty(),
        to_ty: TrustVcType::Float { width: 32 },
    };
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, zero.clone(), zero.clone())),
        Some(true),
        "a float converted from an integer is never NaN, so it equals itself"
    );
    let widened = TrustVcExpr::Cast {
        expr: Box::new(zero),
        from_ty: TrustVcType::Float { width: 32 },
        to_ty: TrustVcType::Float { width: 64 },
    };
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Ne, widened.clone(), widened)),
        Some(false),
        "widening a value that is never NaN keeps it off NaN"
    );
}

#[test]
fn test_try_compute_eval_structural_equality_preserves_symbolic_arithmetic() {
    let symbolic_sum = i32_arith(ArithOp::Add, i32_var("x"), i32_lit(1));

    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            symbolic_sum.clone(),
            symbolic_sum.clone()
        )),
        None,
        "structural equality must not hide symbolic checked-arithmetic obligations"
    );
}

#[test]
fn test_try_compute_eval_structural_equality_preserves_unknown_mismatches() {
    let x_plus_one = i32_arith(ArithOp::Add, i32_var("x"), i32_lit(1));
    let x_plus_two = i32_arith(ArithOp::Add, i32_var("x"), i32_lit(2));

    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            x_plus_one.clone(),
            x_plus_two.clone()
        )),
        None,
        "non-identical unknown expressions must still fail closed for equality"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Ne, x_plus_one, x_plus_two)),
        None,
        "non-identical unknown expressions must still fail closed for inequality"
    );
}

#[test]
fn test_try_compute_eval_structural_equality_preserves_known_bad_arithmetic() {
    let div_by_zero = i32_arith(ArithOp::Div, i32_lit(1), i32_lit(0));
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, div_by_zero.clone(), div_by_zero)),
        None,
        "structural equality must not hide known division by zero"
    );

    let add_overflow = i32_arith(ArithOp::Add, i32_lit(i128::MAX), i32_lit(1));
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, add_overflow.clone(), add_overflow)),
        None,
        "structural equality must not hide known checked arithmetic overflow"
    );
}

#[test]
fn test_try_compute_eval_reduces_finite_bitwise_constants() {
    let cases = [
        (
            SpecialArithOp::BitAnd,
            u8_lit(0b1010),
            u8_lit(0b1100),
            u8_lit(0b1000),
            "u8 bitand",
        ),
        (
            SpecialArithOp::BitOr,
            u8_lit(0b1010),
            u8_lit(0b0101),
            u8_lit(0b1111),
            "u8 bitor",
        ),
        (
            SpecialArithOp::BitXor,
            u8_lit(0b1010),
            u8_lit(0b1100),
            u8_lit(0b0110),
            "u8 bitxor",
        ),
        (
            SpecialArithOp::Shl,
            u8_lit(0b0001),
            u32_lit(3),
            u8_lit(0b1000),
            "u8 shl",
        ),
        (
            SpecialArithOp::Shr,
            u8_lit(0b1000),
            u32_lit(2),
            u8_lit(0b0010),
            "u8 logical shr",
        ),
        (
            SpecialArithOp::Shr,
            i8_lit(-4),
            u32_lit(1),
            i8_lit(-2),
            "i8 arithmetic shr",
        ),
    ];

    for (op, left, right, expected, label) in cases {
        let ty = crate::ir_lowering::infer_expr_type(&left);
        let expr = compare(CompareOp::Eq, special_arith(op, left, right, ty), expected);
        assert_eq!(
            AYEncoder::try_compute_eval(&expr),
            Some(true),
            "{label} should reduce under finite-width bitwise semantics"
        );
    }
}

#[test]
fn test_try_compute_eval_reduces_integer_bitwise_not() {
    let unsigned_not = compare(
        CompareOp::Eq,
        TrustVcExpr::Not(Box::new(u8_lit(0))),
        u8_lit(255),
    );
    let signed_not = compare(
        CompareOp::Eq,
        TrustVcExpr::Not(Box::new(i32_lit(0))),
        i32_lit(-1),
    );

    assert_eq!(
        AYEncoder::try_compute_eval(&unsigned_not),
        Some(true),
        "!0u8 should reduce to 255"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&signed_not),
        Some(true),
        "!0i32 should reduce to -1"
    );
}

#[test]
fn test_try_compute_eval_reduces_concrete_char_casts_and_comparisons() {
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Gt, char_lit('b'), char_lit('a'))),
        Some(true),
        "concrete char ordering should reduce by scalar value"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            cast(char_lit('A'), char_ty(), u32_ty()),
            u32_lit(65)
        )),
        Some(true),
        "char-to-integer casts should preserve concrete scalar values"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            cast(u8_lit(65), u8_ty(), char_ty()),
            char_lit('A')
        )),
        Some(true),
        "integer-to-char casts should reduce for valid Unicode scalar values"
    );

    let let_bound_char = TrustVcExpr::Let {
        name: "c".to_string(),
        ty: char_ty(),
        value: Box::new(cast(u8_lit(66), u8_ty(), char_ty())),
        body: Box::new(compare(
            CompareOp::Eq,
            TrustVcExpr::Var {
                name: "c".to_string(),
                ty: char_ty(),
            },
            char_lit('B'),
        )),
    };
    assert_eq!(
        AYEncoder::try_compute_eval(&let_bound_char),
        Some(true),
        "let-bound concrete char values should substitute and continue reducing"
    );
}

#[test]
fn test_try_compute_eval_char_casts_fail_closed_for_invalid_scalars() {
    let surrogate = cast(u32_lit(0xD800), u32_ty(), char_ty());
    let too_large = cast(u32_lit(0x11_0000), u32_ty(), char_ty());
    let negative = cast(i32_lit(-1), i32_ty(), char_ty());

    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, surrogate, char_lit('x'))),
        None,
        "surrogate scalar values must not reduce to char"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, too_large, char_lit('x'))),
        None,
        "values above Unicode scalar range must not reduce to char"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, negative, char_lit('x'))),
        None,
        "negative values must not reduce to char"
    );
}

#[test]
fn test_try_compute_eval_bitwise_fails_closed_on_width_errors() {
    let shift_by_width = compare(
        CompareOp::Eq,
        special_arith(SpecialArithOp::Shl, u8_lit(1), u32_lit(8), u8_ty()),
        u8_lit(0),
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&shift_by_width),
        None,
        "shift amounts greater than or equal to the lhs width must fail closed"
    );

    let out_of_range_operand = compare(
        CompareOp::Eq,
        special_arith(SpecialArithOp::BitAnd, u8_lit(256), u8_lit(1), u8_ty()),
        u8_lit(0),
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&out_of_range_operand),
        None,
        "bitwise operands that do not fit their finite-width type must fail closed"
    );
}

#[test]
fn test_try_compute_eval_short_circuits_and_preserves_unknowns() {
    let symbolic_compare = compare(CompareOp::Gt, i32_var("x"), i32_lit(0));

    let and_short_circuit = TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(TrustVcExpr::BoolLit(false)),
        right: Box::new(symbolic_compare.clone()),
    };
    let and_needs_rhs = TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(TrustVcExpr::BoolLit(true)),
        right: Box::new(symbolic_compare.clone()),
    };
    let or_short_circuit = TrustVcExpr::Logic {
        op: LogicOp::Or,
        left: Box::new(TrustVcExpr::BoolLit(true)),
        right: Box::new(symbolic_compare.clone()),
    };
    let or_needs_rhs = TrustVcExpr::Logic {
        op: LogicOp::Or,
        left: Box::new(TrustVcExpr::BoolLit(false)),
        right: Box::new(symbolic_compare.clone()),
    };
    let negated_compare = TrustVcExpr::Not(Box::new(compare(
        CompareOp::Gt,
        i32_arith(ArithOp::Add, i32_lit(2), i32_lit(1)),
        i32_lit(2),
    )));
    let false_premise = TrustVcExpr::Implies {
        premise: Box::new(TrustVcExpr::BoolLit(false)),
        conclusion: Box::new(symbolic_compare.clone()),
    };
    let true_conclusion = TrustVcExpr::Implies {
        premise: Box::new(symbolic_compare.clone()),
        conclusion: Box::new(TrustVcExpr::BoolLit(true)),
    };
    let concrete_false = TrustVcExpr::Implies {
        premise: Box::new(TrustVcExpr::BoolLit(true)),
        conclusion: Box::new(TrustVcExpr::BoolLit(false)),
    };

    assert_eq!(
        AYEncoder::try_compute_eval(&and_short_circuit),
        Some(false),
        "false && unknown should short-circuit to false"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&and_needs_rhs),
        None,
        "true && unknown should stay unknown"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&or_short_circuit),
        Some(true),
        "true || unknown should short-circuit to true"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&or_needs_rhs),
        None,
        "false || unknown should stay unknown"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&negated_compare),
        Some(false),
        "Not should invert a computable comparison"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&false_premise),
        Some(true),
        "false ==> unknown should short-circuit to true"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&true_conclusion),
        Some(true),
        "unknown ==> true should short-circuit to true"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&concrete_false),
        Some(false),
        "true ==> false should compute to false"
    );
}

#[test]
fn test_try_compute_eval_reduces_bool_ite() {
    let symbolic_compare = compare(CompareOp::Gt, i32_var("x"), i32_lit(0));
    let true_guard = compare(CompareOp::Gt, i32_lit(7), i32_lit(3));
    let false_guard = compare(CompareOp::Gt, i32_lit(3), i32_lit(7));

    let concrete_true = TrustVcExpr::Ite {
        cond: Box::new(true_guard),
        then_branch: Box::new(TrustVcExpr::BoolLit(true)),
        else_branch: Box::new(symbolic_compare.clone()),
        ty: TrustVcType::Bool,
    };
    let concrete_false = TrustVcExpr::Ite {
        cond: Box::new(false_guard),
        then_branch: Box::new(TrustVcExpr::BoolLit(true)),
        else_branch: Box::new(TrustVcExpr::BoolLit(false)),
        ty: TrustVcType::Bool,
    };
    let active_unknown = TrustVcExpr::Ite {
        cond: Box::new(TrustVcExpr::BoolLit(true)),
        then_branch: Box::new(symbolic_compare),
        else_branch: Box::new(TrustVcExpr::BoolLit(false)),
        ty: TrustVcType::Bool,
    };

    assert_eq!(
        AYEncoder::try_compute_eval(&concrete_true),
        Some(true),
        "bool Ite should evaluate the selected concrete branch"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&concrete_false),
        Some(false),
        "bool Ite should return false when the selected branch computes false"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&active_unknown),
        None,
        "bool Ite must fail closed when the selected branch remains symbolic"
    );
}

#[test]
fn test_try_compute_eval_reduces_let_bindings_with_shadowing() {
    let expr = i32_let(
        "x",
        i32_lit(4),
        i32_let(
            "r1",
            i32_arith(ArithOp::Add, i32_var("x"), i32_lit(1)),
            i32_let(
                "x",
                i32_lit(5),
                i32_let(
                    "r2",
                    i32_arith(ArithOp::Add, i32_var("x"), i32_lit(1)),
                    compare(CompareOp::Eq, i32_var("r1"), i32_var("r2")),
                ),
            ),
        ),
    );

    assert_eq!(
        AYEncoder::try_compute_eval(&expr),
        Some(false),
        "lets_bad-style shadowing should compute r1=5, r2=6 and return false"
    );
}

#[test]
fn test_try_reduce_to_int_reduces_let_bound_arithmetic() {
    let expr = i32_let(
        "x",
        i32_arith(ArithOp::Add, i32_lit(2), i32_lit(3)),
        i32_arith(ArithOp::Mul, i32_var("x"), i32_lit(2)),
    );

    assert_eq!(
        AYEncoder::try_reduce_to_int(&expr),
        Some(10),
        "integer reduction should evaluate let-bound arithmetic"
    );
}

#[test]
fn test_try_compute_eval_fails_closed_on_unused_bad_let_initializer() {
    let expr = i32_let(
        "x",
        i32_arith(ArithOp::Div, i32_lit(1), i32_lit(0)),
        TrustVcExpr::BoolLit(true),
    );

    assert_eq!(
        AYEncoder::try_compute_eval(&expr),
        None,
        "compute mode must not ignore an unsupported let initializer"
    );
}

#[test]
fn test_try_compute_eval_reduces_finite_sequence_constants() {
    let seq = seq_from_values(u8_ty(), vec![u8_lit(10), u8_lit(20), u8_lit(30)]);
    let same_seq = seq_from_values(u8_ty(), vec![u8_lit(10), u8_lit(20), u8_lit(30)]);
    let different_seq = seq_from_values(u8_ty(), vec![u8_lit(10), u8_lit(21), u8_lit(30)]);

    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, seq_len(seq.clone()), usize_lit(3))),
        Some(true),
        "finite Seq::len should reduce to its concrete length"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            seq_get(seq.clone(), usize_lit(1), u8_ty()),
            u8_lit(20)
        )),
        Some(true),
        "finite Seq::index/get should reduce in bounds"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            seq_index(seq.clone(), usize_lit(2), u8_ty()),
            u8_lit(30)
        )),
        Some(true),
        "bracket-style finite Seq indexing should reduce in bounds"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&seq_contains(seq.clone(), u8_lit(10))),
        Some(true),
        "finite Seq::contains should reduce for concrete membership"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, seq.clone(), same_seq)),
        Some(true),
        "finite Seq equality should compare concrete elements"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Ne, seq, different_seq)),
        Some(true),
        "finite Seq inequality should compare concrete elements"
    );
}

#[test]
fn test_try_compute_eval_sequence_counterexamples_reduce_false() {
    let seq = seq_from_values(u8_ty(), vec![u8_lit(10), u8_lit(20), u8_lit(30)]);
    let different_seq = seq_from_values(u8_ty(), vec![u8_lit(10), u8_lit(20), u8_lit(31)]);

    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, seq_len(seq.clone()), usize_lit(2))),
        Some(false),
        "wrong finite Seq length should compute to false"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            seq_get(seq.clone(), usize_lit(1), u8_ty()),
            u8_lit(21)
        )),
        Some(false),
        "wrong finite Seq element should compute to false"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&seq_contains(seq.clone(), u8_lit(99))),
        Some(false),
        "missing finite Seq element should compute contains() to false"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, seq, different_seq)),
        Some(false),
        "different finite Seq values should compute equality to false"
    );
}

#[test]
fn test_try_compute_eval_reduces_finite_sequence_push_last_update_add() {
    let pushed = seq_push(seq_empty(u8_ty()), u8_lit(4), u8_ty());
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            seq_len(pushed.clone()),
            usize_lit(1)
        )),
        Some(true),
        "finite Seq::push should extend the concrete length"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            seq_last(pushed.clone(), u8_ty()),
            u8_lit(4)
        )),
        Some(true),
        "finite Seq::last should read the last pushed element"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&seq_is_empty(pushed)),
        Some(false),
        "finite Seq::push should make an empty sequence non-empty"
    );

    let updated = seq_update(
        seq_from_values(u8_ty(), vec![u8_lit(10), u8_lit(20), u8_lit(30)]),
        usize_lit(1),
        u8_lit(50),
        u8_ty(),
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            seq_get(updated.clone(), usize_lit(0), u8_ty()),
            u8_lit(10)
        )),
        Some(true),
        "finite Seq::update should preserve elements before the updated index"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            seq_get(updated.clone(), usize_lit(1), u8_ty()),
            u8_lit(50)
        )),
        Some(true),
        "finite Seq::update should replace the target element"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            seq_get(updated, usize_lit(2), u8_ty()),
            u8_lit(30)
        )),
        Some(true),
        "finite Seq::update should preserve elements after the updated index"
    );

    let joined = seq_add(
        seq_from_values(u8_ty(), vec![u8_lit(1), u8_lit(2), u8_lit(3)]),
        seq_from_values(u8_ty(), vec![u8_lit(4), u8_lit(5)]),
        u8_ty(),
    );
    let expected = seq_from_values(
        u8_ty(),
        vec![u8_lit(1), u8_lit(2), u8_lit(3), u8_lit(4), u8_lit(5)],
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            seq_len(joined.clone()),
            usize_lit(5)
        )),
        Some(true),
        "finite Seq::add should compute the concatenated length"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, joined, expected)),
        Some(true),
        "finite Seq::add should concatenate concrete elements in order"
    );
}

#[test]
fn test_try_compute_eval_sequence_push_update_last_add_counterexamples_reduce_false() {
    let pushed = seq_push(seq_empty(u8_ty()), u8_lit(4), u8_ty());
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            seq_last(pushed, u8_ty()),
            u8_lit(5)
        )),
        Some(false),
        "wrong finite Seq::last value should compute to false"
    );

    let updated = seq_update(
        seq_from_values(u8_ty(), vec![u8_lit(1), u8_lit(2), u8_lit(3)]),
        usize_lit(1),
        u8_lit(5),
        u8_ty(),
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            seq_get(updated, usize_lit(1), u8_ty()),
            u8_lit(2)
        )),
        Some(false),
        "wrong finite Seq::update value should compute to false"
    );

    let joined = seq_add(
        seq_from_values(u8_ty(), vec![u8_lit(1), u8_lit(2), u8_lit(3)]),
        seq_from_values(u8_ty(), vec![u8_lit(4), u8_lit(5)]),
        u8_ty(),
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, seq_len(joined), usize_lit(4))),
        Some(false),
        "wrong finite Seq::add length should compute to false"
    );
}

#[test]
fn test_try_compute_eval_sequence_lets_and_updates() {
    let base = seq_from_values(u8_ty(), vec![u8_lit(10), u8_lit(20), u8_lit(30)]);
    let mut updated = seq_update(seq_var("s", u8_ty()), usize_lit(1), u8_lit(25), u8_ty());
    if let TrustVcExpr::CollectionOp { receiver_name, .. } = &mut updated {
        *receiver_name = Some("s".to_string());
    };
    let expr = TrustVcExpr::Let {
        name: "s".to_string(),
        ty: seq_ty(u8_ty()),
        value: Box::new(base),
        body: Box::new(compare(
            CompareOp::Eq,
            seq_get(updated, usize_lit(1), u8_ty()),
            u8_lit(25),
        )),
    };

    assert_eq!(
        AYEncoder::try_compute_eval(&expr),
        Some(true),
        "let-bound finite Seq values should substitute and continue reducing"
    );
}

#[test]
fn test_try_compute_eval_sequence_view_and_cast_constants() {
    let seq = seq_from_values(u8_ty(), vec![u8_lit(10), u8_lit(20), u8_lit(30)]);
    let viewed = seq_view(seq, u8_ty());
    let casted = TrustVcExpr::Cast {
        expr: Box::new(viewed),
        from_ty: seq_ty(u8_ty()),
        to_ty: seq_ty(u8_ty()),
    };

    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            seq_get(casted.clone(), usize_lit(2), u8_ty()),
            u8_lit(30)
        )),
        Some(true),
        "array-literal-style view plus Seq cast should preserve finite elements"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&seq_contains(casted, u8_lit(40))),
        Some(false),
        "array-literal-style view plus Seq cast should still compute false contains"
    );
}

#[test]
fn test_try_compute_eval_reduces_finite_sequence_subrange() {
    let seq = seq_from_values(
        u8_ty(),
        vec![u8_lit(10), u8_lit(20), u8_lit(30), u8_lit(40)],
    );
    let subrange = seq_subrange(seq.clone(), usize_lit(1), usize_lit(3), u8_ty());
    let expected = seq_from_values(u8_ty(), vec![u8_lit(20), u8_lit(30)]);
    let wrong = seq_from_values(u8_ty(), vec![u8_lit(10), u8_lit(30)]);

    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, subrange.clone(), expected)),
        Some(true),
        "finite Seq::subrange should reduce to the concrete bounded slice"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, subrange.clone(), wrong)),
        Some(false),
        "finite Seq::subrange equality should reject wrong concrete elements"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, seq_len(subrange), usize_lit(2))),
        Some(true),
        "finite Seq::subrange length should reduce after slicing"
    );
}

#[test]
fn test_try_compute_eval_sequence_fails_closed_on_symbolic_or_bad_indices() {
    let symbolic_seq = seq_from_values(i32_ty(), vec![i32_var("x")]);
    let concrete_seq = seq_from_values(u8_ty(), vec![u8_lit(10), u8_lit(20)]);

    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            seq_get(symbolic_seq, usize_lit(0), i32_ty()),
            i32_lit(0)
        )),
        None,
        "finite Seq compute must fail closed when any element is symbolic"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            seq_get(concrete_seq.clone(), usize_lit(2), u8_ty()),
            u8_lit(0)
        )),
        None,
        "out-of-bounds finite Seq indexing must fail closed"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            seq_get(concrete_seq, i32_var("i"), u8_ty()),
            u8_lit(10)
        )),
        None,
        "symbolic finite Seq indices must fail closed"
    );
}

#[test]
fn test_try_compute_eval_sequence_subrange_fails_closed_on_bad_bounds() {
    let seq = seq_from_values(u8_ty(), vec![u8_lit(10), u8_lit(20), u8_lit(30)]);
    let inverted = seq_subrange(seq.clone(), usize_lit(2), usize_lit(1), u8_ty());
    let out_of_bounds = seq_subrange(seq.clone(), usize_lit(0), usize_lit(4), u8_ty());
    let symbolic_start = seq_subrange(seq, i32_var("i"), usize_lit(2), u8_ty());

    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            inverted,
            seq_from_values(u8_ty(), vec![])
        )),
        None,
        "inverted finite Seq::subrange bounds must fail closed"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            out_of_bounds,
            seq_from_values(u8_ty(), vec![])
        )),
        None,
        "out-of-bounds finite Seq::subrange bounds must fail closed"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            symbolic_start,
            seq_from_values(u8_ty(), vec![u8_lit(20)])
        )),
        None,
        "symbolic finite Seq::subrange bounds must fail closed"
    );
}

#[test]
fn test_try_compute_eval_sequence_update_and_last_fail_closed_on_bad_inputs() {
    let seq = seq_from_values(u8_ty(), vec![u8_lit(10), u8_lit(20)]);
    let out_of_bounds_update = seq_update(seq.clone(), usize_lit(2), u8_lit(30), u8_ty());
    let symbolic_index_update = seq_update(seq, i32_var("i"), u8_lit(30), u8_ty());
    let symbolic_value_update = seq_update(
        seq_from_values(i32_ty(), vec![i32_lit(10), i32_lit(20)]),
        usize_lit(1),
        i32_var("x"),
        i32_ty(),
    );
    let empty_last = seq_last(seq_empty(u8_ty()), u8_ty());

    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            out_of_bounds_update,
            seq_from_values(u8_ty(), vec![u8_lit(10), u8_lit(30)])
        )),
        None,
        "out-of-bounds finite Seq::update must fail closed"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            symbolic_index_update,
            seq_from_values(u8_ty(), vec![u8_lit(10), u8_lit(30)])
        )),
        None,
        "symbolic finite Seq::update index must fail closed"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(
            CompareOp::Eq,
            symbolic_value_update,
            seq_from_values(i32_ty(), vec![i32_lit(10), i32_lit(0)])
        )),
        None,
        "symbolic finite Seq::update value must fail closed"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, empty_last, u8_lit(0))),
        None,
        "finite Seq::last on an empty sequence must fail closed"
    );
}

#[test]
fn test_try_compute_eval_reduces_bounded_forall_over_sequence() {
    let seq = seq_from_values(u8_ty(), vec![u8_lit(1), u8_lit(2), u8_lit(3)]);
    let i = TrustVcExpr::Var {
        name: "i".to_string(),
        ty: usize_ty(),
    };
    let guard = compare(CompareOp::Lt, i.clone(), usize_lit(3));
    let body = logic(
        LogicOp::Or,
        TrustVcExpr::Not(Box::new(guard)),
        compare(CompareOp::Ge, seq_get(seq, i.clone(), u8_ty()), u8_lit(1)),
    );

    assert_eq!(
        AYEncoder::try_compute_eval(&quantifier(QuantifierKind::Forall, "i", usize_ty(), body)),
        Some(true),
        "bounded forall should enumerate only the guarded finite index range"
    );
}

#[test]
fn test_try_compute_eval_bounded_forall_counterexample_reduces_false() {
    let seq = seq_from_values(u8_ty(), vec![u8_lit(1), u8_lit(2), u8_lit(3)]);
    let i = TrustVcExpr::Var {
        name: "i".to_string(),
        ty: usize_ty(),
    };
    let guard = compare(CompareOp::Lt, i.clone(), usize_lit(3));
    let body = logic(
        LogicOp::Or,
        TrustVcExpr::Not(Box::new(guard)),
        compare(CompareOp::Le, seq_get(seq, i.clone(), u8_ty()), u8_lit(2)),
    );

    assert_eq!(
        AYEncoder::try_compute_eval(&quantifier(QuantifierKind::Forall, "i", usize_ty(), body)),
        Some(false),
        "bounded forall should return false when an enumerated index refutes the body"
    );
}

#[test]
fn test_try_compute_eval_reduces_small_domain_exists() {
    let x = TrustVcExpr::Var {
        name: "x".to_string(),
        ty: u8_ty(),
    };
    let witness = compare(CompareOp::Eq, x, u8_lit(42));

    assert_eq!(
        AYEncoder::try_compute_eval(&quantifier(QuantifierKind::Exists, "x", u8_ty(), witness)),
        Some(true),
        "small finite integer domains should be enumerable for exists"
    );
}

#[test]
fn test_try_compute_eval_bounded_quantifiers_fail_closed_outside_slice() {
    let i = TrustVcExpr::Var {
        name: "i".to_string(),
        ty: usize_ty(),
    };
    let too_wide_guard = compare(CompareOp::Lt, i.clone(), usize_lit(600));
    let too_wide_body = logic(
        LogicOp::Or,
        TrustVcExpr::Not(Box::new(too_wide_guard)),
        compare(CompareOp::Ge, i.clone(), usize_lit(0)),
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&quantifier(
            QuantifierKind::Forall,
            "i",
            usize_ty(),
            too_wide_body
        )),
        None,
        "bounded quantifier compute must fail closed above the enumeration cap"
    );

    let unbounded_body = compare(CompareOp::Ge, i, usize_lit(0));
    assert_eq!(
        AYEncoder::try_compute_eval(&quantifier(
            QuantifierKind::Forall,
            "i",
            usize_ty(),
            unbounded_body
        )),
        None,
        "wide unguarded quantifiers must remain unsupported in compute mode"
    );
}

#[test]
fn test_try_const_eval_typed_reduces_nullary_datatype_constructor_equality() {
    let status_ty = enum_ty(
        "ComputeStatus",
        vec![("Valid", vec![]), ("Invalid", vec![])],
    );
    let valid = datatype_ctor(status_ty.clone(), "Valid", vec![]);
    let same_valid = datatype_ctor(status_ty.clone(), "Valid", vec![]);
    let invalid = datatype_ctor(status_ty, "Invalid", vec![]);

    assert_eq!(
        AYEncoder::try_const_eval_typed(&compare(CompareOp::Eq, valid.clone(), same_valid), 32),
        Some(true),
        "nullary datatype constructors with the same variant should const-fold as equal"
    );
    assert_eq!(
        AYEncoder::try_const_eval_typed(
            &compare(CompareOp::Eq, valid.clone(), invalid.clone()),
            32
        ),
        Some(false),
        "nullary datatype constructors with different variants should const-fold as unequal"
    );
    assert_eq!(
        AYEncoder::try_const_eval_typed(&compare(CompareOp::Ne, valid, invalid), 32),
        Some(true),
        "nullary datatype constructor disequality should const-fold by variant identity"
    );
}

#[test]
fn test_try_compute_eval_reduces_datatype_struct_and_tuple_like_constants() {
    let pair_ty = datatype_ty(
        "ComputePair",
        vec![("x", u8_ty()), ("flag", TrustVcType::Bool)],
    );
    let left = datatype_ctor(
        pair_ty.clone(),
        "ComputePair",
        vec![u8_lit(7), TrustVcExpr::BoolLit(true)],
    );
    let same = datatype_ctor(
        pair_ty.clone(),
        "ComputePair",
        vec![u8_lit(7), TrustVcExpr::BoolLit(true)],
    );
    let different = datatype_ctor(
        pair_ty.clone(),
        "ComputePair",
        vec![u8_lit(8), TrustVcExpr::BoolLit(true)],
    );
    let selected_x = datatype_selector(left.clone(), &pair_ty, "ComputePair", "x", 0, u8_ty());

    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, left.clone(), same)),
        Some(true),
        "datatype constructor equality should compare concrete fields"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, left.clone(), different)),
        Some(false),
        "datatype constructor equality should reject differing concrete fields"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, selected_x, u8_lit(7))),
        Some(true),
        "single-variant struct selectors should reduce from concrete constructors"
    );

    let tuple_ty = datatype_ty(
        "ComputeTuple",
        vec![("0", u8_ty()), ("1", TrustVcType::Bool)],
    );
    let tuple = datatype_ctor(
        tuple_ty.clone(),
        "ComputeTuple",
        vec![u8_lit(5), TrustVcExpr::BoolLit(false)],
    );
    let tuple_0 = datatype_selector(tuple, &tuple_ty, "ComputeTuple", "0", 0, u8_ty());

    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, tuple_0, u8_lit(5))),
        Some(true),
        "tuple-struct field selectors should reduce from concrete constructors"
    );
}

#[test]
fn test_try_compute_eval_reduces_concrete_datatype_testers() {
    let option_ty = option_bool_ty();
    let some_true = datatype_ctor(option_ty.clone(), "Some", vec![TrustVcExpr::BoolLit(true)]);
    let is_some = datatype_tester(some_true.clone(), &option_ty, "Some");
    let is_none = datatype_tester(some_true, &option_ty, "None");

    assert_eq!(
        AYEncoder::try_compute_eval(&is_some),
        Some(true),
        "datatype tester should reduce to true for the concrete variant"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&is_none),
        Some(false),
        "datatype tester should reduce to false for a different concrete variant"
    );
}

#[test]
fn test_try_compute_eval_reduces_concrete_datatype_match() {
    let option_ty = option_bool_ty();
    let some_true = datatype_ctor(option_ty.clone(), "Some", vec![TrustVcExpr::BoolLit(true)]);
    let some_false = datatype_ctor(option_ty.clone(), "Some", vec![TrustVcExpr::BoolLit(false)]);
    let none = datatype_ctor(option_ty.clone(), "None", vec![]);
    let binding = TrustVcExpr::Var {
        name: "b".to_string(),
        ty: TrustVcType::Bool,
    };

    let some_true_match = TrustVcExpr::Match {
        scrutinee: Box::new(some_true),
        arms: vec![
            MatchArm::new(
                MatchPattern::Constructor {
                    variant_name: "Some".to_string(),
                    bindings: vec!["b".to_string()],
                    has_rest: false,
                },
                binding.clone(),
            ),
            MatchArm::new(MatchPattern::Wildcard, TrustVcExpr::BoolLit(false)),
        ],
        ty: TrustVcType::Bool,
    };
    let some_false_match = TrustVcExpr::Match {
        scrutinee: Box::new(some_false),
        arms: vec![
            MatchArm::new(
                MatchPattern::Constructor {
                    variant_name: "Some".to_string(),
                    bindings: vec!["b".to_string()],
                    has_rest: false,
                },
                TrustVcExpr::Not(Box::new(binding)),
            ),
            MatchArm::new(MatchPattern::Wildcard, TrustVcExpr::BoolLit(false)),
        ],
        ty: TrustVcType::Bool,
    };
    let none_match = TrustVcExpr::Match {
        scrutinee: Box::new(none),
        arms: vec![
            MatchArm::new(
                MatchPattern::Constructor {
                    variant_name: "Some".to_string(),
                    bindings: vec![
                        crate::match_pattern_scope::IGNORED_MATCH_BINDING_PREFIX.to_string()
                            + "option_payload",
                    ],
                    has_rest: false,
                },
                TrustVcExpr::BoolLit(false),
            ),
            MatchArm::new(MatchPattern::Wildcard, TrustVcExpr::BoolLit(true)),
        ],
        ty: TrustVcType::Bool,
    };

    assert_eq!(AYEncoder::try_compute_eval(&some_true_match), Some(true));
    assert_eq!(AYEncoder::try_compute_eval(&some_false_match), Some(true));
    assert_eq!(AYEncoder::try_compute_eval(&none_match), Some(true));
}

#[test]
fn test_try_compute_eval_datatype_match_fails_closed_on_symbolic_scrutinee() {
    let option_ty = option_bool_ty();
    let symbolic_some = datatype_ctor(
        option_ty.clone(),
        "Some",
        vec![TrustVcExpr::Var {
            name: "payload".to_string(),
            ty: TrustVcType::Bool,
        }],
    );
    let expr = TrustVcExpr::Match {
        scrutinee: Box::new(symbolic_some),
        arms: vec![
            MatchArm::new(
                MatchPattern::Constructor {
                    variant_name: "Some".to_string(),
                    bindings: vec!["b".to_string()],
                    has_rest: false,
                },
                TrustVcExpr::Var {
                    name: "b".to_string(),
                    ty: TrustVcType::Bool,
                },
            ),
            MatchArm::new(MatchPattern::Wildcard, TrustVcExpr::BoolLit(false)),
        ],
        ty: TrustVcType::Bool,
    };

    assert_eq!(
        AYEncoder::try_compute_eval(&expr),
        None,
        "datatype match compute must fail closed when the scrutinee cannot reduce to a concrete constructor"
    );
}

#[test]
fn test_try_compute_eval_refutes_datatype_constructor_with_known_bad_field() {
    let car_ty = datatype_ty(
        "ComputeCar",
        vec![("passengers", u8_ty()), ("four_doors", TrustVcType::Bool)],
    );
    let passengers = TrustVcExpr::Var {
        name: "passengers".to_string(),
        ty: u8_ty(),
    };
    let left = datatype_ctor(
        car_ty.clone(),
        "ComputeCar",
        vec![passengers.clone(), TrustVcExpr::BoolLit(true)],
    );
    let right = datatype_ctor(
        car_ty.clone(),
        "ComputeCar",
        vec![passengers, TrustVcExpr::BoolLit(false)],
    );

    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, left.clone(), right.clone())),
        Some(false),
        "datatype equality should refute constructors with a definitely unequal field"
    );
    assert_eq!(
        AYEncoder::try_const_eval_typed(&compare(CompareOp::Eq, left.clone(), right.clone()), 32),
        Some(false),
        "typed const-eval should refute constructor equality with a definitely unequal field"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Ne, left, right)),
        Some(true),
        "datatype disequality should hold with a definitely unequal field"
    );
}

#[test]
fn test_try_compute_eval_datatype_constructor_fields_fail_closed_on_symbolic_mismatch() {
    let pair_ty = datatype_ty("ComputePair", vec![("x", u8_ty())]);
    let left = datatype_ctor(
        pair_ty.clone(),
        "ComputePair",
        vec![TrustVcExpr::Var {
            name: "x".to_string(),
            ty: u8_ty(),
        }],
    );
    let right = datatype_ctor(
        pair_ty.clone(),
        "ComputePair",
        vec![TrustVcExpr::Var {
            name: "y".to_string(),
            ty: u8_ty(),
        }],
    );

    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, left.clone(), right.clone())),
        None,
        "datatype constructor equality must fail closed when fields may or may not match"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Ne, left, right)),
        None,
        "datatype constructor disequality must fail closed when fields may or may not match"
    );
}

#[test]
fn test_try_compute_eval_reduces_datatype_let_bound_selector() {
    let pair_ty = datatype_ty(
        "ComputePair",
        vec![("x", u8_ty()), ("flag", TrustVcType::Bool)],
    );
    let value = datatype_ctor(
        pair_ty.clone(),
        "ComputePair",
        vec![u8_lit(11), TrustVcExpr::BoolLit(false)],
    );
    let var = TrustVcExpr::Var {
        name: "pair".to_string(),
        ty: pair_ty.clone(),
    };
    let selected = datatype_selector(var, &pair_ty, "ComputePair", "x", 0, u8_ty());
    let expr = TrustVcExpr::Let {
        name: "pair".to_string(),
        ty: pair_ty,
        value: Box::new(value),
        body: Box::new(compare(CompareOp::Eq, selected, u8_lit(11))),
    };

    assert_eq!(
        AYEncoder::try_compute_eval(&expr),
        Some(true),
        "let-bound concrete datatype values should substitute and reduce selectors"
    );
}

#[test]
fn test_try_compute_eval_datatype_constants_fail_closed_on_symbolic_or_bad_selector() {
    let pair_ty = datatype_ty(
        "ComputePair",
        vec![("x", u8_ty()), ("flag", TrustVcType::Bool)],
    );
    let symbolic = datatype_ctor(
        pair_ty.clone(),
        "ComputePair",
        vec![
            TrustVcExpr::Var {
                name: "x".to_string(),
                ty: u8_ty(),
            },
            TrustVcExpr::BoolLit(true),
        ],
    );
    let concrete = datatype_ctor(
        pair_ty.clone(),
        "ComputePair",
        vec![u8_lit(7), TrustVcExpr::BoolLit(true)],
    );
    let bad_selector = TrustVcExpr::FnCall {
        name: "ComputePair_ComputePair_missing".to_string(),
        args: vec![concrete.clone()],
        return_ty: u8_ty(),
    };

    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, symbolic, concrete.clone())),
        None,
        "datatype compute must fail closed when constructor fields are symbolic"
    );
    assert_eq!(
        AYEncoder::try_compute_eval(&compare(CompareOp::Eq, bad_selector, u8_lit(7))),
        None,
        "unknown datatype selectors must fail closed"
    );
}
