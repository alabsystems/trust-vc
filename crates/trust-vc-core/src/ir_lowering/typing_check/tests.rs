//! Unit tests of the IR typing validator.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::ir::CollectionOp;
use crate::ir_expr::{ArithOp, CompareOp, MatchArm, QuantifierKind};

const U8: TrustVcType = TrustVcType::Uint { width: 8 };
const I8: TrustVcType = TrustVcType::Int { width: 8 };
const U64: TrustVcType = TrustVcType::Uint { width: 64 };

fn lit(value: i128, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::IntLit { value, ty }
}
fn var(name: &str, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty,
    }
}
fn seq(ty: TrustVcType) -> TrustVcType {
    TrustVcType::Seq(Box::new(ty))
}
fn cop(
    op: CollectionOp,
    receiver: TrustVcExpr,
    args: Vec<TrustVcExpr>,
    ty: TrustVcType,
) -> TrustVcExpr {
    TrustVcExpr::CollectionOp {
        op,
        receiver: Box::new(receiver),
        receiver_name: Some("s".to_string()),
        args,
        ty,
    }
}
fn index(receiver: TrustVcExpr, elem_ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Index {
        receiver: Box::new(receiver),
        index: Box::new(lit(0, U64)),
        receiver_name: Some("s".to_string()),
        elem_ty,
    }
}
fn check(expr: &TrustVcExpr, variables: &[(&str, TrustVcType)]) -> Result<(), String> {
    let variables: HashMap<String, TrustVcType> = variables
        .iter()
        .map(|(name, ty)| ((*name).to_string(), ty.clone()))
        .collect();
    validate_ir_typing(
        expr,
        &TypingScope {
            variables: Some(&variables),
            locals: None,
            functions: None,
            parameters: None,
        },
    )
}

/// §5b rules 2/6: a literal is a value of its declared type; the
/// placeholder holds any value, and a signed magnitude under `-` is the
/// negated literal (`-128i8`).
#[test]
fn a_literal_is_a_value_of_its_declared_type() {
    for (value, ty) in [
        (-1, TrustVcType::Nat),
        (-1, U8),
        (256, U8),
        (200, I8),
        (-129, I8),
        (0x11_0000, TrustVcType::Char),
    ] {
        assert!(
            check(&lit(value, ty.clone()), &[]).is_err(),
            "{value} at {ty:?}"
        );
    }
    for (value, ty) in [
        (0, TrustVcType::Nat),
        (255, U8),
        (-128, I8),
        (i128::from(u32::MAX), TrustVcType::Int { width: 32 }),
        (-1, TrustVcType::MathInt),
    ] {
        assert!(
            check(&lit(value, ty.clone()), &[]).is_ok(),
            "{value} at {ty:?}"
        );
    }
    let neg = |value, ty| TrustVcExpr::Neg(Box::new(lit(value, ty)));
    assert!(check(&neg(128, I8), &[]).is_ok());
    assert!(check(&neg(129, I8), &[]).is_err());
}

/// A lie ONE LEVEL UP — the receiver of the element read — is refused
/// where it is made, at every depth (r9: `s.take(1)` of a `Seq<u8>`
/// declared `Seq<i8>` and read at `i8` gave -56 for 200).
#[test]
fn a_receiver_claim_is_derived_at_every_depth() {
    let s = || var("s", seq(U8));
    let vars = [("s", seq(U8))];
    let take = |ty| {
        cop(
            CollectionOp::Take,
            s(),
            vec![lit(1, TrustVcType::MathInt)],
            ty,
        )
    };
    assert!(check(&index(take(seq(U8)), U8), &vars).is_ok());
    assert!(check(&index(take(seq(I8)), I8), &vars).is_err());
    // Two levels: a consistent `take` under a lying `reverse`.
    let reversed = cop(CollectionOp::Reverse, take(seq(U8)), vec![], seq(I8));
    assert!(check(&index(reversed, I8), &vars).is_err());
    // A `let`, a conditional and a `match` binder carrying the lie.
    let let_lie = TrustVcExpr::Let {
        name: "v".to_string(),
        ty: seq(I8),
        value: Box::new(s()),
        body: Box::new(index(var("v", seq(I8)), I8)),
    };
    assert!(check(&let_lie, &vars).is_err());
    let ite_lie = TrustVcExpr::Ite {
        cond: Box::new(TrustVcExpr::BoolLit(true)),
        then_branch: Box::new(s()),
        else_branch: Box::new(s()),
        ty: seq(I8),
    };
    assert!(check(&index(ite_lie, I8), &vars).is_err());
    let match_lie = TrustVcExpr::Match {
        scrutinee: Box::new(s()),
        arms: vec![MatchArm::new(
            MatchPattern::Ident("g".to_string()),
            var("g", seq(I8)),
        )],
        ty: seq(I8),
    };
    assert!(check(&match_lie, &vars).is_err());
    // A map `insert` declaring another value type.
    let map_u = TrustVcType::Map(Box::new(U8), Box::new(U8));
    let map_i = TrustVcType::Map(Box::new(U8), Box::new(I8));
    let insert = TrustVcExpr::CollectionOp {
        op: CollectionOp::Insert,
        receiver: Box::new(var("m", map_u.clone())),
        receiver_name: Some("m".to_string()),
        args: vec![lit(0, U8), lit(200, U8)],
        ty: map_i,
    };
    assert!(check(&insert, &[("m", map_u)]).is_err());
    // The nested sequence read at a lying inner type.
    let ss = var("ss", seq(seq(U8)));
    assert!(check(&index(ss, seq(I8)), &[("ss", seq(seq(U8)))]).is_err());
}

/// Rule 1: an integer node's declared type is the type its operands
/// derive; the untyped placeholder over literals is typed later.
#[test]
fn an_integer_node_declares_its_derived_type() {
    let x = || var("x", U8);
    let add = |r: TrustVcExpr, ty| TrustVcExpr::Arith {
        op: ArithOp::Add,
        left: Box::new(x()),
        right: Box::new(r),
        ty,
    };
    let vars = [("x", U8)];
    assert!(check(&add(lit(1, U8), U8), &vars).is_ok());
    assert!(check(&add(lit(1, U8), I8), &vars).is_err());
    assert!(check(&add(lit(1, U8), TrustVcType::MathInt), &vars).is_ok());
    let n = || var("n", TrustVcType::Nat);
    let nat_sub = TrustVcExpr::Arith {
        op: ArithOp::Sub,
        left: Box::new(n()),
        right: Box::new(n()),
        ty: TrustVcType::Nat,
    };
    assert!(check(&nat_sub, &[("n", TrustVcType::Nat)]).is_err());
    let placeholder = TrustVcType::Int { width: 32 };
    let untyped = TrustVcExpr::Arith {
        op: ArithOp::Add,
        left: Box::new(lit(3_000_000_000, placeholder.clone())),
        right: Box::new(lit(1, placeholder.clone())),
        ty: placeholder,
    };
    assert!(check(&untyped, &[]).is_ok());
}

/// A variable, a cast operand, a call result and a compared composite are
/// read at the type their binder/operand/declaration gives them.
#[test]
fn binders_casts_calls_and_compares_agree() {
    let quantified = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("i".to_string(), U8)],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Ge,
            left: Box::new(var("i", I8)),
            right: Box::new(lit(0, I8)),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };
    assert!(check(&quantified, &[]).is_err());
    assert!(check(&var("x", I8), &[("x", U8)]).is_err());
    let cast = TrustVcExpr::Cast {
        expr: Box::new(var("x", U8)),
        from_ty: I8,
        to_ty: TrustVcType::MathInt,
    };
    assert!(check(&cast, &[("x", U8)]).is_err());
    let compare = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(var("a", seq(U8))),
        right: Box::new(var("b", seq(I8))),
    };
    assert!(check(&compare, &[("a", seq(U8)), ("b", seq(I8))]).is_err());
    let functions: HashMap<String, TrustVcType> = [("f".to_string(), seq(U8))].into();
    let call = |ty| TrustVcExpr::FnCall {
        name: "f".to_string(),
        args: vec![],
        return_ty: ty,
    };
    let scope = TypingScope {
        variables: None,
        locals: None,
        functions: Some(&functions),
        parameters: None,
    };
    assert!(validate_ir_typing(&call(seq(U8)), &scope).is_ok());
    assert!(validate_ir_typing(&call(seq(I8)), &scope).is_err());
}

/// A collection operation's result is the type its receiver and arguments
/// derive (`infer_collection_op_type`), not only for element reads and
/// receiver-typed operations (r10: `to_set` declared `Set<i8>` over a
/// `Seq<u8>` held -56); a length is an `Int` term read at its own value.
#[test]
fn a_collection_result_is_derived() {
    let s = || var("s", seq(U8));
    let vars = [("s", seq(U8))];
    let set = |ty| TrustVcType::Set(Box::new(ty));
    assert!(check(&cop(CollectionOp::ToSet, s(), vec![], set(U8)), &vars).is_ok());
    assert!(check(&cop(CollectionOp::ToSet, s(), vec![], set(I8)), &vars).is_err());
    assert!(check(&cop(CollectionOp::View, s(), vec![], seq(I8)), &vars).is_err());
    for ok in [U64, TrustVcType::Nat, TrustVcType::MathInt, I8] {
        assert!(check(&cop(CollectionOp::Len, s(), vec![], ok), &vars).is_ok());
    }
    assert!(check(&cop(CollectionOp::Len, s(), vec![], seq(U8)), &vars).is_err());
    // A closure whose declared return is not its body's type.
    let closure = |ret: TrustVcType| TrustVcExpr::SpecClosure {
        params: vec![("x".to_string(), U8)],
        body: Box::new(var("x", U8)),
        ty: TrustVcType::SpecFn(vec![U8], Box::new(ret)),
    };
    assert!(check(&closure(U8), &[]).is_ok());
    assert!(check(&closure(I8), &[]).is_err());
    let mapped = |ret, ty| cop(CollectionOp::SeqMapValues, s(), vec![closure(ret)], ty);
    assert!(check(&mapped(U8, seq(U8)), &vars).is_ok());
    assert!(check(&mapped(U8, seq(I8)), &vars).is_err());
}

/// A join declared at a type that holds no integer FORGETS its operands'
/// element types; an element read of a receiver with no element type, and a
/// map key of another integer type, are refused.
#[test]
fn a_join_does_not_forget_and_a_read_has_an_element_type() {
    let s = || var("s", seq(U8));
    let vars = [("s", seq(U8))];
    let erased = TrustVcType::TypeParam("T".to_string());
    let ite = TrustVcExpr::Ite {
        cond: Box::new(TrustVcExpr::BoolLit(true)),
        then_branch: Box::new(s()),
        else_branch: Box::new(s()),
        ty: erased.clone(),
    };
    assert!(check(&ite, &vars).is_err());
    let forget = TrustVcExpr::Let {
        name: "v".to_string(),
        ty: erased.clone(),
        value: Box::new(s()),
        body: Box::new(TrustVcExpr::BoolLit(true)),
    };
    assert!(check(&forget, &vars).is_err());
    assert!(check(
        &index(var("t", erased.clone()), I8),
        &[("t", erased.clone())]
    )
    .is_err());
    assert!(check(
        &index(var("t", erased.clone()), erased.clone()),
        &[("t", erased)]
    )
    .is_ok());
    let map_u = TrustVcType::Map(Box::new(U8), Box::new(U8));
    let read = |key| TrustVcExpr::Index {
        receiver: Box::new(var("m", map_u.clone())),
        index: Box::new(key),
        receiver_name: Some("m".to_string()),
        elem_ty: U8,
    };
    assert!(check(&read(lit(200, U8)), &[("m", map_u.clone())]).is_ok());
    assert!(check(&read(lit(-56, I8)), &[("m", map_u.clone())]).is_err());
}
