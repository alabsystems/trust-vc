// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_tree_branch_size_sums_children() {
    let mut encoder = AYEncoder::new();
    let (name, variants) = tree_i32_components();
    let encoding = encoder.register_datatype(&name, &variants).unwrap();
    let leaf = encoding.variant("Leaf").expect("Leaf variant");
    let branch = encoding.variant("Branch").expect("Branch variant");
    let ConstructorKind::Function(leaf_ctor) = &leaf.constructor else {
        panic!("Leaf should be a function constructor");
    };
    let ConstructorKind::Function(branch_ctor) = &branch.constructor else {
        panic!("Branch should be a function constructor");
    };

    let bv1 = encoder.solver.try_bv_const(1, 32).unwrap();
    let bv2 = encoder.solver.try_bv_const(2, 32).unwrap();
    let left = encoder.solver.try_apply(leaf_ctor, &[bv1]).unwrap();
    let right = encoder.solver.try_apply(leaf_ctor, &[bv2]).unwrap();
    let tree = encoder
        .solver
        .try_apply(branch_ctor, &[left, right])
        .unwrap();

    let size_func = encoder
        .dt_size_func("Tree_i32")
        .expect("size function registered")
        .clone();
    let size_tree = encoder.solver.try_apply(&size_func, &[tree]).unwrap();

    let expected = encoder.solver.int_const(1);
    let neq = encoder.solver.try_neq(size_tree, expected).unwrap();
    encoder.solver.try_assert_term(neq).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "size(Branch(Leaf(1), Leaf(2))) should be 1 (1 + 0 + 0), got {:?}",
        result
    );
}

#[test]
fn test_tree_nested_branch_size_is_correct() {
    let mut encoder = AYEncoder::new();
    let (name, variants) = tree_i32_components();
    let encoding = encoder.register_datatype(&name, &variants).unwrap();
    let leaf = encoding.variant("Leaf").expect("Leaf variant");
    let branch = encoding.variant("Branch").expect("Branch variant");
    let ConstructorKind::Function(leaf_ctor) = &leaf.constructor else {
        panic!("Leaf should be a function constructor");
    };
    let ConstructorKind::Function(branch_ctor) = &branch.constructor else {
        panic!("Branch should be a function constructor");
    };

    let bv1 = encoder.solver.try_bv_const(1, 32).unwrap();
    let bv2 = encoder.solver.try_bv_const(2, 32).unwrap();
    let bv3 = encoder.solver.try_bv_const(3, 32).unwrap();
    let leaf1 = encoder.solver.try_apply(leaf_ctor, &[bv1]).unwrap();
    let leaf2 = encoder.solver.try_apply(leaf_ctor, &[bv2]).unwrap();
    let leaf3 = encoder.solver.try_apply(leaf_ctor, &[bv3]).unwrap();
    let inner = encoder
        .solver
        .try_apply(branch_ctor, &[leaf1, leaf2])
        .unwrap();
    let outer = encoder
        .solver
        .try_apply(branch_ctor, &[inner, leaf3])
        .unwrap();

    let size_func = encoder
        .dt_size_func("Tree_i32")
        .expect("size function registered")
        .clone();
    let size_outer = encoder.solver.try_apply(&size_func, &[outer]).unwrap();

    let expected = encoder.solver.int_const(2);
    let neq = encoder.solver.try_neq(size_outer, expected).unwrap();
    encoder.solver.try_assert_term(neq).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "size(Branch(Branch(Leaf,Leaf), Leaf)) should be 2, got {:?}",
        result
    );
}

#[test]
fn test_dt_size_builtin_encodes_registered_recursive_datatype_var() {
    use crate::ir::{CompareOp, TrustVcExpr};
    use crate::vc::VariableDecl;

    let mut encoder = AYEncoder::new();
    let (name, variants) = list_i32_components();
    encoder.register_datatype(&name, &variants).unwrap();
    let list_ty = TrustVcType::Datatype {
        name: name.clone(),
        variants: variants.clone(),
    };
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "list".to_string(),
            ty: list_ty.clone(),
        })
        .unwrap();

    let expr = TrustVcExpr::Compare {
        op: CompareOp::Ge,
        left: Box::new(TrustVcExpr::FnCall {
            name: "__trust_vc_dt_size".to_string(),
            args: vec![TrustVcExpr::Var {
                name: "list".to_string(),
                ty: list_ty,
            }],
            return_ty: TrustVcType::MathInt,
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::Int { width: 32 },
        }),
    };

    let term = encoder
        .encode_condition_typed(&expr)
        .expect("__trust_vc_dt_size(list) >= 0 should encode");
    let negated = encoder.solver.try_not(term).unwrap();
    encoder.solver.try_assert_term(negated).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "__trust_vc_dt_size(list) >= 0 should follow from the registered non-negativity axiom, got {:?}",
        result
    );
}

#[test]
fn test_dt_size_builtin_accepts_recursive_ref_argument() {
    use crate::ir::TrustVcExpr;
    use crate::vc::VariableDecl;

    let mut encoder = AYEncoder::new();
    let (name, variants) = list_i32_components();
    encoder.register_datatype(&name, &variants).unwrap();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "tail".to_string(),
            ty: TrustVcType::RecursiveRef(name.clone()),
        })
        .unwrap();

    let expr = TrustVcExpr::FnCall {
        name: "__trust_vc_dt_size".to_string(),
        args: vec![TrustVcExpr::Var {
            name: "tail".to_string(),
            ty: TrustVcType::RecursiveRef(name),
        }],
        return_ty: TrustVcType::MathInt,
    };

    encoder
        .encode_condition_typed(&expr)
        .expect("__trust_vc_dt_size should accept RecursiveRef arguments");
}

#[test]
fn test_dt_size_builtin_rejects_non_recursive_datatype_argument() {
    use crate::ir::TrustVcExpr;
    use crate::vc::VariableDecl;

    let mut encoder = AYEncoder::new();
    let (name, variants) = option_u64_components();
    encoder.register_datatype(&name, &variants).unwrap();
    let option_ty = TrustVcType::Datatype {
        name: name.clone(),
        variants: variants.clone(),
    };
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "opt".to_string(),
            ty: option_ty.clone(),
        })
        .unwrap();

    let expr = TrustVcExpr::FnCall {
        name: "__trust_vc_dt_size".to_string(),
        args: vec![TrustVcExpr::Var {
            name: "opt".to_string(),
            ty: option_ty,
        }],
        return_ty: TrustVcType::MathInt,
    };

    let err = encoder
        .encode_condition_typed(&expr)
        .expect_err("non-recursive datatypes must fail closed for __trust_vc_dt_size");
    let message = err.to_string();
    assert!(
        message.contains("no registered size function"),
        "error should mention the missing recursive size function, got: {message}"
    );
}
