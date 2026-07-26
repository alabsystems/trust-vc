//! Round-trip and type-propagation tests for ir_lowering module.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::ir::TrustVcType;
use crate::ir_expr::*;

use super::tests_support::env_with;

fn assert_lowers(expr_src: &str, vars: &[(&str, &str)]) {
    let expr: syn::Expr =
        syn::parse_str(expr_src).unwrap_or_else(|e| panic!("failed to parse '{expr_src}': {e}"));
    let env = env_with(vars);
    if let Err(err) = lower_syn_expr(&expr, &env) {
        panic!("failed to lower '{expr_src}': {err}");
    }
}

// === Round-trip coverage for existing condition-string patterns ===

#[test]
fn round_trip_existing_condition_patterns() {
    let cases: Vec<(&str, Vec<(&str, &str)>)> = vec![
        ("x > 0", vec![("x", "i32")]),
        ("y < 10", vec![("y", "i32")]),
        ("x > 0 && y", vec![("x", "i32"), ("y", "bool")]),
        ("n - 1 < n", vec![("n", "i32")]),
        ("s.len() >= 0", vec![("s", "Seq<i32>")]),
        ("x.wrapping_add(1) < y", vec![("x", "u8"), ("y", "u32")]),
        ("m.get(5) == x", vec![("m", "Map<i32, i64>"), ("x", "i64")]),
        (
            "forall(|i: u64| !(i < 3) || s.index(i) >= 0)",
            vec![("s", "Seq<i32>")],
        ),
        (
            "(if cond { x } else { y }) > 0",
            vec![("cond", "bool"), ("x", "i32"), ("y", "i32")],
        ),
        ("u32::MAX > one", vec![("one", "u32")]),
    ];

    for (expr_src, vars) in cases {
        assert_lowers(expr_src, &vars);
    }
}

#[test]
fn round_trip_arithmetic_patterns() {
    let cases: Vec<(&str, Vec<(&str, &str)>)> = vec![
        ("x + 0 == x", vec![("x", "i32")]),
        ("x * 1 == x", vec![("x", "i32")]),
        ("x - x == 0", vec![("x", "i32")]),
        ("x + y == y + x", vec![("x", "i32"), ("y", "i32")]),
        (
            "(x + y) + z == x + (y + z)",
            vec![("x", "i32"), ("y", "i32"), ("z", "i32")],
        ),
        ("10 / 3 == 3", vec![]),
        ("7 % 2 == 1", vec![]),
        ("x / 1 == x", vec![("x", "i32")]),
        ("x % 1 == 0", vec![("x", "i32")]),
        ("(-7) / 2 == (-3)", vec![]),
        ("(-7) % 2 == (-1)", vec![]),
    ];
    for (expr_src, vars) in cases {
        assert_lowers(expr_src, &vars);
    }
}

#[test]
fn round_trip_bitwise_and_shift_patterns() {
    let cases: Vec<(&str, Vec<(&str, &str)>)> = vec![
        ("x & 0 == 0", vec![("x", "u32")]),
        ("x | 0 == x", vec![("x", "u32")]),
        ("x ^ x == 0", vec![("x", "u32")]),
        ("x << 2", vec![("x", "u32")]),
        ("x >> 1 == 1073741824", vec![("x", "u32")]),
    ];
    for (expr_src, vars) in cases {
        assert_lowers(expr_src, &vars);
    }
}

#[test]
fn round_trip_negation_and_not_patterns() {
    let cases: Vec<(&str, Vec<(&str, &str)>)> = vec![
        ("!(x > 0)", vec![("x", "i32")]),
        ("!(x < x)", vec![("x", "i32")]),
        ("-(-x) == x", vec![("x", "i32")]),
        ("!!b == b", vec![("b", "bool")]),
        ("!(p && !p)", vec![("p", "bool")]),
    ];
    for (expr_src, vars) in cases {
        assert_lowers(expr_src, &vars);
    }
}

#[test]
fn round_trip_conditional_patterns() {
    let cases: Vec<(&str, Vec<(&str, &str)>)> = vec![
        ("if x > 0 { 1 } else { 0 } == 1", vec![("x", "i32")]),
        (
            "if x > 0 { if x > 10 { 2 } else { 1 } } else { 0 } == 1",
            vec![("x", "i32")],
        ),
        (
            "match x { 1 => 10, 2 => 20, _ => 0 } == 10",
            vec![("x", "i32")],
        ),
        ("match x { y => y + 1 } == 6", vec![("x", "i32")]),
    ];
    for (expr_src, vars) in cases {
        assert_lowers(expr_src, &vars);
    }
}

#[test]
fn round_trip_block_and_let_patterns() {
    let cases: Vec<(&str, Vec<(&str, &str)>)> = vec![
        ("{ x } == 42", vec![("x", "i32")]),
        ("{ let y = x + 1; y } == 11", vec![("x", "i32")]),
        ("{ let x = 10; x } == 10", vec![]),
    ];
    for (expr_src, vars) in cases {
        assert_lowers(expr_src, &vars);
    }
}

#[test]
fn round_trip_cast_patterns() {
    let cases: Vec<(&str, Vec<(&str, &str)>)> = vec![
        ("(x as i64) == y", vec![("x", "i32"), ("y", "i64")]),
        ("(x as i32) == y", vec![("x", "u32"), ("y", "i32")]),
        ("(x as u32) == y", vec![("x", "i32"), ("y", "u32")]),
    ];
    for (expr_src, vars) in cases {
        assert_lowers(expr_src, &vars);
    }
}

#[test]
fn round_trip_collection_patterns() {
    let cases: Vec<(&str, Vec<(&str, &str)>)> = vec![
        ("s.len() == 3", vec![("s", "Seq<i32>")]),
        ("s.push(42).len() == 3", vec![("s", "Seq<i32>")]),
        ("s.first() == s.first()", vec![("s", "Seq<i32>")]),
        ("s.last() == s.last()", vec![("s", "Seq<i32>")]),
        ("s.is_empty()", vec![("s", "Seq<i32>")]),
        ("s.update(0, 99).index(0) == 99", vec![("s", "Seq<i32>")]),
        (
            "s.drop_last().len() == s.drop_last().len()",
            vec![("s", "Seq<i32>")],
        ),
        ("s.take(3).len() == 3", vec![("s", "Seq<i32>")]),
        ("s.skip(1).index(0) == 42", vec![("s", "Seq<i32>")]),
        ("s.subrange(1, 3).index(0) == 42", vec![("s", "Seq<i32>")]),
        (
            "s1.concat(s2).len() == 5",
            vec![("s1", "Seq<i32>"), ("s2", "Seq<i32>")],
        ),
    ];
    for (expr_src, vars) in cases {
        assert_lowers(expr_src, &vars);
    }
}

#[test]
fn round_trip_set_patterns() {
    let cases: Vec<(&str, Vec<(&str, &str)>)> = vec![
        ("s.contains(5)", vec![("s", "Set<i32>")]),
        ("s.insert(5).contains(5)", vec![("s", "Set<i32>")]),
        ("!s.remove(5).contains(5)", vec![("s", "Set<i32>")]),
        (
            "s1.union(s2).contains(3)",
            vec![("s1", "Set<i32>"), ("s2", "Set<i32>")],
        ),
        (
            "s1.intersect(s2).contains(3)",
            vec![("s1", "Set<i32>"), ("s2", "Set<i32>")],
        ),
        (
            "s1.difference(s2).contains(3)",
            vec![("s1", "Set<i32>"), ("s2", "Set<i32>")],
        ),
    ];
    for (expr_src, vars) in cases {
        assert_lowers(expr_src, &vars);
    }
}

#[test]
fn round_trip_map_patterns() {
    let cases: Vec<(&str, Vec<(&str, &str)>)> = vec![
        ("m.get(5) == 10", vec![("m", "Map<i32, i32>")]),
        (
            "m.insert(5, true).get(5) == true",
            vec![("m", "Map<i32, bool>")],
        ),
        ("m.len() >= 0", vec![("m", "Map<i32, i32>")]),
    ];
    for (expr_src, vars) in cases {
        assert_lowers(expr_src, &vars);
    }
}

#[test]
fn round_trip_quantifier_patterns() {
    let cases: Vec<(&str, Vec<(&str, &str)>)> = vec![
        ("forall(|x: i32| x == x)", vec![]),
        ("exists(|x: i32| x == 0)", vec![]),
        ("forall(|x: i32, y: i32| x + y == y + x)", vec![]),
        ("forall(|x: i32| !(x > 5) || x > 0)", vec![]),
        ("forall(|x: u32| x >= 0)", vec![]),
        ("forall(|x: u8| x + 1 > 0)", vec![]),
        (
            "forall(|i: u64| !(i < 2) || s.index(i) >= 0)",
            vec![("s", "Seq<i32>")],
        ),
    ];
    for (expr_src, vars) in cases {
        assert_lowers(expr_src, &vars);
    }
}

#[test]
fn untyped_closure_param_rejected() {
    // forall(|x| ...) without type annotation must produce an error.
    // Previously this silently defaulted to Int{32}, causing wrong range
    // guards and wrapping semantics (#2078).
    let expr: syn::Expr = syn::parse_str("forall(|x| x > 0)").unwrap();
    let env = TypeEnv::new();
    let err = lower_syn_expr(&expr, &env).expect_err("untyped param must be rejected");
    let msg = err.to_string();
    assert!(
        msg.contains("requires an explicit type annotation"),
        "error should mention type annotation requirement, got: {msg}",
    );
    assert!(
        msg.contains("'x'"),
        "error should name the parameter, got: {msg}",
    );
}

#[test]
fn round_trip_complex_nested_patterns() {
    let cases: Vec<(&str, Vec<(&str, &str)>)> = vec![
        ("x > 0 && x < 100 && x != 50", vec![("x", "i32")]),
        ("(x < 0 || x > 3) && x < 10", vec![("x", "i32")]),
        ("x != 0 && 10 / x > 0", vec![("x", "i32")]),
        ("p || !p", vec![("p", "bool")]),
        (
            "if x > 0 { match x { 1 => 10, _ => 20 } } else { 0 } == 10",
            vec![("x", "i32")],
        ),
        ("forall(|x: i32| !(x == 0) || ((-7) / 2 == (-3)))", vec![]),
    ];
    for (expr_src, vars) in cases {
        assert_lowers(expr_src, &vars);
    }
}

// === Type propagation tests ===

#[test]
fn arith_propagates_operand_type() {
    let expr: syn::Expr = syn::parse_str("x + y").unwrap();
    let env = env_with(&[("x", "u64"), ("y", "u64")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::Arith { ty, .. } => {
            assert_eq!(
                ty,
                TrustVcType::Uint { width: 64 },
                "arith should propagate u64 from operands"
            );
        }
        other => panic!("expected Arith, got {:?}", other),
    }
}

#[test]
fn shift_propagates_operand_type() {
    let expr: syn::Expr = syn::parse_str("x << 2").unwrap();
    let env = env_with(&[("x", "u64")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::SpecialArith { ty, .. } => {
            assert_eq!(
                ty,
                TrustVcType::Uint { width: 64 },
                "shift should propagate u64 from lhs"
            );
        }
        other => panic!("expected SpecialArith, got {:?}", other),
    }
}

#[test]
fn ite_propagates_then_branch_type() {
    let expr: syn::Expr = syn::parse_str("if cond { x } else { y }").unwrap();
    let env = env_with(&[("cond", "bool"), ("x", "u64"), ("y", "u64")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::Ite { ty, .. } => {
            assert_eq!(
                ty,
                TrustVcType::Uint { width: 64 },
                "ite should propagate u64 from then branch"
            );
        }
        other => panic!("expected Ite, got {:?}", other),
    }
}

#[test]
fn wrapping_arith_propagates_receiver_type() {
    let expr: syn::Expr = syn::parse_str("x.wrapping_add(y)").unwrap();
    let env = env_with(&[("x", "u64"), ("y", "u64")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::WrappingArith { ty, .. } => {
            assert_eq!(
                ty,
                TrustVcType::Uint { width: 64 },
                "wrapping arith should propagate u64"
            );
        }
        other => panic!("expected WrappingArith, got {:?}", other),
    }
}

#[test]
fn collection_len_returns_uint_pointer_width() {
    let expr: syn::Expr = syn::parse_str("s.len()").unwrap();
    let env = env_with(&[("s", "Seq<u64>")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::CollectionOp { ty, .. } => {
            assert_eq!(
                ty,
                TrustVcType::Uint {
                    width: crate::ir::pointer_width()
                },
                "len() should return unsigned pointer_width (#1745)"
            );
        }
        other => panic!("expected CollectionOp, got {:?}", other),
    }
}

#[test]
fn index_propagates_element_type() {
    let expr: syn::Expr = syn::parse_str("arr[0]").unwrap();
    let env = env_with(&[("arr", "Seq<u64>")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::Index { elem_ty, .. } => {
            assert_eq!(
                elem_ty,
                TrustVcType::Uint { width: 64 },
                "index should propagate element type"
            );
        }
        other => panic!("expected Index, got {:?}", other),
    }
}
