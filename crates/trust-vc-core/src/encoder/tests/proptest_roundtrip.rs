//! Property-based roundtrip tests for TrustVcExpr encoding.
//!
//! These tests verify that the TrustVcExpr -> ay Term encoding path:
//! 1. Never panics for well-formed expressions
//! 2. Is deterministic (same input -> same output)
//! 3. Preserves symmetry of commutative operations
//! 4. Preserves logical equivalences
//! 5. Handles nested expressions without crashing
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::error::TrustVcResult;
use crate::ir::TrustVcType;
use crate::ir_expr::{ArithOp, CompareOp, LogicOp, TrustVcExpr};
use proptest::prelude::*;

const MAX_EXPR_DEPTH: u32 = 3;

fn encode_expr(expr: &TrustVcExpr) -> TrustVcResult<Term> {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::bitvec(32));
    let y = solver.declare_const("y", Sort::bitvec(32));
    let b = solver.declare_const("b", Sort::Bool);

    let mut variables = std::collections::HashMap::new();
    variables.insert("x".to_string(), x);
    variables.insert("y".to_string(), y);
    variables.insert("b".to_string(), b);

    let mut var_types = std::collections::HashMap::new();
    var_types.insert("x".to_string(), TrustVcType::Int { width: 32 });
    var_types.insert("y".to_string(), TrustVcType::Int { width: 32 });
    var_types.insert("b".to_string(), TrustVcType::Bool);

    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    parser.term_widths.insert(x, (32, true));
    parser.term_widths.insert(y, (32, true));

    parser.encode_trust_vc_expr(expr)
}

fn arith_op_strategy() -> impl Strategy<Value = ArithOp> {
    proptest::prop_oneof![
        Just(ArithOp::Add),
        Just(ArithOp::Sub),
        Just(ArithOp::Mul),
        Just(ArithOp::Div),
        Just(ArithOp::Rem),
    ]
}

fn compare_op_strategy() -> impl Strategy<Value = CompareOp> {
    proptest::prop_oneof![
        Just(CompareOp::Eq),
        Just(CompareOp::Ne),
        Just(CompareOp::Lt),
        Just(CompareOp::Le),
        Just(CompareOp::Gt),
        Just(CompareOp::Ge),
    ]
}

fn logic_op_strategy() -> impl Strategy<Value = LogicOp> {
    proptest::prop_oneof![Just(LogicOp::And), Just(LogicOp::Or)]
}

fn i32_lit_expr(value: i32) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value: i128::from(value),
        ty: TrustVcType::Int { width: 32 },
    }
}

fn i32_expr_string(value: i32) -> String {
    if value < 0 {
        format!("0 - {}", -i64::from(value))
    } else {
        value.to_string()
    }
}

fn i32_lit_strategy() -> impl Strategy<Value = TrustVcExpr> {
    any::<i32>().prop_map(i32_lit_expr)
}

fn int_leaf_strategy() -> proptest::strategy::BoxedStrategy<TrustVcExpr> {
    proptest::prop_oneof![
        i32_lit_strategy(),
        prop::strategy::LazyJust::new(|| TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Int { width: 32 },
        }),
    ]
    .boxed()
}

fn bool_leaf_strategy() -> proptest::strategy::BoxedStrategy<TrustVcExpr> {
    proptest::prop_oneof![
        prop::strategy::LazyJust::new(|| TrustVcExpr::BoolLit(true)),
        prop::strategy::LazyJust::new(|| TrustVcExpr::BoolLit(false)),
        (
            compare_op_strategy(),
            int_leaf_strategy(),
            int_leaf_strategy()
        )
            .prop_map(|(op, left, right)| TrustVcExpr::Compare {
                op,
                left: Box::new(left),
                right: Box::new(right),
            },),
    ]
    .boxed()
}

fn bool_expr_strategy(depth: u32) -> proptest::strategy::BoxedStrategy<TrustVcExpr> {
    if depth == 0 {
        return bool_leaf_strategy();
    }

    proptest::prop_oneof![
        3 => bool_leaf_strategy(),
        3 => (compare_op_strategy(), int_expr_strategy(depth - 1), int_expr_strategy(depth - 1))
            .prop_map(|(op, left, right)| TrustVcExpr::Compare {
                op,
                left: Box::new(left),
                right: Box::new(right),
            }),
        2 => (logic_op_strategy(), bool_expr_strategy(depth - 1), bool_expr_strategy(depth - 1))
            .prop_map(|(op, left, right)| TrustVcExpr::Logic {
                op,
                left: Box::new(left),
                right: Box::new(right),
            }),
        1 => bool_expr_strategy(depth - 1).prop_map(|expr| TrustVcExpr::Not(Box::new(expr))),
        1 => (bool_expr_strategy(depth - 1), bool_expr_strategy(depth - 1)).prop_map(
            |(premise, conclusion)| TrustVcExpr::Implies {
                premise: Box::new(premise),
                conclusion: Box::new(conclusion),
            },
        ),
    ]
    .boxed()
}

fn int_expr_strategy(depth: u32) -> proptest::strategy::BoxedStrategy<TrustVcExpr> {
    if depth == 0 {
        return int_leaf_strategy();
    }

    proptest::prop_oneof![
        3 => int_leaf_strategy(),
        3 => (arith_op_strategy(), int_expr_strategy(depth - 1), int_expr_strategy(depth - 1))
            .prop_map(|(op, left, right)| TrustVcExpr::Arith {
                op,
                left: Box::new(left),
                right: Box::new(right),
                ty: TrustVcType::Int { width: 32 },
            }),
        2 => int_expr_strategy(depth - 1).prop_map(|expr| TrustVcExpr::Neg(Box::new(expr))),
        2 => (
            bool_expr_strategy(depth - 1),
            int_expr_strategy(depth - 1),
            int_expr_strategy(depth - 1),
        )
            .prop_map(|(cond, then_branch, else_branch)| TrustVcExpr::Ite {
                cond: Box::new(cond),
                then_branch: Box::new(then_branch),
                else_branch: Box::new(else_branch),
                ty: TrustVcType::Int { width: 32 },
            }),
        1 => (int_expr_strategy(depth - 1), int_expr_strategy(depth - 1)).prop_map(
            |(value, body)| TrustVcExpr::Let {
                name: "t".to_string(),
                ty: TrustVcType::Int { width: 32 },
                value: Box::new(value),
                body: Box::new(TrustVcExpr::Arith {
                    op: ArithOp::Add,
                    left: Box::new(TrustVcExpr::Var {
                        name: "t".to_string(),
                        ty: TrustVcType::Int { width: 32 },
                    }),
                    right: Box::new(body),
                    ty: TrustVcType::Int { width: 32 },
                }),
            },
        ),
    ]
    .boxed()
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 10_000, ..ProptestConfig::default() })]

    #[test]
    fn prop_encode_never_panics(expr in int_expr_strategy(MAX_EXPR_DEPTH)) {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| encode_expr(&expr)));
        prop_assert!(result.is_ok(), "encoding panicked for int expr: {expr:?}");
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 10_000, ..ProptestConfig::default() })]

    #[test]
    fn prop_encode_bool_never_panics(expr in bool_expr_strategy(MAX_EXPR_DEPTH)) {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| encode_expr(&expr)));
        prop_assert!(result.is_ok(), "encoding panicked for bool expr: {expr:?}");
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 10_000, ..ProptestConfig::default() })]

    #[test]
    fn prop_encoding_deterministic(expr in int_expr_strategy(MAX_EXPR_DEPTH)) {
        let first = encode_expr(&expr);
        let second = encode_expr(&expr);

        prop_assert_eq!(
            format!("{first:?}"),
            format!("{second:?}"),
            "encoding should be deterministic for {:?}",
            expr,
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 10_000, ..ProptestConfig::default() })]

    #[test]
    fn prop_add_commutative_via_solver(a in -1000i32..1000, b in -1000i32..1000) {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("a", i32_ty());
        ctx.declare_var_typed("b", i32_ty());
        ctx.push_assume("a_value", &format!("a == {}", i32_expr_string(a)));
        ctx.push_assume("b_value", &format!("b == {}", i32_expr_string(b)));
        ctx.push_obligation(ProofObligation::assert("commutative", "a + b == b + a"));

        let result = ctx.verify();

        prop_assert!(
            matches!(result, VerifyResult::Verified),
            "addition commutativity failed for a={a}, b={b}: {result:?}",
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 10_000, ..ProptestConfig::default() })]

    #[test]
    fn prop_comparison_symmetry_eq(a in -500i32..500, b in -500i32..500) {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("a", i32_ty());
        ctx.declare_var_typed("b", i32_ty());
        ctx.push_assume("a_value", &format!("a == {}", i32_expr_string(a)));
        ctx.push_assume("b_value", &format!("b == {}", i32_expr_string(b)));
        ctx.push_obligation(ProofObligation::assert("eq_symmetry", "(a == b) == (b == a)"));

        let result = ctx.verify();

        prop_assert!(
            matches!(result, VerifyResult::Verified),
            "equality symmetry failed for a={a}, b={b}: {result:?}",
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 10_000, ..ProptestConfig::default() })]

    #[test]
    fn prop_implies_contrapositive(a in any::<bool>(), b in any::<bool>()) {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("a", TrustVcType::Bool);
        ctx.declare_var_typed("b", TrustVcType::Bool);
        ctx.push_assume("a_value", &format!("a == {a}"));
        ctx.push_assume("b_value", &format!("b == {b}"));
        ctx.push_obligation(ProofObligation::assert(
            "contrapositive",
            "(!a || b) == (b || !a)",
        ));

        let result = ctx.verify();

        prop_assert!(
            matches!(result, VerifyResult::Verified),
            "implication contrapositive failed for a={a}, b={b}: {result:?}",
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 10_000, ..ProptestConfig::default() })]

    #[test]
    fn prop_let_binding_substitution(v in -1000i32..1000) {
        let mut ctx = VerificationContext::new();
        let value = i32_expr_string(v);
        ctx.push_obligation(ProofObligation::assert(
            "let_substitution",
            format!("{{ let x = {value}; x }} == {value}"),
        ));

        let result = ctx.verify();

        prop_assert!(
            matches!(result, VerifyResult::Verified),
            "let binding substitution failed for v={v}: {result:?}",
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 10_000, ..ProptestConfig::default() })]

    #[test]
    fn prop_ite_deterministic_encoding(c in any::<bool>(), t in -1000i32..1000, e in -1000i32..1000) {
        let expr = TrustVcExpr::Ite {
            cond: Box::new(TrustVcExpr::BoolLit(c)),
            then_branch: Box::new(i32_lit_expr(t)),
            else_branch: Box::new(i32_lit_expr(e)),
            ty: TrustVcType::Int { width: 32 },
        };

        let first = encode_expr(&expr);
        let second = encode_expr(&expr);

        prop_assert_eq!(
            format!("{first:?}"),
            format!("{second:?}"),
            "ITE encoding should be deterministic for {:?}",
            expr,
        );
    }
}
