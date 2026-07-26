// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for visitor-based query method migration (#2452),
//! fold_expr_children identity, and collect_conjuncts.

use super::*;

/// Quantifier whose trigger contains an overflow-prone expression (Arith)
/// but whose body does not must still return false from `may_emit_overflow_checks()`.
///
/// Pins the intentional exclusion of trigger expressions from the overflow
/// precheck. Trigger patterns are E-matching hints that don't produce
/// overflow side-channel predicates in the solver formula.
#[test]
fn test_may_emit_overflow_quantifier_trigger_with_arith_body_without() {
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".into(), i32_ty())],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(var_x()),
            right: Box::new(lit_1()),
        }),
        // Trigger contains an arithmetic expression that would emit overflow
        // checks if it were in the body, but triggers are not checked.
        triggers: Some(vec![vec![add_expr()]]),
        trigger_inference_mode: None,
    };
    assert!(
        !expr.may_emit_overflow_checks(true),
        "Quantifier with overflow-prone trigger but pure-comparison body \
         should NOT may_emit_overflow_checks — triggers are not logical content"
    );
}

/// Quantifier whose trigger contains a collection index but whose body
/// does not must still return false from `may_emit_overflow_checks()`.
#[test]
fn test_may_emit_overflow_quantifier_trigger_with_collection_body_without() {
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("i".into(), i32_ty())],
        body: Box::new(TrustVcExpr::BoolLit(true)),
        triggers: Some(vec![vec![index_expr()]]),
        trigger_inference_mode: None,
    };
    assert!(
        !expr.may_emit_overflow_checks(false),
        "Quantifier with collection trigger but leaf body should NOT \
         may_emit_overflow_checks"
    );
}

/// Verify that the generic visitor `walk_expr` visits match arm bodies
/// by using `contains_quantifier` on a match expression with a quantifier
/// nested inside an arm body.
#[test]
fn test_visitor_walks_match_arm_body() {
    let expr = TrustVcExpr::Match {
        scrutinee: Box::new(var_x()),
        arms: vec![MatchArm::new(
            MatchPattern::Wildcard,
            simple_forall_no_triggers(),
        )],
        ty: TrustVcType::Bool,
    };
    assert!(
        expr.contains_quantifier(),
        "Visitor must walk into match arm bodies to find nested quantifiers"
    );
}

/// Verify that walk_expr visits quantifier trigger expressions by using a
/// custom visitor. The default `walk_expr` visits triggers, but the query
/// methods intentionally skip them. This test exercises the infrastructure.
#[test]
fn test_walk_expr_visits_quantifier_triggers() {
    use crate::ir_expr_traversal::{walk_expr as walk, TrustVcExprVisitor};

    struct CountVisits {
        count: usize,
    }
    impl TrustVcExprVisitor for CountVisits {
        fn visit_expr(&mut self, expr: &TrustVcExpr) {
            self.count += 1;
            walk(self, expr);
        }
    }

    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".into(), i32_ty())],
        body: Box::new(TrustVcExpr::BoolLit(true)),
        triggers: Some(vec![vec![var_x(), lit_1()]]),
        trigger_inference_mode: None,
    };

    let mut v = CountVisits { count: 0 };
    v.visit_expr(&expr);
    // Expected: 1 (Quantifier) + 1 (body: BoolLit) + 2 (trigger: var_x, lit_1) = 4
    assert_eq!(
        v.count, 4,
        "walk_expr must visit the quantifier, its body, and all trigger expressions"
    );
}

/// Verify that fold_expr_children correctly rebuilds a tree by folding
/// an identity folder (no overrides) and checking equality.
#[test]
fn test_fold_identity_preserves_tree() {
    use crate::ir_expr_traversal::{fold_expr_children, TrustVcExprFolder};

    struct Identity;
    impl TrustVcExprFolder for Identity {}

    let original = TrustVcExpr::Ite {
        cond: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(var_x()),
            right: Box::new(lit_1()),
        }),
        then_branch: Box::new(add_expr()),
        else_branch: Box::new(TrustVcExpr::Neg(Box::new(var_x()))),
        ty: i32_ty(),
    };

    let folded = fold_expr_children(&mut Identity, original.clone());
    assert_eq!(
        original, folded,
        "Identity folder must preserve tree structure"
    );
}

/// Comprehensive fold_expr_children identity test covering all 21 TrustVcExpr
/// variants. The original test above covers 6/21 (Ite, Compare, Var, IntLit,
/// Arith, Neg). This test covers the remaining 15 variants to ensure the
/// identity folder preserves every variant's structure.
///
/// Part of P1-972 coverage gap finding.
#[test]
fn test_fold_identity_all_variants() {
    use crate::ir_expr_traversal::{fold_expr_children, TrustVcExprFolder};

    struct Identity;
    impl TrustVcExprFolder for Identity {}

    let ty = i32_ty();
    let seq_ty = TrustVcType::Seq(Box::new(ty.clone()));

    // Build one expression per variant not covered by the original test.
    let cases: Vec<(&str, TrustVcExpr)> = vec![
        ("BoolLit", TrustVcExpr::BoolLit(true)),
        (
            "Logic",
            TrustVcExpr::Logic {
                op: LogicOp::And,
                left: Box::new(TrustVcExpr::BoolLit(true)),
                right: Box::new(TrustVcExpr::BoolLit(false)),
            },
        ),
        (
            "Not",
            TrustVcExpr::Not(Box::new(TrustVcExpr::BoolLit(true))),
        ),
        (
            "Implies",
            TrustVcExpr::Implies {
                premise: Box::new(TrustVcExpr::BoolLit(true)),
                conclusion: Box::new(TrustVcExpr::BoolLit(false)),
            },
        ),
        (
            "Match",
            TrustVcExpr::Match {
                scrutinee: Box::new(var_x()),
                arms: vec![MatchArm {
                    pattern: MatchPattern::Lit(lit_1()),
                    body: lit_1(),
                    guard: None,
                }],
                ty: ty.clone(),
            },
        ),
        (
            "Let",
            TrustVcExpr::Let {
                name: "t".into(),
                ty: ty.clone(),
                value: Box::new(lit_1()),
                body: Box::new(var_x()),
            },
        ),
        (
            "Cast",
            TrustVcExpr::Cast {
                expr: Box::new(var_x()),
                from_ty: ty.clone(),
                to_ty: TrustVcType::Int { width: 64 },
            },
        ),
        (
            "CollectionOp",
            TrustVcExpr::CollectionOp {
                op: CollectionOp::Len,
                receiver: Box::new(TrustVcExpr::Var {
                    name: "s".into(),
                    ty: seq_ty.clone(),
                }),
                receiver_name: Some("s".into()),
                args: vec![],
                ty: TrustVcType::Uint { width: 64 },
            },
        ),
        ("Index", index_expr()),
        (
            "Quantifier",
            TrustVcExpr::Quantifier {
                kind: QuantifierKind::Forall,
                bound_vars: vec![("y".into(), ty.clone())],
                body: Box::new(TrustVcExpr::BoolLit(true)),
                triggers: Some(vec![vec![var_x()]]),
                trigger_inference_mode: None,
            },
        ),
        (
            "FnCall",
            TrustVcExpr::FnCall {
                name: "foo".into(),
                args: vec![var_x(), lit_1()],
                return_ty: ty.clone(),
            },
        ),
        (
            "IntConst",
            TrustVcExpr::IntConst {
                ty: ty.clone(),
                kind: IntConstKind::Max,
            },
        ),
        (
            "SpecialArith",
            TrustVcExpr::SpecialArith {
                op: SpecialArithOp::BitAnd,
                left: Box::new(var_x()),
                right: Box::new(lit_1()),
                ty: ty.clone(),
            },
        ),
        (
            "WrappingArith",
            TrustVcExpr::WrappingArith {
                mode: WrappingMode::Wrapping,
                op: ArithOp::Add,
                left: Box::new(var_x()),
                right: Box::new(lit_1()),
                ty: ty.clone(),
            },
        ),
        (
            "Choose",
            TrustVcExpr::Choose {
                var_name: "c".into(),
                var_ty: ty.clone(),
                condition: Box::new(TrustVcExpr::BoolLit(true)),
                key: "k".into(),
                also_assert: None,
            },
        ),
    ];

    for (label, expr) in cases {
        let folded = fold_expr_children(&mut Identity, expr.clone());
        assert_eq!(
            expr, folded,
            "Identity folder must preserve {label} variant"
        );
    }
}

// ─── collect_conjuncts tests (#2485) ────────────────────────────────

fn var_a() -> TrustVcExpr {
    TrustVcExpr::Var {
        name: "a".into(),
        ty: TrustVcType::Bool,
    }
}

fn var_b() -> TrustVcExpr {
    TrustVcExpr::Var {
        name: "b".into(),
        ty: TrustVcType::Bool,
    }
}

fn var_c() -> TrustVcExpr {
    TrustVcExpr::Var {
        name: "c".into(),
        ty: TrustVcType::Bool,
    }
}

fn var_d() -> TrustVcExpr {
    TrustVcExpr::Var {
        name: "d".into(),
        ty: TrustVcType::Bool,
    }
}

fn and(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn or(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Logic {
        op: LogicOp::Or,
        left: Box::new(left),
        right: Box::new(right),
    }
}

#[test]
fn test_collect_conjuncts_single_expr() {
    let expr = var_a();
    let conjuncts = expr.collect_conjuncts();
    assert_eq!(conjuncts.len(), 1);
    assert!(std::ptr::eq(conjuncts[0], &expr));
}

#[test]
fn test_collect_conjuncts_two_parts() {
    let expr = and(var_a(), var_b());
    let conjuncts = expr.collect_conjuncts();
    assert_eq!(conjuncts.len(), 2);
}

#[test]
fn test_collect_conjuncts_left_leaning_three() {
    // (a && b) && c — left-leaning, as produced by combine_conjuncts
    let expr = and(and(var_a(), var_b()), var_c());
    let conjuncts = expr.collect_conjuncts();
    assert_eq!(conjuncts.len(), 3);
}

#[test]
fn test_collect_conjuncts_right_leaning_three() {
    // a && (b && c) — right-leaning
    let expr = and(var_a(), and(var_b(), var_c()));
    let conjuncts = expr.collect_conjuncts();
    assert_eq!(conjuncts.len(), 3);
}

#[test]
fn test_collect_conjuncts_balanced_four() {
    // (a && b) && (c && d)
    let expr = and(and(var_a(), var_b()), and(var_c(), var_d()));
    let conjuncts = expr.collect_conjuncts();
    assert_eq!(conjuncts.len(), 4);
}

#[test]
fn test_collect_conjuncts_non_and_is_atomic() {
    // Or, Implies, Not — should NOT be split
    let or_expr = or(var_a(), var_b());
    assert_eq!(or_expr.collect_conjuncts().len(), 1);

    let implies = TrustVcExpr::Implies {
        premise: Box::new(var_a()),
        conclusion: Box::new(var_b()),
    };
    assert_eq!(implies.collect_conjuncts().len(), 1);

    let not = TrustVcExpr::Not(Box::new(var_a()));
    assert_eq!(not.collect_conjuncts().len(), 1);

    let bool_lit = TrustVcExpr::BoolLit(true);
    assert_eq!(bool_lit.collect_conjuncts().len(), 1);
}
