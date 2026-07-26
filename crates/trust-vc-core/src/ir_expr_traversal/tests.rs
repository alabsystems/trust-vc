// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ir::{CompareOp, LogicOp, QuantifierKind, TrustVcType};
use crate::ir_expr::{MatchArm, MatchPattern, TrustVcExpr};
use crate::ir_place::TrustVcPlace;
use std::collections::{BTreeSet, HashSet};

fn i32_ty() -> TrustVcType {
    TrustVcType::Int { width: 32 }
}

fn bool_var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: TrustVcType::Bool,
    }
}

fn int_var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: i32_ty(),
    }
}

#[test]
fn test_walk_expr_visits_pattern_literals_and_place_indices() {
    struct Vars {
        names: BTreeSet<String>,
    }

    impl TrustVcExprVisitor for Vars {
        fn visit_expr(&mut self, expr: &TrustVcExpr) {
            if let TrustVcExpr::Var { name, .. } = expr {
                self.names.insert(name.clone());
            }
            walk_expr(self, expr);
        }
    }

    let expr = TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(TrustVcExpr::ReadPlace {
            place: TrustVcPlace::root("seq", TrustVcType::Seq(Box::new(i32_ty())))
                .index(int_var("idx"), i32_ty()),
            ty: i32_ty(),
        }),
        right: Box::new(TrustVcExpr::Match {
            scrutinee: Box::new(int_var("scrutinee")),
            arms: vec![MatchArm::new(
                MatchPattern::Lit(int_var("pattern_lit")),
                bool_var("body_var"),
            )],
            ty: TrustVcType::Bool,
        }),
    };

    let mut visitor = Vars {
        names: BTreeSet::new(),
    };
    visitor.visit_expr(&expr);

    assert_eq!(
        visitor.names,
        BTreeSet::from([
            "body_var".to_string(),
            "idx".to_string(),
            "pattern_lit".to_string(),
            "scrutinee".to_string(),
        ])
    );
}

#[test]
fn test_expr_references_any_name_respects_shadowing() {
    let expr = TrustVcExpr::Let {
        name: "x".to_string(),
        ty: i32_ty(),
        value: Box::new(int_var("free_input")),
        body: Box::new(TrustVcExpr::Quantifier {
            kind: QuantifierKind::Forall,
            bound_vars: vec![("y".to_string(), i32_ty())],
            body: Box::new(TrustVcExpr::Compare {
                op: CompareOp::Eq,
                left: Box::new(int_var("x")),
                right: Box::new(int_var("y")),
            }),
            triggers: Some(vec![vec![int_var("x"), int_var("y")]]),
            trigger_inference_mode: None,
        }),
    };

    let shadowed = HashSet::from(["x", "y"]);
    assert!(
        !expr_references_any_name(&expr, &shadowed),
        "let/quantifier-bound names must not be reported as free references"
    );

    let free_name = HashSet::from(["free_input"]);
    assert!(
        expr_references_any_name(&expr, &free_name),
        "free variable in let value should still be reported"
    );
}

#[test]
fn test_walk_expr_scoped_tracks_match_bindings() {
    struct MatchBindingSeen {
        saw_bound_match_name: bool,
    }

    impl ScopeAwareTrustVcExprVisitor for MatchBindingSeen {
        fn visit_expr_scoped(&mut self, expr: &TrustVcExpr, bound: &HashSet<&str>) -> bool {
            if let TrustVcExpr::Var { name, .. } = expr {
                if name == "matched" && bound.contains("matched") {
                    self.saw_bound_match_name = true;
                }
            }
            true
        }
    }

    let expr = TrustVcExpr::Match {
        scrutinee: Box::new(int_var("scrutinee")),
        arms: vec![MatchArm::new(
            MatchPattern::Ident("matched".to_string()),
            int_var("matched"),
        )],
        ty: i32_ty(),
    };

    let mut visitor = MatchBindingSeen {
        saw_bound_match_name: false,
    };
    walk_expr_scoped(&mut visitor, &expr, &HashSet::new());
    assert!(visitor.saw_bound_match_name);
}

#[test]
fn test_free_root_names_respects_shadowing_and_place_indices() {
    let expr = TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(TrustVcExpr::ReadPlace {
            place: TrustVcPlace::root("seq", TrustVcType::Seq(Box::new(i32_ty())))
                .index(int_var("idx"), i32_ty()),
            ty: i32_ty(),
        }),
        right: Box::new(TrustVcExpr::Let {
            name: "idx".to_string(),
            ty: i32_ty(),
            value: Box::new(int_var("outer_idx")),
            body: Box::new(TrustVcExpr::PlaceDisjoint {
                left: TrustVcPlace::root("left", i32_ty()),
                right: TrustVcPlace::root("right", i32_ty()).index(int_var("idx"), i32_ty()),
            }),
        }),
    };

    let roots = free_root_names(&expr);
    assert_eq!(
        roots,
        HashSet::from([
            "seq".to_string(),
            "idx".to_string(),
            "outer_idx".to_string(),
            "left".to_string(),
            "right".to_string(),
        ]),
    );
}

#[test]
fn test_fold_expr_scoped_children_renames_only_free_vars() {
    struct RenameFreeX;

    impl ScopeAwareTrustVcExprFolder for RenameFreeX {
        fn fold_expr_scoped(&mut self, expr: TrustVcExpr, bound: &HashSet<&str>) -> TrustVcExpr {
            match expr {
                TrustVcExpr::Var { name, ty } if name == "x" && !bound.contains("x") => {
                    TrustVcExpr::Var {
                        name: "renamed_x".to_string(),
                        ty,
                    }
                }
                other => fold_expr_scoped_children(self, other, bound),
            }
        }
    }

    let expr = TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(int_var("x")),
        right: Box::new(TrustVcExpr::Let {
            name: "x".to_string(),
            ty: i32_ty(),
            value: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: i32_ty(),
            }),
            body: Box::new(int_var("x")),
        }),
    };

    let folded = RenameFreeX.fold_expr_scoped(expr, &HashSet::new());
    let expected = TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(int_var("renamed_x")),
        right: Box::new(TrustVcExpr::Let {
            name: "x".to_string(),
            ty: i32_ty(),
            value: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: i32_ty(),
            }),
            body: Box::new(int_var("x")),
        }),
    };

    assert_eq!(folded, expected);
}
