// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for contains_quantifier, has_non_skolemized_quantifier,
//! may_emit_overflow_checks, and references_collection.

use super::*;

// ============================================================
// contains_quantifier tests
// ============================================================

#[test]
fn test_contains_quantifier_leaf_nodes_false() {
    assert!(!TrustVcExpr::BoolLit(true).contains_quantifier());
    assert!(!TrustVcExpr::BoolLit(false).contains_quantifier());
    assert!(!lit_1().contains_quantifier());
    assert!(!var_x().contains_quantifier());
    assert!(!(TrustVcExpr::IntConst {
        ty: i32_ty(),
        kind: IntConstKind::Max,
    })
    .contains_quantifier());
}

#[test]
fn test_contains_quantifier_direct_quantifier() {
    assert!(simple_forall_no_triggers().contains_quantifier());
    assert!(simple_forall_with_triggers().contains_quantifier());
    assert!(simple_exists().contains_quantifier());
}

#[test]
fn test_contains_quantifier_nested_in_logic() {
    let expr = TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(TrustVcExpr::BoolLit(true)),
        right: Box::new(simple_forall_no_triggers()),
    };
    assert!(expr.contains_quantifier());
}

#[test]
fn test_contains_quantifier_nested_in_not() {
    let expr = TrustVcExpr::Not(Box::new(simple_exists()));
    assert!(expr.contains_quantifier());
}

#[test]
fn test_contains_quantifier_nested_in_implies() {
    let expr = TrustVcExpr::Implies {
        premise: Box::new(TrustVcExpr::BoolLit(true)),
        conclusion: Box::new(simple_forall_with_triggers()),
    };
    assert!(expr.contains_quantifier());
}

#[test]
fn test_contains_quantifier_nested_in_ite() {
    let expr = TrustVcExpr::Ite {
        cond: Box::new(TrustVcExpr::BoolLit(true)),
        then_branch: Box::new(simple_exists()),
        else_branch: Box::new(TrustVcExpr::BoolLit(false)),
        ty: TrustVcType::Bool,
    };
    assert!(expr.contains_quantifier());
}

#[test]
fn test_contains_quantifier_nested_in_let() {
    let expr = TrustVcExpr::Let {
        name: "y".into(),
        ty: i32_ty(),
        value: Box::new(lit_1()),
        body: Box::new(simple_forall_no_triggers()),
    };
    assert!(expr.contains_quantifier());
}

#[test]
fn test_contains_quantifier_false_for_arith() {
    assert!(!add_expr().contains_quantifier());
}

#[test]
fn test_contains_quantifier_nested_in_fn_call() {
    let expr = TrustVcExpr::FnCall {
        name: "f".into(),
        args: vec![simple_forall_no_triggers()],
        return_ty: TrustVcType::Bool,
    };
    assert!(expr.contains_quantifier());
}

#[test]
fn test_contains_quantifier_nested_in_collection_op() {
    let expr = TrustVcExpr::CollectionOp {
        op: CollectionOp::Push,
        receiver: Box::new(TrustVcExpr::Var {
            name: "s".into(),
            ty: TrustVcType::Seq(Box::new(TrustVcType::Bool)),
        }),
        receiver_name: Some("s".into()),
        args: vec![simple_exists()],
        ty: TrustVcType::Seq(Box::new(TrustVcType::Bool)),
    };
    assert!(expr.contains_quantifier());
}

// ============================================================
// has_non_skolemized_quantifier tests
// ============================================================

#[test]
fn test_non_skolemized_forall_no_triggers_is_skolemized() {
    // Trigger-less forall is Skolemized by the encoder → returns false
    assert!(!simple_forall_no_triggers().has_non_skolemized_quantifier());
}

#[test]
fn test_non_skolemized_forall_empty_triggers_is_skolemized() {
    // Forall with empty trigger list is also Skolemized
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".into(), i32_ty())],
        body: Box::new(TrustVcExpr::BoolLit(true)),
        triggers: Some(vec![]),
        trigger_inference_mode: None,
    };
    assert!(!expr.has_non_skolemized_quantifier());
}

#[test]
fn test_non_skolemized_forall_with_triggers_not_skolemized() {
    // Triggered forall goes through ay quantifiers → returns true
    assert!(simple_forall_with_triggers().has_non_skolemized_quantifier());
}

#[test]
fn test_non_skolemized_exists_always_true() {
    // Exists is never Skolemized → always returns true
    assert!(simple_exists().has_non_skolemized_quantifier());
}

#[test]
fn test_non_skolemized_exists_with_triggers() {
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Exists,
        bound_vars: vec![("x".into(), i32_ty())],
        body: Box::new(TrustVcExpr::BoolLit(true)),
        triggers: Some(vec![vec![var_x()]]),
        trigger_inference_mode: None,
    };
    assert!(expr.has_non_skolemized_quantifier());
}

// ============================================================
// may_emit_overflow_checks tests
// ============================================================

#[test]
fn test_may_emit_overflow_checks_false_for_pure_comparison() {
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(var_x()),
        right: Box::new(var_x()),
    };

    assert!(
        !expr.may_emit_overflow_checks(true),
        "pure comparisons should not trigger auxiliary overflow prechecks"
    );
}

#[test]
fn test_may_emit_overflow_checks_for_arith_respects_flag() {
    assert!(
        add_expr().may_emit_overflow_checks(true),
        "checked arithmetic should require an auxiliary overflow precheck"
    );
    assert!(
        !add_expr().may_emit_overflow_checks(false),
        "plain arithmetic without overflow checking should not require the auxiliary pass"
    );
}

#[test]
fn test_may_emit_overflow_checks_false_for_quantified_arith_body() {
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".into(), i32_ty())],
        body: Box::new(add_expr()),
        triggers: None,
        trigger_inference_mode: None,
    };

    assert!(
        !expr.may_emit_overflow_checks(true),
        "arithmetic inside quantifier bodies is modeled in the main formula, not through outer overflow side-channel checks"
    );
}

#[test]
fn test_may_emit_overflow_checks_true_for_quantified_collection_body() {
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("i".into(), i32_ty())],
        body: Box::new(index_expr()),
        triggers: None,
        trigger_inference_mode: None,
    };

    assert!(
        expr.may_emit_overflow_checks(true),
        "collection/index predicates in quantifier bodies still need the auxiliary precheck path"
    );
}

#[test]
fn test_may_emit_overflow_checks_true_for_collection_access_without_flag() {
    assert!(
        collection_len_op().may_emit_overflow_checks(false),
        "collection operations can emit bounds/length predicates even without arithmetic overflow checking"
    );
    assert!(
        index_expr().may_emit_overflow_checks(false),
        "indexing can emit bounds predicates even without arithmetic overflow checking"
    );
}

#[test]
fn test_may_emit_overflow_checks_true_for_shift_without_flag() {
    let expr = TrustVcExpr::SpecialArith {
        op: SpecialArithOp::Shl,
        left: Box::new(var_x()),
        right: Box::new(lit_1()),
        ty: i32_ty(),
    };

    assert!(
        expr.may_emit_overflow_checks(false),
        "shift expressions always require shift-bound checks"
    );
}

#[test]
fn test_may_emit_overflow_checks_true_for_division_without_flag() {
    // Division/remainder partiality (div-by-zero, signed MIN/-1) is gated by
    // `div0_behavior`, not the arithmetic-overflow flag. The precheck must
    // therefore report them even when `check_overflow == false` (e.g. BitVector
    // mode), or the div-by-zero obligation gets silently skipped and a
    // tautology like `x / y == x / y` verifies unsoundly. (#div0-bv-precheck)
    for op in [ArithOp::Div, ArithOp::Rem] {
        let expr = TrustVcExpr::Arith {
            op,
            left: Box::new(var_x()),
            right: Box::new(var_x()),
            ty: i32_ty(),
        };
        assert!(
            expr.may_emit_overflow_checks(false),
            "{op:?} must require the auxiliary precheck even without overflow checking \
             so the div-by-zero / MIN-over-(-1) obligation is not skipped"
        );
        assert!(
            expr.may_emit_overflow_checks(true),
            "{op:?} must require the auxiliary precheck with overflow checking too"
        );
    }
}

#[test]
fn test_may_emit_overflow_checks_false_for_quantified_division_body() {
    // Inside a quantifier body the partiality predicate is modeled in the main
    // formula, not via an outer side-channel, mirroring the additive-arith case.
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".into(), i32_ty())],
        body: Box::new(TrustVcExpr::Arith {
            op: ArithOp::Div,
            left: Box::new(var_x()),
            right: Box::new(var_x()),
            ty: i32_ty(),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };
    assert!(
        !expr.may_emit_overflow_checks(false),
        "division inside a quantifier body does not emit an outer overflow side-channel check"
    );
}

#[test]
fn test_non_skolemized_nested_skolemized_only() {
    // A logic expression wrapping only a Skolemized forall → false
    let expr = TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(TrustVcExpr::BoolLit(true)),
        right: Box::new(simple_forall_no_triggers()),
    };
    assert!(!expr.has_non_skolemized_quantifier());
}

#[test]
fn test_non_skolemized_nested_non_skolemized() {
    // A logic expression wrapping a triggered forall → true
    let expr = TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(TrustVcExpr::BoolLit(true)),
        right: Box::new(simple_forall_with_triggers()),
    };
    assert!(expr.has_non_skolemized_quantifier());
}

#[test]
fn test_non_skolemized_leaf_nodes_false() {
    assert!(!TrustVcExpr::BoolLit(true).has_non_skolemized_quantifier());
    assert!(!var_x().has_non_skolemized_quantifier());
    assert!(!lit_1().has_non_skolemized_quantifier());
}

// ============================================================
// references_collection tests
// ============================================================

#[test]
fn test_references_collection_direct_op() {
    assert!(collection_len_op().references_collection());
}

#[test]
fn test_references_collection_direct_index() {
    assert!(index_expr().references_collection());
}

#[test]
fn test_references_collection_leaf_nodes_false() {
    assert!(!TrustVcExpr::BoolLit(true).references_collection());
    assert!(!var_x().references_collection());
    assert!(!lit_1().references_collection());
    assert!(!(TrustVcExpr::IntConst {
        ty: i32_ty(),
        kind: IntConstKind::Min,
    })
    .references_collection());
}

#[test]
fn test_references_collection_nested_in_quantifier() {
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("i".into(), i32_ty())],
        body: Box::new(index_expr()),
        triggers: None,
        trigger_inference_mode: None,
    };
    assert!(expr.references_collection());
}

#[test]
fn test_references_collection_pure_arith_false() {
    let expr = TrustVcExpr::Arith {
        op: ArithOp::Add,
        left: Box::new(var_x()),
        right: Box::new(lit_1()),
        ty: i32_ty(),
    };
    assert!(!expr.references_collection());
}

#[test]
fn test_references_collection_nested_in_implies() {
    let expr = TrustVcExpr::Implies {
        premise: Box::new(TrustVcExpr::BoolLit(true)),
        conclusion: Box::new(collection_len_op()),
    };
    assert!(expr.references_collection());
}

#[test]
fn test_references_collection_nested_in_cast() {
    let expr = TrustVcExpr::Cast {
        expr: Box::new(collection_len_op()),
        from_ty: TrustVcType::Uint { width: 64 },
        to_ty: i32_ty(),
    };
    assert!(expr.references_collection());
}

#[test]
fn test_references_collection_nested_in_fn_call() {
    let expr = TrustVcExpr::FnCall {
        name: "f".into(),
        args: vec![index_expr()],
        return_ty: i32_ty(),
    };
    assert!(expr.references_collection());
}

#[test]
fn test_references_collection_quantifier_without_collection_false() {
    // A quantifier with pure arithmetic body should NOT reference collections
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".into(), i32_ty())],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(var_x()),
            right: Box::new(lit_1()),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };
    assert!(!expr.references_collection());
}

/// Var with Seq type must return true — gates confirmation check (#2241).
/// If this returns false, collection-typed variables bypass the confirmation
/// check, allowing ay-dpll non-determinism to produce false proofs.
#[test]
fn test_references_collection_var_with_seq_type() {
    let expr = TrustVcExpr::Var {
        name: "s".into(),
        ty: TrustVcType::Seq(Box::new(i32_ty())),
    };
    assert!(
        expr.references_collection(),
        "Var with Seq type must reference collection for confirmation check"
    );
}

/// Var with Set type must return true — same gate as Seq.
#[test]
fn test_references_collection_var_with_set_type() {
    let expr = TrustVcExpr::Var {
        name: "s".into(),
        ty: TrustVcType::Set(Box::new(i32_ty())),
    };
    assert!(
        expr.references_collection(),
        "Var with Set type must reference collection for confirmation check"
    );
}

/// Var with Map type must return true — same gate as Seq.
#[test]
fn test_references_collection_var_with_map_type() {
    let expr = TrustVcExpr::Var {
        name: "m".into(),
        ty: TrustVcType::Map(Box::new(i32_ty()), Box::new(i32_ty())),
    };
    assert!(
        expr.references_collection(),
        "Var with Map type must reference collection for confirmation check"
    );
}

/// FnCall returning a collection type must return true.
/// Functions like `fn get_seq() -> Seq<i32>` produce collection-typed
/// results that can trigger ay-dpll non-determinism.
#[test]
fn test_references_collection_fn_returning_collection() {
    let expr = TrustVcExpr::FnCall {
        name: "get_seq".into(),
        args: vec![],
        return_ty: TrustVcType::Seq(Box::new(i32_ty())),
    };
    assert!(
        expr.references_collection(),
        "FnCall returning Seq must reference collection for confirmation check"
    );
}

/// Quantifier with collection-referencing triggers but pure-arith body
/// returns false — triggers are NOT checked by `references_collection()`.
///
/// This is correct because `references_collection()` gates whether the
/// ay-dpll array theory is involved in the assertion's logical content.
/// Trigger patterns are E-matching hints, not logical content — they don't
/// add array theory terms to the solver formula. If the body is pure
/// arithmetic, the solver never exercises the non-deterministic array
/// theory code path, so the confirmation check is unnecessary.
///
/// Documents the intentional exclusion of triggers from the collection
/// reference check. If triggers were included, assertions with pure
/// arithmetic bodies but collection-typed trigger patterns (common in
/// broadcast assumptions) would incur unnecessary 2x solver overhead.
#[test]
fn test_references_collection_quantifier_trigger_with_collection_body_without() {
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("i".into(), i32_ty())],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(var_x()),
            right: Box::new(lit_1()),
        }),
        // Trigger references a collection operation (index expr), but the body does not
        triggers: Some(vec![vec![index_expr()]]),
        trigger_inference_mode: None,
    };
    assert!(
        !expr.references_collection(),
        "Quantifier with collection trigger but pure-arith body should NOT \
         reference collection — triggers are E-matching hints, not logical content"
    );
}
