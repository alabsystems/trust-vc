// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for ground-term pool registration, flush, and instantiation.
//!
//! Extracted from `ground_pool.rs` to keep production code under 500 lines.

use super::*;
use ay_dpll::api::{Logic, Solver, Sort};

#[test]
fn test_duplicate_register_does_not_bump_revision_or_count() {
    let mut solver = Solver::try_new(Logic::All).expect("solver should construct");
    let x = solver.declare_const("x", Sort::bitvec(32));
    let _f = solver
        .try_declare_fun("f", &[Sort::bitvec(32)], Sort::bitvec(32))
        .expect("function should declare");

    let mut pool = GroundTermPool::new();

    assert!(pool.register("f", vec![x]));
    let revision = pool.revision_for_tests();
    assert!(
        !pool.register("f", vec![x]),
        "duplicate registration should be skipped"
    );
    assert_eq!(
        pool.revision_for_tests(),
        revision,
        "duplicate registration must not bump the pool revision"
    );
    assert_eq!(
        pool.ground_term_count(),
        1,
        "duplicate registration must not add a second entry"
    );
}

#[test]
fn test_needs_flush_false_when_no_axioms() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::bitvec(32));
    let mut pool = GroundTermPool::new();
    pool.register("f", vec![x]);
    assert!(
        !pool.needs_flush(),
        "pool with ground terms but no axioms should not need flush"
    );
}

#[test]
fn test_needs_flush_true_after_axiom_registration() {
    let mut pool = GroundTermPool::new();
    let axiom = GroundAxiom {
        name: "ax1".to_string(),
        seed_symbols: vec!["f".to_string()],
        seed_triggers: Vec::new(),
        bound_vars: vec!["v".to_string()],
        expr: TrustVcExpr::BoolLit(true),
    };
    pool.register_axiom(axiom);
    assert!(pool.needs_flush(), "pool with an axiom should need flush");
}

#[test]
fn test_needs_flush_false_after_mark_flushed() {
    let mut pool = GroundTermPool::new();
    pool.register_axiom(GroundAxiom {
        name: "ax1".to_string(),
        seed_symbols: vec!["f".to_string()],
        seed_triggers: Vec::new(),
        bound_vars: vec!["v".to_string()],
        expr: TrustVcExpr::BoolLit(true),
    });
    assert!(pool.needs_flush());
    pool.mark_flushed();
    assert!(
        !pool.needs_flush(),
        "pool should not need flush after mark_flushed"
    );
}

#[test]
fn test_pending_instantiations_matches_any_seed_symbol() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::bitvec(32));
    let y = solver.declare_const("y", Sort::bitvec(32));

    let mut pool = GroundTermPool::new();
    pool.register("f", vec![x]);
    pool.register("g", vec![y]);
    pool.register_axiom(GroundAxiom {
        name: "ax_f".to_string(),
        seed_symbols: vec!["f".to_string()],
        seed_triggers: Vec::new(),
        bound_vars: vec!["v".to_string()],
        expr: TrustVcExpr::BoolLit(true),
    });

    let pending = pool.pending_instantiations();
    assert_eq!(
        pending.len(),
        1,
        "only f(x) should match seed_symbols ['f'], not g(y)"
    );
    assert_eq!(pending[0].axiom.name, "ax_f");
    assert_eq!(pending[0].arg_terms, vec![x]);
}

#[test]
fn test_pending_instantiations_support_alternative_seed_symbols() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::bitvec(32));
    let y = solver.declare_const("y", Sort::bitvec(32));

    let mut pool = GroundTermPool::new();
    pool.register("f", vec![x]);
    pool.register("g", vec![y]);
    pool.register_axiom(GroundAxiom {
        name: "ax_fg".to_string(),
        seed_symbols: vec!["f".to_string(), "g".to_string()],
        seed_triggers: Vec::new(),
        bound_vars: vec!["v".to_string()],
        expr: TrustVcExpr::BoolLit(true),
    });

    let pending = pool.pending_instantiations();
    assert_eq!(
        pending.len(),
        2,
        "alternative singleton seed symbols should match either trigger head"
    );
    assert!(pending.iter().any(|work| work.arg_terms == vec![x]));
    assert!(pending.iter().any(|work| work.arg_terms == vec![y]));
}

#[test]
fn test_pending_instantiations_skip_solver_only_multi_trigger_axioms() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::bitvec(32));

    let mut pool = GroundTermPool::new();
    pool.register("f", vec![x]);
    pool.register_axiom(GroundAxiom {
        name: "ax_solver_only".to_string(),
        seed_symbols: Vec::new(),
        seed_triggers: Vec::new(),
        bound_vars: vec!["v".to_string()],
        expr: TrustVcExpr::BoolLit(true),
    });

    assert!(
        pool.pending_instantiations().is_empty(),
        "solver-only multi-trigger axioms must not fabricate eager-seed work"
    );
}

#[test]
fn test_pending_instantiations_skips_arity_mismatch() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::bitvec(32));
    let y = solver.declare_const("y", Sort::bitvec(32));

    let mut pool = GroundTermPool::new();
    // Register f(x, y) — arity 2
    pool.register("f", vec![x, y]);
    // Axiom expects arity 1
    pool.register_axiom(GroundAxiom {
        name: "ax_f".to_string(),
        seed_symbols: vec!["f".to_string()],
        seed_triggers: Vec::new(),
        bound_vars: vec!["v".to_string()],
        expr: TrustVcExpr::BoolLit(true),
    });

    let pending = pool.pending_instantiations();
    assert!(
        pending.is_empty(),
        "arity mismatch (2 args vs 1 bound var) should skip: got {} pending",
        pending.len()
    );
}

#[test]
fn test_pending_instantiations_match_singleton_arithmetic_trigger_shape() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let ground_arg = solver.int_const(5);
    let math_int = crate::ir::TrustVcType::MathInt;
    let two = TrustVcExpr::IntLit {
        value: 2,
        ty: math_int.clone(),
    };
    let three = TrustVcExpr::IntLit {
        value: 3,
        ty: math_int.clone(),
    };
    let ground_expr = TrustVcExpr::Arith {
        op: crate::ir::ArithOp::Add,
        left: Box::new(two.clone()),
        right: Box::new(three.clone()),
        ty: math_int.clone(),
    };
    let pattern_expr = TrustVcExpr::Arith {
        op: crate::ir::ArithOp::Add,
        left: Box::new(TrustVcExpr::Var {
            name: "a".to_string(),
            ty: math_int.clone(),
        }),
        right: Box::new(TrustVcExpr::Var {
            name: "b".to_string(),
            ty: math_int,
        }),
        ty: crate::ir::TrustVcType::MathInt,
    };

    let mut pool = GroundTermPool::new();
    pool.register_expr("some_fn", vec![ground_arg], vec![ground_expr]);
    pool.register_axiom(GroundAxiom {
        name: "ax_some_fn".to_string(),
        seed_symbols: Vec::new(),
        seed_triggers: vec![GroundTrigger {
            symbol: "some_fn".to_string(),
            arg_patterns: vec![pattern_expr],
            bound_exprs: None,
        }],
        bound_vars: vec!["a".to_string(), "b".to_string()],
        expr: TrustVcExpr::BoolLit(true),
    });

    let pending = pool.pending_instantiations();
    assert_eq!(
        pending.len(),
        1,
        "some_fn(a + b) should match the ground call shape some_fn(2 + 3)"
    );
    assert_eq!(
        pending[0].bound_exprs,
        Some(vec![two, three]),
        "arithmetic trigger matching should bind a=2 and b=3"
    );
}

#[test]
fn test_pending_instantiations_prefer_trigger_shape_over_seed_symbol() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let ground_arg = solver.int_const(3);
    let math_int = crate::ir::TrustVcType::MathInt;
    let two = TrustVcExpr::IntLit {
        value: 2,
        ty: math_int.clone(),
    };
    let one = TrustVcExpr::IntLit {
        value: 1,
        ty: math_int.clone(),
    };
    let ground_expr = TrustVcExpr::Arith {
        op: crate::ir::ArithOp::Add,
        left: Box::new(two.clone()),
        right: Box::new(one.clone()),
        ty: math_int.clone(),
    };
    let pattern_expr = TrustVcExpr::Arith {
        op: crate::ir::ArithOp::Add,
        left: Box::new(TrustVcExpr::Var {
            name: "a".to_string(),
            ty: math_int.clone(),
        }),
        right: Box::new(one),
        ty: math_int,
    };

    let mut pool = GroundTermPool::new();
    pool.register_expr("some_fn", vec![ground_arg], vec![ground_expr]);
    pool.register_axiom(GroundAxiom {
        name: "ax_some_fn".to_string(),
        seed_symbols: vec!["some_fn".to_string()],
        seed_triggers: vec![GroundTrigger {
            symbol: "some_fn".to_string(),
            arg_patterns: vec![pattern_expr],
            bound_exprs: None,
        }],
        bound_vars: vec!["a".to_string()],
        expr: TrustVcExpr::BoolLit(true),
    });

    let pending = pool.pending_instantiations();
    assert_eq!(
        pending.len(),
        1,
        "some_fn(a + 1) should match by trigger shape before symbol-only seeding"
    );
    assert_eq!(
        pending[0].bound_exprs,
        Some(vec![two]),
        "trigger shape should bind a=2 instead of falling back to raw arg terms"
    );
}

#[test]
fn test_pending_instantiations_do_not_fallback_to_seed_symbol_for_trigger_mismatch() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let ground_arg = solver.int_const(4);
    let math_int = crate::ir::TrustVcType::MathInt;
    let two = TrustVcExpr::IntLit {
        value: 2,
        ty: math_int.clone(),
    };
    let one = TrustVcExpr::IntLit {
        value: 1,
        ty: math_int.clone(),
    };
    let ground_expr = TrustVcExpr::Arith {
        op: crate::ir::ArithOp::Add,
        left: Box::new(two.clone()),
        right: Box::new(two),
        ty: math_int.clone(),
    };
    let pattern_expr = TrustVcExpr::Arith {
        op: crate::ir::ArithOp::Add,
        left: Box::new(TrustVcExpr::Var {
            name: "a".to_string(),
            ty: math_int.clone(),
        }),
        right: Box::new(one),
        ty: math_int,
    };

    let mut pool = GroundTermPool::new();
    pool.register_expr("some_fn", vec![ground_arg], vec![ground_expr]);
    pool.register_axiom(GroundAxiom {
        name: "ax_some_fn".to_string(),
        seed_symbols: vec!["some_fn".to_string()],
        seed_triggers: vec![GroundTrigger {
            symbol: "some_fn".to_string(),
            arg_patterns: vec![pattern_expr],
            bound_exprs: None,
        }],
        bound_vars: vec!["a".to_string()],
        expr: TrustVcExpr::BoolLit(true),
    });

    let pending = pool.pending_instantiations();
    assert!(
        pending.is_empty(),
        "some_fn(a + 1) must not fall back to symbol-only seeding for nonmatching some_fn(2 + 2)"
    );
}

#[test]
fn test_mark_instantiated_prevents_re_instantiation() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::bitvec(32));

    let mut pool = GroundTermPool::new();
    pool.register("f", vec![x]);
    pool.register_axiom(GroundAxiom {
        name: "ax_f".to_string(),
        seed_symbols: vec!["f".to_string()],
        seed_triggers: Vec::new(),
        bound_vars: vec!["v".to_string()],
        expr: TrustVcExpr::BoolLit(true),
    });

    assert_eq!(pool.pending_instantiations().len(), 1);

    pool.mark_instantiated("ax_f", vec![x]);
    assert!(
        pool.pending_instantiations().is_empty(),
        "mark_instantiated should prevent re-instantiation of the same (axiom, args) pair"
    );
}

#[test]
fn test_multiple_ground_terms_produce_multiple_instantiations() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::bitvec(32));
    let y = solver.declare_const("y", Sort::bitvec(32));

    let mut pool = GroundTermPool::new();
    pool.register("f", vec![x]);
    pool.register("f", vec![y]);
    pool.register_axiom(GroundAxiom {
        name: "ax_f".to_string(),
        seed_symbols: vec!["f".to_string()],
        seed_triggers: Vec::new(),
        bound_vars: vec!["v".to_string()],
        expr: TrustVcExpr::BoolLit(true),
    });

    let pending = pool.pending_instantiations();
    assert_eq!(
        pending.len(),
        2,
        "two distinct ground terms for same symbol should produce two instantiations"
    );
}

#[test]
fn test_reset_flush_state_re_enables_flush() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::bitvec(32));

    let mut pool = GroundTermPool::new();
    pool.register("f", vec![x]);
    pool.register_axiom(GroundAxiom {
        name: "ax_f".to_string(),
        seed_symbols: vec!["f".to_string()],
        seed_triggers: Vec::new(),
        bound_vars: vec!["v".to_string()],
        expr: TrustVcExpr::BoolLit(true),
    });

    // Simulate first flush cycle
    pool.mark_instantiated("ax_f", vec![x]);
    pool.mark_flushed();
    assert!(!pool.needs_flush());
    assert!(
        pool.pending_instantiations().is_empty(),
        "after mark_instantiated, no pending work"
    );

    // Reset flush state (simulates solver pop retracting flushed axioms)
    pool.reset_flush_state();
    assert!(
        pool.needs_flush(),
        "reset_flush_state must re-enable needs_flush so axioms are re-flushed"
    );
    assert_eq!(
        pool.pending_instantiations().len(),
        1,
        "reset_flush_state must clear instantiated_pairs so f(x) is re-instantiated"
    );
}

#[test]
fn test_new_registration_after_flush_triggers_needs_flush() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::bitvec(32));
    let y = solver.declare_const("y", Sort::bitvec(32));

    let mut pool = GroundTermPool::new();
    pool.register("f", vec![x]);
    pool.register_axiom(GroundAxiom {
        name: "ax_f".to_string(),
        seed_symbols: vec!["f".to_string()],
        seed_triggers: Vec::new(),
        bound_vars: vec!["v".to_string()],
        expr: TrustVcExpr::BoolLit(true),
    });
    pool.mark_flushed();
    assert!(!pool.needs_flush());

    // New ground term after flush should trigger needs_flush again
    pool.register("f", vec![y]);
    assert!(
        pool.needs_flush(),
        "new ground term after mark_flushed should trigger needs_flush"
    );
}
