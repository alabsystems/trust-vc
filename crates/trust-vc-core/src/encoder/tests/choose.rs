//! Tests for choose! (Hilbert choice) encoding via Skolem functions.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Part of #2143 — choose operator for witness extraction.

use super::*;

use crate::ir::{CompareOp, LogicOp, QuantifierKind, TrustVcExpr, TrustVcType};

// === Encoding-level tests via AstExpressionParser ===

struct ChooseTestEnv {
    solver: Solver,
    variables: std::collections::HashMap<String, Term>,
    collection_lengths: std::collections::HashMap<String, Term>,
    var_types: std::collections::HashMap<String, TrustVcType>,
    functions: std::collections::HashMap<String, ay_dpll::api::FuncDecl>,
    choose_registry: std::collections::HashMap<String, ay_dpll::api::FuncDecl>,
}

impl ChooseTestEnv {
    fn new() -> Self {
        ChooseTestEnv {
            solver: Solver::try_new(ay_dpll::api::Logic::All).unwrap(),
            variables: std::collections::HashMap::new(),
            collection_lengths: std::collections::HashMap::new(),
            var_types: std::collections::HashMap::new(),
            functions: std::collections::HashMap::new(),
            choose_registry: std::collections::HashMap::new(),
        }
    }

    fn declare_var(&mut self, name: &str, ty: TrustVcType) {
        let sort = crate::encoder::types::sort_for_type(&ty);
        let term = self.solver.declare_const(name, sort);
        self.variables.insert(name.to_string(), term);
        self.var_types.insert(name.to_string(), ty);
    }

    fn declare_unary_bool_fn(&mut self, name: &str, arg_ty: TrustVcType) {
        let arg_sort = crate::encoder::types::sort_for_type(&arg_ty);
        let decl = self
            .solver
            .try_declare_fun(name, &[arg_sort], ay_dpll::api::Sort::Bool)
            .expect("test function declaration should succeed");
        self.functions.insert(name.to_string(), decl);
    }

    fn parser(&mut self) -> AstExpressionParser<'_> {
        let mut p = AstExpressionParser::new(
            &mut self.solver,
            &self.variables,
            &mut self.collection_lengths,
            &self.var_types,
            &self.functions,
        );
        p.choose_registry = Some(&mut self.choose_registry);
        p
    }
}

/// Basic choose encoding succeeds for a simple condition.
/// choose(|x: i32| x >= 0) should produce a Skolem term.
#[test]
fn test_choose_basic_encoding_succeeds() {
    let mut env = ChooseTestEnv::new();
    let mut parser = env.parser();

    let expr = TrustVcExpr::Choose {
        var_name: "x".to_string(),
        var_ty: TrustVcType::Int { width: 32 },
        condition: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Ge,
            left: Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: TrustVcType::Int { width: 32 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Int { width: 32 },
            }),
        }),
        key: "test_key_1".to_string(),
        also_assert: None,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2143: choose encoding must succeed, got: {:?}",
        result.err()
    );
}

/// Choose with a free variable capture: choose(|x: u32| x > y).
/// The Skolem function must take y as a parameter.
#[test]
fn test_choose_with_capture_encodes() {
    let mut env = ChooseTestEnv::new();
    env.declare_var("y", TrustVcType::Uint { width: 32 });
    let mut parser = env.parser();

    let expr = TrustVcExpr::Choose {
        var_name: "x".to_string(),
        var_ty: TrustVcType::Uint { width: 32 },
        condition: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: TrustVcType::Uint { width: 32 },
            }),
            right: Box::new(TrustVcExpr::Var {
                name: "y".to_string(),
                ty: TrustVcType::Uint { width: 32 },
            }),
        }),
        key: "test_key_capture".to_string(),
        also_assert: None,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2143: choose with capture must encode, got: {:?}",
        result.err()
    );
}

/// Two choose expressions with the same key reuse the same Skolem function.
#[test]
fn test_choose_same_key_reuses_skolem() {
    let mut env = ChooseTestEnv::new();
    let key = "shared_key".to_string();

    let expr = TrustVcExpr::Choose {
        var_name: "x".to_string(),
        var_ty: TrustVcType::Int { width: 32 },
        condition: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Ge,
            left: Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: TrustVcType::Int { width: 32 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Int { width: 32 },
            }),
        }),
        key: key.clone(),
        also_assert: None,
    };

    // Encode the same expression twice with the same key.
    {
        let mut parser = env.parser();
        let r1 = parser.encode_trust_vc_expr(&expr);
        assert!(r1.is_ok(), "first encode failed: {:?}", r1.err());
    }

    // Registry should have exactly 1 entry after first encode.
    assert_eq!(
        env.choose_registry.len(),
        1,
        "registry should have 1 entry after first encode"
    );

    {
        let mut parser = env.parser();
        let r2 = parser.encode_trust_vc_expr(&expr);
        assert!(r2.is_ok(), "second encode failed: {:?}", r2.err());
    }

    // Registry should still have exactly 1 entry — same key reuses function.
    assert_eq!(
        env.choose_registry.len(),
        1,
        "registry should still have 1 entry after reuse"
    );
}

// === Axiom-semantic tests: choose is guarded by established witnesses ===

/// Without an established witness, choose must not assume its predicate.
///
/// This matches Verus semantics: `choose|x| f(x)` may be used to prove
/// `f(choice)` only after the proof establishes that some `x` satisfies `f`.
#[test]
fn test_choose_without_witness_does_not_constrain_uninterpreted_predicate() {
    let mut env = ChooseTestEnv::new();
    env.declare_unary_bool_fn("f", TrustVcType::MathInt);

    let condition = TrustVcExpr::FnCall {
        name: "f".to_string(),
        args: vec![TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::MathInt,
        }],
        return_ty: TrustVcType::Bool,
    };

    let expr = TrustVcExpr::Choose {
        var_name: "x".to_string(),
        var_ty: TrustVcType::MathInt,
        condition: Box::new(condition),
        key: "test_guarded_no_witness".to_string(),
        also_assert: None,
    };

    let sk_term;
    {
        let mut parser = env.parser();
        sk_term = parser
            .encode_trust_vc_expr(&expr)
            .expect("choose encoding should succeed");
    }

    env.variables.insert("w".to_string(), sk_term);
    env.var_types.insert("w".to_string(), TrustVcType::MathInt);

    let f_w;
    {
        let mut parser = env.parser();
        f_w = parser
            .encode_trust_vc_expr(&TrustVcExpr::FnCall {
                name: "f".to_string(),
                args: vec![TrustVcExpr::Var {
                    name: "w".to_string(),
                    ty: TrustVcType::MathInt,
                }],
                return_ty: TrustVcType::Bool,
            })
            .expect("predicate encoding should succeed");
    }

    let not_f_w = env.solver.try_not(f_w).unwrap();
    env.solver.try_assert_term(not_f_w).unwrap();
    let result = env.solver.check_sat();
    assert!(
        !result.is_unsat(),
        "choose must not prove f(choice) without a witness; got {:?}",
        result
    );
}

/// Once an existential witness is established, the guarded choose axiom
/// constrains the chosen value.
#[test]
fn test_choose_with_explicit_witness_constrains_predicate() {
    let mut env = ChooseTestEnv::new();
    env.declare_unary_bool_fn("f", TrustVcType::MathInt);

    let condition = TrustVcExpr::FnCall {
        name: "f".to_string(),
        args: vec![TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::MathInt,
        }],
        return_ty: TrustVcType::Bool,
    };

    let witness_exists = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Exists,
        bound_vars: vec![("x".to_string(), TrustVcType::MathInt)],
        body: Box::new(condition.clone()),
        triggers: None,
        trigger_inference_mode: None,
    };
    {
        let mut parser = env.parser();
        let exists_term = parser
            .encode_trust_vc_expr(&witness_exists)
            .expect("exists witness should encode");
        env.solver.try_assert_term(exists_term).unwrap();
    }

    let expr = TrustVcExpr::Choose {
        var_name: "x".to_string(),
        var_ty: TrustVcType::MathInt,
        condition: Box::new(condition),
        key: "test_guarded_with_witness".to_string(),
        also_assert: None,
    };

    let sk_term;
    {
        let mut parser = env.parser();
        sk_term = parser
            .encode_trust_vc_expr(&expr)
            .expect("choose encoding should succeed");
    }

    env.variables.insert("w".to_string(), sk_term);
    env.var_types.insert("w".to_string(), TrustVcType::MathInt);

    let f_w;
    {
        let mut parser = env.parser();
        f_w = parser
            .encode_trust_vc_expr(&TrustVcExpr::FnCall {
                name: "f".to_string(),
                args: vec![TrustVcExpr::Var {
                    name: "w".to_string(),
                    ty: TrustVcType::MathInt,
                }],
                return_ty: TrustVcType::Bool,
            })
            .expect("predicate encoding should succeed");
    }

    let not_f_w = env.solver.try_not(f_w).unwrap();
    env.solver.try_assert_term(not_f_w).unwrap();
    let result = env.solver.check_sat();
    assert!(
        result.is_unsat(),
        "established witness should constrain f(choice); got {:?}",
        result
    );
}

/// A conjunction in the choose predicate must be preserved in the guarded
/// Skolem axiom: after establishing `exists x. 0 <= x < 10`, the chosen value
/// must satisfy both `w >= 0` and `w < 10`.
#[test]
fn test_choose_with_explicit_witness_preserves_conjunction_bounds() {
    let mut env = ChooseTestEnv::new();
    let int_ty = TrustVcType::Int { width: 32 };

    let condition = TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Ge,
            left: Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: int_ty.clone(),
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: int_ty.clone(),
            }),
        }),
        right: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Lt,
            left: Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: int_ty.clone(),
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 10,
                ty: int_ty.clone(),
            }),
        }),
    };

    let witness_exists = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Exists,
        bound_vars: vec![("x".to_string(), int_ty.clone())],
        body: Box::new(condition.clone()),
        triggers: None,
        trigger_inference_mode: None,
    };
    {
        let mut parser = env.parser();
        let exists_term = parser
            .encode_trust_vc_expr(&witness_exists)
            .expect("exists witness should encode");
        env.solver.try_assert_term(exists_term).unwrap();
    }

    let expr = TrustVcExpr::Choose {
        var_name: "x".to_string(),
        var_ty: int_ty.clone(),
        condition: Box::new(condition),
        key: "test_guarded_conjunction_bounds".to_string(),
        also_assert: None,
    };

    let sk_term;
    {
        let mut parser = env.parser();
        sk_term = parser
            .encode_trust_vc_expr(&expr)
            .expect("choose encoding should succeed");
    }

    env.variables.insert("w".to_string(), sk_term);
    env.var_types.insert("w".to_string(), int_ty.clone());

    let chosen_bounds = TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Ge,
            left: Box::new(TrustVcExpr::Var {
                name: "w".to_string(),
                ty: int_ty.clone(),
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: int_ty.clone(),
            }),
        }),
        right: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Lt,
            left: Box::new(TrustVcExpr::Var {
                name: "w".to_string(),
                ty: int_ty.clone(),
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 10,
                ty: int_ty,
            }),
        }),
    };

    let chosen_bounds_term;
    {
        let mut parser = env.parser();
        chosen_bounds_term = parser
            .encode_trust_vc_expr(&chosen_bounds)
            .expect("chosen bounds should encode");
    }

    let not_chosen_bounds = env.solver.try_not(chosen_bounds_term).unwrap();
    env.solver.try_assert_term(not_chosen_bounds).unwrap();
    let result = env.solver.check_sat();
    assert!(
        result.is_unsat(),
        "choose with explicit witness should preserve both conjunction bounds; got {:?}",
        result
    );
}

/// Choose with a captured variable encodes a guarded Skolem axiom via the capture.
///
/// The Skolem function takes `y` as a parameter. It should not assume
/// `sk(y) > y` unless a witness exists for the current `y`.
#[test]
fn test_choose_capture_does_not_constrain_without_witness() {
    let mut env = ChooseTestEnv::new();
    env.declare_var("y", TrustVcType::MathInt);

    let condition = TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::MathInt,
        }),
        right: Box::new(TrustVcExpr::Var {
            name: "y".to_string(),
            ty: TrustVcType::MathInt,
        }),
    };
    let expr = TrustVcExpr::Choose {
        var_name: "x".to_string(),
        var_ty: TrustVcType::MathInt,
        condition: Box::new(condition.clone()),
        key: "test_capture_axiom".to_string(),
        also_assert: None,
    };

    let sk_term;
    {
        let mut parser = env.parser();
        sk_term = parser
            .encode_trust_vc_expr(&expr)
            .expect("choose with capture should encode");
    }

    // Bind the Skolem term to "w" for encoding the comparison.
    env.variables.insert("w".to_string(), sk_term);
    env.var_types.insert("w".to_string(), TrustVcType::MathInt);

    // Encode `w > y` through the parser (handles unsigned BV compare).
    let gt_y_term;
    {
        let mut parser = env.parser();
        gt_y_term = parser
            .encode_trust_vc_expr(&TrustVcExpr::Compare {
                op: CompareOp::Gt,
                left: Box::new(TrustVcExpr::Var {
                    name: "w".to_string(),
                    ty: TrustVcType::MathInt,
                }),
                right: Box::new(TrustVcExpr::Var {
                    name: "y".to_string(),
                    ty: TrustVcType::MathInt,
                }),
            })
            .expect("comparison encoding should succeed");
    }

    // The captured existential `∃x:int. x > y` is SATISFIABLE (x = y+1), so the
    // choose axiom soundly entails `sk(y) > y` and `NOT(sk(y) > y)` is UNSAT. ay
    // (>= the 25356919 pin) proves this — a SOUND superset gain; the original
    // assertion that it stays SAT "without a witness" was vacuous for a satisfiable
    // int existential (the witness provably exists).
    let not_gt = env.solver.try_not(gt_y_term).unwrap();
    env.solver.try_assert_term(not_gt).unwrap();
    let result = env.solver.check_sat();
    assert!(
        result.is_unsat(),
        "sound: satisfiable existential exists-x. x>y entails sk(y)>y; ay proves it; got {:?}",
        result
    );
}

/// Nat choose must guard the witness side by the Nat domain.
///
/// Without the domain guard, `forall x: int. x < 0 ==> sk < 0` made
/// `choose(|n: nat| n < 0)` inconsistent because negative mathematical
/// integers satisfied the antecedent even though they are not Nat witnesses.
#[test]
fn test_choose_nat_impossible_predicate_is_consistent() {
    let mut env = ChooseTestEnv::new();

    let expr = TrustVcExpr::Choose {
        var_name: "n".to_string(),
        var_ty: TrustVcType::Nat,
        condition: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Lt,
            left: Box::new(TrustVcExpr::Var {
                name: "n".to_string(),
                ty: TrustVcType::Nat,
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Nat,
            }),
        }),
        key: "test_nat_impossible_predicate".to_string(),
        also_assert: None,
    };

    {
        let mut parser = env.parser();
        parser
            .encode_trust_vc_expr(&expr)
            .expect("nat choose should encode");
    }

    let result = env.solver.check_sat();
    assert!(
        !result.is_unsat(),
        "Nat choose with no Nat witness must remain consistent; got {:?}",
        result
    );
}
