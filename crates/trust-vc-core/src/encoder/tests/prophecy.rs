//! Tests for prophecy variable encoding — Part of #2519.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Follows the choose.rs test pattern: AstExpressionParser-level tests for
//! encoding mechanics, AYEncoder-level tests for end-to-end verification.

use super::*;

use crate::ir::{TrustVcExpr, TrustVcType};

// === Encoding-level tests via AstExpressionParser ===

struct ProphecyTestEnv {
    solver: Solver,
    variables: std::collections::HashMap<String, Term>,
    collection_lengths: std::collections::HashMap<String, Term>,
    var_types: std::collections::HashMap<String, TrustVcType>,
    functions: std::collections::HashMap<String, ay_dpll::api::FuncDecl>,
    prophecy_registry: std::collections::HashMap<String, Term>,
}

impl ProphecyTestEnv {
    fn new() -> Self {
        ProphecyTestEnv {
            solver: Solver::try_new(ay_dpll::api::Logic::All).unwrap(),
            variables: std::collections::HashMap::new(),
            collection_lengths: std::collections::HashMap::new(),
            var_types: std::collections::HashMap::new(),
            functions: std::collections::HashMap::new(),
            prophecy_registry: std::collections::HashMap::new(),
        }
    }

    fn declare_var(&mut self, name: &str, ty: TrustVcType) {
        let sort = crate::encoder::types::sort_for_type(&ty);
        let term = self.solver.declare_const(name, sort);
        self.variables.insert(name.to_string(), term);
        self.var_types.insert(name.to_string(), ty);
    }

    fn parser(&mut self) -> AstExpressionParser<'_> {
        let mut p = AstExpressionParser::new(
            &mut self.solver,
            &self.variables,
            &mut self.collection_lengths,
            &self.var_types,
            &self.functions,
        );
        p.prophecy_registry = Some(&mut self.prophecy_registry);
        p
    }
}

/// Basic prophecy creation: ProphecyNew produces a term.
#[test]
fn test_prophecy_new_encoding_succeeds() {
    let mut env = ProphecyTestEnv::new();
    let mut parser = env.parser();

    let expr = TrustVcExpr::ProphecyNew {
        name: "p".to_string(),
        ty: TrustVcType::Int { width: 32 },
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2519: prophecy new encoding must succeed, got: {:?}",
        result.err()
    );
}

/// Same prophecy name returns the same term (registry dedup).
#[test]
fn test_prophecy_same_name_reuses_term() {
    let mut env = ProphecyTestEnv::new();

    let expr = TrustVcExpr::ProphecyNew {
        name: "p".to_string(),
        ty: TrustVcType::Int { width: 32 },
    };

    let t1 = {
        let mut parser = env.parser();
        parser.encode_trust_vc_expr(&expr).unwrap()
    };

    assert_eq!(
        env.prophecy_registry.len(),
        1,
        "registry should have 1 entry after first encode"
    );

    let t2 = {
        let mut parser = env.parser();
        parser.encode_trust_vc_expr(&expr).unwrap()
    };

    assert_eq!(
        env.prophecy_registry.len(),
        1,
        "registry should still have 1 entry after reuse"
    );
    assert_eq!(t1, t2, "same prophecy name must return same term");
}

/// DISCRIMINATING: ProphecyResolve constrains the prophecy to equal the resolved value.
/// After resolving to 42, p != 42 must be UNSAT (the resolve forces the value).
#[test]
fn test_prophecy_basic_resolve() {
    let mut env = ProphecyTestEnv::new();

    // Create the prophecy first.
    {
        let mut parser = env.parser();
        let new_expr = TrustVcExpr::ProphecyNew {
            name: "p".to_string(),
            ty: TrustVcType::Int { width: 32 },
        };
        parser.encode_trust_vc_expr(&new_expr).unwrap();
    }

    // Resolve it to 42.
    {
        let mut parser = env.parser();
        let resolve_expr = TrustVcExpr::ProphecyResolve {
            name: "p".to_string(),
            value: Box::new(TrustVcExpr::IntLit {
                value: 42,
                ty: TrustVcType::Int { width: 32 },
            }),
        };
        parser.encode_trust_vc_expr(&resolve_expr).unwrap();
    }

    // DISCRIMINATING: p != 42 must be UNSAT — the resolve forces p == 42.
    // Without the resolve, p is unconstrained and p != 42 would be SAT.
    {
        let prophecy_term = *env.prophecy_registry.get("p").unwrap();
        let forty_two = env.solver.try_bv_const(42, 32).unwrap();
        let eq = env.solver.try_eq(prophecy_term, forty_two).unwrap();
        let neq = env.solver.try_not(eq).unwrap();
        let result = env.solver.check_sat_assuming(&[neq]);
        assert!(
            result.is_unsat(),
            "#2519: prophecy resolved to 42 — p != 42 must be UNSAT, got {:?}",
            result
        );
    }
}

/// Unresolved prophecy is unconstrained — should be SAT with any value.
#[test]
fn test_prophecy_unresolved_is_unconstrained() {
    let mut env = ProphecyTestEnv::new();

    {
        let mut parser = env.parser();
        let new_expr = TrustVcExpr::ProphecyNew {
            name: "q".to_string(),
            ty: TrustVcType::Int { width: 32 },
        };
        parser.encode_trust_vc_expr(&new_expr).unwrap();
    }

    // Without resolution, the prophecy should be satisfiable with q == 0.
    let prophecy_term = *env.prophecy_registry.get("q").unwrap();
    let zero = env.solver.try_bv_const(0, 32).unwrap();
    let eq_zero = env.solver.try_eq(prophecy_term, zero).unwrap();
    let result_zero = env.solver.check_sat_assuming(&[eq_zero]);
    assert_eq!(
        result_zero,
        ay_dpll::api::SolveResult::Sat,
        "#2519: unresolved prophecy must be SAT with q == 0"
    );

    // And also satisfiable with q == 99.
    let ninety_nine = env.solver.try_bv_const(99, 32).unwrap();
    let eq_99 = env.solver.try_eq(prophecy_term, ninety_nine).unwrap();
    let result_99 = env.solver.check_sat_assuming(&[eq_99]);
    assert_eq!(
        result_99,
        ay_dpll::api::SolveResult::Sat,
        "#2519: unresolved prophecy must be SAT with q == 99"
    );
}

/// Resolving an unknown prophecy name returns an error.
#[test]
fn test_prophecy_resolve_unknown_name_errors() {
    let mut env = ProphecyTestEnv::new();
    let mut parser = env.parser();

    let resolve_expr = TrustVcExpr::ProphecyResolve {
        name: "nonexistent".to_string(),
        value: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::Int { width: 32 },
        }),
    };

    let result = parser.encode_trust_vc_expr(&resolve_expr);
    assert!(
        result.is_err(),
        "#2519: resolving unknown prophecy must error"
    );
    let err_msg = format!("{:?}", result.err().unwrap());
    assert!(
        err_msg.contains("nonexistent"),
        "#2519: error must mention the unknown prophecy name, got: {}",
        err_msg
    );
}

/// DISCRIMINATING: Prophecy used in assumption before resolution propagates
/// constraints through the resolve. After assuming p > 0 and resolving p = x,
/// x <= 0 must be UNSAT (the constraint flows through the equality).
#[test]
fn test_prophecy_constrained_before_resolve() {
    let mut env = ProphecyTestEnv::new();
    env.declare_var("x", TrustVcType::Int { width: 32 });

    // Create prophecy.
    {
        let mut parser = env.parser();
        let new_expr = TrustVcExpr::ProphecyNew {
            name: "p".to_string(),
            ty: TrustVcType::Int { width: 32 },
        };
        parser.encode_trust_vc_expr(&new_expr).unwrap();
    }

    // Assume: p > 0 (prophecy is used in reasoning before resolution).
    {
        let prophecy_term = *env.prophecy_registry.get("p").unwrap();
        let zero = env.solver.try_bv_const(0, 32).unwrap();
        let p_gt_zero = env.solver.try_bvsgt(prophecy_term, zero).unwrap();
        env.solver.try_assert_term(p_gt_zero).unwrap();
    }

    // Resolve: p = x.
    {
        let mut parser = env.parser();
        let resolve_expr = TrustVcExpr::ProphecyResolve {
            name: "p".to_string(),
            value: Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: TrustVcType::Int { width: 32 },
            }),
        };
        parser.encode_trust_vc_expr(&resolve_expr).unwrap();
    }

    // DISCRIMINATING: p > 0 and p == x forces x > 0, so x <= 0 must be UNSAT.
    // Without the resolve, x is unconstrained and x <= 0 would be SAT.
    let x_term = *env.variables.get("x").unwrap();
    let zero = env.solver.try_bv_const(0, 32).unwrap();
    let x_gt_zero = env.solver.try_bvsgt(x_term, zero).unwrap();
    let x_le_zero = env.solver.try_not(x_gt_zero).unwrap();
    let result = env.solver.check_sat_assuming(&[x_le_zero]);
    assert!(
        result.is_unsat(),
        "#2519: after assuming p > 0 and resolving p = x, x <= 0 must be UNSAT, got {:?}",
        result
    );
}
