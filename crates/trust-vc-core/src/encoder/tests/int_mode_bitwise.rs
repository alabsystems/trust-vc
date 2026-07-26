//! Int-mode (quantifier body) bitwise operation tests (#1822).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::ir::{CompareOp, SpecialArithOp, TrustVcType};
use crate::ir_expr::{QuantifierKind, TrustVcExpr};

struct Env {
    solver: Solver,
    variables: std::collections::HashMap<String, Term>,
    collection_lengths: std::collections::HashMap<String, Term>,
    var_types: std::collections::HashMap<String, TrustVcType>,
    functions: std::collections::HashMap<String, FuncDecl>,
}

impl Env {
    fn new() -> Self {
        Env {
            solver: Solver::try_new(Logic::All).unwrap(),
            variables: std::collections::HashMap::new(),
            collection_lengths: std::collections::HashMap::new(),
            var_types: std::collections::HashMap::new(),
            functions: std::collections::HashMap::new(),
        }
    }

    fn parser(&mut self) -> AstExpressionParser<'_> {
        AstExpressionParser::new(
            &mut self.solver,
            &self.variables,
            &mut self.collection_lengths,
            &self.var_types,
            &self.functions,
        )
    }

    fn add_u32_var(&mut self, name: &str) -> Term {
        let t = self.solver.declare_const(name, Sort::Int);
        self.variables.insert(name.to_string(), t);
        self.var_types
            .insert(name.to_string(), TrustVcType::Uint { width: 32 });
        t
    }
}

fn u32_var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: TrustVcType::Uint { width: 32 },
    }
}

fn u32_lit(v: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value: v,
        ty: TrustVcType::Uint { width: 32 },
    }
}

fn special_arith(op: SpecialArithOp, left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::SpecialArith {
        op,
        left: Box::new(left),
        right: Box::new(right),
        ty: TrustVcType::Uint { width: 32 },
    }
}

/// Wrap body in `forall |x: u32| body`.
fn forall_u32(body: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), TrustVcType::Uint { width: 32 })],
        body: Box::new(body),
        triggers: None,
        trigger_inference_mode: None,
    }
}

fn compare_ge(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: CompareOp::Ge,
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn compare_lt(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: CompareOp::Lt,
        left: Box::new(left),
        right: Box::new(right),
    }
}

// ========================================================================
// Left shift (#1822)
// ========================================================================

/// DISCRIMINATING: x << 3 in a forall body must encode successfully.
#[test]
fn test_shl_literal_in_quantifier_encodes() {
    let mut env = Env::new();
    let mut parser = env.parser();
    let expr = forall_u32(compare_ge(
        special_arith(SpecialArithOp::Shl, u32_var("x"), u32_lit(3)),
        u32_lit(0),
    ));
    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "x << 3 in quantifier must encode: {:?}",
        result.err()
    );
}

/// DISCRIMINATING: 1 << 5 == 32 must be semantically correct in Int mode.
#[test]
fn test_shl_literal_semantic_correctness() {
    let mut env = Env::new();
    let x = env.add_u32_var("x");
    let mut parser = env.parser();
    parser.quantifier_depth = 1;
    parser.push_quantifier_scope(&[("x".to_string(), TrustVcType::Uint { width: 32 })]);

    let result_term = parser
        .encode_trust_vc_expr(&special_arith(
            SpecialArithOp::Shl,
            u32_var("x"),
            u32_lit(5),
        ))
        .expect("shl in int_mode must not panic");
    parser.pop_quantifier_scope();
    drop(parser);

    // x=1 → x<<5 = 32
    let one = env.solver.int_const(1);
    let x_is_one = env.solver.try_eq(x, one).unwrap();
    let thirty_two = env.solver.int_const(32);
    let result_is_32 = env.solver.try_eq(result_term, thirty_two).unwrap();
    let implication = env.solver.try_implies(x_is_one, result_is_32).unwrap();
    let neg = env.solver.try_not(implication).unwrap();
    env.solver.try_push().unwrap();
    env.solver.try_assert_term(neg).unwrap();
    let sat = env.solver.try_check_sat().unwrap();
    env.solver.try_pop().unwrap();
    assert!(sat.is_unsat(), "1 << 5 should be 32: {:?}", sat);
}

// ========================================================================
// Right shift (#1822)
// ========================================================================

/// DISCRIMINATING: x >> 3 in a forall body must encode successfully.
#[test]
fn test_shr_literal_in_quantifier_encodes() {
    let mut env = Env::new();
    let mut parser = env.parser();
    let expr = forall_u32(compare_ge(
        special_arith(SpecialArithOp::Shr, u32_var("x"), u32_lit(3)),
        u32_lit(0),
    ));
    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "x >> 3 in quantifier must encode: {:?}",
        result.err()
    );
}

/// DISCRIMINATING: 32 >> 3 == 4 must be semantically correct in Int mode.
#[test]
fn test_shr_literal_semantic_correctness() {
    let mut env = Env::new();
    let x = env.add_u32_var("x");
    let mut parser = env.parser();
    parser.quantifier_depth = 1;
    parser.push_quantifier_scope(&[("x".to_string(), TrustVcType::Uint { width: 32 })]);

    let result_term = parser
        .encode_trust_vc_expr(&special_arith(
            SpecialArithOp::Shr,
            u32_var("x"),
            u32_lit(3),
        ))
        .expect("shr in int_mode must not panic");
    parser.pop_quantifier_scope();
    drop(parser);

    // x=32 → x>>3 = 4
    let c32 = env.solver.int_const(32);
    let x_is_32 = env.solver.try_eq(x, c32).unwrap();
    let c4 = env.solver.int_const(4);
    let result_is_4 = env.solver.try_eq(result_term, c4).unwrap();
    let implication = env.solver.try_implies(x_is_32, result_is_4).unwrap();
    let neg = env.solver.try_not(implication).unwrap();
    env.solver.try_push().unwrap();
    env.solver.try_assert_term(neg).unwrap();
    let sat = env.solver.try_check_sat().unwrap();
    env.solver.try_pop().unwrap();
    assert!(sat.is_unsat(), "32 >> 3 should be 4: {:?}", sat);
}

// ========================================================================
// BitAnd with power-of-2 mask (#1822)
// ========================================================================

/// DISCRIMINATING: x & 0xFF in a forall body must encode as x mod 256.
#[test]
fn test_bitand_pow2_mask_in_quantifier_encodes() {
    let mut env = Env::new();
    let mut parser = env.parser();
    let expr = forall_u32(compare_lt(
        special_arith(SpecialArithOp::BitAnd, u32_var("x"), u32_lit(255)),
        u32_lit(256),
    ));
    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "x & 0xFF in quantifier must encode: {:?}",
        result.err()
    );
}

/// DISCRIMINATING: 0x1234 & 0xFF == 0x34 must be semantically correct.
#[test]
fn test_bitand_pow2_mask_semantic_correctness() {
    let mut env = Env::new();
    let x = env.add_u32_var("x");
    let mut parser = env.parser();
    parser.quantifier_depth = 1;
    parser.push_quantifier_scope(&[("x".to_string(), TrustVcType::Uint { width: 32 })]);

    let result_term = parser
        .encode_trust_vc_expr(&special_arith(
            SpecialArithOp::BitAnd,
            u32_var("x"),
            u32_lit(255),
        ))
        .expect("bitand mask in int_mode must not panic");
    parser.pop_quantifier_scope();
    drop(parser);

    // x=0x1234 → x & 0xFF = 0x34
    let val = env.solver.int_const(0x1234);
    let x_is_val = env.solver.try_eq(x, val).unwrap();
    let expected = env.solver.int_const(0x34);
    let result_is_52 = env.solver.try_eq(result_term, expected).unwrap();
    let implication = env.solver.try_implies(x_is_val, result_is_52).unwrap();
    let neg = env.solver.try_not(implication).unwrap();
    env.solver.try_push().unwrap();
    env.solver.try_assert_term(neg).unwrap();
    let sat = env.solver.try_check_sat().unwrap();
    env.solver.try_pop().unwrap();
    assert!(sat.is_unsat(), "0x1234 & 0xFF should be 0x34: {:?}", sat);
}

/// DISCRIMINATING: Commutative mask — 0xFFFF & x must also work.
#[test]
fn test_bitand_pow2_mask_commutative() {
    let mut env = Env::new();
    env.add_u32_var("x");
    let mut parser = env.parser();
    parser.quantifier_depth = 1;
    parser.push_quantifier_scope(&[("x".to_string(), TrustVcType::Uint { width: 32 })]);
    let result = parser.encode_trust_vc_expr(&special_arith(
        SpecialArithOp::BitAnd,
        u32_lit(0xFFFF),
        u32_var("x"),
    ));
    parser.pop_quantifier_scope();
    assert!(
        result.is_ok(),
        "0xFFFF & x (commutative) must encode: {:?}",
        result.err()
    );
}

// ========================================================================
// Error cases — good diagnostics (#1822)
// ========================================================================

/// DISCRIMINATING: Variable shift amount must produce a clear error.
#[test]
fn test_shl_variable_shift_in_int_mode_errors() {
    let mut env = Env::new();
    env.add_u32_var("x");
    env.add_u32_var("n");
    let mut parser = env.parser();
    parser.quantifier_depth = 1;

    let result = parser.encode_trust_vc_expr(&special_arith(
        SpecialArithOp::Shl,
        u32_var("x"),
        u32_var("n"),
    ));
    assert!(result.is_err(), "Variable shift in Int mode must fail");
    let msg = result.unwrap_err().to_string();
    assert!(
        msg.contains("literal shift amount"),
        "Should mention literal: {}",
        msg
    );
    assert!(
        msg.contains("assert_by_bit_vector"),
        "Should suggest BV: {}",
        msg
    );
}

/// DISCRIMINATING: BitOr in Int mode must error with BV hint.
#[test]
fn test_bitor_in_int_mode_errors_with_hint() {
    let mut env = Env::new();
    env.add_u32_var("x");
    let mut parser = env.parser();
    parser.quantifier_depth = 1;
    let result = parser.encode_trust_vc_expr(&special_arith(
        SpecialArithOp::BitOr,
        u32_var("x"),
        u32_lit(1),
    ));
    assert!(result.is_err(), "BitOr in Int mode must fail");
    assert!(result
        .unwrap_err()
        .to_string()
        .contains("assert_by_bit_vector"));
}

/// DISCRIMINATING: BitXor in Int mode must error with BV hint.
#[test]
fn test_bitxor_in_int_mode_errors_with_hint() {
    let mut env = Env::new();
    env.add_u32_var("x");
    let mut parser = env.parser();
    parser.quantifier_depth = 1;
    let result = parser.encode_trust_vc_expr(&special_arith(
        SpecialArithOp::BitXor,
        u32_var("x"),
        u32_lit(1),
    ));
    assert!(result.is_err(), "BitXor in Int mode must fail");
    assert!(result
        .unwrap_err()
        .to_string()
        .contains("assert_by_bit_vector"));
}

/// DISCRIMINATING: Non-power-of-2 BitAnd mask must error with hint.
#[test]
fn test_bitand_non_pow2_mask_errors() {
    let mut env = Env::new();
    env.add_u32_var("x");
    let mut parser = env.parser();
    parser.quantifier_depth = 1;
    // 0xF0 = 240 — not 2^k - 1
    let result = parser.encode_trust_vc_expr(&special_arith(
        SpecialArithOp::BitAnd,
        u32_var("x"),
        u32_lit(0xF0),
    ));
    assert!(result.is_err(), "Non-pow2 BitAnd mask must fail");
    assert!(result.unwrap_err().to_string().contains("power-of-2 masks"));
}

/// DISCRIMINATING: Shift amount >= bit width must error.
#[test]
fn test_shl_out_of_range_shift_errors() {
    let mut env = Env::new();
    env.add_u32_var("x");
    let mut parser = env.parser();
    parser.quantifier_depth = 1;
    let result = parser.encode_trust_vc_expr(&special_arith(
        SpecialArithOp::Shl,
        u32_var("x"),
        u32_lit(32),
    ));
    assert!(result.is_err(), "Shift by >= bit width must fail");
    assert!(result.unwrap_err().to_string().contains("out of range"));
}

// ========================================================================
// Non-BV type fail-closed regression (#2297)
// ========================================================================

/// DISCRIMINATING: Shl with Opaque type must error, not silently default to 32.
/// Regression: previously `ty.bit_width().unwrap_or(32)` masked the problem.
#[test]
fn test_shl_opaque_type_errors_instead_of_defaulting() {
    let mut env = Env::new();
    let t = env.solver.declare_const("x", Sort::Int);
    env.variables.insert("x".to_string(), t);
    env.var_types.insert(
        "x".to_string(),
        TrustVcType::Opaque("legacy-u64".to_string()),
    );

    let mut parser = env.parser();
    parser.quantifier_depth = 1;
    parser.push_quantifier_scope(&[(
        "x".to_string(),
        TrustVcType::Opaque("legacy-u64".to_string()),
    )]);

    let opaque_var = TrustVcExpr::Var {
        name: "x".to_string(),
        ty: TrustVcType::Opaque("legacy-u64".to_string()),
    };
    let opaque_shift = TrustVcExpr::SpecialArith {
        op: SpecialArithOp::Shl,
        left: Box::new(opaque_var),
        right: Box::new(TrustVcExpr::IntLit {
            value: 3,
            ty: TrustVcType::Opaque("legacy-u64".to_string()),
        }),
        ty: TrustVcType::Opaque("legacy-u64".to_string()),
    };
    let result = parser.encode_trust_vc_expr(&opaque_shift);
    parser.pop_quantifier_scope();

    assert!(
        result.is_err(),
        "Opaque type shift must fail, not default to 32-bit: {:?}",
        result.ok()
    );
    let err = result.unwrap_err().to_string();
    assert!(
        err.contains("known bit width"),
        "Error should mention bit width requirement: {}",
        err
    );
}

/// DISCRIMINATING: Shr with Opaque type must also error.
#[test]
fn test_shr_opaque_type_errors_instead_of_defaulting() {
    let mut env = Env::new();
    let t = env.solver.declare_const("x", Sort::Int);
    env.variables.insert("x".to_string(), t);
    env.var_types.insert(
        "x".to_string(),
        TrustVcType::Opaque("legacy-u64".to_string()),
    );

    let mut parser = env.parser();
    parser.quantifier_depth = 1;
    parser.push_quantifier_scope(&[(
        "x".to_string(),
        TrustVcType::Opaque("legacy-u64".to_string()),
    )]);

    let opaque_var = TrustVcExpr::Var {
        name: "x".to_string(),
        ty: TrustVcType::Opaque("legacy-u64".to_string()),
    };
    let opaque_shift = TrustVcExpr::SpecialArith {
        op: SpecialArithOp::Shr,
        left: Box::new(opaque_var),
        right: Box::new(TrustVcExpr::IntLit {
            value: 3,
            ty: TrustVcType::Opaque("legacy-u64".to_string()),
        }),
        ty: TrustVcType::Opaque("legacy-u64".to_string()),
    };
    let result = parser.encode_trust_vc_expr(&opaque_shift);
    parser.pop_quantifier_scope();

    assert!(
        result.is_err(),
        "Opaque type shift must fail, not default to 32-bit: {:?}",
        result.ok()
    );
    let err = result.unwrap_err().to_string();
    assert!(
        err.contains("known bit width"),
        "Error should mention bit width requirement: {}",
        err
    );
}
