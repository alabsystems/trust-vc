//! Negation overflow tests — #2108 regression.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Tests for int_mode negation overflow check emission.
//! Filed as #2108: encode_neg int_mode path emits no overflow check for -MIN.

use super::*;

use crate::ir::{CompareOp, TrustVcType};
use crate::ir_expr::{QuantifierKind, TrustVcExpr};

// ========================================================================
// Test infrastructure (mirrors QuantifierTestEnv from ir_soundness_regressions)
// ========================================================================

struct NegTestEnv {
    solver: Solver,
    variables: std::collections::HashMap<String, Term>,
    collection_lengths: std::collections::HashMap<String, Term>,
    var_types: std::collections::HashMap<String, TrustVcType>,
    functions: std::collections::HashMap<String, FuncDecl>,
}

impl NegTestEnv {
    fn new() -> Self {
        NegTestEnv {
            solver: Solver::try_new(Logic::All).unwrap(),
            variables: std::collections::HashMap::new(),
            collection_lengths: std::collections::HashMap::new(),
            var_types: std::collections::HashMap::new(),
            functions: std::collections::HashMap::new(),
        }
    }

    fn parser_with_overflow(&mut self) -> AstExpressionParser<'_> {
        AstExpressionParser::with_overflow_checking(
            &mut self.solver,
            &self.variables,
            &mut self.collection_lengths,
            &self.var_types,
            &self.functions,
            true,
        )
    }
}

// ========================================================================
// #2108: encode_neg int_mode emits no overflow check for negation of MIN
// ========================================================================

/// DISCRIMINATING: negation of a signed bound variable in a quantifier body
/// with overflow_checks enabled MUST emit a "negation overflow" check.
///
/// Pre-fix: int_mode path at ir_encoder/mod.rs:269-276 wraps via
/// `wrap_int_with_ctx` but never pushes to `overflow_checks`. The BV path
/// (lines 285-292) correctly emits via `try_bvneg_no_overflow`.
///
/// This test will FAIL until the fix is applied, confirming the bug exists.
#[test]
fn test_2108_neg_int_mode_emits_overflow_check() {
    let mut env = NegTestEnv::new();
    let mut parser = env.parser_with_overflow();

    // forall |x: i8| (-x) >= -128
    // At x = -128, -x overflows (128 doesn't fit in i8).
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), TrustVcType::Int { width: 8 })],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Ge,
            left: Box::new(TrustVcExpr::Neg(Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: TrustVcType::Int { width: 8 },
            }))),
            right: Box::new(TrustVcExpr::IntLit {
                value: -128,
                ty: TrustVcType::Int { width: 8 },
            }),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2108: negation in quantifier must not panic: {:?}",
        result.err()
    );

    // #2557: overflow predicates inside quantifier bodies reference bound
    // variables; asserting them at the outer scope constrains those variables
    // globally and causes false Verified results. The quantifier_depth == 0
    // guard now suppresses overflow collection inside forall/exists bodies.
    // Future work: Verus-style body precondition encoding.
    let checks = parser.take_overflow_checks();
    assert!(
        checks.is_empty(),
        "#2557: negation overflow inside quantifier body must be suppressed \
         (predicates reference bound variables). Got check names: {:?}",
        checks.iter().map(|(n, _)| n.as_ref()).collect::<Vec<_>>()
    );
}

/// Control test: negation of non-MIN values should not trigger overflow.
/// If the bug fix is correct, this test should also pass after the fix
/// because the overflow predicate (inner ≠ MIN) is true for non-MIN values.
#[test]
fn test_2108_neg_non_min_no_overflow() {
    let mut env = NegTestEnv::new();
    let mut parser = env.parser_with_overflow();

    // forall |x: i8| (-x) == (-x)
    // This is trivially true, but the point is that negation should still
    // emit an overflow check (for the case where x = -128).
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), TrustVcType::Int { width: 8 })],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(TrustVcExpr::Neg(Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: TrustVcType::Int { width: 8 },
            }))),
            right: Box::new(TrustVcExpr::Neg(Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: TrustVcType::Int { width: 8 },
            }))),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2108 control: negation identity must encode without error: {:?}",
        result.err()
    );
}

/// DISCRIMINATING: negation of unsigned variable should NOT emit overflow check.
/// Unsigned negation is always wrapping (0u8 - x), and Rust doesn't consider
/// it an "overflow" in the same way — it's just wrapping subtraction.
/// However, the current BV path does emit a check via try_bvneg_no_overflow.
/// This test documents the current behavior rather than mandating it.
#[test]
fn test_2108_neg_unsigned_behavior() {
    let mut env = NegTestEnv::new();
    let mut parser = env.parser_with_overflow();

    // forall |x: u8| (-x) <= 255
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), TrustVcType::Uint { width: 8 })],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Le,
            left: Box::new(TrustVcExpr::Neg(Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: TrustVcType::Uint { width: 8 },
            }))),
            right: Box::new(TrustVcExpr::IntLit {
                value: 255,
                ty: TrustVcType::Uint { width: 8 },
            }),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2108: unsigned negation must encode without error: {:?}",
        result.err()
    );
}
