//! Saturating arithmetic missing-bounds regressions — #2109.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Saturating arithmetic must fail closed when bounds cannot be resolved.

use super::*;

use crate::ir::{ArithOp, TrustVcType, WrappingMode};
use crate::ir_expr::TrustVcExpr;

struct SaturatingMissingBoundsEnv {
    solver: Solver,
    variables: std::collections::HashMap<String, Term>,
    collection_lengths: std::collections::HashMap<String, Term>,
    var_types: std::collections::HashMap<String, TrustVcType>,
    functions: std::collections::HashMap<String, FuncDecl>,
}

impl SaturatingMissingBoundsEnv {
    fn new() -> Self {
        SaturatingMissingBoundsEnv {
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
}

/// REGRESSION: BV saturating arithmetic on typed operands must succeed.
///
/// Since #2029, `encode_var` populates `term_widths` from the IR-declared Var
/// type, so Var-based WrappingArith always has width metadata available via
/// the operand term_widths (even if the outer WrappingArith `ty` is Opaque).
/// Previously (#2109) this test verified the missing-width error path, but
/// the #2029 fix made that path unreachable for typed Var operands.
///
/// The error path still exists in `encode_wrapping_arith` for future expression
/// types that don't propagate `term_widths`, but cannot be reached via the
/// current `encode_trust_vc_expr` API with typed Var nodes.
#[test]
fn test_2109_saturating_add_bv_typed_operands_succeeds() {
    let mut env = SaturatingMissingBoundsEnv::new();
    let x = env.solver.declare_const("x", Sort::bitvec(8));
    let y = env.solver.declare_const("y", Sort::bitvec(8));
    env.variables.insert("x".to_string(), x);
    env.variables.insert("y".to_string(), y);
    env.var_types
        .insert("x".to_string(), TrustVcType::Uint { width: 8 });
    env.var_types
        .insert("y".to_string(), TrustVcType::Uint { width: 8 });

    let mut parser = env.parser();

    // Remove term_widths: encode_var will re-insert them from the Var type.
    parser.term_widths.remove(&x);
    parser.term_widths.remove(&y);

    let expr = TrustVcExpr::WrappingArith {
        mode: WrappingMode::Saturating,
        op: ArithOp::Add,
        left: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Uint { width: 8 },
        }),
        right: Box::new(TrustVcExpr::Var {
            name: "y".to_string(),
            ty: TrustVcType::Uint { width: 8 },
        }),
        ty: TrustVcType::Opaque("u8".to_string()),
    };

    // Since #2029, encode_var re-populates term_widths from the Var type,
    // so the saturating encoder can derive width from the operand metadata
    // even when the outer WrappingArith ty is Opaque.
    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2109/#2029: saturating_add with typed Var operands should succeed, got: {:?}",
        result.err()
    );
}

/// DISCRIMINATING: int_mode saturating arithmetic must return an encode error
/// when no per-expression type width or quantifier wrap context is available.
#[test]
fn test_2109_saturating_add_int_mode_missing_wrap_ctx_errors() {
    let mut env = SaturatingMissingBoundsEnv::new();
    let mut parser = env.parser();
    parser.quantifier_depth = 1; // Force int_mode without a quantifier scope.

    let expr = TrustVcExpr::WrappingArith {
        mode: WrappingMode::Saturating,
        op: ArithOp::Add,
        left: Box::new(TrustVcExpr::IntLit {
            value: 1,
            ty: TrustVcType::MathInt,
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 2,
            ty: TrustVcType::MathInt,
        }),
        ty: TrustVcType::Opaque("int-mode-no-wrap".to_string()),
    };

    let err = parser
        .encode_trust_vc_expr(&expr)
        .expect_err("#2109: int_mode saturating_add must fail when wrap context is missing");
    assert!(
        err.to_string().contains("requires wrap context"),
        "#2109: expected missing-wrap-context saturating error, got: {}",
        err
    );
}
