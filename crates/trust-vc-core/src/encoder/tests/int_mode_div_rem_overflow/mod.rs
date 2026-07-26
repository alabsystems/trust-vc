//! Direct tests for Int-mode signed div/rem overflow guard generation.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Covers `AstExpressionParser::int_mode_signed_div_rem_no_overflow` branches
//! that are hard to isolate through end-to-end expression parsing.
//!
//! Original monolith (779 lines, 15 tests) split for maintainability (#2145).

use super::*;

mod constant_zero_and_bv;
mod int_mode_and_width;
mod quantifier_and_wrapping;

// Shared helpers used across submodules

pub(super) fn make_parser<'a>(
    solver: &'a mut Solver,
    variables: &'a std::collections::HashMap<String, Term>,
    collection_lengths: &'a mut std::collections::HashMap<String, Term>,
    var_types: &'a std::collections::HashMap<String, crate::ir::TrustVcType>,
    functions: &'a std::collections::HashMap<String, FuncDecl>,
) -> AstExpressionParser<'a> {
    AstExpressionParser::new(solver, variables, collection_lengths, var_types, functions)
}

pub(super) fn make_parser_with_overflow<'a>(
    solver: &'a mut Solver,
    variables: &'a std::collections::HashMap<String, Term>,
    collection_lengths: &'a mut std::collections::HashMap<String, Term>,
    var_types: &'a std::collections::HashMap<String, crate::ir::TrustVcType>,
    functions: &'a std::collections::HashMap<String, FuncDecl>,
) -> AstExpressionParser<'a> {
    AstExpressionParser::with_overflow_checking(
        solver,
        variables,
        collection_lengths,
        var_types,
        functions,
        true,
    )
}

pub(super) fn signed_var(name: &str) -> crate::ir_expr::TrustVcExpr {
    crate::ir_expr::TrustVcExpr::Var {
        name: name.to_string(),
        ty: crate::ir::TrustVcType::Int { width: 32 },
    }
}

pub(super) fn signed_lit(value: i128) -> crate::ir_expr::TrustVcExpr {
    crate::ir_expr::TrustVcExpr::IntLit {
        value,
        ty: crate::ir::TrustVcType::Int { width: 32 },
    }
}

pub(super) fn signed_div_expr(
    left: crate::ir_expr::TrustVcExpr,
    right: crate::ir_expr::TrustVcExpr,
) -> crate::ir_expr::TrustVcExpr {
    crate::ir_expr::TrustVcExpr::Arith {
        op: crate::ir::ArithOp::Div,
        left: Box::new(left),
        right: Box::new(right),
        ty: crate::ir::TrustVcType::Int { width: 32 },
    }
}

pub(super) fn signed_rem_expr(
    left: crate::ir_expr::TrustVcExpr,
    right: crate::ir_expr::TrustVcExpr,
) -> crate::ir_expr::TrustVcExpr {
    crate::ir_expr::TrustVcExpr::Arith {
        op: crate::ir::ArithOp::Rem,
        left: Box::new(left),
        right: Box::new(right),
        ty: crate::ir::TrustVcType::Int { width: 32 },
    }
}

pub(super) fn typed_var(name: &str, ty: crate::ir::TrustVcType) -> crate::ir_expr::TrustVcExpr {
    crate::ir_expr::TrustVcExpr::Var {
        name: name.to_string(),
        ty,
    }
}

pub(super) fn typed_div_expr(
    left: crate::ir_expr::TrustVcExpr,
    right: crate::ir_expr::TrustVcExpr,
    ty: crate::ir::TrustVcType,
) -> crate::ir_expr::TrustVcExpr {
    crate::ir_expr::TrustVcExpr::Arith {
        op: crate::ir::ArithOp::Div,
        left: Box::new(left),
        right: Box::new(right),
        ty,
    }
}

pub(super) fn typed_rem_expr(
    left: crate::ir_expr::TrustVcExpr,
    right: crate::ir_expr::TrustVcExpr,
    ty: crate::ir::TrustVcType,
) -> crate::ir_expr::TrustVcExpr {
    crate::ir_expr::TrustVcExpr::Arith {
        op: crate::ir::ArithOp::Rem,
        left: Box::new(left),
        right: Box::new(right),
        ty,
    }
}
