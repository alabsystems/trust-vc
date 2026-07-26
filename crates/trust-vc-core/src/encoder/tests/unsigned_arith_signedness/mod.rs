//! Unsigned arithmetic signedness discrimination tests (#2070).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! These tests catch the bug where `encode_arith` uses
//! `operands_are_unsigned(term_widths)` instead of the IR-level TrustVcType
//! to determine signedness. For unsigned division/remainder, this causes
//! `bvsdiv`/`bvsrem` to be selected instead of `bvudiv`/`bvurem`.
//!
//! Key insight: for u32 values with the high bit set (>= 2^31),
//! signed and unsigned division give different results because signed
//! interpretation treats them as negative.
//!
//! Original monolith (668 lines, 10 tests) split for maintainability (#2145).

use super::*;

mod explicit_unsigned;
mod unsuffixed_literal;

pub(super) fn unsigned_var(name: &str) -> crate::ir_expr::TrustVcExpr {
    crate::ir_expr::TrustVcExpr::Var {
        name: name.to_string(),
        ty: crate::ir::TrustVcType::Uint { width: 32 },
    }
}

pub(super) fn unsigned_lit(value: i128) -> crate::ir_expr::TrustVcExpr {
    crate::ir_expr::TrustVcExpr::IntLit {
        value,
        ty: crate::ir::TrustVcType::Uint { width: 32 },
    }
}

pub(super) fn unsigned_div_expr(
    left: crate::ir_expr::TrustVcExpr,
    right: crate::ir_expr::TrustVcExpr,
) -> crate::ir_expr::TrustVcExpr {
    crate::ir_expr::TrustVcExpr::Arith {
        op: crate::ir::ArithOp::Div,
        left: Box::new(left),
        right: Box::new(right),
        ty: crate::ir::TrustVcType::Uint { width: 32 },
    }
}

pub(super) fn unsigned_rem_expr(
    left: crate::ir_expr::TrustVcExpr,
    right: crate::ir_expr::TrustVcExpr,
) -> crate::ir_expr::TrustVcExpr {
    crate::ir_expr::TrustVcExpr::Arith {
        op: crate::ir::ArithOp::Rem,
        left: Box::new(left),
        right: Box::new(right),
        ty: crate::ir::TrustVcType::Uint { width: 32 },
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

pub(super) fn make_unsigned_parser<'a>(
    solver: &'a mut Solver,
    variables: &'a std::collections::HashMap<String, Term>,
    collection_lengths: &'a mut std::collections::HashMap<String, Term>,
    var_types: &'a std::collections::HashMap<String, crate::ir::TrustVcType>,
    functions: &'a std::collections::HashMap<String, FuncDecl>,
) -> AstExpressionParser<'a> {
    AstExpressionParser::new(solver, variables, collection_lengths, var_types, functions)
}

pub(super) fn make_unsigned_parser_with_overflow<'a>(
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
