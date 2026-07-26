//! Regression tests for #2100: FnCall/checked/saturating width metadata.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Tests verify that:
//! - encode_fn_call tracks return_ty in term_widths (#2100a)
//! - encode_wrapping_arith derives semantics from WrappingArith ty (#2100b)
//! - Checked arithmetic uses unsigned semantics for unsigned types
//! - Saturating arithmetic clamps correctly even with missing metadata
//!
//! Original monolith (524 lines + 183 line sub-module, 10 tests) split
//! for maintainability (#2145).

use super::*;

use crate::ir::{ArithOp, TrustVcType, WrappingMode};
use crate::ir_expr::TrustVcExpr;
use crate::ir_lowering::{lower_syn_expr, TypeEnv};

mod fncall_width;
mod ty_fallback;

pub(super) struct QuantifierTestEnv {
    pub(super) solver: Solver,
    pub(super) variables: std::collections::HashMap<String, Term>,
    pub(super) collection_lengths: std::collections::HashMap<String, Term>,
    pub(super) var_types: std::collections::HashMap<String, TrustVcType>,
    pub(super) functions: std::collections::HashMap<String, FuncDecl>,
}

impl QuantifierTestEnv {
    pub(super) fn new() -> Self {
        QuantifierTestEnv {
            solver: Solver::try_new(Logic::All).unwrap(),
            variables: std::collections::HashMap::new(),
            collection_lengths: std::collections::HashMap::new(),
            var_types: std::collections::HashMap::new(),
            functions: std::collections::HashMap::new(),
        }
    }

    pub(super) fn parser(&mut self) -> AstExpressionParser<'_> {
        AstExpressionParser::new(
            &mut self.solver,
            &self.variables,
            &mut self.collection_lengths,
            &self.var_types,
            &self.functions,
        )
    }

    pub(super) fn parser_with_overflow(&mut self) -> AstExpressionParser<'_> {
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
