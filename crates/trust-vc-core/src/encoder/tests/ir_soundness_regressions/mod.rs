//! IR encoder soundness regressions split by issue cluster.
//!
//! Split from monolithic `ir_soundness_regressions.rs` (1,557 lines) into
//! smaller domain modules for maintainability (#2145).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

use std::borrow::Cow;

use crate::ir::{ArithOp, CompareOp, LogicOp, TrustVcType, WrappingMode};
use crate::ir_expr::{MatchArm, MatchPattern, QuantifierKind, TrustVcExpr};

struct QuantifierTestEnv {
    solver: Solver,
    variables: std::collections::HashMap<String, Term>,
    collection_lengths: std::collections::HashMap<String, Term>,
    var_types: std::collections::HashMap<String, TrustVcType>,
    functions: std::collections::HashMap<String, FuncDecl>,
}

impl QuantifierTestEnv {
    /// Empty environment — quantifier-bound vars are declared inline.
    fn new() -> Self {
        QuantifierTestEnv {
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

fn assert_overflow_checks_hold_under(
    solver: &mut Solver,
    checks: &[(Cow<'static, str>, Term)],
    constraint: Term,
    label: &str,
) {
    solver.try_push().unwrap();
    solver.try_assert_term(constraint).unwrap();
    for (name, pred) in checks {
        solver.try_push().unwrap();
        let neg = solver.try_not(*pred).unwrap();
        solver.try_assert_term(neg).unwrap();
        let sat = solver.try_check_sat().unwrap();
        solver.try_pop().unwrap();
        assert!(
            !sat.is_sat(),
            "#2107 {}: '{}' falsifiable — guard missing",
            label,
            name
        );
    }
    solver.try_pop().unwrap();
}

mod arith_in_quantifier;
mod bv_not_fallback;
mod chained_ops;
mod compare_int_arith_leak_tests;
mod compare_signedness_soundness;
mod const_eval_typed;
mod exists_quantifier;
mod ite_overflow_guards;
mod match_int_arith_leak;
mod match_semantics;
mod match_term_widths;
mod neg_wrap_context;
mod place_int_arith_leak;
mod promoted_compare_scope;
mod short_circuit_guards;
mod width_and_signedness;
