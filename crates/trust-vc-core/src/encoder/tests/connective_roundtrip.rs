// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! End-to-end verifier round-trips for the Verus boolean connectives `==>`,
//! `<==`, and `<==>`: parse the upstream surface syntax, lower it to IR, encode
//! it to a solver term, and check validity by asserting the *negation* and
//! querying SAT.
//!
//!   - UNSAT(¬formula)  =>  the formula is valid (should-verify).
//!   - SAT(¬formula)    =>  the formula has a counterexample (should-fail).
//!
//! This exercises the full sound-rewrite path (`<==` → reversed `Implies`,
//! `<==>` → `(P ==> Q) && (Q ==> P)`) the way `assert_by_bit_vector!` does, so a
//! regression in the macro/IR lowering surfaces here as a wrong verdict — not
//! just a structural mismatch.

use super::*;

use crate::chained_comparisons::parse_expr_str_with_chains;
use crate::ir::TrustVcType;

/// Owns the solver and symbol tables for a single connective round-trip.
struct ConnectiveTestEnv {
    solver: Solver,
    variables: std::collections::HashMap<String, Term>,
    collection_lengths: std::collections::HashMap<String, Term>,
    var_types: std::collections::HashMap<String, TrustVcType>,
    functions: std::collections::HashMap<String, FuncDecl>,
}

impl ConnectiveTestEnv {
    fn new(vars: &[(&str, TrustVcType)]) -> Self {
        let mut env = ConnectiveTestEnv {
            solver: Solver::try_new(ay_dpll::api::Logic::All).unwrap(),
            variables: std::collections::HashMap::new(),
            collection_lengths: std::collections::HashMap::new(),
            var_types: std::collections::HashMap::new(),
            functions: std::collections::HashMap::new(),
        };
        for (name, ty) in vars {
            let sort = crate::encoder::types::sort_for_type(ty);
            let term = env.solver.declare_const(name, sort);
            env.variables.insert((*name).to_string(), term);
            env.var_types.insert((*name).to_string(), ty.clone());
        }
        env
    }

    /// Build the typing environment used to lower the Verus-surface string.
    fn type_env(&self) -> crate::ir_lowering::TypeEnv {
        let mut env = crate::ir_lowering::TypeEnv::new();
        for (name, ty) in &self.var_types {
            env.insert(name.clone(), ty.clone());
        }
        env
    }

    /// Parse + lower + encode `src` to a Bool term.
    fn encode(&mut self, src: &str) -> Term {
        let type_env = self.type_env();
        let syn_expr =
            parse_expr_str_with_chains(src).unwrap_or_else(|err| panic!("parse `{src}`: {err}"));
        let ir = crate::ir_lowering::lower_syn_expr(&syn_expr, &type_env)
            .unwrap_or_else(|err| panic!("lower `{src}`: {err:?}"));
        let mut parser = AstExpressionParser::new(
            &mut self.solver,
            &self.variables,
            &mut self.collection_lengths,
            &self.var_types,
            &self.functions,
        );
        parser
            .encode_trust_vc_expr(&ir)
            .unwrap_or_else(|err| panic!("encode `{src}`: {err:?}"))
    }

    /// Returns true iff `src` encodes to a *valid* boolean formula
    /// (i.e. its negation is UNSAT).
    fn is_valid(&mut self, src: &str) -> bool {
        let term = self.encode(src);
        let negated = self.solver.try_not(term).unwrap();
        self.solver.try_assert_term(negated).unwrap();
        self.solver.try_check_sat().unwrap().is_unsat()
    }
}

fn bool_env() -> ConnectiveTestEnv {
    ConnectiveTestEnv::new(&[("p", TrustVcType::Bool), ("q", TrustVcType::Bool)])
}

// ---- should-verify (valid) ----

#[test]
fn forward_implies_from_conjunction_is_valid() {
    // `(p && q) ==> p` is a tautology.
    assert!(
        bool_env().is_valid("(p && q) ==> p"),
        "`(p && q) ==> p` must verify"
    );
}

#[test]
fn reverse_implies_to_conjunction_is_valid() {
    // `p <== (p && q)` is `(p && q) ==> p`, a tautology.
    assert!(
        bool_env().is_valid("p <== (p && q)"),
        "`p <== (p && q)` must verify"
    );
}

#[test]
fn iff_reflexive_is_valid() {
    // `p <==> p` is a tautology.
    assert!(bool_env().is_valid("p <==> p"), "`p <==> p` must verify");
}

#[test]
fn iff_contrapositive_is_valid() {
    // `(p ==> q) <==> (!q ==> !p)` — contrapositive equivalence, valid.
    assert!(
        bool_env().is_valid("(p ==> q) <==> (!q ==> !p)"),
        "contrapositive equivalence must verify"
    );
}

#[test]
fn iff_and_double_implication_agree_is_valid() {
    // `(p <==> q) <==> ((p ==> q) && (q ==> p))` — the expansion is the
    // definition, so this is valid. Guards that the `<==>` rewrite matches the
    // hand-written `&&` of implications.
    assert!(
        bool_env().is_valid("(p <==> q) <==> ((p ==> q) && (q ==> p))"),
        "`<==>` must be equivalent to its hand-expanded form"
    );
}

// ---- should-fail (counterexample) ----

#[test]
fn iff_of_distinct_vars_is_not_valid() {
    // `p <==> q` is false when p=true, q=false: must NOT verify.
    assert!(
        !bool_env().is_valid("p <==> q"),
        "`p <==> q` must have a counterexample"
    );
}

#[test]
fn reverse_implies_of_distinct_vars_is_not_valid() {
    // `p <== q` is `q ==> p`, false when q=true, p=false: must NOT verify.
    assert!(
        !bool_env().is_valid("p <== q"),
        "`p <== q` must have a counterexample"
    );
}

#[test]
fn forward_implies_of_distinct_vars_is_not_valid() {
    // `p ==> q` is false when p=true, q=false: must NOT verify.
    assert!(
        !bool_env().is_valid("p ==> q"),
        "`p ==> q` must have a counterexample"
    );
}

#[test]
fn iff_swapped_direction_is_not_equivalent_to_single_implication() {
    // `(p <==> q) <==> (p ==> q)` is NOT valid: when p=false, q=true the LHS is
    // false but `p ==> q` is true, so the biconditional fails. This pins that
    // `<==>` is the *full* biconditional, not a one-directional implication.
    assert!(
        !bool_env().is_valid("(p <==> q) <==> (p ==> q)"),
        "`<==>` must not collapse to a single implication"
    );
}

// ---- bit-vector-typed connectives (cluster #2778 shape) ----

fn u32_env() -> ConnectiveTestEnv {
    ConnectiveTestEnv::new(&[
        ("x", TrustVcType::Uint { width: 32 }),
        ("y", TrustVcType::Uint { width: 32 }),
    ])
}

#[test]
fn iff_over_bitvector_zero_extend_order_is_valid() {
    // Mirrors the upstream `a < b <==> (a as i64) < b` shape (test_eq_ineq2):
    // zero-extending both u32 operands to u64 preserves the strict order, so the
    // biconditional is valid. Exercises `<==>` over bit-vector comparisons.
    assert!(
        u32_env().is_valid("(x < y) <==> ((x as u64) < (y as u64))"),
        "u32<u32 must be equivalent to its zero-extended u64 comparison"
    );
}

#[test]
fn reverse_implies_over_bitvector_order_is_valid() {
    // `(x < y) <== ((x as u64) < (y as u64))` is `(u64 lt) ==> (u32 lt)`, valid
    // because zero-extension is order-preserving in both directions.
    assert!(
        u32_env().is_valid("(x < y) <== ((x as u64) < (y as u64))"),
        "reverse implication over zero-extended comparison must verify"
    );
}

#[test]
fn iff_over_bitvector_wrong_extension_is_not_valid() {
    // Truncating u32 down to u8 does NOT preserve order, so the biconditional
    // `(x < y) <==> ((x as u8) < (y as u8))` has a counterexample
    // (e.g. x = 0x100, y = 0x001: u32 says 0x100 > 1, u8 says 0 < 1).
    assert!(
        !u32_env().is_valid("(x < y) <==> ((x as u8) < (y as u8))"),
        "u32 order must NOT match the truncated u8 comparison"
    );
}
