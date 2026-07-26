//! Coverage tests for `cast.rs` integer cast and int-to-bool paths.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Covers cast_int_to_bool, cast_int_to_int (widening, narrowing,
//! same-width, int-mode wrapping), and error paths that had zero coverage.

use super::*;

use crate::ir::TrustVcType;
use crate::ir_expr::TrustVcExpr;

fn int_var(name: &str, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.into(),
        ty,
    }
}

struct CastEnv {
    solver: Solver,
    x: Term,
    variables: std::collections::HashMap<String, Term>,
    var_types: std::collections::HashMap<String, TrustVcType>,
    collection_lengths: std::collections::HashMap<String, Term>,
    functions: std::collections::HashMap<String, FuncDecl>,
}

impl CastEnv {
    fn bv(name: &str, sort: Sort, ty: TrustVcType) -> Self {
        let mut solver = Solver::try_new(Logic::All).unwrap();
        let x = solver.declare_const(name, sort);
        let mut variables = std::collections::HashMap::new();
        variables.insert(name.into(), x);
        let mut var_types = std::collections::HashMap::new();
        var_types.insert(name.into(), ty);
        CastEnv {
            solver,
            x,
            variables,
            var_types,
            collection_lengths: std::collections::HashMap::new(),
            functions: std::collections::HashMap::new(),
        }
    }

    fn encode_cast_bv(
        &mut self,
        from_ty: TrustVcType,
        to_ty: TrustVcType,
        width: u32,
        signed: bool,
    ) -> Term {
        let expr = TrustVcExpr::Cast {
            expr: Box::new(int_var("x", from_ty.clone())),
            from_ty,
            to_ty,
        };
        let mut parser = AstExpressionParser::new(
            &mut self.solver,
            &self.variables,
            &mut self.collection_lengths,
            &self.var_types,
            &self.functions,
        );
        parser.use_int_arithmetic = false;
        parser.term_widths.insert(self.x, (width, signed));
        let term = parser
            .encode_trust_vc_expr(&expr)
            .expect("cast should encode");
        drop(parser);
        term
    }

    fn encode_cast_int_mode(&mut self, from_ty: TrustVcType, to_ty: TrustVcType) -> Term {
        let expr = TrustVcExpr::Cast {
            expr: Box::new(int_var("x", from_ty.clone())),
            from_ty,
            to_ty,
        };
        let mut parser = AstExpressionParser::new(
            &mut self.solver,
            &self.variables,
            &mut self.collection_lengths,
            &self.var_types,
            &self.functions,
        );
        parser.quantifier_depth = 1;
        let term = parser
            .encode_trust_vc_expr(&expr)
            .expect("cast should encode");
        drop(parser);
        term
    }

    /// Assert x == input ∧ ¬(cast == expected) is unsat.
    fn assert_bv_maps_to(
        &mut self,
        cast: Term,
        input: i64,
        expected: i64,
        w_in: u32,
        w_out: u32,
        label: &str,
    ) {
        self.solver.try_push().unwrap();
        let in_term = self.solver.try_bv_const(input, w_in).unwrap();
        let exp_term = self.solver.try_bv_const(expected, w_out).unwrap();
        let x_eq = self.solver.try_eq(self.x, in_term).unwrap();
        let c_eq = self.solver.try_eq(cast, exp_term).unwrap();
        let neg = self.solver.try_not(c_eq).unwrap();
        self.solver.try_assert_term(x_eq).unwrap();
        self.solver.try_assert_term(neg).unwrap();
        let sat = self.solver.try_check_sat().unwrap();
        self.solver.try_pop().unwrap();
        assert!(sat.is_unsat(), "{label}: got {sat:?}");
    }

    fn assert_int_maps_to(&mut self, cast: Term, input: i64, expected: i64, label: &str) {
        self.solver.try_push().unwrap();
        let in_term = self.solver.int_const(input);
        let exp_term = self.solver.int_const(expected);
        let x_eq = self.solver.try_eq(self.x, in_term).unwrap();
        let c_eq = self.solver.try_eq(cast, exp_term).unwrap();
        let neg = self.solver.try_not(c_eq).unwrap();
        self.solver.try_assert_term(x_eq).unwrap();
        self.solver.try_assert_term(neg).unwrap();
        let sat = self.solver.try_check_sat().unwrap();
        self.solver.try_pop().unwrap();
        assert!(sat.is_unsat(), "{label}: got {sat:?}");
    }

    /// Assert x == input → cast_term holds (bool true).
    fn assert_bv_bool_true(&mut self, cast: Term, input: i64, w: u32, label: &str) {
        self.solver.try_push().unwrap();
        let in_term = self.solver.try_bv_const(input, w).unwrap();
        let x_eq = self.solver.try_eq(self.x, in_term).unwrap();
        let neg = self.solver.try_not(cast).unwrap();
        self.solver.try_assert_term(x_eq).unwrap();
        self.solver.try_assert_term(neg).unwrap();
        let sat = self.solver.try_check_sat().unwrap();
        self.solver.try_pop().unwrap();
        assert!(sat.is_unsat(), "{label}: got {sat:?}");
    }

    /// Assert x == input → ¬cast_term (bool false).
    fn assert_bv_bool_false(&mut self, cast: Term, input: i64, w: u32, label: &str) {
        self.solver.try_push().unwrap();
        let in_term = self.solver.try_bv_const(input, w).unwrap();
        let x_eq = self.solver.try_eq(self.x, in_term).unwrap();
        self.solver.try_assert_term(x_eq).unwrap();
        self.solver.try_assert_term(cast).unwrap();
        let sat = self.solver.try_check_sat().unwrap();
        self.solver.try_pop().unwrap();
        assert!(sat.is_unsat(), "{label}: got {sat:?}");
    }
}

// ========================================================================
// cast_int_to_bool — BV mode
// ========================================================================

/// DISCRIMINATING: u32 → Bool in BV mode. Nonzero=true, zero=false.
#[test]
fn test_cast_int_to_bool_bv_mode() {
    let mut env = CastEnv::bv("x", Sort::bitvec(32), TrustVcType::Uint { width: 32 });
    let cast = env.encode_cast_bv(
        TrustVcType::Uint { width: 32 },
        TrustVcType::Bool,
        32,
        false,
    );
    env.assert_bv_bool_true(cast, 5, 32, "nonzero (5) → true");
    env.assert_bv_bool_false(cast, 0, 32, "zero → false");
}

// ========================================================================
// cast_int_to_bool — Int mode
// ========================================================================

/// DISCRIMINATING: i32 → Bool in Int mode. Nonzero=true, zero=false.
#[test]
fn test_cast_int_to_bool_int_mode() {
    let mut env = CastEnv::bv("x", Sort::Int, TrustVcType::Int { width: 32 });
    let cast = env.encode_cast_int_mode(TrustVcType::Int { width: 32 }, TrustVcType::Bool);
    // Nonzero → true
    env.solver.try_push().unwrap();
    let v42 = env.solver.int_const(42);
    let x_eq = env.solver.try_eq(env.x, v42).unwrap();
    let neg = env.solver.try_not(cast).unwrap();
    env.solver.try_assert_term(x_eq).unwrap();
    env.solver.try_assert_term(neg).unwrap();
    let sat = env.solver.try_check_sat().unwrap();
    env.solver.try_pop().unwrap();
    assert!(sat.is_unsat(), "int mode: 42 → true: {sat:?}");

    // Zero → false
    env.solver.try_push().unwrap();
    let v0 = env.solver.int_const(0);
    let x_eq0 = env.solver.try_eq(env.x, v0).unwrap();
    env.solver.try_assert_term(x_eq0).unwrap();
    env.solver.try_assert_term(cast).unwrap();
    let sat = env.solver.try_check_sat().unwrap();
    env.solver.try_pop().unwrap();
    assert!(sat.is_unsat(), "int mode: 0 → false: {sat:?}");
}

// ========================================================================
// finite integer -> mathematical int
// ========================================================================

/// unsigned finite integer casts to mathematical int produce an Int-sorted
/// term. The executable Set corpus test covers the `Set::len() as int >= 0`
/// proof path that motivated this bridge.
#[test]
fn test_cast_uint_to_math_int_encodes_int_sort() {
    let mut env = CastEnv::bv("x", Sort::bitvec(8), TrustVcType::Uint { width: 8 });
    let cast = env.encode_cast_bv(
        TrustVcType::Uint { width: 8 },
        TrustVcType::MathInt,
        8,
        false,
    );
    assert_eq!(env.solver.term_sort(cast), Sort::Int);
}

/// signed finite integer casts to mathematical int also produce an Int-sorted
/// term rather than falling through to finite-width cast handling.
#[test]
fn test_cast_int_to_math_int_encodes_int_sort() {
    let mut env = CastEnv::bv("x", Sort::bitvec(8), TrustVcType::Int { width: 8 });
    let cast = env.encode_cast_bv(TrustVcType::Int { width: 8 }, TrustVcType::MathInt, 8, true);
    assert_eq!(env.solver.term_sort(cast), Sort::Int);
}

// ========================================================================
// cast_int_to_int — widening
// ========================================================================

/// DISCRIMINATING: u8 → u32 zero-extends. 200 stays 200 (not sign-extended to -56).
#[test]
fn test_cast_int_widen_zero_extend_unsigned() {
    let mut env = CastEnv::bv("x", Sort::bitvec(8), TrustVcType::Uint { width: 8 });
    let cast = env.encode_cast_bv(
        TrustVcType::Uint { width: 8 },
        TrustVcType::Uint { width: 32 },
        8,
        false,
    );
    env.assert_bv_maps_to(cast, 200, 200, 8, 32, "u8→u32 zero-extend: 200→200");
}

/// DISCRIMINATING: i8 → i32 sign-extends. -56 (0xC8) stays -56.
#[test]
fn test_cast_int_widen_sign_extend_signed() {
    let mut env = CastEnv::bv("x", Sort::bitvec(8), TrustVcType::Int { width: 8 });
    let cast = env.encode_cast_bv(
        TrustVcType::Int { width: 8 },
        TrustVcType::Int { width: 32 },
        8,
        true,
    );
    env.assert_bv_maps_to(cast, -56, -56, 8, 32, "i8→i32 sign-extend: -56→-56");
}

// ========================================================================
// cast_int_to_int — narrowing
// ========================================================================

/// DISCRIMINATING: i32 → u8 extracts low 8 bits.
#[test]
fn test_cast_int_narrow_extracts_low_bits() {
    let mut env = CastEnv::bv("x", Sort::bitvec(32), TrustVcType::Int { width: 32 });
    let cast = env.encode_cast_bv(
        TrustVcType::Int { width: 32 },
        TrustVcType::Uint { width: 8 },
        32,
        true,
    );
    env.assert_bv_maps_to(cast, 0x1234_0056, 0x56, 32, 8, "i32→u8: low bits");
}

// ========================================================================
// cast_int_to_int — same-width
// ========================================================================

/// DISCRIMINATING: i32 → u32 reinterprets signedness via a FRESH, bit-identical
/// term carrying the new signedness — it must NOT clobber the source variable's
/// tracked signedness (which would later trip `encode_var`'s metadata guard and
/// fail-close `by(bit_vector)` cast cases; see
/// `bv_signedness_reinterpret_cast`).
#[test]
fn test_cast_int_same_width_signedness_reinterpret() {
    let mut env = CastEnv::bv("x", Sort::bitvec(32), TrustVcType::Int { width: 32 });
    let expr = TrustVcExpr::Cast {
        expr: Box::new(int_var("x", TrustVcType::Int { width: 32 })),
        from_ty: TrustVcType::Int { width: 32 },
        to_ty: TrustVcType::Uint { width: 32 },
    };
    let mut parser = AstExpressionParser::new(
        &mut env.solver,
        &env.variables,
        &mut env.collection_lengths,
        &env.var_types,
        &env.functions,
    );
    parser.use_int_arithmetic = false;
    parser.term_widths.insert(env.x, (32, true));
    let cast = parser.encode_trust_vc_expr(&expr).expect("same-width cast");
    let cast_info = parser.term_widths.get(&cast).copied();
    let source_info = parser.term_widths.get(&env.x).copied();
    drop(parser);

    assert_ne!(
        cast, env.x,
        "reinterpret returns a fresh term, not the clobbered source"
    );
    assert_eq!(
        cast_info,
        Some((32, false)),
        "cast result is tracked unsigned"
    );
    assert_eq!(
        source_info,
        Some((32, true)),
        "source variable keeps its signed metadata (no clobber)"
    );

    // The fresh term is bit-identical to the source: `cast != x` is unsat.
    env.solver.try_push().unwrap();
    let c_eq = env.solver.try_eq(cast, env.x).unwrap();
    let neg = env.solver.try_not(c_eq).unwrap();
    env.solver.try_assert_term(neg).unwrap();
    let sat = env.solver.try_check_sat().unwrap();
    env.solver.try_pop().unwrap();
    assert!(
        sat.is_unsat(),
        "reinterpret preserves the bit pattern (cast == x): {sat:?}"
    );
}

// ========================================================================
// cast_int_to_int — int mode wrapping
// ========================================================================

/// DISCRIMINATING: u8 → i32 in int mode wraps via wrap_int_to_explicit_range.
#[test]
fn test_cast_int_to_int_int_mode_wraps() {
    let mut env = CastEnv::bv("x", Sort::Int, TrustVcType::Uint { width: 8 });
    let cast = env.encode_cast_int_mode(
        TrustVcType::Uint { width: 8 },
        TrustVcType::Int { width: 32 },
    );
    env.assert_int_maps_to(cast, 100, 100, "int mode u8→i32: 100→100");
}

// ========================================================================
// cast error paths
// ========================================================================

/// DISCRIMINATING: Bool → Seq<i32> is unsupported — must error.
#[test]
fn test_cast_unsupported_types_returns_error() {
    let mut env = CastEnv::bv("b", Sort::Bool, TrustVcType::Bool);
    let expr = TrustVcExpr::Cast {
        expr: Box::new(int_var("b", TrustVcType::Bool)),
        from_ty: TrustVcType::Bool,
        to_ty: TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
    };
    let mut parser = AstExpressionParser::new(
        &mut env.solver,
        &env.variables,
        &mut env.collection_lengths,
        &env.var_types,
        &env.functions,
    );
    let result = parser.encode_trust_vc_expr(&expr);
    assert!(result.is_err(), "Bool→Seq should error: {result:?}");
    assert!(
        result.unwrap_err().to_string().contains("unsupported cast"),
        "error should mention unsupported cast"
    );
}

/// DISCRIMINATING: Seq<i32> → i32 is unsupported — must error.
#[test]
fn test_cast_non_integer_from_type_returns_error() {
    let seq_ty = TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }));
    let mut env = CastEnv::bv("x", Sort::Int, seq_ty.clone());
    let expr = TrustVcExpr::Cast {
        expr: Box::new(int_var("x", seq_ty.clone())),
        from_ty: seq_ty,
        to_ty: TrustVcType::Int { width: 32 },
    };
    let mut parser = AstExpressionParser::new(
        &mut env.solver,
        &env.variables,
        &mut env.collection_lengths,
        &env.var_types,
        &env.functions,
    );
    let result = parser.encode_trust_vc_expr(&expr);
    assert!(result.is_err(), "Seq→i32 should error: {result:?}");
}
