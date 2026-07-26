//! FnCall return type width metadata and checked/saturating with FnCall tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from ir_soundness_2100/mod.rs (#2145).

use super::*;

// ========================================================================
// #2100 regression: FnCall results must carry width metadata for overflow
// ========================================================================
//
// Before the fix, encode_fn_call ignored return_ty and did not insert
// term_widths metadata. When two FnCall results were used as operands to
// checked/saturating arithmetic, coerced_width_info was None:
// - Checked defaulted to is_signed=true (wrong for unsigned types)
// - Saturating returned the raw result without clamping (no width available)
//
// Fix: (a) encode_fn_call now tracks return_ty in term_widths,
//      (b) encode_wrapping_arith derives semantics from the WrappingArith
//          node's ty field as primary source.

/// DISCRIMINATING: FnCall encoding must register `return_ty` width metadata.
/// Without this, downstream width coercion for mixed-width operands can fail.
#[test]
fn test_2100_fncall_tracks_return_type_width_info() {
    let mut env = QuantifierTestEnv::new();
    let f_decl = env
        .solver
        .try_declare_fun("f", &[], Sort::bitvec(8))
        .expect("declare f");
    env.functions.insert("f".to_string(), f_decl);

    let mut parser = env.parser();
    let call = TrustVcExpr::FnCall {
        name: "f".to_string(),
        args: vec![],
        return_ty: TrustVcType::Uint { width: 8 },
    };
    let call_term = parser
        .encode_trust_vc_expr(&call)
        .expect("#2100: FnCall encoding should succeed");
    let width_info = parser.term_widths.get(&call_term).copied();
    assert_eq!(
        width_info,
        Some((8, false)),
        "#2100: FnCall return_ty metadata missing/wrong, got: {:?}",
        width_info
    );
}

/// DISCRIMINATING: end-to-end return type propagation must preserve u8
/// metadata from TypeEnv -> lowered FnCall.return_ty -> encoder term_widths.
#[test]
fn test_2100_fncall_return_type_propagates_end_to_end_from_type_env() {
    let mut env = QuantifierTestEnv::new();
    let f_decl = env
        .solver
        .try_declare_fun("f", &[], Sort::bitvec(8))
        .expect("declare f");
    env.functions.insert("f".to_string(), f_decl);

    let mut type_env = TypeEnv::new();
    type_env.insert_fn("f".to_string(), TrustVcType::Uint { width: 8 });

    let expr: syn::Expr = syn::parse_str("f()").expect("parse f()");
    let lowered = lower_syn_expr(&expr, &type_env)
        .expect("#2100: lowering should use TypeEnv return type for f()");

    match &lowered {
        TrustVcExpr::FnCall {
            name, return_ty, ..
        } => {
            assert_eq!(name, "f");
            assert_eq!(*return_ty, TrustVcType::Uint { width: 8 });
        }
        other => panic!("#2100: expected lowered FnCall, got {:?}", other),
    }

    let mut parser = env.parser();
    let call_term = parser
        .encode_trust_vc_expr(&lowered)
        .expect("#2100: encoding lowered FnCall should succeed");
    let width_info = parser.term_widths.get(&call_term).copied();
    assert_eq!(
        width_info,
        Some((8, false)),
        "#2100: end-to-end return type metadata missing/wrong, got: {:?}",
        width_info
    );
}

/// DISCRIMINATING: checked_add on two u8 FnCall results must use unsigned
/// overflow semantics (bvadd_no_overflow with is_signed=false), not the
/// signed default.
///
/// Pre-fix: coerced_width_info was None for FnCall terms, so is_signed
/// defaulted to true — emitting signed overflow checks for unsigned types.
#[test]
fn test_2100_checked_add_fncall_unsigned_semantics() {
    let mut env = QuantifierTestEnv::new();

    // Declare two uninterpreted functions: f() -> u8, g() -> u8
    let f_decl = env
        .solver
        .try_declare_fun("f", &[], Sort::bitvec(8))
        .expect("declare f");
    let g_decl = env
        .solver
        .try_declare_fun("g", &[], Sort::bitvec(8))
        .expect("declare g");
    env.functions.insert("f".to_string(), f_decl);
    env.functions.insert("g".to_string(), g_decl);

    let mut parser = env.parser_with_overflow();

    // checked_add(f(), g()) with ty=Uint{8}
    let expr = TrustVcExpr::WrappingArith {
        mode: WrappingMode::Checked,
        op: ArithOp::Add,
        left: Box::new(TrustVcExpr::FnCall {
            name: "f".to_string(),
            args: vec![],
            return_ty: TrustVcType::Uint { width: 8 },
        }),
        right: Box::new(TrustVcExpr::FnCall {
            name: "g".to_string(),
            args: vec![],
            return_ty: TrustVcType::Uint { width: 8 },
        }),
        ty: TrustVcType::Uint { width: 8 },
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2100: checked_add on FnCall results must not fail: {:?}",
        result.err()
    );

    // Must emit overflow check (unsigned: no underflow check for unsigned add)
    let checks = std::mem::take(&mut parser.overflow_checks);
    assert!(
        checks.iter().any(|(name, _)| name.contains("checked_add")),
        "#2100: checked_add must emit overflow check, got: {:?}",
        checks.iter().map(|(n, _)| n.as_ref()).collect::<Vec<_>>()
    );

    // Unsigned checked_add should NOT emit underflow check (only signed does).
    // If is_signed defaulted to true (the bug), an underflow check would appear.
    let has_underflow = checks.iter().any(|(name, _)| name.contains("underflow"));
    assert!(
        !has_underflow,
        "#2100 SOUNDNESS: unsigned checked_add emitted underflow check — \
         indicates is_signed defaulted to true (the pre-fix bug). Got: {:?}",
        checks.iter().map(|(n, _)| n.as_ref()).collect::<Vec<_>>()
    );
}

/// DISCRIMINATING: saturating_add on two u8 FnCall results must clamp to
/// [0, 255], not return raw BV result.
///
/// Pre-fix: coerced_width_info was None, so the saturating path returned
/// the raw result without clamping — effectively treating saturating_add
/// as wrapping_add.
#[test]
fn test_2100_saturating_add_fncall_clamps_correctly() {
    let mut env = QuantifierTestEnv::new();

    // Declare f() -> u8
    let u8_sort = Sort::bitvec(8);
    let f_decl = env
        .solver
        .try_declare_fun("f", &[], u8_sort)
        .expect("declare f");
    env.functions.insert("f".to_string(), f_decl.clone());

    let mut parser = env.parser();

    // saturating_add(f(), 1u8) with ty=Uint{8}
    let expr = TrustVcExpr::WrappingArith {
        mode: WrappingMode::Saturating,
        op: ArithOp::Add,
        left: Box::new(TrustVcExpr::FnCall {
            name: "f".to_string(),
            args: vec![],
            return_ty: TrustVcType::Uint { width: 8 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 1,
            ty: TrustVcType::Uint { width: 8 },
        }),
        ty: TrustVcType::Uint { width: 8 },
    };

    let sat_result = parser
        .encode_trust_vc_expr(&expr)
        .expect("#2100: saturating_add on FnCall must not fail");
    drop(parser);

    // Semantic check: when f() == 255, saturating_add(255, 1) must be 255
    // (clamped), not 0 (wrapping). If width metadata was missing, the
    // saturating path returns raw result (wrapping) — 255 + 1 = 0 in BV(8).
    let f_term = env.solver.try_apply(&f_decl, &[]).unwrap();
    let val_255 = env.solver.try_bv_const(255i64, 8).unwrap();
    let f_is_255 = env.solver.try_eq(f_term, val_255).unwrap();
    let result_is_255 = env.solver.try_eq(sat_result, val_255).unwrap();
    let should_hold = env.solver.try_implies(f_is_255, result_is_255).unwrap();

    env.solver.try_push().unwrap();
    let neg = env.solver.try_not(should_hold).unwrap();
    env.solver.try_assert_term(neg).unwrap();
    let sat = env.solver.try_check_sat().unwrap();
    env.solver.try_pop().unwrap();
    assert!(
        sat.is_unsat(),
        "#2100 SOUNDNESS: saturating_add(255, 1) should clamp to 255, \
         but solver found counterexample: {:?}. This indicates the saturating \
         path returned raw (wrapping) result instead of clamped.",
        sat
    );
}
