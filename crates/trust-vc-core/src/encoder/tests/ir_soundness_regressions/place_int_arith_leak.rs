// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression tests for place_encoding.rs use_int_arithmetic restore-on-exit.
//!
//! `encode_read_place` temporarily flips `use_int_arithmetic = false` when
//! projecting BV-typed selector results (matching the pattern in
//! match_encode.rs). The manual save/restore was safe but fragile — it relied
//! on the `?` operator firing before the flag modification. Hardened to use
//! `with_flag_unwind_safe!` for defense-in-depth (same class as #2643).

use super::*;

use crate::encoder::datatype::datatype_carrier_sort;
use crate::ir::DatatypeVariant;
use crate::ir_place::TrustVcPlace;

fn counter_u64_ty() -> TrustVcType {
    TrustVcType::Datatype {
        name: "CounterU64".to_string(),
        variants: vec![DatatypeVariant::new(
            "CounterU64",
            vec![
                ("count".to_string(), u64_ty()),
                ("label".to_string(), TrustVcType::MathInt),
            ],
        )],
    }
}

/// Declares the datatype receiver `d` over the native datatype carrier sort
/// (`Sort::Uninterpreted("CounterU64")`) rather than the legacy shared
/// `Sort::Int`. The native-datatype migration makes selectors take the carrier
/// sort as their domain (see `place_encoding.rs`), so the receiver term must be
/// carrier-sorted for the field projection to encode. The MathInt-mode-
/// preservation property under test is unchanged.
fn declare_counter_var(env: &mut QuantifierTestEnv) {
    let dt_ty = counter_u64_ty();
    let d = env
        .solver
        .declare_const("d", datatype_carrier_sort("CounterU64"));
    env.variables.insert("d".into(), d);
    env.var_types.insert("d".into(), dt_ty);
}

// ========================================================================
// ReadPlace field projection: success path
// ========================================================================

/// DISCRIMINATING: use_int_arithmetic must be restored after encoding a
/// ReadPlace with a BV-typed field in an all-Int (MathInt) context.
///
/// encode_read_place enters BV mode when projecting a BV-typed selector
/// result (field_ty.bit_width() > 0 → use_int_arithmetic = false).
/// The with_flag_unwind_safe! wrapper restores the flag after the
/// projection completes.
#[test]
fn test_place_field_preserves_int_mode_after_bv_projection() {
    let mut env = QuantifierTestEnv::new();

    // MathInt variable — use_int_arithmetic starts true
    let n = env.solver.int_var("n");
    env.variables.insert("n".into(), n);
    env.var_types.insert("n".into(), TrustVcType::MathInt);

    // Datatype variable with BV-typed field — over the native carrier sort.
    declare_counter_var(&mut env);
    let dt_ty = counter_u64_ty();

    let mut parser = env.parser();
    assert!(
        parser.use_int_arithmetic,
        "precondition: all-MathInt context should start with use_int_arithmetic = true"
    );

    // Encode ReadPlace(d.count) — the u64 field triggers BV mode
    let place = TrustVcPlace::root("d", dt_ty).field("count", u64_ty());
    let read_expr = TrustVcExpr::ReadPlace {
        place,
        ty: u64_ty(),
    };

    let result = parser.encode_trust_vc_expr(&read_expr);
    assert!(
        result.is_ok(),
        "ReadPlace(d.count) should encode without error: {:?}",
        result.err()
    );

    // CRITICAL: use_int_arithmetic must be restored to true
    assert!(
        parser.use_int_arithmetic,
        "use_int_arithmetic must be restored after ReadPlace with BV field projection"
    );
}

/// DISCRIMINATING: MathInt arithmetic must succeed AFTER encoding a ReadPlace
/// with a BV-typed field. Without flag restoration, Int arithmetic on Sort::Int
/// terms would attempt BV operations, causing sort mismatches.
#[test]
fn test_int_arithmetic_works_after_bv_place_projection() {
    let mut env = QuantifierTestEnv::new();

    let n = env.solver.int_var("n");
    env.variables.insert("n".into(), n);
    env.var_types.insert("n".into(), TrustVcType::MathInt);

    declare_counter_var(&mut env);
    let dt_ty = counter_u64_ty();

    let mut parser = env.parser();

    // First: encode ReadPlace with BV field (triggers flag flip)
    let place = TrustVcPlace::root("d", dt_ty).field("count", u64_ty());
    let read_expr = TrustVcExpr::ReadPlace {
        place,
        ty: u64_ty(),
    };
    parser.encode_trust_vc_expr(&read_expr).unwrap();

    // Second: encode MathInt arithmetic that requires Int mode
    let arith_expr = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(TrustVcExpr::Var {
                name: "n".into(),
                ty: TrustVcType::MathInt,
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 1,
                ty: TrustVcType::MathInt,
            }),
            ty: TrustVcType::MathInt,
        }),
        right: Box::new(TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(TrustVcExpr::Var {
                name: "n".into(),
                ty: TrustVcType::MathInt,
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 1,
                ty: TrustVcType::MathInt,
            }),
            ty: TrustVcType::MathInt,
        }),
    };

    let result = parser.encode_trust_vc_expr(&arith_expr);
    assert!(
        result.is_ok(),
        "MathInt arithmetic after BV-typed ReadPlace should succeed in all-Int context, \
         got error: {:?}",
        result.err()
    );
}

/// CONTROL: ReadPlace on a MathInt-typed field should not affect
/// use_int_arithmetic at all (bit_width() returns None for MathInt).
#[test]
fn test_place_mathint_field_preserves_int_mode() {
    let mut env = QuantifierTestEnv::new();

    let n = env.solver.int_var("n");
    env.variables.insert("n".into(), n);
    env.var_types.insert("n".into(), TrustVcType::MathInt);

    declare_counter_var(&mut env);
    let dt_ty = counter_u64_ty();

    let mut parser = env.parser();
    assert!(parser.use_int_arithmetic, "precondition");

    // Encode ReadPlace(d.label) — MathInt field, no BV toggle
    let place = TrustVcPlace::root("d", dt_ty).field("label", TrustVcType::MathInt);
    let read_expr = TrustVcExpr::ReadPlace {
        place,
        ty: TrustVcType::MathInt,
    };

    parser.encode_trust_vc_expr(&read_expr).unwrap();
    assert!(
        parser.use_int_arithmetic,
        "MathInt-typed field projection should not affect use_int_arithmetic"
    );
}
