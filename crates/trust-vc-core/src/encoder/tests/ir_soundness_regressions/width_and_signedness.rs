//! #2036 regressions: quantifier wrapping width and signedness resolution.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ========================================================================
// #2036/#1794 regression: Mixed-width quantifier scope uses widest width
// ========================================================================
//
// Before #2036, the IR encoder used find_map (first match) to determine
// the wrapping context for quantifier-bound variables. #2036 changed to
// narrowest width. #1794 changes to widest width, matching Rust's type
// promotion rules where narrower types are promoted before arithmetic.

/// Mixed-width quantifier (u32 + u8): scope resolves to width=32 (#1794).
/// Verify by pushing a mixed-width scope and checking wrap_int_to_bv_range
/// produces modular arithmetic at width 32.
#[test]
fn test_2036_mixed_width_scope_wraps_at_widest() {
    let mut env = QuantifierTestEnv::new();

    let bound_vars = vec![
        ("x".to_string(), TrustVcType::Uint { width: 32 }),
        ("y".to_string(), TrustVcType::Uint { width: 8 }),
    ];
    let x = env.solver.declare_const("x", Sort::Int);
    env.variables.insert("x".to_string(), x);
    env.var_types
        .insert("x".to_string(), TrustVcType::Uint { width: 32 });

    let mut parser = env.parser();
    parser.quantifier_depth = 1;
    parser.push_quantifier_scope(&bound_vars);

    // Verify the scope resolved to width=32 (#1794: widest), unsigned.
    let sem = parser.current_quantifier_wrap_semantics();
    assert!(sem.is_some(), "#2036: scope should have wrap semantics");
    let sem = sem.unwrap();
    assert_eq!(
        sem.width, 32,
        "#1794: should use widest width (32), got {}",
        sem.width
    );
    assert!(sem.is_unsigned, "#2036: all unsigned vars → unsigned");

    // Semantic check: wrap at (width=32, unsigned) should keep 300 intact (300 < 2^32).
    let val_300 = parser.solver.int_const(300);
    let wrapped = parser
        .wrap_int_to_explicit_range(val_300, sem.width, sem.is_unsigned)
        .expect("wrap should succeed");
    parser.pop_quantifier_scope();
    drop(parser);

    let expected = env.solver.int_const(300); // 300 mod 2^32 = 300
    let eq = env.solver.try_eq(wrapped, expected).unwrap();
    env.solver.try_push().unwrap();
    let neg = env.solver.try_not(eq).unwrap();
    env.solver.try_assert_term(neg).unwrap();
    let sat = env.solver.try_check_sat().unwrap();
    env.solver.try_pop().unwrap();
    assert!(
        sat.is_unsat(),
        "#1794: wrap(300) with width=32 should be 300, solver says: {:?}",
        sat
    );
}

/// Mixed-signedness (u8 + i32): scope resolves to signed, width=32 (#1794).
/// Signed wrapping of 200 at width 32: 200 (fits in i32, no wrapping needed).
#[test]
fn test_2036_mixed_signedness_scope_wraps_signed() {
    let mut env = QuantifierTestEnv::new();

    let bound_vars = vec![
        ("x".to_string(), TrustVcType::Uint { width: 8 }),
        ("y".to_string(), TrustVcType::Int { width: 32 }),
    ];
    let x = env.solver.declare_const("x", Sort::Int);
    env.variables.insert("x".to_string(), x);
    env.var_types
        .insert("x".to_string(), TrustVcType::Uint { width: 8 });

    let mut parser = env.parser();
    parser.quantifier_depth = 1;
    parser.push_quantifier_scope(&bound_vars);

    // Verify: mixed signedness → signed, width=32 (#1794: widest).
    let sem = parser.current_quantifier_wrap_semantics();
    assert!(sem.is_some(), "#2036: scope should have wrap semantics");
    let sem = sem.unwrap();
    assert_eq!(sem.width, 32, "#1794: widest width should be 32");
    assert!(!sem.is_unsigned, "#2036: mixed signedness → signed");

    // Semantic check: signed wrap of 200 at (width=32, signed).
    // 200 fits in i32 range [-2^31, 2^31), so wrapping produces 200.
    let val_200 = parser.solver.int_const(200);
    let wrapped = parser
        .wrap_int_to_explicit_range(val_200, sem.width, sem.is_unsigned)
        .expect("wrap should succeed");
    parser.pop_quantifier_scope();
    drop(parser);

    let expected = env.solver.int_const(200);
    let eq = env.solver.try_eq(wrapped, expected).unwrap();
    env.solver.try_push().unwrap();
    let neg = env.solver.try_not(eq).unwrap();
    env.solver.try_assert_term(neg).unwrap();
    let sat = env.solver.try_check_sat().unwrap();
    env.solver.try_pop().unwrap();
    assert!(
        sat.is_unsat(),
        "#1794: signed wrap(200) at width=32 should be 200, solver says: {:?}",
        sat
    );
}

/// Verify ArithSemantics resolution directly: widest-width (#1794), signed-unless-all-unsigned.
#[test]
fn test_2036_arith_semantics_resolution_correctness() {
    use crate::encoder::arith_semantics::{resolve_quantifier_wrap, ArithSemantics};

    // All unsigned, different widths → widest width (#1794), unsigned
    let vars = vec![
        ("x".to_string(), TrustVcType::Uint { width: 32 }),
        ("y".to_string(), TrustVcType::Uint { width: 8 }),
    ];
    let sem = resolve_quantifier_wrap(&vars);
    assert_eq!(
        sem,
        Some(ArithSemantics {
            width: 32,
            is_unsigned: true
        }),
        "#1794: should pick widest width (32), all unsigned"
    );

    // Mixed signedness → signed
    let vars = vec![
        ("x".to_string(), TrustVcType::Uint { width: 8 }),
        ("y".to_string(), TrustVcType::Int { width: 32 }),
    ];
    let sem = resolve_quantifier_wrap(&vars);
    assert_eq!(
        sem,
        Some(ArithSemantics {
            width: 32,
            is_unsigned: false
        }),
        "#1794: mixed signedness → signed, widest width (32)"
    );

    // Single var → uses that var's properties
    let vars = vec![("x".to_string(), TrustVcType::Int { width: 64 })];
    let sem = resolve_quantifier_wrap(&vars);
    assert_eq!(
        sem,
        Some(ArithSemantics {
            width: 64,
            is_unsigned: false
        }),
        "#2036: single i64 var → width 64, signed"
    );

    // No integer vars → None
    let vars = vec![("b".to_string(), TrustVcType::Bool)];
    let sem = resolve_quantifier_wrap(&vars);
    assert_eq!(sem, None, "#2036: no integer vars → None");
}

/// #1560: direct IR compare must re-type default `Int{32}` literals from the
/// peer operand before BV coercion.
///
/// Without the fix, `3_000_000_000` is encoded as signed BV32 because it still
/// carries the default `Int{32}` IR type. Width coercion then sign-extends that
/// BV32 term to 64 bits, producing `0xFFFF_FFFF_B2D0_5E00` instead of
/// `0x0000_0000_B2D0_5E00`, so equality with a `u64` variable fails.
#[test]
fn test_1560_default_i32_literal_compare_uses_peer_u64_type() {
    let mut env = QuantifierTestEnv::new();

    let x = env.solver.declare_const("x", Sort::bitvec(64));
    env.variables.insert("x".to_string(), x);
    env.var_types
        .insert("x".to_string(), TrustVcType::Uint { width: 64 });

    let expr = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Uint { width: 64 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 3_000_000_000,
            ty: TrustVcType::Int { width: 32 },
        }),
    };

    let condition = {
        let mut parser = env.parser();
        parser
            .encode_trust_vc_expr(&expr)
            .expect("u64 == default Int{32} literal should encode")
    };

    let x_val = env.solver.try_bv_const(3_000_000_000_i64, 64).unwrap();
    let eq_x = env.solver.try_eq(x, x_val).unwrap();
    env.solver.try_push().unwrap();
    env.solver.try_assert_term(eq_x).unwrap();
    env.solver.try_assert_term(condition).unwrap();
    let sat = env.solver.try_check_sat().unwrap();
    env.solver.try_pop().unwrap();

    assert_eq!(
        sat,
        SolveResult::Sat,
        "#1560: direct IR compare must preserve literal value 3_000_000_000 in u64 context"
    );
}

/// #1560: direct IR ordering must also borrow the peer unsigned type before
/// choosing the signed or unsigned BV comparison opcode.
///
/// Without the fix, this still uses `bvsgt` because the default `Int{32}`
/// literal is only retagged for term construction, not for the `unsigned`
/// decision. `255u8` then behaves like `-1i8`, making `x > 0` spuriously
/// false in the direct IR path.
#[test]
fn test_1560_default_i32_literal_compare_uses_unsigned_ordering() {
    let mut env = QuantifierTestEnv::new();

    let x = env.solver.declare_const("x", Sort::bitvec(8));
    env.variables.insert("x".to_string(), x);
    env.var_types
        .insert("x".to_string(), TrustVcType::Uint { width: 8 });

    let expr = TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Uint { width: 8 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::Int { width: 32 },
        }),
    };

    let condition = {
        let mut parser = env.parser();
        parser
            .encode_trust_vc_expr(&expr)
            .expect("u8 > default Int{32} literal should encode")
    };

    let x_val = env.solver.try_bv_const(255, 8).unwrap();
    let eq_x = env.solver.try_eq(x, x_val).unwrap();
    env.solver.try_push().unwrap();
    env.solver.try_assert_term(eq_x).unwrap();
    env.solver.try_assert_term(condition).unwrap();
    let sat = env.solver.try_check_sat().unwrap();
    env.solver.try_pop().unwrap();

    assert_eq!(
        sat,
        SolveResult::Sat,
        "#1560: direct IR compare must use unsigned ordering for u8 > default Int{{32}} zero"
    );
}
