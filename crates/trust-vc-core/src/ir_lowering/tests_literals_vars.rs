//! Tests for literal, variable, and associated constant lowering.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::ir::TrustVcType;
use crate::ir_expr::*;

use super::tests_support::env_with;

// === Literal lowering ===

#[test]
fn lower_bool_lit_true() {
    let expr: syn::Expr = syn::parse_str("true").unwrap();
    let result = lower_syn_expr(&expr, &TypeEnv::new()).unwrap();
    assert_eq!(result, TrustVcExpr::BoolLit(true));
}

#[test]
fn lower_bool_lit_false() {
    let expr: syn::Expr = syn::parse_str("false").unwrap();
    let result = lower_syn_expr(&expr, &TypeEnv::new()).unwrap();
    assert_eq!(result, TrustVcExpr::BoolLit(false));
}

#[test]
fn lower_unit_literal() {
    let expr: syn::Expr = syn::parse_str("()").unwrap();
    let result = lower_syn_expr(&expr, &TypeEnv::new()).unwrap();
    assert_eq!(result, TrustVcExpr::UnitLit);
}

#[test]
fn lower_int_lit_unsuffixed() {
    let expr: syn::Expr = syn::parse_str("42").unwrap();
    let result = lower_syn_expr(&expr, &TypeEnv::new()).unwrap();
    assert_eq!(
        result,
        TrustVcExpr::IntLit {
            value: 42,
            ty: TrustVcType::Int { width: 32 }
        }
    );
}

#[test]
fn lower_int_lit_u64_suffix() {
    let expr: syn::Expr = syn::parse_str("100u64").unwrap();
    let result = lower_syn_expr(&expr, &TypeEnv::new()).unwrap();
    assert_eq!(
        result,
        TrustVcExpr::IntLit {
            value: 100,
            ty: TrustVcType::Uint { width: 64 }
        }
    );
}

#[test]
fn lower_decimal_real_lit_is_exact_rational() {
    let expr: syn::Expr = syn::parse_str("1.50").unwrap();
    let result = lower_syn_expr(&expr, &TypeEnv::new()).unwrap();
    assert_eq!(
        result,
        TrustVcExpr::Arith {
            op: ArithOp::Div,
            left: Box::new(TrustVcExpr::IntLit {
                value: 3,
                ty: TrustVcType::Real,
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 2,
                ty: TrustVcType::Real,
            }),
            ty: TrustVcType::Real,
        }
    );
}

#[test]
fn lower_decimal_real_lit_with_positive_exponent_to_integer_real() {
    let expr: syn::Expr = syn::parse_str("1.2e3").unwrap();
    let result = lower_syn_expr(&expr, &TypeEnv::new()).unwrap();
    assert_eq!(
        result,
        TrustVcExpr::IntLit {
            value: 1200,
            ty: TrustVcType::Real,
        }
    );
}

#[test]
fn lower_suffixed_integral_float_lit_to_int_float_cast() {
    let expr: syn::Expr = syn::parse_str("1.0f64").unwrap();
    let result = lower_syn_expr(&expr, &TypeEnv::new()).unwrap();
    assert_eq!(
        result,
        TrustVcExpr::Cast {
            expr: Box::new(TrustVcExpr::IntLit {
                value: 1,
                ty: TrustVcType::Int { width: 32 },
            }),
            from_ty: TrustVcType::Int { width: 32 },
            to_ty: TrustVcType::Float { width: 64 },
        }
    );
}

#[test]
fn lower_suffixed_fractional_float_lit_fails_closed() {
    let expr: syn::Expr = syn::parse_str("1.5f64").unwrap();
    let err = lower_syn_expr(&expr, &TypeEnv::new())
        .expect_err("fractional f64 literal should fail closed");
    assert!(matches!(err, LoweringError::InvalidLiteral(_)));
    assert!(
        err.to_string()
            .contains("unsupported non-integral f64 literal"),
        "unexpected float literal error: {err}",
    );
}

#[test]
fn lower_char_lit() {
    let expr: syn::Expr = syn::parse_str("'a'").unwrap();
    let result = lower_syn_expr(&expr, &TypeEnv::new()).unwrap();
    assert_eq!(
        result,
        TrustVcExpr::IntLit {
            value: i128::from(u32::from('a')),
            ty: TrustVcType::Char
        }
    );
}

#[test]
fn lower_string_lit_builds_native_string_literal() {
    // A string literal lowers unconditionally to `StringLit`; the encoder maps it
    // to ay's native `Sort::String` constant, which decides constant (dis)equality
    // soundly. (The former `native-strings`-feature gate is removed — the encoder
    // path was already unconditional.)
    let expr: syn::Expr = syn::parse_str("\"hello\"").unwrap();
    let result = lower_syn_expr(&expr, &TypeEnv::new()).expect("string literal should lower");
    assert_eq!(result, TrustVcExpr::StringLit("hello".into()));
}

// === PhantomData constructor lowering ===

#[test]
fn lower_phantom_data_constructor_to_unit_lit() {
    // `PhantomData`, `PhantomData::<T>`, and the `core::marker` /
    // `std::marker` qualified forms are the unique inhabitant of the
    // zero-sized marker type, so they lower to the unit literal (cluster
    // #2779). Mirrors Verus's `phantom_data_is_unit`.
    for src in [
        "PhantomData::<u64>",
        "core::marker::PhantomData::<u64>",
        "std::marker::PhantomData::<bool>",
    ] {
        let expr: syn::Expr = syn::parse_str(src).unwrap();
        let result = lower_syn_expr(&expr, &TypeEnv::new())
            .unwrap_or_else(|e| panic!("{src} should lower: {e}"));
        assert_eq!(result, TrustVcExpr::UnitLit, "{src} should be UnitLit");
    }
}

#[test]
fn lower_bare_phantom_data_constructor_to_unit_lit() {
    // Bare `PhantomData` with no in-scope variable of that name is the
    // constructor and lowers to the unit literal.
    let expr: syn::Expr = syn::parse_str("PhantomData").unwrap();
    let result = lower_syn_expr(&expr, &TypeEnv::new()).unwrap();
    assert_eq!(result, TrustVcExpr::UnitLit);
}

#[test]
fn lower_phantom_data_shadowed_by_local_var_resolves_to_var() {
    // A same-named local variable shadows the constructor: `PhantomData`
    // must resolve to that variable, NOT silently become a unit literal.
    // This keeps the constructor arm from clobbering a real binding.
    let expr: syn::Expr = syn::parse_str("PhantomData").unwrap();
    let env = env_with(&[("PhantomData", "u64")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert_eq!(
        result,
        TrustVcExpr::Var {
            name: "PhantomData".into(),
            ty: TrustVcType::Uint { width: 64 },
        }
    );
}

#[test]
fn lower_unrelated_two_segment_path_still_fails_closed() {
    // The PhantomData arm must not loosen the existing fail-closed behavior
    // for unrelated multi-segment paths.
    let expr: syn::Expr = syn::parse_str("SomeType::SOME_CONST").unwrap();
    let err = lower_syn_expr(&expr, &TypeEnv::new())
        .expect_err("unrelated qualified path must fail closed");
    assert!(
        matches!(err, LoweringError::UnsupportedExpr(_)),
        "got: {err:?}"
    );
}

// === Variable lowering ===

#[test]
fn lower_var_found() {
    let expr: syn::Expr = syn::parse_str("x").unwrap();
    let env = env_with(&[("x", "i32")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert_eq!(
        result,
        TrustVcExpr::Var {
            name: "x".into(),
            ty: TrustVcType::Int { width: 32 }
        }
    );
}

#[test]
fn lower_var_not_found() {
    let expr: syn::Expr = syn::parse_str("y").unwrap();
    let result = lower_syn_expr(&expr, &TypeEnv::new());
    assert!(matches!(result, Err(LoweringError::UnresolvedVar(_))));
}

// === Associated constants ===

#[test]
fn lower_assoc_const_max() {
    let expr: syn::Expr = syn::parse_str("i32::MAX").unwrap();
    let result = lower_syn_expr(&expr, &TypeEnv::new()).unwrap();
    assert_eq!(
        result,
        TrustVcExpr::IntConst {
            ty: TrustVcType::Int { width: 32 },
            kind: IntConstKind::Max
        }
    );
}

#[test]
fn lower_assoc_const_min() {
    let expr: syn::Expr = syn::parse_str("u8::MIN").unwrap();
    let result = lower_syn_expr(&expr, &TypeEnv::new()).unwrap();
    assert_eq!(
        result,
        TrustVcExpr::IntConst {
            ty: TrustVcType::Uint { width: 8 },
            kind: IntConstKind::Min
        }
    );
}

#[test]
fn lower_assoc_const_bits_is_u32_value() {
    let expr: syn::Expr = syn::parse_str("i16::BITS").unwrap();
    let result = lower_syn_expr(&expr, &TypeEnv::new()).unwrap();
    assert_eq!(
        result,
        TrustVcExpr::IntLit {
            value: 16,
            ty: TrustVcType::Uint { width: 32 }
        }
    );
}

#[test]
fn lower_assoc_const_bits_uses_pointer_width_for_usize() {
    let expr: syn::Expr = syn::parse_str("usize::BITS").unwrap();
    let result = lower_syn_expr(&expr, &TypeEnv::new()).unwrap();
    assert_eq!(
        result,
        TrustVcExpr::IntLit {
            value: i128::from(crate::ir::pointer_width()),
            ty: TrustVcType::Uint { width: 32 }
        }
    );
}
