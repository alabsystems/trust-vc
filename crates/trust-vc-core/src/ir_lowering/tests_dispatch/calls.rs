// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Function call lowering tests (named calls, coercion, special builtins).

use crate::ir::TrustVcType;
use crate::ir_expr::*;
use crate::ir_lowering::tests_support::env_with;
use crate::ir_lowering::*;

#[test]
fn lower_named_fn_call() {
    let expr: syn::Expr = syn::parse_str("foo(x, y)").unwrap();
    let env = env_with(&[("x", "i32"), ("y", "i32"), ("foo", "i32")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert_eq!(name, "foo");
            assert_eq!(args.len(), 2);
            assert_eq!(
                args[0],
                TrustVcExpr::Var {
                    name: "x".into(),
                    ty: TrustVcType::Int { width: 32 }
                },
                "first arg must be lowered variable x: i32"
            );
            assert_eq!(
                args[1],
                TrustVcExpr::Var {
                    name: "y".into(),
                    ty: TrustVcType::Int { width: 32 }
                },
                "second arg must be lowered variable y: i32"
            );
            assert_eq!(
                return_ty,
                TrustVcType::Int { width: 32 },
                "return_ty must match TypeEnv registration"
            );
        }
        other => panic!("expected FnCall, got {:?}", other),
    }
}

#[test]
fn lower_wrapping_free_function_intrinsics() {
    for (src, expected_op) in [
        ("add(x, y)", ArithOp::Add),
        ("sub(x, y)", ArithOp::Sub),
        ("mul(x, y)", ArithOp::Mul),
    ] {
        let expr: syn::Expr = syn::parse_str(src).unwrap();
        let env = env_with(&[("x", "u32"), ("y", "u32")]);
        let result = lower_syn_expr(&expr, &env).unwrap();
        match result {
            TrustVcExpr::WrappingArith {
                mode,
                op,
                left,
                right,
                ty,
            } => {
                assert_eq!(mode, WrappingMode::Wrapping);
                assert_eq!(op, expected_op);
                assert_eq!(ty, TrustVcType::Uint { width: 32 });
                assert_eq!(
                    *left,
                    TrustVcExpr::Var {
                        name: "x".into(),
                        ty: TrustVcType::Uint { width: 32 },
                    }
                );
                assert_eq!(
                    *right,
                    TrustVcExpr::Var {
                        name: "y".into(),
                        ty: TrustVcType::Uint { width: 32 },
                    }
                );
            }
            other => panic!("expected WrappingArith for {src}, got {:?}", other),
        }
    }
}

#[test]
fn lower_wrapping_free_function_coerces_unsuffixed_literal_to_peer_type() {
    let expr: syn::Expr = syn::parse_str("add(x, 1)").unwrap();
    let env = env_with(&[("x", "u8")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::WrappingArith { right, ty, .. } => {
            assert_eq!(ty, TrustVcType::Uint { width: 8 });
            assert_eq!(
                *right,
                TrustVcExpr::IntLit {
                    value: 1,
                    ty: TrustVcType::Uint { width: 8 },
                }
            );
        }
        other => panic!("expected WrappingArith, got {:?}", other),
    }
}

#[test]
fn lower_wrapping_free_function_wrong_arity_stays_fn_call() {
    let expr: syn::Expr = syn::parse_str("add(x)").unwrap();
    let mut env = env_with(&[("x", "u32")]);
    env.insert_fn("add".to_string(), TrustVcType::Uint { width: 32 });
    env.insert_fn_params("add".to_string(), vec![TrustVcType::Uint { width: 32 }]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert_eq!(name, "add");
            assert_eq!(args.len(), 1);
            assert_eq!(return_ty, TrustVcType::Uint { width: 32 });
        }
        other => panic!("expected FnCall fallback, got {:?}", other),
    }
}

#[test]
fn lower_wrapping_free_function_math_int_operands_stay_fn_call() {
    let expr: syn::Expr = syn::parse_str("add(x, y)").unwrap();
    let env = env_with(&[("x", "int"), ("y", "int"), ("add", "int")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert_eq!(name, "add");
            assert_eq!(args.len(), 2);
            assert_eq!(return_ty, TrustVcType::MathInt);
        }
        other => panic!("expected FnCall fallback, got {:?}", other),
    }
}

#[test]
fn lower_registered_finite_add_stays_fn_call() {
    let expr: syn::Expr = syn::parse_str("add(x, y)").unwrap();
    let mut env = env_with(&[("x", "u32"), ("y", "u32")]);
    env.insert_fn("add".to_string(), TrustVcType::Uint { width: 32 });
    env.insert_fn_params(
        "add".to_string(),
        vec![
            TrustVcType::Uint { width: 32 },
            TrustVcType::Uint { width: 32 },
        ],
    );
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert_eq!(name, "add");
            assert_eq!(args.len(), 2);
            assert_eq!(return_ty, TrustVcType::Uint { width: 32 });
        }
        other => panic!("expected registered add to remain FnCall, got {:?}", other),
    }
}

#[test]
fn lower_primitive_associated_default_constructors() {
    let u32_expr: syn::Expr = syn::parse_str("u32::default()").unwrap();
    let bool_expr: syn::Expr = syn::parse_str("bool::default()").unwrap();

    assert_eq!(
        lower_syn_expr(&u32_expr, &TypeEnv::new()).expect("u32 default should lower"),
        TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::Uint { width: 32 },
        }
    );
    assert_eq!(
        lower_syn_expr(&bool_expr, &TypeEnv::new()).expect("bool default should lower"),
        TrustVcExpr::BoolLit(false)
    );
}

/// Every fixed-width primitive integer (plus `isize`/`usize`) `Default` lowers to
/// `IntLit { value: 0 }` at the suffix-mapped signedness and width. Rust's
/// `Default` for these is definitionally `0`, matching Verus
/// (../verus/source/rust_verify_test/tests/default_trait.rs). This pins the exact
/// type so a regression to a wrong width/signedness is caught.
#[test]
fn lower_all_primitive_integer_default_constructors_to_zero_at_correct_width() {
    let ptr = crate::ir::pointer_width();
    let cases: &[(&str, TrustVcType)] = &[
        ("i8", TrustVcType::Int { width: 8 }),
        ("i16", TrustVcType::Int { width: 16 }),
        ("i32", TrustVcType::Int { width: 32 }),
        ("i64", TrustVcType::Int { width: 64 }),
        ("i128", TrustVcType::Int { width: 128 }),
        ("isize", TrustVcType::Int { width: ptr }),
        ("u8", TrustVcType::Uint { width: 8 }),
        ("u16", TrustVcType::Uint { width: 16 }),
        ("u32", TrustVcType::Uint { width: 32 }),
        ("u64", TrustVcType::Uint { width: 64 }),
        ("u128", TrustVcType::Uint { width: 128 }),
        ("usize", TrustVcType::Uint { width: ptr }),
    ];
    for (name, ty) in cases {
        let src = format!("{name}::default()");
        let expr: syn::Expr = syn::parse_str(&src).unwrap();
        assert_eq!(
            lower_syn_expr(&expr, &TypeEnv::new())
                .unwrap_or_else(|e| panic!("{src} should lower: {e}")),
            TrustVcExpr::IntLit {
                value: 0,
                ty: ty.clone(),
            },
            "{src} must lower to IntLit{{0}} at {ty:?}"
        );
    }
}

/// Ghost-only numeric type names (`int`/`nat`/`real`) are NOT constructible via
/// Rust's `Default` in source; the extended integer-default recognition must not
/// fabricate a value for them. They stay fail-closed at the generic `Default`
/// catch-all (unknown return type), never silently lowering to `0`.
#[test]
fn lower_ghost_numeric_default_constructor_stays_fail_closed() {
    for name in ["int", "nat", "real"] {
        let src = format!("{name}::default()");
        let expr: syn::Expr = syn::parse_str(&src).unwrap();
        let result = lower_syn_expr(&expr, &TypeEnv::new());
        // Must NOT lower to a fabricated `0`: ghost numeric types have no Rust
        // `Default` in source, so the generic-`Default` catch-all rejects them.
        assert!(
            result.is_err(),
            "{src} must fail closed, not silently lower to {result:?}"
        );
    }
}

#[test]
fn lower_explicit_option_associated_default_constructor() {
    let expr: syn::Expr = syn::parse_str("Option::<u32>::default()").unwrap();
    let result = lower_syn_expr(&expr, &TypeEnv::new()).expect("Option default should lower");
    match result {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert!(name.contains("None"), "constructor should be None: {name}");
            assert!(args.is_empty(), "Option::default is nullary");
            assert_eq!(return_ty, TrustVcType::from_str("Option<u32>").unwrap());
        }
        other => panic!("expected Option None constructor, got {other:?}"),
    }
}

#[test]
fn lower_untyped_default_constructor_stays_fail_closed() {
    let expr: syn::Expr = syn::parse_str("Default::default()").unwrap();
    let err = lower_syn_expr(&expr, &TypeEnv::new()).expect_err("untyped Default remains blocked");
    assert!(
        err.to_string()
            .contains("unknown return type for function 'Default::default'"),
        "unexpected error: {err}"
    );
}

#[test]
fn lower_core_mem_size_of_primitives_and_references_to_usize_literals() {
    for (src, expected) in [
        ("core::mem::size_of::<u8>()", 1),
        ("core::mem::size_of::<bool>()", 1),
        ("core::mem::size_of::<u16>()", 2),
        ("core::mem::size_of::<usize>()", (usize::BITS / 8) as i128),
        ("core::mem::size_of::<&u8>()", (usize::BITS / 8) as i128),
        (
            "std::mem::size_of::<*const u8>()",
            (usize::BITS / 8) as i128,
        ),
        ("mem::size_of::<[u16; 3]>()", 6),
    ] {
        let expr: syn::Expr = syn::parse_str(src).unwrap();
        let env = env_with(&[]);
        let result = lower_syn_expr(&expr, &env).unwrap();
        assert_eq!(
            result,
            TrustVcExpr::IntLit {
                value: expected,
                ty: TrustVcType::Uint { width: usize::BITS },
            },
            "{src} should lower to a concrete usize literal",
        );
    }
}

#[test]
fn lower_core_mem_size_of_fails_closed_for_unknown_layout_type() {
    let expr: syn::Expr = syn::parse_str("core::mem::size_of::<Vec<u8>>()").unwrap();
    let env = env_with(&[]);
    let err = lower_syn_expr(&expr, &env).expect_err("unsupported layout type should fail closed");
    let message = err.to_string();
    assert!(
        message.contains("core::mem::size_of is only modeled") && message.contains("Seq<u8>"),
        "unsupported type error should name size_of and resolved Seq<u8>, got: {message}",
    );
}

#[test]
fn lower_core_mem_align_of_primitives_references_and_arrays_to_usize_literals() {
    for (src, expected) in [
        ("core::mem::align_of::<()>()", std::mem::align_of::<()>()),
        (
            "core::mem::align_of::<bool>()",
            std::mem::align_of::<bool>(),
        ),
        ("core::mem::align_of::<u16>()", std::mem::align_of::<u16>()),
        ("core::mem::align_of::<u32>()", std::mem::align_of::<u32>()),
        ("core::mem::align_of::<&u8>()", std::mem::align_of::<&u8>()),
        (
            "std::mem::align_of::<*const u8>()",
            std::mem::align_of::<*const u8>(),
        ),
        (
            "mem::align_of::<[u16; 3]>()",
            std::mem::align_of::<[u16; 3]>(),
        ),
    ] {
        let expr: syn::Expr = syn::parse_str(src).unwrap();
        let env = env_with(&[]);
        let result = lower_syn_expr(&expr, &env).unwrap();
        assert_eq!(
            result,
            TrustVcExpr::IntLit {
                value: expected as i128,
                ty: TrustVcType::Uint { width: usize::BITS },
            },
            "{src} should lower to a concrete usize literal",
        );
    }
}

#[test]
fn lower_core_mem_align_of_fails_closed_for_unknown_layout_type() {
    let expr: syn::Expr = syn::parse_str("core::mem::align_of::<Vec<u8>>()").unwrap();
    let env = env_with(&[]);
    let err = lower_syn_expr(&expr, &env).expect_err("unsupported layout type should fail closed");
    let message = err.to_string();
    assert!(
        message.contains("core::mem::align_of is only modeled") && message.contains("Seq<u8>"),
        "unsupported type error should name align_of and resolved Seq<u8>, got: {message}",
    );
}

#[test]
fn lower_wrapping_free_function_rejects_mismatched_finite_widths() {
    let expr: syn::Expr = syn::parse_str("add(x, y)").unwrap();
    let env = env_with(&[("x", "u8"), ("y", "u32")]);
    let err = lower_syn_expr(&expr, &env)
        .expect_err("mismatched-width add should not be lowered as wrapping intrinsic");
    let msg = err.to_string();
    assert!(
        msg.contains("unknown return type for function 'add'"),
        "mismatched intrinsic fallback should report unknown function, got: {msg}"
    );
}

#[test]
fn lower_fn_call_return_ty_from_env() {
    let expr: syn::Expr = syn::parse_str("helper(x)").unwrap();
    let env = env_with(&[("x", "u32"), ("helper", "u32")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::FnCall {
            name, return_ty, ..
        } => {
            assert_eq!(name, "helper");
            assert_eq!(return_ty, TrustVcType::Uint { width: 32 });
        }
        other => panic!("expected FnCall, got {:?}", other),
    }
}

#[test]
fn lower_fn_call_unknown_function_errors() {
    let expr: syn::Expr = syn::parse_str("unknown_pred(x)").unwrap();
    let env = env_with(&[("x", "i32")]);
    let err =
        lower_syn_expr(&expr, &env).expect_err("unknown function must produce TypeInference error");
    match err {
        LoweringError::TypeInference(msg) => {
            assert!(
                msg.contains("unknown_pred"),
                "error should name the unknown function, got: {msg}"
            );
            assert!(
                msg.contains("prepare_context"),
                "error should include actionable guidance mentioning prepare_context, got: {msg}"
            );
        }
        other => panic!("expected TypeInference error, got {:?}", other),
    }
}

#[test]
fn lower_fn_call_in_arith_gets_correct_ty() {
    let expr: syn::Expr = syn::parse_str("x + helper(x)").unwrap();
    let env = env_with(&[("x", "u32"), ("helper", "u32")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::Arith { ty, .. } => {
            assert_eq!(
                ty,
                TrustVcType::Uint { width: 32 },
                "Arith ty should be Uint{{32}} when both operands are u32, \
                 not Bool from hardcoded FnCall return_ty"
            );
        }
        other => panic!("expected Arith, got {:?}", other),
    }
}

/// Unsuffixed integer literals in function call arguments must be coerced to
/// match the function's declared parameter types.
#[test]
fn lower_fn_call_coerces_unsuffixed_literal_arg_to_param_type() {
    let expr: syn::Expr = syn::parse_str("check(42)").unwrap();
    let mut env = env_with(&[]);
    env.insert_fn("check".to_string(), TrustVcType::Bool);
    env.insert_fn_params("check".to_string(), vec![TrustVcType::Uint { width: 8 }]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::FnCall { args, .. } => {
            assert_eq!(
                args[0],
                TrustVcExpr::IntLit {
                    value: 42,
                    ty: TrustVcType::Uint { width: 8 }
                },
                "unsuffixed literal 42 must be coerced to u8 to match param type"
            );
        }
        other => panic!("expected FnCall, got {:?}", other),
    }
}

/// Non-default-width suffixed literals must NOT be coerced.
#[test]
fn lower_fn_call_preserves_non_default_suffixed_literal_arg() {
    let expr: syn::Expr = syn::parse_str("check(42u16)").unwrap();
    let mut env = env_with(&[]);
    env.insert_fn("check".to_string(), TrustVcType::Bool);
    env.insert_fn_params("check".to_string(), vec![TrustVcType::Uint { width: 8 }]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::FnCall { args, .. } => {
            assert_eq!(
                args[0],
                TrustVcExpr::IntLit {
                    value: 42,
                    ty: TrustVcType::Uint { width: 16 }
                },
                "suffixed literal 42u16 must NOT be coerced to u8"
            );
        }
        other => panic!("expected FnCall, got {:?}", other),
    }
}

/// When no param types are registered, args pass through unchanged.
#[test]
fn lower_fn_call_no_param_types_no_coercion() {
    let expr: syn::Expr = syn::parse_str("unknown(42)").unwrap();
    let mut env = env_with(&[]);
    env.insert_fn("unknown".to_string(), TrustVcType::Int { width: 32 });
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::FnCall { args, .. } => {
            assert_eq!(
                args[0],
                TrustVcExpr::IntLit {
                    value: 42,
                    ty: TrustVcType::Int { width: 32 }
                },
                "without param types registered, literal stays at default Int{{32}}"
            );
        }
        other => panic!("expected FnCall, got {:?}", other),
    }
}

#[test]
fn lower_trust_vc_dt_size_returns_math_int() {
    let expr: syn::Expr = syn::parse_str("__trust_vc_dt_size(x)").unwrap();
    let env = env_with(&[("x", "i32")]);
    let result = lower_syn_expr(&expr, &env).expect("__trust_vc_dt_size should lower");
    match result {
        TrustVcExpr::FnCall {
            name, return_ty, ..
        } => {
            assert_eq!(name, "__trust_vc_dt_size");
            assert_eq!(return_ty, TrustVcType::MathInt);
        }
        other => panic!("expected FnCall for __trust_vc_dt_size, got {:?}", other),
    }
}

#[test]
fn lower_non_path_function_call_rejected() {
    let expr: syn::Expr = syn::parse_str("(get_fn)(1)").unwrap();
    let env = env_with(&[]);
    let err = lower_syn_expr(&expr, &env).expect_err("non-path function call must be rejected");
    let msg = err.to_string();
    assert!(
        msg.contains("non-path function call"),
        "error should mention non-path call, got: {msg}",
    );
}

#[test]
fn lower_cow_borrowed_constructor_infers_str_inner_type() {
    let expr: syn::Expr = syn::parse_str("Cow::Borrowed(s)").unwrap();
    let env = env_with(&[("s", "str")]);
    let result = lower_syn_expr(&expr, &env).expect("Cow::Borrowed should lower");
    match result {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert!(
                name.contains("Borrowed"),
                "constructor should mention Borrowed: {name}"
            );
            assert_eq!(args.len(), 1);
            assert_eq!(return_ty.to_type_string(), "Cow<str>");
            assert_eq!(return_ty.cow_inner_type(), Some(TrustVcType::StrSlice));
        }
        other => panic!("expected Cow constructor FnCall, got {:?}", other),
    }
}

#[test]
fn lower_cow_owned_constructor_infers_scalar_inner_type() {
    let expr: syn::Expr = syn::parse_str("std::borrow::Cow::Owned(x)").unwrap();
    let env = env_with(&[("x", "u64")]);
    let result = lower_syn_expr(&expr, &env).expect("Cow::Owned should lower");
    match result {
        TrustVcExpr::FnCall {
            name, return_ty, ..
        } => {
            assert!(
                name.contains("Owned"),
                "constructor should mention Owned: {name}"
            );
            assert_eq!(return_ty.to_type_string(), "Cow<u64>");
            assert_eq!(
                return_ty.cow_inner_type(),
                Some(TrustVcType::Uint { width: 64 })
            );
        }
        other => panic!("expected Cow constructor FnCall, got {:?}", other),
    }
}

#[test]
fn lower_cow_constructor_rejects_wrong_arity() {
    let expr: syn::Expr = syn::parse_str("Cow::Owned(x, y)").unwrap();
    let env = env_with(&[("x", "u64"), ("y", "u64")]);
    let err = lower_syn_expr(&expr, &env).expect_err("wrong Cow arity must fail");
    assert!(
        err.to_string().contains("Cow::Owned"),
        "error should mention Cow constructor, got: {err}",
    );
}
