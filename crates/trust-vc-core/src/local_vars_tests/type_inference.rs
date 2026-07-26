//! Tests for infer_type_from_expr.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// --- infer_type_from_expr tests ---

#[test]
fn test_infer_int_literal_no_suffix() {
    let expr: syn::Expr = syn::parse_str("42").unwrap();
    match infer_type_from_expr(&expr) {
        TypeInference::Inferred(ty) => assert_eq!(ty, "i32"),
        other => panic!(
            "Expected Inferred(i32), got {:?}",
            type_inference_debug(&other)
        ),
    }
}

#[test]
fn test_infer_int_literal_u64_suffix() {
    let expr: syn::Expr = syn::parse_str("42u64").unwrap();
    match infer_type_from_expr(&expr) {
        TypeInference::Inferred(ty) => assert_eq!(ty, "u64"),
        other => panic!(
            "Expected Inferred(u64), got {:?}",
            type_inference_debug(&other)
        ),
    }
}

#[test]
fn test_infer_bool_literal() {
    let expr: syn::Expr = syn::parse_str("true").unwrap();
    // syn parses `true` as Expr::Lit(Lit::Bool), so infer_type_from_expr
    // correctly returns Inferred("bool") via the Bool arm at line 294.
    match infer_type_from_expr(&expr) {
        TypeInference::Inferred(ty) => assert_eq!(ty, "bool"),
        other => panic!("Expected Inferred(\"bool\"), got {:?}", other),
    }
}

#[test]
fn test_infer_float_no_suffix() {
    let expr: syn::Expr = syn::parse_str("3.14").unwrap();
    match infer_type_from_expr(&expr) {
        TypeInference::Inferred(ty) => assert_eq!(ty, "f64"),
        other => panic!(
            "Expected Inferred(f64), got {:?}",
            type_inference_debug(&other)
        ),
    }
}

#[test]
fn test_infer_float_f32_suffix() {
    let expr: syn::Expr = syn::parse_str("3.14f32").unwrap();
    match infer_type_from_expr(&expr) {
        TypeInference::Inferred(ty) => assert_eq!(ty, "f32"),
        other => panic!(
            "Expected Inferred(f32), got {:?}",
            type_inference_debug(&other)
        ),
    }
}

#[test]
fn test_infer_string_literal() {
    let expr: syn::Expr = syn::parse_str("\"hello\"").unwrap();
    match infer_type_from_expr(&expr) {
        TypeInference::UnsupportedStringLiteral => {}
        other => panic!(
            "Expected UnsupportedStringLiteral, got {:?}",
            type_inference_debug(&other)
        ),
    }
}

#[test]
fn test_infer_char_literal() {
    let expr: syn::Expr = syn::parse_str("'a'").unwrap();
    match infer_type_from_expr(&expr) {
        TypeInference::Inferred(ty) => assert_eq!(ty, "char"),
        other => panic!(
            "Expected Inferred(char), got {:?}",
            type_inference_debug(&other)
        ),
    }
}

#[test]
fn test_infer_negated_literal() {
    let expr: syn::Expr = syn::parse_str("-5").unwrap();
    match infer_type_from_expr(&expr) {
        TypeInference::Inferred(ty) => assert_eq!(ty, "i32"),
        other => panic!(
            "Expected Inferred(i32), got {:?}",
            type_inference_debug(&other)
        ),
    }
}

#[test]
fn test_infer_negated_suffixed() {
    let expr: syn::Expr = syn::parse_str("-5i64").unwrap();
    match infer_type_from_expr(&expr) {
        TypeInference::Inferred(ty) => assert_eq!(ty, "i64"),
        other => panic!(
            "Expected Inferred(i64), got {:?}",
            type_inference_debug(&other)
        ),
    }
}

#[test]
fn test_infer_variable_reference() {
    let expr: syn::Expr = syn::parse_str("x").unwrap();
    match infer_type_from_expr(&expr) {
        TypeInference::InferFromRef(name) => assert_eq!(name, "x"),
        other => panic!(
            "Expected InferFromRef(x), got {:?}",
            type_inference_debug(&other)
        ),
    }
}

#[test]
fn test_infer_binary_with_variable() {
    let expr: syn::Expr = syn::parse_str("x + 1").unwrap();
    match infer_type_from_expr(&expr) {
        TypeInference::InferFromRef(name) => assert_eq!(name, "x"),
        other => panic!(
            "Expected InferFromRef(x), got {:?}",
            type_inference_debug(&other)
        ),
    }
}

#[test]
fn test_infer_binary_variable_on_right() {
    let expr: syn::Expr = syn::parse_str("1 + y").unwrap();
    match infer_type_from_expr(&expr) {
        TypeInference::InferFromRef(name) => assert_eq!(name, "y"),
        other => panic!(
            "Expected InferFromRef(y), got {:?}",
            type_inference_debug(&other)
        ),
    }
}

#[test]
fn test_infer_binary_two_literals() {
    let expr: syn::Expr = syn::parse_str("1 + 2").unwrap();
    match infer_type_from_expr(&expr) {
        TypeInference::Inferred(ty) => assert_eq!(ty, "i32"),
        other => panic!(
            "Expected Inferred(i32) for lit+lit, got {:?}",
            type_inference_debug(&other)
        ),
    }
}

#[test]
fn test_infer_cast_expression() {
    let expr: syn::Expr = syn::parse_str("x as u64").unwrap();
    match infer_type_from_expr(&expr) {
        TypeInference::Inferred(ty) => assert_eq!(ty, "u64"),
        other => panic!(
            "Expected Inferred(u64), got {:?}",
            type_inference_debug(&other)
        ),
    }
}

#[test]
fn test_infer_paren_expression() {
    let expr: syn::Expr = syn::parse_str("(42)").unwrap();
    match infer_type_from_expr(&expr) {
        TypeInference::Inferred(ty) => assert_eq!(ty, "i32"),
        other => panic!(
            "Expected Inferred(i32), got {:?}",
            type_inference_debug(&other)
        ),
    }
}

#[test]
fn test_infer_function_call_unknown() {
    let expr: syn::Expr = syn::parse_str("foo(x)").unwrap();
    match infer_type_from_expr(&expr) {
        TypeInference::Unknown => {}
        other => panic!(
            "Expected Unknown for fn call, got {:?}",
            type_inference_debug(&other)
        ),
    }
}

#[test]
fn test_infer_option_constructor_call() {
    let expr: syn::Expr = syn::parse_str("Some(42u32)").unwrap();
    match infer_type_from_expr(&expr) {
        TypeInference::Inferred(ty) => assert_eq!(ty, "Option<u32>"),
        other => panic!(
            "Expected Inferred(Option<u32>), got {:?}",
            type_inference_debug(&other)
        ),
    }
}

#[test]
fn test_infer_explicit_option_none_path() {
    let expr: syn::Expr = syn::parse_str("Option::<u32>::None").unwrap();
    match infer_type_from_expr(&expr) {
        TypeInference::Inferred(ty) => assert_eq!(ty, "Option<u32>"),
        other => panic!(
            "Expected Inferred(Option<u32>), got {:?}",
            type_inference_debug(&other)
        ),
    }
}

#[test]
fn test_infer_explicit_result_constructor_call() {
    let expr: syn::Expr = syn::parse_str("Err::<u32, u32>(99)").unwrap();
    match infer_type_from_expr(&expr) {
        TypeInference::Inferred(ty) => assert_eq!(ty, "Result<u32, u32>"),
        other => panic!(
            "Expected Inferred(Result<u32, u32>), got {:?}",
            type_inference_debug(&other)
        ),
    }
}

#[test]
fn test_infer_method_call_unknown() {
    let expr: syn::Expr = syn::parse_str("x.abs()").unwrap();
    match infer_type_from_expr(&expr) {
        TypeInference::Unknown => {}
        other => panic!(
            "Expected Unknown for method call, got {:?}",
            type_inference_debug(&other)
        ),
    }
}

fn type_inference_debug(ti: &TypeInference) -> String {
    match ti {
        TypeInference::Inferred(ty) => format!("Inferred({})", ty),
        TypeInference::InferFromRef(name) => format!("InferFromRef({})", name),
        TypeInference::UnsupportedStringLiteral => "UnsupportedStringLiteral".to_string(),
        TypeInference::Unknown => "Unknown".to_string(),
    }
}
