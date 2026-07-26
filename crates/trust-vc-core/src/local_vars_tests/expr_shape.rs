//! Tests for extract_type_string, extract_first_ident, and wrapper erasure.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// --- extract_type_string tests ---

#[test]
fn test_extract_type_string_primitive_i32() {
    let ty: syn::Type = syn::parse_str("i32").unwrap();
    assert_eq!(extract_type_string(&ty), "i32");
}

#[test]
fn test_extract_type_string_primitive_u64() {
    let ty: syn::Type = syn::parse_str("u64").unwrap();
    assert_eq!(extract_type_string(&ty), "u64");
}

#[test]
fn test_extract_type_string_bool() {
    let ty: syn::Type = syn::parse_str("bool").unwrap();
    assert_eq!(extract_type_string(&ty), "bool");
}

#[test]
fn test_extract_type_string_generic_seq() {
    let ty: syn::Type = syn::parse_str("Seq<i32>").unwrap();
    assert_eq!(extract_type_string(&ty), "Seq<i32>");
}

#[test]
fn test_extract_type_string_generic_set() {
    let ty: syn::Type = syn::parse_str("Set<u64>").unwrap();
    assert_eq!(extract_type_string(&ty), "Set<u64>");
}

#[test]
fn test_extract_type_string_generic_map() {
    let ty: syn::Type = syn::parse_str("Map<i32, bool>").unwrap();
    // Spaces removed by replace(' ', "")
    assert_eq!(extract_type_string(&ty), "Map<i32,bool>");
}

#[test]
fn test_extract_type_string_reference() {
    let ty: syn::Type = syn::parse_str("&i32").unwrap();
    assert_eq!(extract_type_string(&ty), "i32");
}

#[test]
fn test_extract_type_string_mut_reference() {
    let ty: syn::Type = syn::parse_str("&mut u64").unwrap();
    assert_eq!(extract_type_string(&ty), "u64");
}

// --- extract_first_ident tests ---

#[test]
fn test_extract_first_ident_variable() {
    let expr: syn::Expr = syn::parse_str("x").unwrap();
    assert_eq!(extract_first_ident(&expr), Some("x".to_string()));
}

#[test]
fn test_extract_first_ident_paren() {
    let expr: syn::Expr = syn::parse_str("(y)").unwrap();
    assert_eq!(extract_first_ident(&expr), Some("y".to_string()));
}

#[test]
fn test_extract_first_ident_literal() {
    let expr: syn::Expr = syn::parse_str("42").unwrap();
    assert_eq!(extract_first_ident(&expr), None);
}

#[test]
fn test_extract_first_ident_function_call() {
    let expr: syn::Expr = syn::parse_str("foo(x)").unwrap();
    assert_eq!(extract_first_ident(&expr), None);
}

// --- Ghost/Tracked wrapper erasure (Part of #2427) ---

#[test]
fn test_extract_type_string_tracked_u32_erases() {
    let ty: syn::Type = syn::parse_str("Tracked<u32>").unwrap();
    assert_eq!(extract_type_string(&ty), "u32");
}

#[test]
fn test_extract_type_string_ghost_bool_erases() {
    let ty: syn::Type = syn::parse_str("Ghost<bool>").unwrap();
    assert_eq!(extract_type_string(&ty), "bool");
}

#[test]
fn test_extract_type_string_tracked_seq_erases_wrapper_only() {
    let ty: syn::Type = syn::parse_str("Tracked<Seq<i32>>").unwrap();
    assert_eq!(extract_type_string(&ty), "Seq<i32>");
}

#[test]
fn test_extract_type_string_ref_tracked_erases_both() {
    let ty: syn::Type = syn::parse_str("&Tracked<u64>").unwrap();
    assert_eq!(extract_type_string(&ty), "u64");
}

#[test]
fn test_extract_type_string_ghost_string_erases() {
    let ty: syn::Type = syn::parse_str("Ghost<String>").unwrap();
    assert_eq!(extract_type_string(&ty), "String");
}

#[test]
fn test_extract_type_string_qualified_proph_erases() {
    let ty: syn::Type = syn::parse_str("trust_vc_types::Proph<u64>").unwrap();
    assert_eq!(extract_type_string(&ty), "u64");
}

#[test]
fn test_extract_type_string_qualified_tracked_erases() {
    let ty: syn::Type = syn::parse_str("trust_vc_types::Tracked<Seq<i32>>").unwrap();
    assert_eq!(extract_type_string(&ty), "Seq<i32>");
}

#[test]
fn test_extract_type_string_snapshot_u32_erases() {
    let ty: syn::Type = syn::parse_str("Snapshot<u32>").unwrap();
    assert_eq!(extract_type_string(&ty), "u32");
}

#[test]
fn test_extract_type_string_snapshot_seq_erases_wrapper_only() {
    let ty: syn::Type = syn::parse_str("Snapshot<Seq<i32>>").unwrap();
    assert_eq!(extract_type_string(&ty), "Seq<i32>");
}
