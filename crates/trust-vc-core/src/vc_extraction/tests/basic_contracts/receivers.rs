// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::*;

#[test]
fn test_extract_self_receiver_binding() {
    let input: syn::FnArg = syn::parse_quote!(self);
    let vars = extract_vars_from_input(&input).unwrap();

    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].0, "self");
    assert_eq!(vars[0].1, "Self");
}

#[test]
fn test_extract_self_receiver_in_verification_context() {
    let func: syn::ItemFn = syn::parse_quote! {
        fn method(self, x: i32) {
            let _ = x;
        }
    };
    let vc = extract_verification_conditions(&func).unwrap();

    assert!(
        vc.variables
            .iter()
            .any(|v| v.name == "self" && v.ty == crate::ir::TrustVcType::Opaque("Self".to_string())),
        "full VC extraction should register `self` receivers"
    );
    assert!(
        vc.variables
            .iter()
            .any(|v| v.name == "x" && v.ty == crate::ir::TrustVcType::Int { width: 32 }),
        "full VC extraction should keep typed parameters alongside receivers"
    );
}

#[test]
fn test_extract_ref_self_receiver_binding() {
    let input: syn::FnArg = syn::parse_quote!(&self);
    let vars = extract_vars_from_input(&input).unwrap();

    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].0, "self");
    assert_eq!(vars[0].1, "&Self");
}

#[test]
fn test_extract_ref_self_receiver_in_verification_context() {
    let func: syn::ItemFn = syn::parse_quote! {
        fn method(&self, x: &i32) {
            let _ = x;
        }
    };
    let vc = extract_verification_conditions(&func).unwrap();

    assert!(
        vc.variables.iter().any(|v| {
            v.name == "self" && v.ty == crate::ir::TrustVcType::Opaque("Self".to_string())
        }),
        "full VC extraction should register `&self` receivers as their erased referent type"
    );
    assert!(
        vc.is_erased_shared_ref_var("self"),
        "`&self` receivers should be tracked as erased immutable references"
    );
    assert!(
        vc.variables
            .iter()
            .any(|v| v.name == "x" && v.ty == crate::ir::TrustVcType::Int { width: 32 }),
        "reference parameters should bind through full receiver extraction as their erased referent type"
    );
    assert!(
        vc.is_erased_shared_ref_var("x"),
        "`&T` parameters should be tracked as erased immutable references"
    );
}

#[test]
fn test_extract_mut_ref_self_receiver_binding() {
    let input: syn::FnArg = syn::parse_quote!(&mut self);
    let vars = extract_vars_from_input(&input).unwrap();

    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].0, "self");
    assert_eq!(vars[0].1, "&mutSelf");
}

#[test]
fn test_extract_mut_ref_self_receiver_in_verification_context() {
    let func: syn::ItemFn = syn::parse_quote! {
        fn method(&mut self, x: i32) {
            let _ = x;
        }
    };
    let vc = extract_verification_conditions(&func).unwrap();

    assert!(
        vc.variables.iter().any(|v| {
            v.name == "self" && v.ty == crate::ir::TrustVcType::Opaque("Self".to_string())
        }),
        "full VC extraction should register `&mut self` receivers as their referent type"
    );
    assert!(
        !vc.is_erased_shared_ref_var("self"),
        "`&mut self` receivers must not be marked as erased immutable references"
    );
    assert!(
        vc.variables
            .iter()
            .any(|v| v.name == "x" && v.ty == crate::ir::TrustVcType::Int { width: 32 }),
        "mutable receiver extraction should not drop sibling typed parameters"
    );
}
