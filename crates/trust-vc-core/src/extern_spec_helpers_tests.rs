// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use quote::quote;
use syn::parse_quote;

#[test]
fn test_type_to_path_string() {
    let ty: Type = parse_quote!(std::vec::Vec);
    assert_eq!(type_to_path_string(&ty), Some("std::vec::Vec".to_string()));

    let ty: Type = parse_quote!(Option::<T>);
    assert_eq!(type_to_path_string(&ty), Some("Option".to_string()));

    let ty: Type = parse_quote!(&str);
    assert_eq!(type_to_path_string(&ty), None);
}

#[test]
fn test_extract_contracts_valid() {
    let attrs: Vec<Attribute> = vec![
        parse_quote!(#[requires(x > 0)]),
        parse_quote!(#[ensures(result > x)]),
        parse_quote!(#[doc = "test"]),
    ];
    let (requires, ensures) = extract_contracts(&attrs, "extern_spec").expect("should succeed");
    assert_eq!(requires, vec!["x > 0"]);
    assert_eq!(ensures, vec!["result > x"]);
}

#[test]
fn test_extract_contracts_valid_with_qualified_paths() {
    let attrs: Vec<Attribute> = vec![
        parse_quote!(#[trust_vc::requires(x > 0)]),
        parse_quote!(#[trust_vc::ensures(result > x)]),
    ];
    let (requires, ensures) = extract_contracts(&attrs, "extern_spec").expect("should succeed");
    assert_eq!(requires, vec!["x > 0"]);
    assert_eq!(ensures, vec!["result > x"]);
}

#[test]
fn test_extract_contracts_ignores_returns_binder() {
    let attrs: Vec<Attribute> = vec![
        parse_quote!(#[trust_vc::returns(ret)]),
        parse_quote!(#[trust_vc::ensures(ret > 0)]),
    ];
    let (requires, ensures) = extract_contracts(&attrs, "extern_spec").expect("should succeed");
    assert!(requires.is_empty());
    assert_eq!(ensures, vec!["ret > 0"]);
    assert_eq!(
        contract_attr_kind(&attrs[0]),
        Some(ContractAttrKind::Returns)
    );
}

#[test]
fn test_extract_contracts_rejects_bare_requires() {
    let attrs: Vec<Attribute> = vec![parse_quote!(#[requires])];
    let err =
        extract_contracts(&attrs, "extern_spec").expect_err("bare #[requires] should be rejected");
    assert!(
        err.to_string().contains("parenthesized form"),
        "error should mention parenthesized form, got: {err}"
    );
}

#[test]
fn test_extract_contracts_rejects_bare_ensures() {
    let attrs: Vec<Attribute> = vec![parse_quote!(#[ensures])];
    let err =
        extract_contracts(&attrs, "extern_spec").expect_err("bare #[ensures] should be rejected");
    assert!(
        err.to_string().contains("parenthesized form"),
        "error should mention parenthesized form, got: {err}"
    );
}

#[test]
fn test_extract_contracts_rejects_name_value_requires() {
    let attrs: Vec<Attribute> = vec![parse_quote!(#[requires = "x > 0"])];
    let err = extract_contracts(&attrs, "extern_spec")
        .expect_err("name-value #[requires] should be rejected");
    assert!(
        err.to_string().contains("parenthesized form"),
        "error should mention parenthesized form, got: {err}"
    );
}

#[test]
fn test_extract_contracts_rejects_name_value_ensures() {
    let attrs: Vec<Attribute> = vec![parse_quote!(#[ensures = "result > 0"])];
    let err = extract_contracts(&attrs, "extern_spec")
        .expect_err("name-value #[ensures] should be rejected");
    assert!(
        err.to_string().contains("parenthesized form"),
        "error should mention parenthesized form, got: {err}"
    );
}

#[test]
fn test_extract_contracts_ignores_non_trust_vc_namespaced_attrs() {
    let attrs: Vec<Attribute> = vec![
        parse_quote!(#[other::requires(x > 0)]),
        parse_quote!(#[trust_vc::requires(y > 0)]),
        parse_quote!(#[other::ensures(result > 1)]),
        parse_quote!(#[ensures(result > 2)]),
    ];
    let (requires, ensures) = extract_contracts(&attrs, "extern_spec").expect("should succeed");
    assert_eq!(requires, vec!["y > 0"]);
    assert_eq!(ensures, vec!["result > 2"]);
}

#[test]
fn test_extract_contracts_uses_surface_specific_error_message() {
    let attrs: Vec<Attribute> = vec![parse_quote!(#[requires = "x > 0"])];
    let err = extract_contracts(&attrs, "trait_spec").expect_err("should fail");
    let text = err.to_string();
    assert!(text.contains("trait_spec"));
    assert!(!text.contains("extern_spec"));
}

#[test]
fn test_extract_param_names_collects_typed_inputs() {
    let sig: Signature = parse_quote!(fn rotate_left(self, shift: u32, carry: bool) -> u32);
    let names = extract_param_names(&sig, "extern_spec").expect("parameter names should parse");
    assert_eq!(names, vec!["shift", "carry"]);
}

#[test]
fn test_extract_param_names_rejects_patterns() {
    let sig: Signature = parse_quote!(fn pair((lhs, rhs): (u32, u32)) -> u32);
    let err = extract_param_names(&sig, "extern_spec").expect_err("patterns should fail");
    assert!(err
        .to_string()
        .contains("extern_spec parameters must use simple identifiers"));
}

#[test]
fn test_encode_ident_component_injective() {
    let a = encode_ident_component("foo::bar");
    let b = encode_ident_component("foo_bar");
    assert_ne!(a, b, "foo::bar and foo_bar must produce distinct encodings");

    let c = encode_ident_component("Vec<T>");
    let d = encode_ident_component("Vec_T_");
    assert_ne!(c, d, "Vec<T> and Vec_T_ must produce distinct encodings");
}

#[test]
fn test_encode_ident_component_roundtrip_chars() {
    assert_eq!(
        encode_ident_component("std::vec::Vec"),
        "std_P__P_vec_P__P_Vec"
    );
    assert_eq!(encode_ident_component("Option"), "Option");
    assert_eq!(encode_ident_component("foo_bar"), "foo__bar");
}

#[test]
fn test_generate_stub_ident_injective() {
    let a = generate_stub_ident("foo::bar", "method", Span::call_site());
    let b = generate_stub_ident("foo_bar", "method", Span::call_site());
    assert_ne!(
        a.to_string(),
        b.to_string(),
        "stub idents for foo::bar and foo_bar must differ"
    );
}

#[test]
fn test_transform_sig_replaces_self_in_params() {
    let sig: Signature = parse_quote!(fn merge(&self, other: Option<Self>) -> Self);
    let self_ty: Type = parse_quote!(MyType);

    let stub_sig = transform_sig_for_stub(&sig, &self_ty);
    let output = quote!(#stub_sig).to_string();

    assert!(
        output.contains("Option < MyType >"),
        "Self in param type should be replaced: {output}"
    );
    assert!(
        output.contains("-> MyType"),
        "Self in return type should be replaced: {output}"
    );
    assert!(
        !output.contains("Self"),
        "no bare Self should remain: {output}"
    );
}

#[test]
fn test_transform_sig_replaces_self_in_nested_generics() {
    let sig: Signature = parse_quote!(fn process(&self, pairs: Vec<(Self, &Self)>) -> Self);
    let self_ty: Type = parse_quote!(Foo);

    let stub_sig = transform_sig_for_stub(&sig, &self_ty);
    let output = quote!(#stub_sig).to_string();

    assert!(
        !output.contains("Self"),
        "nested Self references should be replaced: {output}"
    );
}

#[test]
fn test_transform_sig_preserves_receiver_lifetime() {
    let sig: Signature = parse_quote!(fn get<'a>(&'a self) -> &'a str);
    let self_ty: Type = parse_quote!(String);

    let stub_sig = transform_sig_for_stub(&sig, &self_ty);
    let output = quote!(#stub_sig).to_string();

    assert!(output.contains("'a"));
    assert!(output.contains("String"));
}
