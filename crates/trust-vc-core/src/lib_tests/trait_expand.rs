// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for trait_expand.rs: `expand_trait_spec` and `expand_trait_impl`.
//!
//! Coverage targets: trait parsing, contract extraction, type parameter
//! handling, error paths, and token-stream structure.

use super::*;
use crate::ir::TrustVcType;
use crate::trait_expand::{parse_trait_decl, parse_trait_impl_decl};

// ──── expand_trait_spec ──────────────────────────────────────────────────

#[test]
fn test_expand_trait_spec_basic_preserves_trait_definition() {
    let input: syn::ItemTrait = syn::parse2(quote! {
        trait Verifiable {
            fn check(&self) -> bool;
        }
    })
    .expect("parse basic trait");

    let expanded = expand_trait_spec(input);
    let expanded_str = expanded.to_string();

    // The original trait definition must survive in the output.
    assert!(
        expanded_str.contains("Verifiable"),
        "trait name must be preserved: {expanded_str}"
    );
    assert!(
        expanded_str.contains("fn check"),
        "trait method must be preserved: {expanded_str}"
    );
    // A hidden helper function must be emitted for the trait decl.
    assert!(
        expanded_str.contains("__trust_vc_trait_decl_"),
        "trait expansion must emit a hidden decl helper: {expanded_str}"
    );
}

#[test]
fn test_expand_trait_spec_with_contracts_strips_contract_attrs() {
    let input: syn::ItemTrait = syn::parse2(quote! {
        trait Bounded {
            #[trust_vc::requires(x > 0)]
            #[trust_vc::ensures(result >= 0)]
            fn transform(&self, x: i32) -> i32;
        }
    })
    .expect("parse trait with contracts");

    let expanded = expand_trait_spec(input);
    let expanded_str = expanded.to_string();

    // Contract attributes must be stripped from the output trait.
    assert!(
        !expanded_str.contains("trust_vc :: requires"),
        "requires attr must be stripped from output trait: {expanded_str}"
    );
    assert!(
        !expanded_str.contains("trust_vc :: ensures"),
        "ensures attr must be stripped from output trait: {expanded_str}"
    );
    // The hidden helper should still reference the trait name.
    assert!(
        expanded_str.contains("Bounded"),
        "trait name must survive stripping: {expanded_str}"
    );
}

#[test]
fn test_expand_trait_spec_generic_trait_parses_type_params() {
    let input: syn::ItemTrait = syn::parse2(quote! {
        trait Container<T> {
            fn get(&self, index: usize) -> T;
            fn len(&self) -> usize;
        }
    })
    .expect("parse generic trait");

    let expanded = expand_trait_spec(input);
    let expanded_str = expanded.to_string();

    // Must produce a valid token stream (no compile_error).
    assert!(
        !expanded_str.contains("compile_error"),
        "generic trait expansion must not error: {expanded_str}"
    );
    assert!(
        expanded_str.contains("Container"),
        "generic trait name must be preserved: {expanded_str}"
    );
}

// ──── expand_trait_impl ──────────────────────────────────────────────────

#[test]
fn test_expand_trait_impl_basic_preserves_impl_block() {
    let input: syn::ItemImpl = syn::parse2(quote! {
        impl Verifiable for MyStruct {
            fn check(&self) -> bool {
                true
            }
        }
    })
    .expect("parse basic trait impl");

    let expanded = expand_trait_impl(input);
    let expanded_str = expanded.to_string();

    assert!(
        expanded_str.contains("MyStruct"),
        "impl self type must be preserved: {expanded_str}"
    );
    assert!(
        expanded_str.contains("Verifiable"),
        "trait name must be preserved in impl: {expanded_str}"
    );
    assert!(
        expanded_str.contains("__trust_vc_trait_impl_decl_"),
        "trait impl expansion must emit a hidden impl decl helper: {expanded_str}"
    );
}

#[test]
fn test_expand_trait_impl_missing_trait_produces_compile_error() {
    // An impl block without `for Trait` (bare impl) must fail.
    let input: syn::ItemImpl = syn::parse2(quote! {
        impl MyStruct {
            fn helper(&self) -> bool {
                false
            }
        }
    })
    .expect("parse bare impl");

    let expanded = expand_trait_impl(input);
    let expanded_str = expanded.to_string();

    assert!(
        expanded_str.contains("compile_error"),
        "bare impl (no trait) must produce compile_error: {expanded_str}"
    );
    assert!(
        expanded_str.contains("impl Trait for Type"),
        "error message must explain the requirement: {expanded_str}"
    );
}

// ──── parse_trait_decl ───────────────────────────────────────────────────

#[test]
fn test_parse_trait_decl_extracts_method_signatures() {
    let input: syn::ItemTrait = syn::parse2(quote! {
        trait Arithmetic {
            fn add(&self, x: i32, y: i32) -> i32;
            fn negate(&self, x: i32) -> i32;
        }
    })
    .expect("parse arithmetic trait");

    let decl = parse_trait_decl(&input).expect("trait decl parsing should succeed");

    assert_eq!(decl.name, "Arithmetic");
    assert_eq!(decl.methods.len(), 2);

    let add = &decl.methods[0];
    assert_eq!(add.name, "add");
    // Receiver is skipped; only typed params remain.
    assert_eq!(add.params.len(), 2);
    assert_eq!(add.params[0].0, "x");
    assert_eq!(add.params[1].0, "y");
    assert_eq!(add.return_type, TrustVcType::Int { width: 32 });

    let negate = &decl.methods[1];
    assert_eq!(negate.name, "negate");
    assert_eq!(negate.params.len(), 1);
    // No supertrait bound → empty (the byte-identical fall-through preserving
    // all pre-unit-6 behaviour).
    assert!(decl.supertraits.is_empty());
}

#[test]
fn test_parse_trait_decl_extracts_supertraits() {
    // Unit 6: `trait T: Super + Other` parses both supertrait names (by last
    // path segment), so the supertrait-method `requires` closure can reach
    // their requires-bearing methods. `?Sized` and lifetime bounds are dropped.
    let input: syn::ItemTrait = syn::parse2(quote! {
        trait T: Super + Other + ?Sized {}
    })
    .expect("parse trait with supertraits");

    let decl = parse_trait_decl(&input).expect("trait decl parsing should succeed");

    assert_eq!(decl.name, "T");
    assert_eq!(
        decl.supertraits,
        vec!["Super".to_string(), "Other".to_string()],
        "both plain supertrait bounds must be parsed (last path segment); `?Sized` dropped"
    );
}

#[test]
fn test_parse_trait_decl_with_contracts_extracts_requires_ensures() {
    let input: syn::ItemTrait = syn::parse2(quote! {
        trait Positive {
            #[trust_vc::requires(x > 0)]
            #[trust_vc::ensures(result > 0)]
            fn double(&self, x: i32) -> i32;
        }
    })
    .expect("parse trait with contracts");

    let decl = parse_trait_decl(&input).expect("trait decl parsing should succeed");
    let method = &decl.methods[0];

    assert_eq!(method.requires, vec!["x > 0"]);
    assert_eq!(method.ensures, vec!["result > 0"]);
}

#[test]
fn test_parse_trait_decl_returns_binder_rewrites_ensures() {
    let input: syn::ItemTrait = syn::parse2(quote! {
        trait Positive {
            #[trust_vc::returns(ret)]
            #[trust_vc::ensures(ret > 0)]
            fn double(&self, x: i32) -> i32;
        }
    })
    .expect("parse trait with returns binder");

    let decl = parse_trait_decl(&input).expect("trait decl parsing should succeed");
    let method = &decl.methods[0];

    assert_eq!(method.ensures, vec!["result > 0"]);
}

#[test]
fn test_parse_trait_decl_returns_binder_rewrites_chained_ensures() {
    let input: syn::ItemTrait = syn::parse2(quote! {
        trait Bounded {
            #[trust_vc::returns(ret)]
            #[trust_vc::ensures(0 <= ret < limit)]
            fn clamp(&self, limit: i32) -> i32;
        }
    })
    .expect("parse trait with returns binder and chained ensures");

    let decl = parse_trait_decl(&input).expect("trait decl parsing should succeed");
    let method = &decl.methods[0];

    assert_eq!(method.ensures, vec!["(0 <= result) && (result < limit)"]);
}

#[test]
fn test_parse_trait_decl_returns_binder_respects_shadowed_ret_binders() {
    let input: syn::ItemTrait = syn::parse2(quote! {
        trait Shadowed {
            #[trust_vc::returns(ret)]
            #[trust_vc::ensures(ret > 0 && (|ret: i32| ret > 10)(x))]
            #[trust_vc::ensures(ret > 0 && (forall|ret: i32| ret > 10))]
            #[trust_vc::ensures((match x { ret => ret > 10 }) && ret > 0)]
            #[trust_vc::ensures(({ let ret = x; ret > 10 }) && ret > 0)]
            fn value(&self, x: i32) -> i32;
        }
    })
    .expect("parse trait with shadowed returns binder");

    let decl = parse_trait_decl(&input).expect("trait decl parsing should succeed");
    let method = &decl.methods[0];
    let compacted = method
        .ensures
        .iter()
        .map(|condition| condition.split_whitespace().collect::<String>())
        .collect::<Vec<_>>();

    assert_eq!(
        compacted,
        vec![
            "result>0&&(|ret:i32|ret>10)(x)",
            "result>0&&(forall(|ret:i32|ret>10))",
            "(matchx{ret=>ret>10})&&result>0",
            "({letret=x;ret>10})&&result>0",
        ]
    );
}

#[test]
fn test_parse_trait_decl_returns_expr_derives_ensures() {
    let input: syn::ItemTrait = syn::parse2(quote! {
        trait Next {
            #[trust_vc::returns(x + 1)]
            fn next(&self, x: i32) -> i32;
        }
    })
    .expect("parse trait with returns expression");

    let decl = parse_trait_decl(&input).expect("trait decl parsing should succeed");
    let method = &decl.methods[0];

    assert_eq!(method.ensures, vec!["result == x + 1"]);
}

#[test]
fn test_parse_trait_decl_returns_chained_expr_derives_normalized_ensures() {
    let input: syn::ItemTrait = syn::parse2(quote! {
        trait InRange {
            #[trust_vc::returns(0 <= x < limit)]
            fn in_range(&self, x: i32, limit: i32) -> bool;
        }
    })
    .expect("parse trait with returns chained expression");

    let decl = parse_trait_decl(&input).expect("trait decl parsing should succeed");
    let method = &decl.methods[0];

    assert_eq!(method.ensures, vec!["result == ((0 <= x) && (x < limit))"]);
}

#[test]
fn test_parse_trait_decl_default_body_extracted() {
    let input: syn::ItemTrait = syn::parse2(quote! {
        trait HasDefault {
            fn is_valid(&self) -> bool {
                true
            }
        }
    })
    .expect("parse trait with default body");

    let decl = parse_trait_decl(&input).expect("trait decl parsing should succeed");
    let method = &decl.methods[0];

    assert!(method.has_default);
    assert!(
        method.default_body.is_some(),
        "default body should be captured"
    );
    let body = method.default_body.as_ref().unwrap();
    assert!(
        body.contains("true"),
        "default body should contain 'true': {body}"
    );
}

#[test]
fn test_parse_trait_decl_generic_param_becomes_type_param() {
    let input: syn::ItemTrait = syn::parse2(quote! {
        trait Converter<T> {
            fn convert(&self, input: T) -> T;
        }
    })
    .expect("parse generic trait");

    let decl = parse_trait_decl(&input).expect("trait decl parsing should succeed");
    let method = &decl.methods[0];

    // The parameter `input: T` should resolve to TypeParam("T").
    assert_eq!(method.params[0].0, "input");
    assert_eq!(method.params[0].1, TrustVcType::TypeParam("T".to_string()));
    assert_eq!(method.return_type, TrustVcType::TypeParam("T".to_string()));
}

// ──── parse_trait_impl_decl ──────────────────────────────────────────────

#[test]
fn test_parse_trait_impl_decl_extracts_method_bindings() {
    let input: syn::ItemImpl = syn::parse2(quote! {
        impl Arithmetic for Calculator {
            fn add(&self, x: i32, y: i32) -> i32 {
                x + y
            }
            fn negate(&self, x: i32) -> i32 {
                -x
            }
        }
    })
    .expect("parse trait impl");

    let decl = parse_trait_impl_decl(&input).expect("trait impl decl parsing should succeed");

    assert_eq!(decl.trait_name, "Arithmetic");
    assert_eq!(decl.method_bindings.len(), 2);
    assert_eq!(decl.method_bindings[0].0, "add");
    assert_eq!(decl.method_bindings[0].1, "Calculator__add");
    assert_eq!(decl.method_bindings[1].0, "negate");
    assert_eq!(decl.method_bindings[1].1, "Calculator__negate");
}
