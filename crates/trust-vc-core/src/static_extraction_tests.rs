// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the static proof extraction and merge-bundle emission pipeline.
//!
//! Split from `static_extraction.rs` for the 500-line limit (#2621).

use super::*;
use crate::context_management::with_clean_thread_locals;
use crate::encoder::tests::expect_counterexample;
use crate::vc::ObligationKind;
use crate::verification_bridge::VerificationPipeline;
use crate::verify_macro::{collect_obligation, collect_variable};
use crate::VerifyResult;
use quote::quote;
use trust_vc_merge_contract::MERGE_BUNDLE_VERSION;

fn parse_attrs(code: &str) -> Vec<syn::Attribute> {
    let item: syn::ItemFn = syn::parse_str(code).expect("parse test function");
    item.attrs
}

fn collect_runtime_contract_pipeline(item: &syn::ItemFn) -> VerificationPipeline {
    let mut_ref_transform = crate::mut_ref_proof::transform_proof_body(&item.sig, &item.block);

    for arg in &item.sig.inputs {
        let syn::FnArg::Typed(pat_type) = arg else {
            continue;
        };
        let syn::Pat::Ident(pat_ident) = pat_type.pat.as_ref() else {
            continue;
        };
        let param_name = pat_ident.ident.to_string();
        if mut_ref_transform.skipped_params.contains(&param_name) {
            continue;
        }
        collect_variable(
            param_name,
            crate::local_vars::extract_type_string(&pat_type.ty),
        );
    }

    let (requires, ensures) = crate::contract_registry::extract_contracts_from_block(&item.block);
    for (index, condition) in requires.iter().enumerate() {
        collect_obligation(
            ObligationKind::Requires,
            format!("runtime_requires_{index}"),
            condition.clone(),
            None,
        );
    }
    for (index, condition) in ensures.iter().enumerate() {
        collect_obligation(
            ObligationKind::Ensures,
            format!("runtime_ensures_{index}"),
            condition.clone(),
            None,
        );
    }

    VerificationPipeline::collect_from_macros()
}

#[test]
fn test_extract_static_proof_context_full_metadata() {
    let attrs = parse_attrs(
        r#"
            #[doc = "trust_vc:proof"]
            #[doc = "trust_vc:proof:tracked=token"]
            #[doc = "trust_vc:requires:x > 0"]
            #[doc = "trust_vc:ensures:x >= 1"]
            #[doc = "trust_vc:param:x:u64"]
            fn lemma_positive(x: u64) {}
            "#,
    );

    let context = extract_static_proof_context(&attrs, "lemma_positive")
        .expect("metadata extraction should succeed")
        .expect("proof metadata should be present");

    assert_eq!(context.fn_name, "lemma_positive");
    assert_eq!(context.params, vec![("x".to_string(), "u64".to_string())]);
    assert_eq!(context.requires, vec!["x > 0"]);
    assert_eq!(context.ensures, vec!["x >= 1"]);
    assert_eq!(context.tracked_params, vec!["token"]);
}

#[test]
fn test_extract_static_proof_context_param_without_type_fails() {
    let attrs = parse_attrs(
        r#"
            #[doc = "trust_vc:proof"]
            #[doc = "trust_vc:param:x"]
            fn lemma_positive(x: u64) {}
            "#,
    );

    let err = extract_static_proof_context(&attrs, "lemma_positive")
        .expect_err("malformed param metadata should fail closed");
    assert!(
        err.to_string().contains("missing type"),
        "unexpected error: {err}"
    );
}

#[test]
fn test_extract_static_proof_context_contracts_without_proof_marker_fail() {
    let attrs = parse_attrs(
        r#"
            #[doc = "trust_vc:requires:x > 0"]
            fn lemma_positive(x: u64) {}
            "#,
    );

    let err = extract_static_proof_context(&attrs, "lemma_positive")
        .expect_err("contract metadata without proof marker should fail closed");
    assert!(
        err.to_string().contains("without trust_vc:proof marker"),
        "unexpected error: {err}"
    );
}

#[test]
fn test_verify_from_static_context_verifies_simple_contract() {
    let context = StaticProofContext {
        fn_name: "lemma_positive".to_string(),
        params: vec![("x".to_string(), "u64".to_string())],
        requires: vec!["x > 0".to_string()],
        ensures: vec!["x >= 1".to_string()],
        tracked_params: Vec::new(),
    };

    let result =
        verify_from_static_context(&context).expect("static verification should return a result");
    assert_eq!(result, VerifyResult::Verified);
}

#[test]
fn test_emit_merge_bundle_produces_v4_bundle() {
    let context = StaticProofContext {
        fn_name: "lemma_positive".to_string(),
        params: vec![("x".to_string(), "u64".to_string())],
        requires: vec!["x > 0".to_string()],
        ensures: vec!["x >= 1".to_string()],
        tracked_params: Vec::new(),
    };

    let bundle = emit_merge_bundle(&context).expect("bundle emission should succeed");
    assert_eq!(bundle.bundle_version(), MERGE_BUNDLE_VERSION);
    assert_eq!(bundle.source_id(), "trust_vc::static::lemma_positive");
    assert_eq!(bundle.variables(), &[VarDecl::new("x", SortMeta::MathInt)]);
    assert_eq!(
        bundle.assumptions(),
        &[
            TypedExpr::new("(<= 0 x)", SortMeta::Bool),
            TypedExpr::new("(< x 18446744073709551616)", SortMeta::Bool),
            TypedExpr::new("(> x 0)", SortMeta::Bool),
        ]
    );
    assert_eq!(
        bundle.assertions(),
        &[TypedExpr::new("(>= x 1)", SortMeta::Bool)]
    );
}

fn verify_result_status(result: &VerifyResult) -> &'static str {
    match result {
        VerifyResult::Verified => "verified",
        VerifyResult::Counterexample { .. } => "counterexample",
        VerifyResult::NotProved { .. } => "not-proved",
        VerifyResult::Unknown { .. } => "unknown",
        VerifyResult::Error { .. } => "error",
    }
}

#[test]
fn test_static_extraction_to_merge_bundle_round_trip() {
    let context = StaticProofContext {
        fn_name: "lemma_positive".to_string(),
        params: vec![("x".to_string(), "u64".to_string())],
        requires: vec!["x > 0".to_string()],
        ensures: vec!["x >= 1".to_string()],
        tracked_params: Vec::new(),
    };

    let bundle = emit_merge_bundle(&context).expect("bundle emission should succeed");
    let json = bundle
        .to_pretty_json()
        .expect("bundle serialization should succeed");
    let roundtrip =
        MergeBundle::from_json_str(&json).expect("bundle deserialization should succeed");
    let verdict = trust_vc_merge_runner::run_bundle(&roundtrip, "round_trip", "ay")
        .expect("merge runner should accept the round-trip bundle");

    let direct =
        verify_from_static_context(&context).expect("static verification should return a result");
    assert_eq!(
        verdict.status(),
        verify_result_status(&direct),
        "merge bundle round-trip must match direct static verification"
    );
    assert_eq!(verdict.status(), "verified");
}

#[test]
fn test_emit_merge_bundle_adds_nat_domain_guard() {
    let context = StaticProofContext {
        fn_name: "lemma_nat".to_string(),
        params: vec![("n".to_string(), "nat".to_string())],
        requires: Vec::new(),
        ensures: vec!["n >= 0".to_string()],
        tracked_params: Vec::new(),
    };

    let bundle = emit_merge_bundle(&context).expect("bundle emission should succeed");
    assert_eq!(
        bundle.assumptions(),
        &[TypedExpr::new("(>= n 0)", SortMeta::Bool)]
    );
}

#[test]
fn test_emit_merge_bundle_rejects_bv_arithmetic_conditions() {
    let context = StaticProofContext {
        fn_name: "lemma_overflow".to_string(),
        params: vec![
            ("x".to_string(), "u32".to_string()),
            ("y".to_string(), "u32".to_string()),
        ],
        requires: vec!["x > 0".to_string(), "y > 0".to_string()],
        ensures: vec!["x + y > 0".to_string()],
        tracked_params: Vec::new(),
    };

    let direct = verify_from_static_context(&context)
        .expect("direct static verification should return a result");
    expect_counterexample(&direct, "u32 overflow case");

    let err = emit_merge_bundle(&context)
        .expect_err("overflow-sensitive BV arithmetic should fail closed");
    assert!(
        err.to_string()
            .contains("does not support arithmetic over finite-width integer parameters"),
        "unexpected error: {err}"
    );
}

#[test]
fn test_static_and_runtime_paths_verify_same_expanded_contracts() {
    with_clean_thread_locals(|| {
        let input: syn::ItemFn = syn::parse2(quote! {
            fn lemma_positive(x: u64) {
                trust_vc::requires!(x > 0);
                trust_vc::ensures!(x >= 1);
            }
        })
        .expect("parse proof fn");
        let runtime_item = input.clone();

        let expanded = crate::expand_proof_with_tracked(input, &[]);
        let generated: syn::ItemFn =
            syn::parse2(expanded).expect("proof expansion should stay parseable");
        let static_context =
            extract_static_proof_context(&generated.attrs, &generated.sig.ident.to_string())
                .expect("static metadata extraction should succeed")
                .expect("static proof context should exist");

        let static_result = verify_from_static_context(&static_context)
            .expect("static verification should return a result");
        let runtime_pipeline = collect_runtime_contract_pipeline(&runtime_item);
        let runtime_result = runtime_pipeline.verify();

        assert_eq!(static_result, VerifyResult::Verified);
        assert_eq!(runtime_result, VerifyResult::Verified);
        assert_eq!(static_result, runtime_result);
        assert_eq!(runtime_pipeline.context().variables().len(), 1);
        assert_eq!(runtime_pipeline.context().obligations().len(), 2);
    });
}
