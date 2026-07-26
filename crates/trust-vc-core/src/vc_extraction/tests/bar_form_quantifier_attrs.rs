// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Bar-delimited Verus quantifier closures in contract attributes.
//!
//! Verus's canonical surface for quantifiers is the bar-delimited closure form
//! `exists |n: T| body` / `forall |n: T| body` (un-parenthesized). The
//! call-form `exists(|n: T| body)` is the desugared shape that plain `syn`
//! accepts. Contract-attribute extraction must accept the bar form and lower it
//! identically to the call form, so that helper-call discovery over `#[requires]`
//! / `#[ensures]` attributes sees the same calls regardless of which surface the
//! contract used.
//!
//! This pins the fix for the parse gap where
//! `#[ensures(exists |n: nat| #[trigger] nat_to_real(n) >= x)]` failed in
//! [`referenced_target_contract_calls`] with "Failed to parse target contract
//! attribute ... unexpected token", while the call form parsed.

use super::super::*;
use quote::ToTokens;

/// Build a single `#[ensures(..)]` attribute carrying `body` verbatim.
fn ensures_attr(body: &str) -> syn::Attribute {
    let item: syn::ItemFn = syn::parse_str(&format!("#[ensures({body})] fn target() {{}}"))
        .expect("synthetic #[ensures] function should parse as an ItemFn");
    item.attrs
        .into_iter()
        .next()
        .expect("synthetic function should carry exactly one attribute")
}

/// Build an `ItemFn` whose only attribute is `#[ensures(<contract>)]`.
fn target_with_ensures(contract: &str) -> syn::ItemFn {
    syn::parse_str(&format!("#[ensures({contract})] fn target() {{}}"))
        .expect("synthetic #[ensures] function should parse as an ItemFn")
}

#[test]
fn bar_form_exists_ensures_parses() {
    let attr = ensures_attr("exists |n: nat| #[trigger] nat_to_real(n) >= x");
    let expr = contract_attribute_expr(&attr)
        .expect("bar-delimited exists closure must parse in a contract attribute");
    // The lowered form is the call form `exists(|n: nat| ...)`.
    assert!(
        matches!(&expr, syn::Expr::Call(_)),
        "bar-form exists must lower to a call expression, got: {}",
        expr.to_token_stream()
    );
}

#[test]
fn bar_form_exists_lowers_identically_to_call_form() {
    let bar = contract_attribute_expr(&ensures_attr(
        "exists |n: nat| #[trigger] nat_to_real(n) >= x",
    ))
    .expect("bar-form exists must parse");
    let call = contract_attribute_expr(&ensures_attr(
        "exists(|n: nat| #[trigger] nat_to_real(n) >= x)",
    ))
    .expect("call-form exists must parse");

    assert_eq!(
        bar.to_token_stream().to_string(),
        call.to_token_stream().to_string(),
        "bar-form exists must lower to the same AST as the call form"
    );
}

#[test]
fn bar_form_forall_lowers_identically_to_call_form() {
    let bar = contract_attribute_expr(&ensures_attr("forall |i: int| i + 0 == i"))
        .expect("bar-form forall must parse");
    let call = contract_attribute_expr(&ensures_attr("forall(|i: int| i + 0 == i)"))
        .expect("call-form forall must parse");

    assert_eq!(
        bar.to_token_stream().to_string(),
        call.to_token_stream().to_string(),
        "bar-form forall must lower to the same AST as the call form"
    );
}

/// Build a verifiable function whose `#[trust_vc::ensures(..)]` carries
/// `contract`, and return the postcondition obligation conditions extracted by
/// the production contract-attribute path.
fn ensures_postconditions(contract: &str) -> Vec<String> {
    let func: syn::ItemFn = syn::parse_str(&format!(
        "#[trust_vc::ensures({contract})] fn target(x: real) {{}}"
    ))
    .expect("synthetic ensures function should parse");
    let vc =
        extract_verification_conditions(&func).expect("bar/call-form ensures must extract cleanly");
    vc.obligations
        .iter()
        .filter(|o| matches!(o.kind, crate::vc::ObligationKind::Assert))
        .map(|o| o.condition.clone())
        .collect()
}

#[test]
fn bar_form_exists_ensures_lowers_to_same_postcondition_as_call_form() {
    let bar = ensures_postconditions("exists |n: nat| #[trigger] nat_to_real(n) >= x");
    let call = ensures_postconditions("exists(|n: nat| #[trigger] nat_to_real(n) >= x)");
    assert_eq!(
        bar, call,
        "bar-form exists ensures must produce the same postcondition obligation as the call form"
    );
    assert!(
        !bar.is_empty(),
        "bar-form exists ensures must yield a postcondition obligation, not silently drop it"
    );
}

#[test]
fn bar_form_exists_extracts_same_helper_calls_as_call_form() {
    let bar_calls = referenced_target_contract_calls(&target_with_ensures(
        "exists |n: nat| #[trigger] nat_to_real(n) >= x",
    ))
    .expect("bar-form exists contract must yield helper calls");
    let call_calls = referenced_target_contract_calls(&target_with_ensures(
        "exists(|n: nat| #[trigger] nat_to_real(n) >= x)",
    ))
    .expect("call-form exists contract must yield helper calls");

    assert_eq!(
        bar_calls, call_calls,
        "bar-form and call-form exists must surface identical helper calls"
    );
    assert!(
        bar_calls
            .iter()
            .any(|reference| reference.source_path == "nat_to_real"),
        "helper call `nat_to_real` must be discovered inside the bar-form exists body, got: {bar_calls:?}"
    );
}
