// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::bridge_proof_statements;
use quote::quote;

fn rewrite(block_src: &str) -> String {
    let block: syn::Block = syn::parse_str(block_src).expect("test block should parse");
    let rewritten = bridge_proof_statements(&block).expect("bridge should rewrite block");
    quote!(#rewritten).to_string()
}

#[test]
fn bridge_rewrites_prophecy_round_trip_statements() {
    let rewritten = rewrite(
        "{ let p: Proph<u64> = Proph::<u64>::new(); let v: u64 = p.view(); p.resolve(v); }",
    );

    assert!(
        rewritten.contains("register_prophecy_local"),
        "new() binding should register prophecy local: {rewritten}"
    );
    assert!(
        rewritten.contains("collect_symbolic_let_binding_expr"),
        "view() binding should become a symbolic let assumption: {rewritten}"
    );
    assert!(
        rewritten.contains("collect_symbolic_assume_expr"),
        "resolve() should become a symbolic assume: {rewritten}"
    );
    assert!(
        rewritten.contains("if false { let _ : u64 = p . view () ; }")
            || rewritten.contains("if false { let _: u64 = p . view () ; }"),
        "view() rewrite should preserve type-checking without runtime execution: {rewritten}"
    );
    assert!(
        rewritten.contains("if false { p . resolve (v) ; }"),
        "resolve() rewrite should preserve type-checking without runtime execution: {rewritten}"
    );
    assert!(
        !rewritten.contains("let v : u64 = p . view () ;"),
        "live runtime view() call should be removed from the block: {rewritten}"
    );
}

#[test]
fn bridge_rewrites_nested_block_arguments() {
    let rewritten = rewrite(
        "{ consume({ let p: Proph<u64> = Proph::<u64>::new(); let v: u64 = p.view(); p.resolve(v); 0u64 }); }",
    );

    assert!(
        rewritten.contains("consume ({ let p : Proph < u64 > = Proph :: < u64 > :: new () ;")
            || rewritten.contains("consume({ let p : Proph < u64 > = Proph :: < u64 > :: new () ;"),
        "nested block argument should remain present after rewriting: {rewritten}"
    );
    assert!(
        rewritten.contains("register_prophecy_local"),
        "nested block arguments should still register prophecy locals: {rewritten}"
    );
    assert!(
        rewritten.contains("collect_symbolic_let_binding_expr"),
        "nested block arguments should still bridge view() bindings: {rewritten}"
    );
    assert!(
        rewritten.contains("collect_symbolic_assume_expr"),
        "nested block arguments should still bridge resolve() calls: {rewritten}"
    );
}

#[test]
fn bridge_rejects_control_flow_over_bridged_local() {
    let block: syn::Block = syn::parse_str(
        "{ let p: Proph<u64> = Proph::<u64>::new(); let v: u64 = p.view(); if v > 0 { trust_vc::assert!(true); } }",
    )
    .expect("test block should parse");

    let err = bridge_proof_statements(&block)
        .err()
        .expect("bridged locals in control flow must fail");
    assert!(
        err.to_string().contains("straight-line proof use"),
        "diagnostic should explain the control-flow restriction: {err}"
    );
}

#[test]
fn bridge_rejects_nested_control_flow_over_bridged_local() {
    let block: syn::Block = syn::parse_str(
        "{ let p: Proph<u64> = Proph::<u64>::new(); let v: u64 = p.view(); consume(if v > 0u64 { 1u64 } else { 0u64 }); }",
    )
    .expect("test block should parse");

    let err = bridge_proof_statements(&block)
        .err()
        .expect("nested control flow over bridged locals must fail");
    assert!(
        err.to_string().contains("if condition"),
        "diagnostic should identify the nested control-flow position: {err}"
    );
}

#[test]
fn bridge_rejects_control_flow_with_bridged_local_introduced_in_condition_block() {
    let block: syn::Block = syn::parse_str(
        "{ if { let p: Proph<u64> = Proph::<u64>::new(); let v: u64 = p.view(); v > 0u64 } { trust_vc::assert!(true); } }",
    )
    .expect("test block should parse");

    let err = bridge_proof_statements(&block)
        .err()
        .expect("condition blocks that derive guards from bridged locals must fail");
    assert!(
        err.to_string().contains("prophecy method `p.view(...)`"),
        "diagnostic should identify the raw prophecy call introduced inside the condition block: {err}"
    );
}

#[test]
fn bridge_rejects_aliased_control_flow_over_bridged_local() {
    let block: syn::Block = syn::parse_str(
        "{ let p: Proph<u64> = Proph::<u64>::new(); let v: u64 = p.view(); let alias: u64 = v; if alias > 0u64 { trust_vc::assert!(true); } }",
    )
    .expect("test block should parse");

    let err = bridge_proof_statements(&block)
        .err()
        .expect("aliased bridged locals in control flow must fail");
    assert!(
        err.to_string().contains("`alias`"),
        "diagnostic should identify the aliased local name: {err}"
    );
}

#[test]
fn bridge_rejects_assigned_control_flow_over_bridged_local() {
    let block: syn::Block = syn::parse_str(
        "{ let p: Proph<u64> = Proph::<u64>::new(); let v: u64 = p.view(); let mut alias: u64 = 0u64; alias = v; if alias > 0u64 { trust_vc::assert!(true); } }",
    )
    .expect("test block should parse");

    let err = bridge_proof_statements(&block)
        .err()
        .expect("assigned bridged locals in control flow must fail");
    assert!(
        err.to_string().contains("`alias`"),
        "diagnostic should identify the assigned local name: {err}"
    );
}

#[test]
fn bridge_allows_control_flow_after_plain_assignment_clears_bridged_local() {
    let block: syn::Block = syn::parse_str(
        "{ let p: Proph<u64> = Proph::<u64>::new(); let v: u64 = p.view(); let mut alias: u64 = v; alias = 0u64; if alias > 0u64 { trust_vc::assert!(true); } }",
    )
    .expect("test block should parse");

    bridge_proof_statements(&block)
        .expect("plain assignment from a concrete expression should clear bridged-local state");
}

#[test]
fn bridge_rejects_compound_assignment_control_flow_over_bridged_local() {
    let block: syn::Block = syn::parse_str(
        "{ let p: Proph<u64> = Proph::<u64>::new(); let v: u64 = p.view(); let mut alias: u64 = 1u64; alias += v; if alias > 0u64 { trust_vc::assert!(true); } }",
    )
    .expect("test block should parse");

    let err = bridge_proof_statements(&block)
        .err()
        .expect("compound-assigned bridged locals in control flow must fail");
    assert!(
        err.to_string().contains("`alias`"),
        "diagnostic should identify the compound-assigned local name: {err}"
    );
}

#[test]
fn bridge_rejects_match_guard_over_bridged_local() {
    let block: syn::Block = syn::parse_str(
        "{ let p: Proph<u64> = Proph::<u64>::new(); let v: u64 = p.view(); match 0u64 { 0u64 if v > 0u64 => trust_vc::assert!(true), _ => trust_vc::assert!(true), } }",
    )
    .expect("test block should parse");

    let err = bridge_proof_statements(&block)
        .err()
        .expect("match guards over bridged locals must fail");
    assert!(
        err.to_string().contains("match guard"),
        "diagnostic should identify the guarded control-flow position: {err}"
    );
}

#[test]
fn bridge_rejects_let_else_over_bridged_local() {
    let block: syn::Block = syn::parse_str(
        "{ let p: Proph<bool> = Proph::<bool>::new(); let b: bool = p.view(); let true = b else { trust_vc::assert!(false); }; }",
    )
    .expect("test block should parse");

    let err = bridge_proof_statements(&block)
        .err()
        .expect("let-else over bridged locals must fail");
    assert!(
        err.to_string().contains("let-else initializer"),
        "diagnostic should identify the let-else control-flow position: {err}"
    );
}

// A prophecy may be resolved at most once. Two resolutions assume two equalities over
// the same prophecy symbol (v == a and v == b), a contradiction that vacuously verifies
// everything downstream — a false-verify the bridge must reject at expansion time.
#[test]
fn bridge_rejects_double_resolve_on_linear_path() {
    let block: syn::Block = syn::parse_str(
        "{ let p: Proph<u64> = Proph::<u64>::new(); let v: u64 = p.view(); p.resolve(v); p.resolve(v); }",
    )
    .expect("test block should parse");

    let err = bridge_proof_statements(&block)
        .err()
        .expect("resolving a prophecy twice on one path must fail (would assume a contradiction)");
    assert!(
        err.to_string().contains("resolved more than once"),
        "diagnostic should explain the single-resolution rule: {err}"
    );
}

// The same prophecy symbol may be resolved once in each of two mutually-exclusive
// branches, because at most one branch runs. The if-condition is prophecy-independent,
// so branching is permitted, and resolved_prophecies is branch-scoped.
#[test]
fn bridge_allows_resolve_once_in_each_disjoint_branch() {
    let block: syn::Block = syn::parse_str(
        "{ let cond: bool = true; let p: Proph<u64> = Proph::<u64>::new(); if cond { p.resolve(1u64); } else { p.resolve(2u64); } }",
    )
    .expect("test block should parse");

    bridge_proof_statements(&block)
        .expect("one resolve in each disjoint branch of an if is allowed");
}

// A resolve inside a branch followed by a resolve on the joined linear path is a
// double-resolve on the branch-taken path, so it must be rejected (the branch's
// resolution is unioned back into the post-if state).
#[test]
fn bridge_rejects_resolve_after_branch_that_already_resolved() {
    let block: syn::Block = syn::parse_str(
        "{ let cond: bool = true; let p: Proph<u64> = Proph::<u64>::new(); if cond { p.resolve(1u64); } p.resolve(2u64); }",
    )
    .expect("test block should parse");

    let err = bridge_proof_statements(&block)
        .err()
        .expect("a resolve after a branch that resolved the same prophecy must fail");
    assert!(
        err.to_string().contains("resolved more than once"),
        "diagnostic should explain the single-resolution rule: {err}"
    );
}

// Re-binding a prophecy with a fresh Proph::new() clears resolvedness, so the new
// prophecy is resolvable again on the same path.
#[test]
fn bridge_allows_resolve_after_reissuing_prophecy() {
    let block: syn::Block = syn::parse_str(
        "{ let p: Proph<u64> = Proph::<u64>::new(); p.resolve(1u64); let p: Proph<u64> = Proph::<u64>::new(); p.resolve(2u64); }",
    )
    .expect("test block should parse");

    bridge_proof_statements(&block)
        .expect("a fresh Proph::new() re-enables resolution for the shadowed name");
}
