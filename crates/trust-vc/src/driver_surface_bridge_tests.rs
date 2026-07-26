// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! No-leak proof for the rustc-driver surface bridge.
//!
//! The contract macros (`requires!`/`ensures!`/`forall!`/`exists!`) carry a
//! `#[cfg(trust_vc_driver)]` arm that emits a `trust_vc_core::__driver_markers::*`
//! CALL, mutually exclusive with the default arms (which for the quantifiers is a
//! vacuous `true`). This module proves — at the token level, without a compiler —
//! that under `--cfg trust_vc_driver`:
//!
//!   * a REAL marker call is emitted (so the driver lowers the real
//!     predicate/quantifier), and
//!   * NO bare `true` survives (the faked-`forall` / vacuous-true false-Verify
//!     leak the driver was built to reject), and
//!   * for `forall!`/`exists!` the REAL closure survives verbatim as the marker's
//!     argument (so the driver reads the real binder + body).
//!
//! It also proves the recut is byte-compatible when the cfg is OFF: under the
//! default (no-cfg) and `test` environments the pre-existing arms survive and the
//! marker never appears.
//!
//! The harness parses each expansion with `syn`, then filters the statements by
//! evaluating their `#[cfg(..)]` predicates against a chosen cfg environment
//! (recursing into surviving blocks), so it checks the *actual* compile-time arm
//! selection rather than brittle substring matching over all arms at once.

use std::collections::HashSet;

use quote::quote;
use syn::{Attribute, Block, Expr, Stmt};

use crate::macro_expand::{expand_ensures, expand_requires};
use crate::macro_expand_ext::{expand_exists, expand_forall};

fn env_set(flags: &[&str]) -> HashSet<String> {
    flags.iter().map(|s| (*s).to_string()).collect()
}

/// Evaluates a `cfg(..)` predicate expression (`ident`, `all(..)`, `any(..)`,
/// `not(..)`) against the set of active cfg flags.
fn eval_cfg_pred(e: &Expr, env: &HashSet<String>) -> bool {
    match e {
        Expr::Path(p) => {
            let name = p
                .path
                .get_ident()
                .map(std::string::ToString::to_string)
                .unwrap_or_default();
            env.contains(&name)
        }
        Expr::Call(c) => {
            let fname = match &*c.func {
                Expr::Path(p) => p
                    .path
                    .get_ident()
                    .map(std::string::ToString::to_string)
                    .unwrap_or_default(),
                _ => String::new(),
            };
            match fname.as_str() {
                "all" => c.args.iter().all(|a| eval_cfg_pred(a, env)),
                "any" => c.args.iter().any(|a| eval_cfg_pred(a, env)),
                "not" => {
                    let inner = c.args.first().expect("not() takes exactly one argument");
                    !eval_cfg_pred(inner, env)
                }
                other => panic!("unexpected cfg predicate function `{other}`"),
            }
        }
        other => panic!("unexpected cfg predicate: {}", quote!(#other)),
    }
}

/// The `cfg(..)` predicate carried by a `#[cfg(..)]` attribute, if any.
fn cfg_pred(attr: &Attribute) -> Option<Expr> {
    if !attr.path().is_ident("cfg") {
        return None;
    }
    Some(
        attr.parse_args::<Expr>()
            .expect("cfg attribute has a parseable predicate"),
    )
}

fn expr_attrs(e: &Expr) -> &[Attribute] {
    match e {
        Expr::Block(b) => &b.attrs,
        Expr::Call(c) => &c.attrs,
        Expr::MethodCall(m) => &m.attrs,
        Expr::Path(p) => &p.attrs,
        Expr::Macro(m) => &m.attrs,
        Expr::Lit(l) => &l.attrs,
        _ => &[],
    }
}

fn stmt_attrs(stmt: &Stmt) -> Vec<Attribute> {
    match stmt {
        Stmt::Local(l) => l.attrs.clone(),
        Stmt::Expr(e, _) => expr_attrs(e).to_vec(),
        Stmt::Macro(m) => m.attrs.clone(),
        Stmt::Item(_) => Vec::new(),
    }
}

/// A statement is active iff *every* `#[cfg(..)]` predicate on it holds.
fn stmt_active(stmt: &Stmt, env: &HashSet<String>) -> bool {
    stmt_attrs(stmt)
        .iter()
        .filter_map(cfg_pred)
        .all(|pred| eval_cfg_pred(&pred, env))
}

/// Filters `stmts` down to those active under `env`, recursing into surviving
/// block expressions so their inner cfg arms are filtered too.
fn surviving(stmts: &[Stmt], env: &HashSet<String>) -> Vec<Stmt> {
    let mut out = Vec::new();
    for stmt in stmts {
        if !stmt_active(stmt, env) {
            continue;
        }
        if let Stmt::Expr(Expr::Block(block_expr), semi) = stmt {
            let mut nested = block_expr.clone();
            nested.block.stmts = surviving(&nested.block.stmts, env);
            out.push(Stmt::Expr(Expr::Block(nested), *semi));
        } else {
            out.push(stmt.clone());
        }
    }
    out
}

/// The tokens the compiler would actually keep for `expansion` under `env`.
fn surviving_string(expansion: proc_macro2::TokenStream, env: &[&str]) -> String {
    let env = env_set(env);
    let block: Block =
        syn::parse2(quote!({ #expansion })).expect("expansion parses as a statement block");
    surviving(&block.stmts, &env)
        .iter()
        .map(|s| quote!(#s).to_string())
        .collect::<Vec<_>>()
        .join(" ")
}

// --- forall!/exists!: the paramount no-leak guard ---------------------------

#[test]
fn forall_under_driver_cfg_emits_real_marker_never_true() {
    // A FALSE quantifier body on purpose: if this leaked to `true`, the driver
    // would vacuously verify a false postcondition. It must become a real marker.
    let expanded = expand_forall(quote! { |x: i32| x < x });

    let driver = surviving_string(expanded.clone(), &["trust_vc_driver"]);
    assert!(
        driver.contains("__driver_markers") && driver.contains("forall"),
        "under trust_vc_driver, forall! must emit the __driver_markers::forall call: {driver}"
    );
    // THE no-leak assertion: no bare `true` survives under the driver cfg.
    assert!(
        !driver.contains("true"),
        "forall! must NOT leak a vacuous `true` under trust_vc_driver (false-Verify): {driver}"
    );
    // The REAL closure survives verbatim as the marker's argument.
    assert!(
        driver.contains("| x") && driver.contains("x < x"),
        "the real closure must survive as the forall marker argument: {driver}"
    );
    assert!(
        !driver.contains("verify_quantifier_inline") && !driver.contains("collect_obligation"),
        "the test/mc arms must be excluded under trust_vc_driver: {driver}"
    );

    // Byte-compatibility when the cfg is OFF: the default arm is still `true`.
    let default = surviving_string(expanded.clone(), &[]);
    assert!(
        default.contains("true") && !default.contains("__driver_markers"),
        "with the cfg off, forall! keeps its existing vacuous-`true` default arm: {default}"
    );

    // The test arm is undisturbed (collection path, no marker).
    let test = surviving_string(expanded, &["test"]);
    assert!(
        !test.contains("__driver_markers"),
        "the cfg(test) collection arm must not carry the driver marker: {test}"
    );
}

#[test]
fn exists_under_driver_cfg_emits_real_marker_never_true() {
    let expanded = expand_exists(quote! { |x: i32| x < x });

    let driver = surviving_string(expanded.clone(), &["trust_vc_driver"]);
    assert!(
        driver.contains("__driver_markers") && driver.contains("exists"),
        "under trust_vc_driver, exists! must emit the __driver_markers::exists call: {driver}"
    );
    assert!(
        !driver.contains("true"),
        "exists! must NOT leak a vacuous `true` under trust_vc_driver: {driver}"
    );
    assert!(
        driver.contains("| x") && driver.contains("x < x"),
        "the real closure must survive as the exists marker argument: {driver}"
    );

    let default = surviving_string(expanded, &[]);
    assert!(
        default.contains("true") && !default.contains("__driver_markers"),
        "with the cfg off, exists! keeps its existing vacuous-`true` default arm: {default}"
    );
}

// --- requires!/ensures!: bare, statement-level markers ----------------------

#[test]
fn requires_under_driver_cfg_emits_bare_marker_call() {
    let expanded = expand_requires(quote! { x < 100 });

    let driver = surviving_string(expanded.clone(), &["trust_vc_driver"]);
    assert!(
        driver.contains("__driver_markers") && driver.contains("requires"),
        "under trust_vc_driver, requires! must emit the __driver_markers::requires call: {driver}"
    );
    // The marker is a bare call (no runtime assert, no vacuous form).
    assert!(
        !driver.contains("assert") && !driver.contains("collect_obligation"),
        "the runtime-assert and collection arms must be excluded under trust_vc_driver: {driver}"
    );

    // Byte-compatibility when the cfg is OFF: the runtime assert still fires.
    let default = surviving_string(expanded.clone(), &[]);
    assert!(
        default.contains("assert") && !default.contains("__driver_markers"),
        "with the cfg off, requires! keeps its runtime assert! arm: {default}"
    );

    // The test arm keeps the collection path, no marker.
    let test = surviving_string(expanded, &["test"]);
    assert!(
        !test.contains("__driver_markers"),
        "the cfg(test) collection arm must not carry the driver marker: {test}"
    );
}

#[test]
fn ensures_under_driver_cfg_emits_bare_marker_call() {
    let expanded = expand_ensures(quote! { ret == x + 1 });

    let driver = surviving_string(expanded.clone(), &["trust_vc_driver"]);
    assert!(
        driver.contains("__driver_markers") && driver.contains("ensures"),
        "under trust_vc_driver, ensures! must emit the __driver_markers::ensures call: {driver}"
    );
    assert!(
        !driver.contains("assert"),
        "the runtime-assert arm must be excluded under trust_vc_driver: {driver}"
    );

    let default = surviving_string(expanded.clone(), &[]);
    assert!(
        default.contains("assert") && !default.contains("__driver_markers"),
        "with the cfg off, ensures! keeps its runtime assert! arm: {default}"
    );

    let test = surviving_string(expanded, &["test"]);
    assert!(
        !test.contains("__driver_markers"),
        "the cfg(test) obligation arm must not carry the driver marker: {test}"
    );
}

// --- mutual exclusivity: exactly one arm under the driver cfg ---------------

#[test]
fn driver_cfg_selects_exactly_one_arm_no_double_emit() {
    // Under trust_vc_driver (test off, trust_mc off), each macro must land on
    // its marker arm ALONE: no vacuous `true`, no runtime assert, no collection
    // alongside it (a double-emit or vacuous-true would be a false-Verify).
    for expanded in [
        expand_forall(quote! { |x: i32| x < x }),
        expand_exists(quote! { |x: i32| x < x }),
        expand_requires(quote! { x < 100 }),
        expand_ensures(quote! { ret == x + 1 }),
    ] {
        let driver = surviving_string(expanded, &["trust_vc_driver"]);
        assert!(
            driver.contains("__driver_markers"),
            "driver arm must be selected: {driver}"
        );
        assert!(
            !driver.contains("verify_quantifier_inline")
                && !driver.contains("collect_obligation")
                && !driver.contains("collect_obligation_expr"),
            "no collection/inline arm may co-exist with the marker: {driver}"
        );
    }
}
