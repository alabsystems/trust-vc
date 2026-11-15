// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

fn parse_expr(s: &str) -> syn::Expr {
    syn::parse_str(s).unwrap()
}
fn lower(s: &str) -> String {
    expr_to_builder_tokens(&parse_expr(s)).unwrap().to_string()
}

#[test]
fn test_literals_and_variables() {
    assert!(lower("true").contains("bool_lit"));
    assert!(lower("42").contains("int_lit"));
    let v = lower("x");
    assert!(v.contains("var") && v.contains("lookup_var_type"));
}

#[test]
fn test_operators() {
    assert!(lower("x > 0").contains("gt"));
    assert!(lower("x + 1").contains("arith_inferred") && lower("x + 1").contains("Add"));
    assert!(lower("x > 0 && y < 10").contains("and"));
    assert!(lower("!flag").contains("not"));
    let n = lower("(x + 1) > (y - 2)");
    assert!(n.contains("gt") && n.contains("Add") && n.contains("Sub"));
}

#[test]
fn test_unsupported_returns_none() {
    assert!(expr_to_builder_tokens(&parse_expr("|x| x + 1")).is_none());
    assert!(expr_to_builder_tokens(&parse_expr("Foo { x: 1 }")).is_none());
}

/// H10: the builder lane emits a bare `fn_call(name, args)` term, which cannot
/// carry a turbofish instantiation. A generic-instantiated call must decline so
/// it reaches the checked string lowering; the plain spelling still lowers.
#[test]
fn test_turbofish_call_declines_builder_lane() {
    assert!(expr_to_builder_tokens(&parse_expr("f::<u8>(x)")).is_none());
    assert!(expr_to_builder_tokens(&parse_expr("f::<u8>(x) == f::<u64>(x)")).is_none());
    assert!(lower("f(x)").contains("fn_call"));
}

#[test]
fn test_extensional_macros_lower_to_builder_helpers() {
    let eq = lower("ext_eq!(s, t)");
    assert!(eq.contains("build_ext_eq_expr"), "ext_eq! builder: {eq}");

    let ne = lower("trust_vc::ext_ne!(s, t)");
    assert!(ne.contains("build_ext_ne_expr"), "ext_ne! builder: {ne}");

    let strict = lower("trust_vc::strict_eq!(s, t)");
    assert!(
        strict.contains("build_strict_eq_expr"),
        "strict_eq! builder: {strict}"
    );

    let equal = lower("equal!(s, t)");
    assert!(
        equal.contains("build_strict_eq_expr"),
        "equal! builder: {equal}"
    );
}

#[test]
fn test_integer_bits_assoc_const_lowers_to_builder_helper() {
    let bits = lower("usize::BITS");
    assert!(
        bits.contains("int_bits") && bits.contains("pointer_width"),
        "usize::BITS builder should preserve pointer-width semantics: {bits}"
    );
}

fn parse_closure(s: &str) -> syn::ExprClosure {
    match parse_expr(s) {
        syn::Expr::Closure(c) => c,
        _ => panic!("expected closure"),
    }
}

#[test]
fn test_closure_forall_single_var() {
    let s = closure_to_quantifier_tokens(&parse_closure("|x: i32| x > 0"), "Forall")
        .unwrap()
        .to_string();
    assert!(s.contains("forall") && s.contains("\"x\"") && s.contains("gt"));
    assert!(
        s.contains("None"),
        "trigger-less forall should stay trigger-less: {s}"
    );
}

#[test]
fn test_closure_forall_math_int_binder() {
    let s = closure_to_quantifier_tokens(&parse_closure("|x: int| x == x"), "Forall")
        .unwrap()
        .to_string();
    assert!(
        s.contains("TrustVcType :: MathInt"),
        "Verus `int` binders should use native MathInt lowering: {s}"
    );
}

#[test]
fn test_closure_exists_nat_binder() {
    let s = closure_to_quantifier_tokens(&parse_closure("|x: nat| x == 0"), "Exists")
        .unwrap()
        .to_string();
    assert!(
        s.contains("TrustVcType :: Nat"),
        "Verus `nat` binders should use native Nat lowering: {s}"
    );
}

#[test]
fn test_closure_forall_preserves_trigger_attr() {
    let s = closure_to_quantifier_tokens(
        &parse_closure("|x: i32| #[trigger] f(x) && x > 0"),
        "Forall",
    )
    .unwrap()
    .to_string();
    assert!(
        s.contains("Some") && s.contains("vec") && s.contains("fn_call") && s.contains("\"f\""),
        "explicit trigger attr should lower to quantifier trigger tokens: {s}"
    );
}

#[test]
fn test_closure_forall_preserves_trigger_attr_inside_block() {
    let s = closure_to_quantifier_tokens(
        &parse_closure("|x: i32| { #[trigger] f(x) && x > 0 }"),
        "Forall",
    )
    .unwrap()
    .to_string();
    assert!(
        s.contains("Some") && s.contains("fn_call") && s.contains("\"f\""),
        "explicit trigger attr inside supported block body should lower to trigger tokens: {s}"
    );
}

#[test]
fn test_closure_exists_multi_var() {
    let s =
        closure_to_quantifier_tokens(&parse_closure("|x: u64, y: i32| x > 0 && y < 10"), "Exists")
            .unwrap()
            .to_string();
    assert!(s.contains("exists") && s.contains("\"x\"") && s.contains("\"y\""));
}

#[test]
fn test_closure_fallback_cases() {
    assert!(closure_to_quantifier_tokens(&parse_closure("|x| x > 0"), "Forall").is_none());
    assert!(closure_to_quantifier_tokens(&parse_closure("|x: i32| x > 0"), "Bad").is_none());
}
