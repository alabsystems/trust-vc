// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use quote::ToTokens;

fn rewrite(source: &str, func_name: &str) -> Option<String> {
    let file: File = syn::parse_str(source).expect("probe source should parse");
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            Item::Fn(item_fn) if item_fn.sig.ident == func_name => Some(item_fn),
            _ => None,
        })
        .expect("probe function should exist");
    infer_untyped_assert_forall_binders(&file, func)
        .map(|rewritten| rewritten.to_token_stream().to_string())
}

const SPEC_F1: &str = r#"
    #[trust_vc::spec]
    fn f1(i: int) -> int { i + 1 }
"#;

#[test]
fn infers_binder_type_from_spec_fn_parameter() {
    let source = format!(
        "{SPEC_F1}
        fn probe() {{
            trust_vc::assert_forall_by!(|x| f1(x) > x, {{}});
        }}"
    );
    let out = rewrite(&source, "probe").expect("untyped binder should be inferred");
    assert!(
        out.contains("x : int"),
        "binder should be annotated `x: int` from f1's parameter, got: {out}"
    );
}

#[test]
fn infers_binder_type_in_verus_assert_forall_surface() {
    let source = format!(
        "{SPEC_F1}
        fn probe() {{
            trust_vc::assert!(assert forall |x| f1(x) > x by {{}});
        }}"
    );
    let out = rewrite(&source, "probe").expect("untyped binder should be inferred");
    assert!(out.contains("x : int"), "got: {out}");
}

#[test]
fn leaves_typed_binders_untouched() {
    let source = format!(
        "{SPEC_F1}
        fn probe() {{
            trust_vc::assert_forall_by!(|x: int| f1(x) > x, {{}});
        }}"
    );
    assert!(
        rewrite(&source, "probe").is_none(),
        "an already-typed binder must not be rewritten"
    );
}

/// FAIL-CLOSED: the binder is never passed to a spec fn, so nothing forces its
/// type. It must stay untyped and hit the typed-binder error downstream.
#[test]
fn unconstrained_binder_is_left_untyped() {
    let source = format!(
        "{SPEC_F1}
        fn probe() {{
            trust_vc::assert_forall_by!(|x| x == x, {{}});
        }}"
    );
    assert!(
        rewrite(&source, "probe").is_none(),
        "a binder with no spec-fn argument occurrence must NOT be guessed"
    );
}

/// FAIL-CLOSED: two spec fns demand different types for the same binder. The
/// program is ill-typed; we must not pick one.
#[test]
fn conflicting_inferences_fail_closed() {
    let source = r#"
        #[trust_vc::spec]
        fn takes_int(i: int) -> bool { true }
        #[trust_vc::spec]
        fn takes_nat(n: nat) -> bool { true }

        fn probe() {
            trust_vc::assert_forall_by!(|x| takes_int(x) && takes_nat(x), {});
        }
    "#;
    assert!(
        rewrite(source, "probe").is_none(),
        "a binder demanded at two different types must NOT be annotated"
    );
}

/// FAIL-CLOSED: an EXEC fn is not callable from a quantifier body, so its
/// signature must never supply a binder type (a local closure or exec helper
/// sharing a spec fn's name cannot hijack the inference).
#[test]
fn exec_fn_signature_does_not_supply_a_type() {
    let source = r#"
        fn exec_helper(i: u64) -> bool { true }

        fn probe() {
            trust_vc::assert_forall_by!(|x| exec_helper(x), {});
        }
    "#;
    assert!(
        rewrite(source, "probe").is_none(),
        "an exec fn must not supply a quantifier binder type"
    );
}

/// A non-bare argument (`x + 1`, `x as int`) says nothing about `x`'s own type
/// and must not pin it.
#[test]
fn non_bare_argument_does_not_pin_the_binder() {
    let source = format!(
        "{SPEC_F1}
        fn probe() {{
            trust_vc::assert_forall_by!(|x| f1(x + 1) > 0, {{}});
        }}"
    );
    assert!(
        rewrite(&source, "probe").is_none(),
        "`f1(x + 1)` must not pin x's type"
    );
}

#[test]
fn infers_only_the_untyped_binder_of_a_mixed_list() {
    let source = r#"
        #[trust_vc::spec]
        fn takes_int(i: int) -> bool { true }

        fn probe() {
            trust_vc::assert_forall_by!(|x: int, y| takes_int(y) && x == x, {});
        }
    "#;
    let out = rewrite(source, "probe").expect("the untyped binder should be inferred");
    assert!(
        out.contains("x : int"),
        "typed binder preserved, got: {out}"
    );
    assert!(
        out.contains("y : int"),
        "untyped binder annotated, got: {out}"
    );
}
