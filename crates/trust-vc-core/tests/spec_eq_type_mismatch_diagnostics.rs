// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Verus-parity diagnostics for spec `==`/`!=` between incompatible types
//! (diagnostic-parity foundation slice 3, FAMILY D — upstream basic.rs
//! `test_spec_eq_type_error_1`/`_2` and the local helper
//! `assert_spec_eq_type_err`).
//!
//! Upstream channel (pinned Verus `a40d57c`,
//! `rust_verify/src/fn_call_to_vir.rs:1761-1786`): a spec equality is legal
//! iff the UNDECORATED operand types (`Box`/`Rc`/`Arc`/`Ghost`/`Tracked`
//! transparent) are equal or both integer-class (`is_smt_arith` — ALL
//! int-class mixes are legal, `u64 == int` included). Anything else is the
//! primary translation-time error
//! "mismatched types; types must be compatible to use == or !=" with both
//! type renderings attached as span labels ("this is `u64`" /
//! "this is `core::option::Option<u64>`" — the pinned upstream patterns
//! `"u64"` and `"::Option<u64>"` are substrings of those renderings).
//!
//! trust-vc implements the SYN-FRONTEND DECIDABLE SUBSET, deliberately
//! narrow so it can never over-reject: both operands must be bare declared
//! PARAMETER identifiers of the verified function, only CONTRACT clause
//! expressions are scanned (body asserts can shadow parameter names),
//! closure sub-expressions are skipped (quantifier binders), and the rule
//! fires only for an int-class operand against a POSITIVELY-known
//! non-integer concrete operand — an unresolved/opaque side means silence.
//! `test_spec_eq_type_error_3` (spec_fn comparand) and `_4` (tuple ×
//! associated-type projection over a declared generic) are now IN scope:
//! `_3` via `render_spec_eq_type`'s `spec_fn(params) -> ret` surface, `_4` via
//! the syntactic tuple × generic-projection rejection with `render_type_verus`'s
//! exact span spacing (`(u64, nat)` / `<X as test_crate::A>::AT`). Still out of
//! scope (needs the rustc/driver frontend's type inference, reported honestly,
//! NOT faked): `_5` (closure inference in a body assert).

use std::fs;
use std::path::Path;
use trust_vc_core::{TrustVcResult, VerifyResult};

const MISMATCH_MSG: &str = "mismatched types; types must be compatible to use == or !=";

fn verify(code: &str, name: &str) -> TrustVcResult<VerifyResult> {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let dir = Path::new("target/spec_eq_type_mismatch_diagnostics");
    fs::create_dir_all(dir).unwrap();
    let mut h = DefaultHasher::new();
    code.hash(&mut h);
    let f = dir.join(format!("{name}_{:016x}.rs", h.finish()));
    fs::write(&f, code).unwrap();
    trust_vc_core::verify_function_from_file(f.to_str().unwrap(), name)
}

/// The error message returned (empty string if the call did not error).
fn err_message(r: &TrustVcResult<VerifyResult>) -> String {
    match r {
        Err(e) => e.to_string(),
        Ok(VerifyResult::Error { message }) => message.clone(),
        _ => String::new(),
    }
}

// ---------------------------------------------------------------------------
// Positive cases: the upstream message with the upstream type renderings
// ---------------------------------------------------------------------------

#[test]
fn u64_vs_option_requires_rejected_with_upstream_message() {
    // Upstream test_spec_eq_type_error_1:
    // assert_spec_eq_type_err(err, "u64", "::Option<u64>").
    let code = r#"
#[trust_vc::requires(a == b)]
fn test(a: u64, b: Option<u64>) {}
"#;
    let r = verify(code, "test");
    let msg = err_message(&r);
    assert!(msg.contains(MISMATCH_MSG), "got {r:?}");
    assert!(msg.contains("u64"), "got {r:?}");
    assert!(msg.contains("::Option<u64>"), "got {r:?}");
}

#[test]
fn spec_fn_type_renders_with_verus_arrow_surface() {
    // Upstream test_spec_eq_type_error_3:
    // assert_spec_eq_type_err(err, "u64", "spec_fn(u64) -> nat"). trust-vc's
    // ghost-closure type `SpecFn<u64, nat>` must render as Verus's span surface
    // `spec_fn(u64) -> nat`, not the raw `SpecFn<u64,nat>`. Reject-only: the
    // verdict is `error` regardless — this pins the rendering fidelity.
    let code = r#"
use trust_vc_types::{nat, SpecFn};
#[trust_vc::requires(a == b)]
fn test(a: u64, b: SpecFn<u64, nat>) {}
"#;
    let r = verify(code, "test");
    let msg = err_message(&r);
    assert!(msg.contains(MISMATCH_MSG), "got {r:?}");
    assert!(msg.contains("u64"), "got {r:?}");
    assert!(msg.contains("spec_fn(u64) -> nat"), "got {r:?}");
}

#[test]
fn tuple_vs_generic_projection_rejected_with_verbatim_span_spacing() {
    // Upstream test_spec_eq_type_error_4:
    // assert_spec_eq_type_err(err, "(u64, nat)", "<X as test_crate::A>::AT").
    // The span labels must carry Verus's EXACT spacing — rendered from the
    // syn::Type (the compacted param source loses the `as` word boundary).
    let code = r#"
use trust_vc_types::nat;
mod test_crate { pub trait A { type AT; } }
#[trust_vc::requires(a == b)]
fn test<X: test_crate::A>(a: (u64, nat), b: <X as test_crate::A>::AT) {}
"#;
    let r = verify(code, "test");
    let msg = err_message(&r);
    assert!(msg.contains(MISMATCH_MSG), "got {r:?}");
    assert!(msg.contains("(u64, nat)"), "tuple span spacing: {r:?}");
    assert!(
        msg.contains("<X as test_crate::A>::AT"),
        "projection span spacing: {r:?}"
    );
}

#[test]
fn tuple_vs_tuple_is_not_rejected() {
    // Two tuples of the SAME type are `types_equal` upstream -> legal. The
    // shape rule must NOT fire (no over-rejection) — the fn is accepted far
    // enough to reach the ordinary "nothing to prove" path, NOT the mismatch
    // error.
    let code = r#"
#[trust_vc::requires(a == b)]
fn test(a: (u64, u32), b: (u64, u32)) {}
"#;
    let r = verify(code, "test");
    let msg = match &r {
        Ok(trust_vc_core::VerifyResult::Error { message }) => message.clone(),
        Err(e) => e.to_string(),
        _ => String::new(),
    };
    assert!(
        !msg.contains(MISMATCH_MSG),
        "tuple == tuple must not trip the spec-eq mismatch rule: {r:?}"
    );
}

#[test]
fn arc_decoration_is_transparent() {
    // Upstream test_spec_eq_type_error_2: std::sync::Arc<Option<u64>> is
    // undecorated to Option<u64> — SAME patterns as case 1.
    let code = r#"
#[trust_vc::requires(a == b)]
fn test(a: u64, b: std::sync::Arc<Option<u64>>) {}
"#;
    let r = verify(code, "test");
    let msg = err_message(&r);
    assert!(msg.contains(MISMATCH_MSG), "got {r:?}");
    assert!(msg.contains("u64"), "got {r:?}");
    assert!(msg.contains("::Option<u64>"), "got {r:?}");
}

#[test]
fn ne_operator_and_reversed_operands_covered() {
    let code = r#"
#[trust_vc::requires(b != a)]
fn test(a: u64, b: Option<u64>) {}
"#;
    let r = verify(code, "test");
    let msg = err_message(&r);
    assert!(
        msg.contains(MISMATCH_MSG),
        "!= and reversed order, got {r:?}"
    );
    assert!(msg.contains("::Option<u64>"), "got {r:?}");
}

#[test]
fn ensures_clause_and_parenthesized_operands_covered() {
    let code = r#"
#[trust_vc::ensures((a) == (b))]
fn test(a: u64, b: Option<u64>) {}
"#;
    let r = verify(code, "test");
    assert!(
        err_message(&r).contains(MISMATCH_MSG),
        "ensures + parens must fire, got {r:?}"
    );
}

#[test]
fn contract_grouped_clause_covered() {
    let code = r#"
#[trust_vc::contract(requires(a == b))]
fn test(a: u64, b: Option<u64>) {}
"#;
    let r = verify(code, "test");
    assert!(
        err_message(&r).contains(MISMATCH_MSG),
        "#[contract]-grouped clause must fire, got {r:?}"
    );
}

#[test]
fn int_vs_bool_rejected() {
    // General-rule evidence: bool is a positively-known non-integer concrete
    // type (upstream: not types_equal, not is_smt_arith -> same error).
    let code = r#"
#[trust_vc::requires(a == b)]
fn test(a: u64, b: bool) {}
"#;
    let r = verify(code, "test");
    let msg = err_message(&r);
    assert!(msg.contains(MISMATCH_MSG), "got {r:?}");
    assert!(msg.contains("`bool`"), "got {r:?}");
}

// ---------------------------------------------------------------------------
// Negative controls: never-reject regressions (pinned legal twins)
// ---------------------------------------------------------------------------

#[test]
fn same_type_comparison_verifies() {
    let code = r#"
#[trust_vc::requires(a == b)]
#[trust_vc::ensures(result == a)]
fn test(a: u64, b: u64) -> u64 { a }
"#;
    let r = verify(code, "test");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "u64 == u64 must stay legal, got {r:?}"
    );
}

#[test]
fn int_class_mix_is_never_the_mismatch_error() {
    // Upstream is_smt_arith: ALL int-class mixes are legal (u64 == int is
    // the pinned upstream control). Whatever verdict the engine reaches,
    // the MISMATCH message must not appear.
    for (t1, t2) in [
        ("u64", "int"),
        ("u64", "u32"),
        ("int", "nat"),
        ("u64", "nat"),
    ] {
        let code = format!(
            r#"
#[trust_vc::requires(a == b)]
fn test(a: {t1}, b: {t2}) {{}}
"#
        );
        let r = verify(&code, "test");
        assert!(
            !err_message(&r).contains(MISMATCH_MSG),
            "int-class mix {t1} == {t2} must not get the mismatch error, got {r:?}"
        );
    }
}

#[test]
fn alias_to_u64_resolves_and_verifies() {
    // The registry resolves same-file aliases; an alias of u64 is int-class.
    let code = r#"
type MyU64 = u64;

#[trust_vc::requires(a == b)]
#[trust_vc::ensures(result == a)]
fn test(a: MyU64, b: u64) -> u64 { a }
"#;
    let r = verify(code, "test");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "alias MyU64 == u64 must stay legal, got {r:?}"
    );
}

#[test]
fn same_datatype_comparison_is_not_the_mismatch_error() {
    // Option<u64> == Option<u64>: types equal upstream -> legal. The rule
    // must stay silent whatever the engine's capability verdict is.
    let code = r#"
#[trust_vc::requires(a == b)]
fn test(a: Option<u64>, b: Option<u64>) {}
"#;
    let r = verify(code, "test");
    assert!(
        !err_message(&r).contains(MISMATCH_MSG),
        "same-datatype comparison must not get the mismatch error, got {r:?}"
    );
}

#[test]
fn unresolved_opaque_type_is_never_rejected() {
    // A positively-unresolvable side (unknown type name) must classify
    // Unknown -> silence (fail toward the existing behavior, whatever it is).
    let code = r#"
#[trust_vc::requires(a == b)]
fn test(a: u64, b: SomeUnknownWidget) {}
"#;
    let r = verify(code, "test");
    assert!(
        !err_message(&r).contains(MISMATCH_MSG),
        "an unresolved operand type must not fire the mismatch error, got {r:?}"
    );
}

#[test]
fn quantifier_binder_shadowing_param_does_not_fire() {
    // A closure/quantifier binder named like an incompatible param must not
    // be resolved to the PARAM type (closure subtrees are skipped).
    let code = r#"
#[trust_vc::requires(trust_vc::forall(|b: u64| b == b))]
fn test(a: u64, b: Option<u64>) {}
"#;
    let r = verify(code, "test");
    assert!(
        !err_message(&r).contains(MISMATCH_MSG),
        "a shadowed binder must not resolve to the param type, got {r:?}"
    );
}

#[test]
fn body_asserts_are_out_of_scope_for_the_rule() {
    // Locals can shadow params in bodies; the rule scans CONTRACT clauses
    // only, so a body assert over a shadowing local must not fire.
    let code = r#"
fn test(a: u64, b: Option<u64>) {
    let b = 5u64;
    trust_vc::assert!(a == b || a != b);
}
"#;
    let r = verify(code, "test");
    assert!(
        !err_message(&r).contains(MISMATCH_MSG),
        "body asserts with shadowing locals must not fire the contract rule, got {r:?}"
    );
}

#[test]
fn non_bare_operands_are_skipped() {
    // `old(b)` is a call, not a bare parameter identifier — skipped (no
    // flow analysis on the syn frontend; fail toward existing behavior).
    let code = r#"
#[trust_vc::ensures(a == old(a))]
fn test(a: u64, b: Option<u64>) {}
"#;
    let r = verify(code, "test");
    assert!(
        !err_message(&r).contains(MISMATCH_MSG),
        "non-bare operands must be skipped, got {r:?}"
    );
}

// ── shadowed-binder corners (fixed after the adversarial verify) ─────────────
// A clause-local binder that shadows a parameter name must NOT be classified
// with the parameter's type — upstream evaluates the binder's own type
// (`{ let b = 10u64; a == b }` is a legal u64 == u64 even when the signature
// has `b: Option<u64>`). Conservative: shadowed idents skip classification.

#[test]
fn let_shadowed_param_in_clause_not_rejected() {
    let code = r#"
#[trust_vc::requires({ let b = 10u64; a == b })]
#[trust_vc::ensures(true)]
fn test(a: u64, b: Option<u64>) {
    trust_vc::assert!(a == 10);
}
"#;
    let r = verify(code, "test");
    let msg = err_message(&r);
    assert!(
        !msg.contains("mismatched types"),
        "let-shadowed binder must not be classified with the param type, got {r:?}"
    );
}

#[test]
fn match_arm_shadowed_param_in_clause_not_rejected() {
    let code = r#"
#[trust_vc::requires(match 1u64 { b => a == b })]
#[trust_vc::ensures(true)]
fn test(a: u64, b: Option<u64>) {
    trust_vc::assert!(a == 1);
}
"#;
    let r = verify(code, "test");
    let msg = err_message(&r);
    assert!(
        !msg.contains("mismatched types"),
        "match-arm-shadowed binder must not be classified, got {r:?}"
    );
}

#[test]
fn if_let_shadowed_param_in_clause_not_rejected() {
    let code = r#"
#[trust_vc::requires(if let Some(b) = c { a == b } else { true })]
#[trust_vc::ensures(true)]
fn test(a: u64, b: Option<u64>, c: Option<u64>) {
    trust_vc::assert!(true);
}
"#;
    let r = verify(code, "test");
    let msg = err_message(&r);
    assert!(
        !msg.contains("mismatched types"),
        "if-let-shadowed binder must not be classified, got {r:?}"
    );
}

/// The rule still fires OUTSIDE the shadowed scope: after the `if let`, the
/// name refers to the parameter again.
#[test]
fn mismatch_after_shadow_scope_still_fires() {
    let code = r#"
#[trust_vc::requires({ { let b = 10u64; } a == b })]
#[trust_vc::ensures(true)]
fn test(a: u64, b: Option<u64>) {
    trust_vc::assert!(true);
}
"#;
    let r = verify(code, "test");
    let msg = err_message(&r);
    assert!(
        msg.contains("mismatched types"),
        "outside the shadow scope the param classification must still fire, got {r:?}"
    );
}
