// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression (#2777): a `let-else` whose pattern uses the `..` rest form in a
//! tuple-struct enum variant AND a nested struct field-rest
//! (`let LetElseX::A(Payload { x, .. }, .., b) = e else { ... }`) must extract
//! its bound fields to the correct datatype projections and verify.
//!
//! The pattern-binding extractor already lowered `x` to the nested struct's `x`
//! selector and `b` to the variant's LAST tuple field selector. The blocker was
//! a *type-environment* collision: the upstream port mirrors Verus's auto-derived
//! accessors by hand-writing inherent methods named exactly like trust-vc's
//! auto-generated datatype accessors (`is_A`, `get_A_0`, `get_A_2`). Registering
//! the redundant user method (a) conflicted with the canonical accessor's
//! metadata ("conflicting method metadata for 'LetElseX.get_A_2'") and (b) tried
//! to emit a body axiom over the method's `match`/`matches!`/`panic!` body, which
//! is not lowerable as a pure spec expression.
//!
//! The fix recognizes a user inherent method whose name coincides with a
//! datatype accessor and resolves `recv.is_A()` / `recv.get_A_0()` through the
//! canonical, encoder-backed accessor instead. That accessor carries the true
//! selector/tester semantics, so this only ever adds true datatype facts — it
//! cannot turn a violable obligation into a false pass (the adversarial cases
//! below confirm wrong bindings still produce a non-`Verified` result).

use trust_vc_core::{extract_verification_conditions_with_file_context, VerifyResult};

/// Shared surface: an enum `LetElseX::A(Payload, u64, bool)` plus hand-written
/// inherent accessors whose names collide with trust-vc's auto-generated
/// datatype accessors, mirroring the upstream `test_let_else_dots` port shape.
const SURFACE: &str = r#"
#[derive(Clone, Copy)]
struct LetElsePayload { x: u64, y: bool, z: i32 }

#[derive(Clone, Copy)]
enum LetElseX { A(LetElsePayload, u64, bool), B(bool) }

#[allow(non_snake_case)]
impl LetElseX {
    fn is_A(&self) -> bool { matches!(self, LetElseX::A(_, _, _)) }
    fn get_A_0(&self) -> LetElsePayload {
        match *self { LetElseX::A(p, _, _) => p, LetElseX::B(_) => panic!() }
    }
    fn get_A_2(&self) -> bool {
        match *self { LetElseX::A(_, _, b) => b, LetElseX::B(_) => panic!() }
    }
}
"#;

fn verify(extra_fn: &str, fname: &str) -> VerifyResult {
    let src = format!("{SURFACE}\n{extra_fn}\n");
    let file = trust_vc_core::parse_file_allow_tracked(&src).expect("source should parse");
    let function = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(f) if f.sig.ident == fname => Some(f),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{fname} should exist"));
    extract_verification_conditions_with_file_context(&file, function)
        .unwrap_or_else(|err| panic!("{fname} should extract (no metadata conflict): {err}"))
        .verify()
}

/// The real regression: the dotted/rest let-else pattern verifies. `x` binds to
/// the nested struct's `x` field of variant-A's first field; `b` binds to
/// variant-A's last (third) field. The `is_A` / `get_A_*` calls resolve to the
/// canonical accessors despite the hand-written same-named methods.
#[test]
fn dotted_rest_let_else_extracts_fields_verifies() {
    let f = r#"
#[trust_vc::contract(ensures(true), returns(result))]
fn dotted_extract(value: LetElseX) {
    let LetElseX::A(LetElsePayload { x, .. }, .., b) = value else { loop {} };
    trust_vc::assert!(x == value.get_A_0().x);
    trust_vc::assert!(b == value.get_A_2());
}
"#;
    assert!(
        matches!(verify(f, "dotted_extract"), VerifyResult::Verified),
        "dotted/rest let-else field extraction should verify"
    );
}

/// The `LetElseX::A(_, _, _)` (all-wildcard) let-else with a diverging `loop`
/// else-arm assumes the variant tester, so `value.is_A()` holds afterward.
#[test]
fn dotted_loop_else_tester_assumption_verifies() {
    let f = r#"
#[trust_vc::contract(ensures(true), returns(result))]
fn dotted_loop(value: LetElseX) {
    let LetElseX::A(_, _, _) = value else { loop {} };
    trust_vc::assert!(value.is_A());
}
"#;
    assert!(
        matches!(verify(f, "dotted_loop"), VerifyResult::Verified),
        "let-else loop-else tester assumption should verify"
    );
}

/// Soundness: `b` is the LAST (bool, field 2) projection. Comparing it to a
/// DIFFERENT bool field of the payload (`get_A_0().y`) must NOT verify — the two
/// are independent, so the canonical selectors leave a counterexample.
#[test]
fn dotted_rest_wrong_field_binding_is_not_verified() {
    let f = r#"
#[trust_vc::contract(ensures(true), returns(result))]
fn dotted_wrong(value: LetElseX) {
    let LetElseX::A(LetElsePayload { x, .. }, .., b) = value else { loop {} };
    trust_vc::assert!(b == value.get_A_0().y);
}
"#;
    let result = verify(f, "dotted_wrong");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "binding `b` (field 2) to a different bool field must not verify, got {result:?}"
    );
}

/// Soundness: the extracted field is genuinely CONSTRAINED to the projection,
/// not left free. Asserting an arbitrary constant value for `x` must not verify.
#[test]
fn dotted_rest_extracted_field_is_constrained_not_free() {
    let f = r#"
#[trust_vc::contract(ensures(true), returns(result))]
fn dotted_const(value: LetElseX) {
    let LetElseX::A(LetElsePayload { x, .. }, .., b) = value else { loop {} };
    trust_vc::assert!(x == 123456789u64);
}
"#;
    let result = verify(f, "dotted_const");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "extracted field `x` is the real payload.x projection, not a free value; \
         asserting an arbitrary constant must not verify, got {result:?}"
    );
}

/// Soundness: the trailing `, m, b` binders distinguish field 1 (`m`) from the
/// nested struct's `x` (field-0's `x`). They are independent, so `x == m` must
/// not verify — proving the rest pattern does not collapse distinct projections.
#[test]
fn dotted_rest_distinct_projections_not_conflated() {
    let f = r#"
#[trust_vc::contract(ensures(true), returns(result))]
fn dotted_distinct(value: LetElseX) {
    let LetElseX::A(LetElsePayload { x, .. }, m, b) = value else { loop {} };
    trust_vc::assert!(x == m);
}
"#;
    let result = verify(f, "dotted_distinct");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "payload.x (field 0's x) and field 1 (m) are independent; x == m must not verify, got {result:?}"
    );
}
