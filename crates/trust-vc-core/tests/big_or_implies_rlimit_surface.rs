// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Verus-surface parity for three bounded frontend gaps driven by upstream
//! basic.rs (slice 4 of the diagnostic/surface-parity foundation):
//!
//! * `|||` bulleted disjunction (upstream `test_big_or` / `test_big_or_fail`):
//!   `assert({ ||| e1 ||| e2 })` lowers to `(e1) || (e2)` exactly like the
//!   upstream BigOr lowering (builtin_macros syntax.rs). Both directions are
//!   pinned: a true disjunction verifies, a false one is refuted. Bullets are
//!   only recognized in LEADING position (upstream: "leading ||| must be
//!   inside a block"), bind loosest of all operators, and mixing `&&&` into a
//!   `|||` sequence fails closed (upstream hard-stops the operand parse).
//!
//! * `==>` implication operands now register referenced spec functions
//!   (upstream `test2` faithful form `x == y ==> f(x, y) == f(y, x)`): the
//!   spec-function catalog's referenced-call collector previously could not
//!   see inside the `__trust_vc_implies!` marker's raw token operands, so the
//!   obligation lowering failed with "type inference failed: unknown return
//!   type for function 'f'". Both directions pinned, in assert! and in
//!   contract-attribute positions, plus the `<==>` marker.
//!
//! * `#[verifier::rlimit(N)]` / `#[verifier::rlimit(infinity)]` (upstream
//!   `test_rlimit_20` / `test_rlimit_inf`): both parse and verify; the budget
//!   mapping tests live in `vc_extraction/tests/verifier_rlimit_attr.rs`
//!   (they assert the extracted context actually carries the mapped
//!   `rlimit_ms`). Malformed arguments fail closed with the verbatim upstream
//!   message "expected number, or `infinity` for rlimit"
//!   (rust_verify/src/attributes.rs get_rlimit_arg).

use std::fs;
use std::path::Path;
use trust_vc_core::{TrustVcResult, VerifyResult};

fn verify(code: &str, name: &str) -> TrustVcResult<VerifyResult> {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let dir = Path::new("target/big_or_implies_rlimit_surface");
    fs::create_dir_all(dir).unwrap();
    let mut h = DefaultHasher::new();
    code.hash(&mut h);
    let f = dir.join(format!("{name}_{:016x}.rs", h.finish()));
    fs::write(&f, code).unwrap();
    trust_vc_core::verify_function_from_file(f.to_str().unwrap(), name)
}

fn err_message(r: &TrustVcResult<VerifyResult>) -> String {
    match r {
        Err(e) => e.to_string(),
        Ok(VerifyResult::Error { message }) => message.clone(),
        _ => String::new(),
    }
}

// ---------------------------------------------------------------------------
// B-1: `|||` bulleted disjunction (upstream test_big_or / test_big_or_fail)
// ---------------------------------------------------------------------------

#[test]
fn big_or_true_disjunction_verifies() {
    // Upstream test_big_or: proof fn test() { assert({ ||| true ||| false }); }
    let r = verify(
        "#[trust_vc::proof]\n\
         #[trust_vc::ensures(true)]\n\
         fn test() { trust_vc::assert!({ ||| true ||| false }); }",
        "test",
    );
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "upstream test_big_or shape should verify, got: {r:?}"
    );
}

#[test]
fn big_or_false_disjunction_is_refuted() {
    // Upstream test_big_or_fail expects exactly one verification failure
    // (assert_one_fails → counterexample-class); the genuinely-false
    // disjunction pins the refutation direction.
    let r = verify(
        "#[trust_vc::proof]\n\
         #[trust_vc::ensures(true)]\n\
         fn test() { trust_vc::assert!({ ||| false ||| false }); }",
        "test",
    );
    assert!(
        matches!(r, Ok(VerifyResult::Counterexample { .. })),
        "false ||| disjunction must be refuted, got: {r:?}"
    );
}

#[test]
fn big_or_three_bullets_verifies_when_one_holds() {
    let r = verify(
        "use trust_vc_types::int;\n\
         #[trust_vc::proof]\n\
         #[trust_vc::ensures(true)]\n\
         fn test(x: int) {\n\
             trust_vc::assert!({ ||| x < 0 ||| x == 0 ||| x > 0 });\n\
         }",
        "test",
    );
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "total trichotomy over ||| bullets should verify, got: {r:?}"
    );
}

#[test]
fn big_or_in_requires_clause_is_assumed() {
    // Bulleted clauses are legal at requires/ensures clause heads upstream.
    let r = verify(
        "use trust_vc_types::int;\n\
         #[trust_vc::requires(||| x > 1 ||| x < 0)]\n\
         #[trust_vc::ensures(true)]\n\
         fn test(x: int) { trust_vc::assert!(x != 1); }",
        "test",
    );
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "||| requires clause should be assumed, got: {r:?}"
    );
}

#[test]
fn big_or_in_requires_clause_is_not_over_assumed() {
    // The disjunction must be assumed as a DISJUNCTION: x < 0 remains
    // possible, so `x > 1` must be refuted.
    let r = verify(
        "use trust_vc_types::int;\n\
         #[trust_vc::requires(||| x > 1 ||| x < 0)]\n\
         #[trust_vc::ensures(true)]\n\
         fn test(x: int) { trust_vc::assert!(x > 1); }",
        "test",
    );
    assert!(
        matches!(r, Ok(VerifyResult::Counterexample { .. })),
        "||| requires must stay a disjunction, got: {r:?}"
    );
}

#[test]
fn big_or_bullets_bind_loosest_of_all_operators() {
    // Upstream bullet operands parse at Precedence::Assign — below `==>` —
    // so `||| a ==> b ||| c` is `(a ==> b) || (c)`, never `a ==> (b || c)`.
    let r = verify(
        "use trust_vc_types::int;\n\
         #[trust_vc::proof]\n\
         #[trust_vc::ensures(true)]\n\
         fn test(x: int) {\n\
             trust_vc::assert!({ ||| x == x ==> x >= x ||| false });\n\
         }",
        "test",
    );
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "implication inside a ||| bullet should verify, got: {r:?}"
    );
}

#[test]
fn big_or_mixed_with_big_and_fails_closed() {
    // Upstream rejects mixing `&&&` into a `|||` sequence (the bullet-operand
    // parse hard-stops at `&&&` and the leftover tokens fail the enclosing
    // parse). Never silently accept it.
    let r = verify(
        "#[trust_vc::proof]\n\
         #[trust_vc::ensures(true)]\n\
         fn test() { trust_vc::assert!({ ||| true &&& false }); }",
        "test",
    );
    let msg = err_message(&r);
    assert!(
        msg.contains("cannot mix `&&&` and `|||`"),
        "mixing must fail closed, got: {r:?}"
    );
}

#[test]
fn big_and_block_form_still_verifies() {
    // Regression pin: the pre-existing `&&&` big-AND surface (upstream
    // test_big_and) must be unaffected by the ||| pass.
    let r = verify(
        "#[trust_vc::proof]\n\
         #[trust_vc::ensures(true)]\n\
         fn test() { trust_vc::assert!({ &&& true &&& true }); }",
        "test",
    );
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "upstream test_big_and shape should verify, got: {r:?}"
    );
}

#[test]
fn big_and_block_form_still_refutes() {
    // Upstream test_big_and_fail: `assert({ &&& true &&& false })` FAILS.
    let r = verify(
        "#[trust_vc::proof]\n\
         #[trust_vc::ensures(true)]\n\
         fn test() { trust_vc::assert!({ &&& true &&& false }); }",
        "test",
    );
    assert!(
        matches!(r, Ok(VerifyResult::Counterexample { .. })),
        "upstream test_big_and_fail shape must be refuted, got: {r:?}"
    );
}

#[test]
fn plain_infix_or_is_untouched() {
    // Negative control: ordinary `||` (no leading bullet) keeps its meaning.
    let r = verify(
        "use trust_vc_types::int;\n\
         #[trust_vc::ensures(true)]\n\
         fn test(x: int) { trust_vc::assert!(x == 1 || x != 1); }",
        "test",
    );
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "plain || must be untouched, got: {r:?}"
    );
}

// ---------------------------------------------------------------------------
// B-2: `==>` operands register referenced spec functions (upstream test2)
// ---------------------------------------------------------------------------

/// The spec fn mirrors the scout's `basic_test2_f` (upstream `uninterp spec fn
/// f(i: int, j: int) -> bool` — the scout gives it the body `i <= j`).
const TEST2_SPEC_FN: &str = "use trust_vc_types::int;\n\
     #[trust_vc::spec]\n\
     fn basic_test2_f(i: int, j: int) -> bool { i <= j }\n";

#[test]
fn upstream_test2_faithful_implication_form_verifies() {
    // Upstream basic.rs test2, faithful `==>` form (previously: "type
    // inference failed: unknown return type for function 'basic_test2_f'").
    let code = format!(
        "{TEST2_SPEC_FN}\
         #[trust_vc::ensures(true)]\n\
         fn test2(b: bool, x: int, y: int, z: int) {{\n\
             trust_vc::assert!(b || !b);\n\
             trust_vc::assume!(b);\n\
             trust_vc::assert!(b);\n\
             trust_vc::assert!(x == y ==> basic_test2_f(x, y) == basic_test2_f(y, x));\n\
             trust_vc::assert!(x + y == y + x);\n\
             trust_vc::assume!(x <= y && y <= z);\n\
             trust_vc::assert!(x <= z);\n\
         }}"
    );
    let r = verify(&code, "test2");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "upstream test2 faithful ==> form should verify, got: {r:?}"
    );
}

#[test]
fn implication_with_spec_fn_false_conclusion_is_refuted() {
    // No over-acceptance: a false implication whose conclusion is a spec-fn
    // call must still produce a counterexample.
    let code = format!(
        "{TEST2_SPEC_FN}\
         #[trust_vc::ensures(true)]\n\
         fn test(x: int, y: int) {{\n\
             trust_vc::assert!(x <= y ==> basic_test2_f(y, x));\n\
         }}"
    );
    let r = verify(&code, "test");
    assert!(
        matches!(r, Ok(VerifyResult::Counterexample { .. })),
        "false ==> conclusion with spec fn must be refuted, got: {r:?}"
    );
}

#[test]
fn implication_with_spec_fn_in_premise_verifies() {
    let code = format!(
        "{TEST2_SPEC_FN}\
         #[trust_vc::ensures(true)]\n\
         fn test(x: int, y: int) {{\n\
             trust_vc::assert!(basic_test2_f(x, y) ==> x <= y);\n\
         }}"
    );
    let r = verify(&code, "test");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "spec fn in ==> premise should verify, got: {r:?}"
    );
}

#[test]
fn iff_with_spec_fn_operand_verifies() {
    // `<==>` shares the marker-operand channel; pin it too.
    let code = format!(
        "{TEST2_SPEC_FN}\
         #[trust_vc::ensures(true)]\n\
         fn test(x: int, y: int) {{\n\
             trust_vc::assert!(basic_test2_f(x, y) <==> x <= y);\n\
         }}"
    );
    let r = verify(&code, "test");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "spec fn in <==> operand should verify, got: {r:?}"
    );
}

#[test]
fn ensures_clause_implication_with_spec_fn_verifies() {
    // Contract-attribute channel (referenced_contract_call_names fallback).
    let code = format!(
        "{TEST2_SPEC_FN}\
         #[trust_vc::ensures(x == y ==> basic_test2_f(x, y))]\n\
         fn test(x: int, y: int) {{}}"
    );
    let r = verify(&code, "test");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "ensures ==> clause with spec fn should verify, got: {r:?}"
    );
}

#[test]
fn ensures_clause_false_implication_with_spec_fn_is_refuted() {
    let code = format!(
        "{TEST2_SPEC_FN}\
         #[trust_vc::ensures(x <= y ==> basic_test2_f(y, x))]\n\
         fn test(x: int, y: int) {{}}"
    );
    let r = verify(&code, "test");
    assert!(
        matches!(r, Ok(VerifyResult::Counterexample { .. })),
        "false ensures ==> clause with spec fn must be refuted, got: {r:?}"
    );
}

#[test]
fn implication_without_spec_fn_still_refutes() {
    // Baseline pin (worked before this slice): pure-arithmetic `==>` CE.
    let r = verify(
        "use trust_vc_types::int;\n\
         #[trust_vc::ensures(true)]\n\
         fn test(x: int, y: int) {\n\
             trust_vc::assert!(x <= y ==> y <= x);\n\
         }",
        "test",
    );
    assert!(
        matches!(r, Ok(VerifyResult::Counterexample { .. })),
        "pure-arith false ==> must stay refuted, got: {r:?}"
    );
}

// ---------------------------------------------------------------------------
// B-3: #[verifier::rlimit(N)] / #[verifier::rlimit(infinity)]
// ---------------------------------------------------------------------------

#[test]
fn upstream_test_rlimit_20_verifies() {
    // Upstream basic.rs test_rlimit_20 (previously the list form EXTRACT-ERRed
    // and the argument was never consumed).
    let r = verify(
        "#[verifier::rlimit(20)]\n\
         #[trust_vc::ensures(true)]\n\
         fn test1() {\n\
             trust_vc::assert!(true);\n\
             trust_vc::assert!(!false);\n\
             trust_vc::assert!(true && true);\n\
             trust_vc::assert!(true || false);\n\
             trust_vc::assert!(true);\n\
         }",
        "test1",
    );
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "upstream test_rlimit_20 shape should verify, got: {r:?}"
    );
}

#[test]
fn upstream_test_rlimit_inf_verifies() {
    let r = verify(
        "#[verifier::rlimit(infinity)]\n\
         #[trust_vc::ensures(true)]\n\
         fn test1() { trust_vc::assert!(true); }",
        "test1",
    );
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "upstream test_rlimit_inf shape should verify, got: {r:?}"
    );
}

#[test]
fn verifier_list_form_rlimit_verifies() {
    let r = verify(
        "#[verifier(rlimit(20))]\n\
         #[trust_vc::ensures(true)]\n\
         fn test1() { trust_vc::assert!(true); }",
        "test1",
    );
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "#[verifier(rlimit(20))] list form should verify, got: {r:?}"
    );
}

#[test]
fn malformed_rlimit_is_rejected_cleanly() {
    // Verbatim upstream message (rust_verify/src/attributes.rs
    // get_rlimit_arg). Previously the path form was SILENTLY IGNORED even
    // with a garbage argument.
    let r = verify(
        "#[verifier::rlimit(frobnitz)]\n\
         #[trust_vc::ensures(true)]\n\
         fn test1() { trust_vc::assert!(true); }",
        "test1",
    );
    let msg = err_message(&r);
    assert!(
        msg.contains("expected number, or `infinity` for rlimit"),
        "malformed rlimit must fail closed with the upstream message, got: {r:?}"
    );
}

#[test]
fn rlimit_does_not_leak_to_sibling_functions() {
    // The budget is per-function: a sibling without the attribute must
    // extract with the default budget and still verify.
    let r = verify(
        "#[verifier::rlimit(20)]\n\
         #[trust_vc::ensures(true)]\n\
         fn limited() { trust_vc::assert!(true); }\n\
         #[trust_vc::ensures(true)]\n\
         fn test1() { trust_vc::assert!(true); }",
        "test1",
    );
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "sibling without rlimit should verify, got: {r:?}"
    );
}
