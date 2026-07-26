// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Verus-parity diagnostics for the `#[verifier::proof_note("…")]` /
//! `#[verifier::custom_err("…")]` family (diagnostic-parity foundation
//! slice 3, FAMILY C — upstream basic.rs `test_requires2`,
//! `test_proof_note_on_*`, `test_multiple_proof_notes_on_*`,
//! `test_custom_err_on_*`, `test_multiple_custom_errs_on_assert`).
//!
//! Upstream channels (pinned Verus `a40d57c`):
//! * AT-MOST-ONE: `rust_verify/src/attributes.rs:1010-1023` rejects two or
//!   more labels of ANY MIX (`proof_note` and `custom_err` both parse to
//!   `Attr::ProofNote`) on one expression/clause with the PRIMARY,
//!   translation-time error "at most one `proof_note` attribute is allowed" —
//!   it fires BEFORE verification, even when the proof would pass.
//! * ERROR-WITH-NOTE: `rust_verify/src/verifier.rs:96-140` renders a FAILING
//!   labeled obligation as the unchanged primary failure diagnostic plus a
//!   secondary "note: {text}" span label (`proof_note`), or with the primary
//!   message REPLACED by the label text (`custom_err`). The upstream harness
//!   classifies these via `assert_help_error_msg`/`assert_vir_error_msg` —
//!   ERROR outcomes carrying the label text — while unlabeled failures are
//!   plain counterexample outcomes (`assert_one_fails`).
//!
//! DELIBERATE VERDICT-TAXONOMY DECISION (explicitly acknowledged, per the
//! slice-3 integrity bar): trust-vc reports a counterexample against a
//! USER-LABELED obligation as `VerifyResult::Error` carrying the label text,
//! mirroring the upstream channel. This is reject-only/fail-closed (never
//! produces `Verified`; `Unknown` is never touched) and strictly opt-in (an
//! obligation only carries a label when the user wrote one) — every
//! unlabeled program's verdict is byte-for-byte unchanged, pinned by the
//! counterexample-discrimination tests below (`test_requires3`/`test_ret`
//! analogs, upstream-verified arithmetic: those cases fail on their
//! UNLABELED clauses and must stay counterexamples).

use std::fs;
use std::path::Path;
use trust_vc_core::{TrustVcResult, VerifyResult};

const AT_MOST_ONE: &str = "at most one `proof_note` attribute is allowed";

fn verify(code: &str, name: &str) -> TrustVcResult<VerifyResult> {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let dir = Path::new("target/proof_note_attribute_diagnostics");
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

fn is_counterexample(r: &TrustVcResult<VerifyResult>) -> bool {
    matches!(r, Ok(VerifyResult::Counterexample { .. }))
}

// ---------------------------------------------------------------------------
// AT-MOST-ONE: translation-time reject, fires even when the proof would pass
// ---------------------------------------------------------------------------

#[test]
fn duplicate_stmt_level_proof_notes_on_passing_assert_rejected() {
    // Upstream test_multiple_proof_notes_on_assert. The assert HOLDS —
    // the reject must fire pre-verification, exactly as upstream.
    let code = r#"
fn caller() {
    #[verifier::proof_note("Statement known to be false")]
    #[verifier::proof_note("This is another proof label")]
    trust_vc::assert!(2 > 1);
}
"#;
    let r = verify(code, "caller");
    assert!(
        err_message(&r).contains(AT_MOST_ONE),
        "duplicate proof_note labels must reject with the upstream message, got {r:?}"
    );
}

#[test]
fn duplicate_stmt_level_proof_notes_on_assume_rejected() {
    // Upstream test_multiple_proof_notes_on_assume.
    let code = r#"
fn caller() {
    #[verifier::proof_note("Statement known to be false")]
    #[verifier::proof_note("This is another proof label")]
    trust_vc::assume!(1 > 2);
}
"#;
    let r = verify(code, "caller");
    assert!(
        err_message(&r).contains(AT_MOST_ONE),
        "duplicate labels on assume must reject, got {r:?}"
    );
}

#[test]
fn duplicate_custom_errs_on_assert_rejected_with_proof_note_message() {
    // Upstream test_multiple_custom_errs_on_assert: two custom_err labels
    // yield the SAME `proof_note` message (both parse to Attr::ProofNote).
    let code = r#"
fn caller() {
    #[verifier::custom_err("Custom assert error")]
    #[verifier::custom_err("Another custom error")]
    trust_vc::assert!(1 > 2);
}
"#;
    let r = verify(code, "caller");
    assert!(
        err_message(&r).contains(AT_MOST_ONE),
        "duplicate custom_err labels must reject with the proof_note message, got {r:?}"
    );
}

#[test]
fn mixed_proof_note_and_custom_err_pool_together() {
    let code = r#"
fn caller() {
    #[verifier::proof_note("a")]
    #[verifier::custom_err("b")]
    trust_vc::assert!(1 > 2);
}
"#;
    let r = verify(code, "caller");
    assert!(
        err_message(&r).contains(AT_MOST_ONE),
        "proof_note and custom_err must POOL (upstream parses both to Attr::ProofNote), got {r:?}"
    );
}

#[test]
fn stmt_level_and_expr_level_labels_pool_together() {
    // Upstream moves statement attrs INSIDE onto the argument expression
    // (builtin_macros/src/syntax.rs:2803), so both positions form ONE pool.
    let code = r#"
fn caller() {
    #[verifier::proof_note("outer")]
    trust_vc::assert!(#[verifier::proof_note("inner")] (2 > 1));
}
"#;
    let r = verify(code, "caller");
    assert!(
        err_message(&r).contains(AT_MOST_ONE),
        "statement-level and expression-level labels must pool, got {r:?}"
    );
}

#[test]
fn duplicate_clause_inner_proof_notes_on_requires_rejected() {
    // Upstream test_multiple_proof_notes_on_requires — fires even though no
    // caller exists (translation-time, proof outcome irrelevant).
    let code = r#"
#[trust_vc::requires(
    #![verifier::proof_note("Property 732")]
    #![verifier::proof_note("Property 451")]
    x == y
)]
#[trust_vc::ensures(result == x)]
fn example(x: u64, y: u64) -> u64 { x }
"#;
    let r = verify(code, "example");
    assert!(
        err_message(&r).contains(AT_MOST_ONE),
        "duplicate clause labels on requires must reject, got {r:?}"
    );
}

#[test]
fn duplicate_clause_inner_proof_notes_on_ensures_rejected() {
    // Upstream test_multiple_proof_notes_on_ensures.
    let code = r#"
#[trust_vc::ensures(
    #![verifier::proof_note("Property 732")]
    #![verifier::proof_note("Property 451")]
    result == x
)]
fn example(x: u64) -> u64 { x }
"#;
    let r = verify(code, "example");
    assert!(
        err_message(&r).contains(AT_MOST_ONE),
        "duplicate clause labels on ensures must reject, got {r:?}"
    );
}

// ---------------------------------------------------------------------------
// ERROR-WITH-NOTE: a FAILING labeled obligation reports through the Verus
// error channel (see the header's verdict-taxonomy acknowledgment)
// ---------------------------------------------------------------------------

#[test]
fn labeled_failing_assert_reports_error_with_note() {
    // Upstream test_proof_note_on_assert:
    // assert_help_error_msg(err, "note: Statement known to be false").
    let code = r#"
fn caller() {
    #[verifier::proof_note("Statement known to be false")]
    trust_vc::assert!(1 > 2);
}
"#;
    let r = verify(code, "caller");
    let msg = err_message(&r);
    assert!(
        msg.contains("note: Statement known to be false"),
        "labeled failing assert must carry the note, got {r:?}"
    );
    assert!(
        msg.contains("assertion failed"),
        "proof_note keeps the PRIMARY failure text unchanged, got {r:?}"
    );
}

#[test]
fn custom_err_failing_assert_replaces_primary_message() {
    // Upstream test_custom_err_on_assert:
    // assert_vir_error_msg(err, "Custom assert error") — the label REPLACES
    // the primary message.
    let code = r#"
fn caller() {
    #[verifier::custom_err("Custom assert error")]
    trust_vc::assert!(1 > 2);
}
"#;
    let r = verify(code, "caller");
    let msg = err_message(&r);
    assert!(
        msg.contains("Custom assert error"),
        "custom_err text must be the reported message, got {r:?}"
    );
    assert!(
        !msg.contains("assertion failed"),
        "custom_err REPLACES the primary message (upstream replacement_error_note), got {r:?}"
    );
}

#[test]
fn labeled_requires_violated_by_caller_reports_error_with_note() {
    // Upstream test_proof_note_on_requires: the CALLER-side precondition
    // failure carries the CALLEE clause's label.
    let code = r#"
#[trust_vc::requires(#![verifier::proof_note("Property 732")] x == y)]
fn example(x: u64, y: u64) -> u64 { x }

fn caller() {
    let _ = example(1, 2);
}
"#;
    let r = verify(code, "caller");
    let msg = err_message(&r);
    assert!(
        msg.contains("note: Property 732"),
        "caller-side precondition failure must carry the callee clause label, got {r:?}"
    );
    assert!(
        msg.contains("precondition not satisfied"),
        "primary precondition failure text unchanged, got {r:?}"
    );
}

#[test]
fn custom_err_requires_violated_by_caller_replaces_message() {
    // Upstream test_custom_err_on_requires.
    let code = r#"
#[trust_vc::requires(#![verifier::custom_err("Custom requires error")] x == y)]
fn example(x: u64, y: u64) -> u64 { x }

fn caller() {
    let _ = example(1, 2);
}
"#;
    let r = verify(code, "caller");
    assert!(
        err_message(&r).contains("Custom requires error"),
        "custom_err requires text must be reported, got {r:?}"
    );
}

#[test]
fn labeled_ensures_violated_by_body_reports_error_with_note() {
    // Upstream test_proof_note_on_ensures (callee-side ensures failure).
    let code = r#"
#[trust_vc::ensures(#![verifier::proof_note("Property 732")] result == 7)]
fn example(x: u64) -> u64 { x }
"#;
    let r = verify(code, "example");
    let msg = err_message(&r);
    assert!(
        msg.contains("note: Property 732"),
        "labeled failing ensures must carry the note, got {r:?}"
    );
    assert!(
        msg.contains("postcondition not satisfied"),
        "primary postcondition failure text unchanged, got {r:?}"
    );
}

#[test]
fn custom_err_ensures_violated_by_body_replaces_message() {
    // Upstream test_custom_err_on_ensures.
    let code = r#"
#[trust_vc::ensures(#![verifier::custom_err("Custom ensures error")] result == 7)]
fn example(x: u64) -> u64 { x }
"#;
    let r = verify(code, "example");
    assert!(
        err_message(&r).contains("Custom ensures error"),
        "custom_err ensures text must be reported, got {r:?}"
    );
}

#[test]
fn labeled_clause_failing_among_unlabeled_clauses_carries_its_note() {
    // Upstream test_requires2: TEST_REQUIRES1 has an unlabeled clause
    // `a <= b` and a labeled clause `b <= c`; the caller violates ONLY the
    // labeled one -> Error with "note: Test label #1".
    let code = r#"
#[trust_vc::requires(a <= b)]
#[trust_vc::requires(#![verifier::proof_note("Test label #1")] b <= c)]
fn test_requires1(a: u64, b: u64, c: u64) {}

fn caller() {
    test_requires1(1, 2, 1);
}
"#;
    let r = verify(code, "caller");
    assert!(
        err_message(&r).contains("note: Test label #1"),
        "the failing LABELED clause must carry its note, got {r:?}"
    );
}

// ---------------------------------------------------------------------------
// COUNTEREXAMPLE DISCRIMINATION: an UNLABELED failing clause keeps its
// counterexample verdict — the upstream Error/CE split reproduced exactly
// ---------------------------------------------------------------------------

#[test]
fn unlabeled_clause_failing_keeps_counterexample() {
    // Upstream test_requires3 (assert_one_fails => Counterexample): the
    // caller violates the UNLABELED clause `a <= b`; the labeled clause
    // holds. Verdict must stay Counterexample — no fabricated error.
    let code = r#"
#[trust_vc::requires(a <= b)]
#[trust_vc::requires(#![verifier::proof_note("Test label #1")] b <= c)]
fn test_requires1(a: u64, b: u64, c: u64) {}

fn caller() {
    test_requires1(2, 1, 2);
}
"#;
    let r = verify(code, "caller");
    assert!(
        is_counterexample(&r),
        "an unlabeled failing clause must stay a counterexample, got {r:?}"
    );
}

#[test]
fn mixed_ensures_with_unlabeled_failing_clause_keeps_counterexample() {
    // Upstream test_ret (assert_one_fails => Counterexample): the labeled
    // ensures clause HOLDS, the unlabeled one FAILS. Same-name ("postcondition")
    // obligations with non-identical labels are ambiguous, so the mapping
    // must fail toward the counterexample — never a fabricated note.
    let code = r#"
#[trust_vc::ensures(#![verifier::proof_note("Test label #3")] result <= 10)]
#[trust_vc::ensures(result == 7)]
fn example(x: u64) -> u64 { 5 }
"#;
    let r = verify(code, "example");
    assert!(
        is_counterexample(&r),
        "an unlabeled failing ensures among labeled siblings must stay a counterexample, got {r:?}"
    );
}

#[test]
fn unlabeled_failing_assert_stays_counterexample() {
    // Baseline taxonomy pin: no label anywhere -> verdict class unchanged.
    let code = r#"
fn caller() {
    trust_vc::assert!(1 > 2);
}
"#;
    let r = verify(code, "caller");
    assert!(
        is_counterexample(&r),
        "an unlabeled failing assert must stay a counterexample, got {r:?}"
    );
}

// ---------------------------------------------------------------------------
// NEGATIVE CONTROLS: no over-rejection, no silent behavior change
// ---------------------------------------------------------------------------

#[test]
fn single_label_on_passing_assert_verifies() {
    let code = r#"
fn caller() {
    #[verifier::proof_note("this assert holds")]
    trust_vc::assert!(2 > 1);
}
"#;
    let r = verify(code, "caller");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "a single label on a passing assert must not change the verdict, got {r:?}"
    );
}

#[test]
fn one_label_per_clause_on_two_clauses_is_legal() {
    // The at-most-one rule pools PER CLAUSE; two clauses with one label each
    // are legal upstream (TEST_REQUIRES1 shape).
    let code = r#"
#[trust_vc::requires(#![verifier::proof_note("clause one")] a <= b)]
#[trust_vc::requires(#![verifier::proof_note("clause two")] b <= c)]
fn test_requires1(a: u64, b: u64, c: u64) {}

fn caller() {
    test_requires1(1, 2, 3);
}
"#;
    let r = verify(code, "caller");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "one label per clause must not trip the at-most-one rule, got {r:?}"
    );
}

#[test]
fn unrelated_attr_is_not_pooled_with_a_label() {
    let code = r#"
fn caller() {
    #[allow(unused_comparisons)]
    #[verifier::proof_note("only one label")]
    trust_vc::assert!(2 > 1);
}
"#;
    let r = verify(code, "caller");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "unrelated attributes must not pool as labels, got {r:?}"
    );
}

#[test]
fn expr_level_label_in_assume_keeps_verifying() {
    // Upstream test_requires3's expr-level proof_note inside assume() —
    // must parse, strip, and keep the proof flowing (P12 shape).
    let code = r#"
fn test(a: u64, b: u64, c: u64) {
    trust_vc::assume!(a <= b);
    trust_vc::assume!(#[verifier::proof_note("Test label #2")] (b <= c));
    trust_vc::assert!(a <= c);
}
"#;
    let r = verify(code, "test");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "an expression-level label inside assume!() must not break the proof, got {r:?}"
    );
}

#[test]
fn bare_and_foreign_qualified_spellings_are_not_labels() {
    // Only `verifier::`/`trust_vc::`-qualified proof_note/custom_err are
    // recognized; a user attribute merely named `proof_note` must not change
    // verdict semantics (the failing assert stays a counterexample) and two
    // of them must not trip the at-most-one rule.
    let code = r#"
fn caller() {
    #[proof_note("not ours")]
    #[other::proof_note("also not ours")]
    trust_vc::assert!(1 > 2);
}
"#;
    let r = verify(code, "caller");
    assert!(
        is_counterexample(&r),
        "unrecognized spellings must be inert, got {r:?}"
    );
}

#[test]
fn malformed_label_argument_fails_closed() {
    // A recognized label with a non-string argument must not be silently
    // dropped — fail-closed with an honest (non-upstream) message.
    let code = r#"
fn caller() {
    #[verifier::proof_note(42)]
    trust_vc::assert!(2 > 1);
}
"#;
    let r = verify(code, "caller");
    assert!(
        err_message(&r).contains("expects exactly one string-literal argument"),
        "a malformed label must fail closed, got {r:?}"
    );
}

#[test]
fn labeled_obligation_never_verifies_spuriously() {
    // Adversarial: the label machinery must be metadata-only — a labeled
    // FALSE assert must never become Verified through any label path.
    let code = r#"
fn caller() {
    #[verifier::proof_note("x")]
    trust_vc::assert!(false);
}
"#;
    let r = verify(code, "caller");
    assert!(
        !matches!(r, Ok(VerifyResult::Verified)),
        "a labeled false assert must never verify, got {r:?}"
    );
}
