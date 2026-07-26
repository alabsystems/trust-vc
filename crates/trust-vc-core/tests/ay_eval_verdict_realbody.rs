// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// NON-VACUOUS native-deductive verification of the REAL ay-pb verdict-chain
// functions `eval_constraint` and `eval_objective_exact` — the actual solver.rs
// BODIES carrying the actual functional-correctness `#[ensures]`, whose contract
// AND body both CALL the `eval_terms` / `eval_terms_checked` folds and
// PATTERN-MATCH on the `PbRel` enum. The proof is non-vacuous precisely because
// the body's `eval_terms(&c.terms,a)` and the spec's `eval_terms(&c.terms,a)`
// are the same congruent uninterpreted symbol (function congruence is the
// body<->spec link). See the fixture header for the full mechanism.
//
// The positive real-body targets and exact UF controls in
// `tests/fixtures/ay_eval_verdict_realbody.rs` mirror the artifact committed to
// the `ay` repo at `crates/ay-pb/proofs/trust_vc/eval_verdict_realbody.rs`.
// The fixture additionally carries a verifier-local scalar Ge boundary control
// so the negative lane has a decisive concrete witness without overstating
// opaque-UF sequence model extraction. `AY_PB_PROOF_SRC` overrides the mirrored
// targets; verifier-local controls always use the checked-in fixture.

use trust_vc_core::verify_function_from_file;
use trust_vc_core::VerifyResult;

fn proof_source() -> String {
    std::env::var("AY_PB_PROOF_SRC").unwrap_or_else(|_| {
        format!(
            "{}/tests/fixtures/ay_eval_verdict_realbody.rs",
            env!("CARGO_MANIFEST_DIR")
        )
    })
}

fn fixture_source() -> String {
    format!(
        "{}/tests/fixtures/ay_eval_verdict_realbody.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verify(name: &str) -> VerifyResult {
    verify_function_from_file(&proof_source(), name)
        .unwrap_or_else(|e| panic!("{name} should extract+verify, got error: {e}"))
}

fn verify_fixture(name: &str) -> VerifyResult {
    verify_function_from_file(&fixture_source(), name)
        .unwrap_or_else(|e| panic!("{name} should extract+verify, got error: {e}"))
}

// ─────────────────── TARGET 1: eval_constraint (REAL body) ───────────────────

/// The REAL `eval_constraint` body proves its `result == match c.rel { Ge =>
/// eval_terms(..) >= rhs, Eq => .. }` contract: congruence makes the body's and
/// the spec's `eval_terms(&c.terms, a)` the same value, so both reduce to the
/// identical match decision.
#[test]
fn eval_constraint_real_body_verified() {
    let v = verify("eval_constraint");
    assert!(
        matches!(v, VerifyResult::Verified),
        "REAL eval_constraint body must PROVE its functional contract; got {v:?}"
    );
}

/// EXACT-SHAPE SOUNDNESS CONTROL: the same contract on a WRONG real body (`>`
/// for `>=` in the Ge arm) MUST fail closed. When AY cannot extract the
/// opaque-UF-over-sequences witness, proof incompleteness is classified as a
/// model-less `NotProved`, never as acceptance or a resource `Unknown`.
#[test]
fn eval_constraint_wrong_ge_not_verified() {
    let v = verify("eval_constraint_wrong_ge");
    // Unknown-as-failure (docs/design-unknown-as-failure.md): the wrong body's
    // refutation now fail-closes to a model-less NotProved — still a verdict of
    // FAILURE (is_failure), which faithfully witnesses non-vacuity (the wrong
    // body does NOT verify).
    assert!(
        v.is_failure(),
        "WRONG exact-UF eval_constraint body (`>` for `>=`) MUST fail closed \
         (Counterexample or NotProved); got {v:?}"
    );
}

/// DECISIVE CONTROL: the identical `>`-versus-`>=` bug over explicit scalar
/// inputs MUST produce a concrete boundary witness (`rel=Ge`, `lhs=rhs`).
#[test]
fn eval_constraint_scalar_wrong_ge_refuted() {
    let v = verify_fixture("eval_constraint_scalar_wrong_ge");
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "scalar Ge boundary bug MUST be concretely refuted; got {v:?}"
    );
}

// ──────────────── TARGET 1b: eval_lit (REAL body, negation) ──────────────────

/// The REAL `eval_lit` body proves its `result == if lit.negated { !v } else { v
/// }` contract (the per-literal negation primitive). Non-vacuous via congruence
/// on the opaque `lit_value` lookup; exercises the `Expr::If`-over-let return-tail
/// scope substitution built for this proof.
#[test]
fn eval_lit_real_body_verified() {
    let v = verify("eval_lit");
    assert!(
        matches!(v, VerifyResult::Verified),
        "REAL eval_lit body must PROVE its negation contract; got {v:?}"
    );
}

/// NON-VACUITY CONTROL: a body that ignores the `negated` flag MUST be refuted
/// with a CONCRETE counterexample binding `lit = PbLit { .., negated: true }` and
/// `lit_value = true` (correct = false, wrong = true) — AY constructing a concrete
/// falsifying PbLit datatype value.
#[test]
fn eval_lit_ignore_negation_refuted() {
    let v = verify("eval_lit_ignore_negation");
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "negation-ignoring eval_lit body MUST be refuted with a counterexample; got {v:?}"
    );
}

// ──────────────── TARGET 2: eval_objective_exact (REAL body) ─────────────────

/// The REAL `eval_objective_exact` body proves its `result ==
/// eval_terms_checked(&objective.terms, assignment)` contract by congruence.
#[test]
fn eval_objective_exact_real_body_verified() {
    let v = verify("eval_objective_exact");
    assert!(
        matches!(v, VerifyResult::Verified),
        "REAL eval_objective_exact body must PROVE its functional contract; got {v:?}"
    );
}

/// NON-VACUITY CONTROL: a deliberately WRONG (negated) contract on the same body
/// (`result != eval_terms_checked(..)`) MUST be refuted — proving the
/// postcondition obligation is genuinely solver-checked, not vacuously dropped.
#[test]
fn eval_objective_exact_negated_contract_refuted() {
    let v = verify("eval_objective_exact_negated_contract");
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "negated eval_objective_exact contract MUST be refuted; got {v:?}"
    );
}

/// SATURATING-SUBSTITUTION CONTROL: the unsound saturating fold MUST NOT verify.
/// With the SAT-direction datatype model-distinguishability built for this task
/// (assumption-rooted element synthesis + `dt_diseq_opaque_satisfiable`), AY now
/// REFUTES it — the obligation negation is a disequality between two distinct
/// `Result<i128,_>`-valued UF applications, which AY satisfies with distinct
/// datatype values (previously `Unknown`). Asserting `!Verified` keeps the
/// SOUNDNESS pin while also covering the upgraded `Counterexample`.
#[test]
fn eval_objective_exact_wrong_saturating_not_verified() {
    let v = verify("eval_objective_exact_wrong_saturating");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "saturating substitution is unsound and MUST NOT verify; got {v:?}"
    );
}

/// CONCRETE-WITNESS form of the saturating-substitution gap (stated at the
/// `&[PbTerm]` level so the falsifying model binds the function's own `result`):
/// AY now refutes it with a CONCRETE `Result`-datatype counterexample binding
/// `result` (the saturating fold's value) to a concrete `Result` element distinct
/// from the checked fold's value — the SAT-direction datatype model construction.
#[test]
fn eval_terms_saturating_distinguishable_bare_refuted() {
    let v = verify("eval_terms_saturating_distinguishable_bare");
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "saturating-vs-checked distinguishability MUST be refuted with a concrete \
         datatype counterexample; got {v:?}"
    );
}

// ─────────────────── kernel-rechecked proof certificate ──────────────────────

/// The REAL `eval_constraint` discharge's UNSAT proof is re-checked by the
/// independent `trust-vc-kernel` (not merely trusted from ay): the whole-body
/// verification report carries a kernel-verified proof certificate.
#[cfg(feature = "proof-certificates")]
#[test]
fn eval_constraint_real_body_kernel_rechecked() {
    use trust_vc_core::extract_verification_conditions_with_file_context;
    use trust_vc_core::VerificationReportOptions;

    let content = std::fs::read_to_string(proof_source()).expect("read proof source");
    let ast = syn::parse_file(&content).expect("parse proof source");
    let func = ast
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(f) if f.sig.ident == "eval_constraint" => Some(f),
            _ => None,
        })
        .expect("eval_constraint present");

    let vc = extract_verification_conditions_with_file_context(&ast, func)
        .expect("extract eval_constraint VC");
    let report = vc.verify_with_report(VerificationReportOptions::new());
    assert!(
        matches!(report.result(), VerifyResult::Verified),
        "eval_constraint must verify under the report path; got {:?}",
        report.result()
    );
    let proof = report
        .proof()
        .expect("verified eval_constraint carries a proof certificate");
    assert!(
        proof.kernel_verified(),
        "eval_constraint UNSAT cert must be re-checked by trust-vc-kernel"
    );
}
