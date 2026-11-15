// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// NON-VACUOUS native-deductive verification of the REAL ay-pb verdict-CHAIN
// gates `verify_all_constraints` (eval.rs:11, the Verified Incumbent Gate) and
// `optimum_upgrade_guard` (portfolio.rs:77, the `OptimumFound` upgrade gate) —
// the actual BODIES carrying the actual functional-correctness `#[ensures]`.
//
// `verify_all_constraints`'s contract is a FORALL over the constraint slice and
// its body is the real `constraints.iter().all(|c| eval_constraint(c, a))` fold;
// the proof is non-vacuous precisely because trust-vc lowers `.iter().all(..)` to
// the SAME bounded universal quantifier the contract spells out (the body<->spec
// link). `optimum_upgrade_guard`'s contract pins the gate to `value <= floor &&
// verify_all_constraints(..)` over the i128/BV128 bound and the congruent VIG
// predicate. See the fixture headers for the full mechanism.
//
// `tests/fixtures/ay_*_realbody.rs` are verbatim copies of the artifacts
// committed to the `ay` repo at `crates/ay-pb/proofs/trust_vc/`. Override the
// directory with `AY_PB_PROOF_DIR` to verify directly against an `ay` checkout.

use trust_vc_core::verify_function_from_file;
use trust_vc_core::VerifyResult;

fn proof_source(file: &str) -> String {
    match std::env::var("AY_PB_PROOF_DIR") {
        Ok(dir) => format!("{dir}/{file}"),
        Err(_) => format!("{}/tests/fixtures/ay_{file}", env!("CARGO_MANIFEST_DIR")),
    }
}

fn verify(file: &str, name: &str) -> VerifyResult {
    verify_function_from_file(&proof_source(file), name)
        .unwrap_or_else(|e| panic!("{name} should extract+verify, got error: {e}"))
}

const VAC: &str = "verify_all_constraints_realbody.rs";
const GATE: &str = "optimum_gate_realbody.rs";

// ───────────── TARGET 3: verify_all_constraints (REAL body) ──────────────

/// The REAL `verify_all_constraints` body proves its `result == forall|i| i <
/// constraints.len() ==> eval_constraint(&constraints[i], a)` contract: the
/// body's `constraints.iter().all(|c| eval_constraint(c, a))` lowers to the
/// identical (alpha-equivalent) bounded universal quantifier.
#[test]
fn verify_all_constraints_real_body_verified() {
    let v = verify(VAC, "verify_all_constraints");
    assert!(
        matches!(v, VerifyResult::Verified),
        "REAL verify_all_constraints body must PROVE its FORALL contract; got {v:?}"
    );
}

/// NON-VACUITY CONTROL: the WRONG (existential) gate reading on the same body
/// MUST NOT verify — the unsound `exists` contract would pass a MODEL violating
/// some constraint. trust-vc fails closed (a `forall` body is not alpha-equal to
/// an `exists` spec, so the equivalence is handed to ay, which does not return
/// `Verified`).
#[test]
fn verify_all_constraints_wrong_exists_not_verified() {
    let v = verify(VAC, "verify_all_constraints_wrong_exists");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "WRONG (exists) verify_all_constraints contract MUST NOT verify; got {v:?}"
    );
}

// ───────────── TARGET 4: optimum_upgrade_guard (REAL body) ───────────────

/// The REAL `optimum_upgrade_guard` body proves its `result == (value <= floor &&
/// verify_all_constraints(..))` contract by i128/BV128 comparison + congruence on
/// the VIG predicate.
#[test]
fn optimum_upgrade_guard_real_body_verified() {
    let v = verify(GATE, "optimum_upgrade_guard");
    assert!(
        matches!(v, VerifyResult::Verified),
        "REAL optimum_upgrade_guard body must PROVE its gate contract; got {v:?}"
    );
}

/// NON-VACUITY CONTROL: dropping the lower-bound guard (`result == VIG`, ignoring
/// `value <= floor`) is UNSOUND (it would fabricate a false `OptimumFound`) and
/// MUST NOT verify. trust-vc fails closed; the witness is `Unknown` rather than a
/// concrete `Counterexample` only because refuting it requires ay to construct a
/// `Seq`-of-datatype model value for `constraints` (the documented ay model-
/// construction boundary). The concrete counterexample is exhibited by the scalar
/// analogue below, pinning that the obligation is genuinely solver-checked.
#[test]
fn optimum_upgrade_guard_drop_floor_not_verified() {
    let v = verify(GATE, "optimum_upgrade_guard_drop_floor");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "drop-floor optimum_upgrade_guard contract MUST NOT verify; got {v:?}"
    );
}

/// CONCRETE-WITNESS non-vacuity: the same drop-floor gate decision over a SCALAR
/// VIG predicate is REFUTED with a concrete `Counterexample` (`value > floor`,
/// `vig == true`), proving the gate postcondition obligation is genuinely
/// solver-checked, not vacuously accepted.
#[test]
fn optimum_upgrade_guard_scalar_drop_floor_refuted() {
    let v = verify(GATE, "optimum_upgrade_guard_scalar_drop_floor");
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "scalar drop-floor gate MUST be refuted with a counterexample; got {v:?}"
    );
}

// ─────────────────── kernel-rechecked proof certificate ──────────────────────

/// The REAL `verify_all_constraints` discharge's UNSAT proof is re-checked by the
/// independent `trust-vc-kernel`: the FORALL-over-slice verdict carries a
/// kernel-verified proof certificate, not merely a trusted ay result.
///
/// The body's `.iter().all(..)` lowers to the same bounded `forall` term as the
/// ensures, so `result == forall ..` is `t == t` and the negated goal trust-vc
/// asserts is the constant `false`. The certificate refutes that posed query
/// and discloses the collapse: its evidence for `verify_all_constraints` is
/// AY's term-builder rewrite.
#[cfg(feature = "proof-certificates")]
#[test]
fn verify_all_constraints_real_body_kernel_rechecked() {
    use trust_vc_core::extract_verification_conditions_with_file_context;
    use trust_vc_core::VerificationReportOptions;

    let content = std::fs::read_to_string(proof_source(VAC)).expect("read proof source");
    let ast = syn::parse_file(&content).expect("parse proof source");
    let func = ast
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(f) if f.sig.ident == "verify_all_constraints" => Some(f),
            _ => None,
        })
        .expect("verify_all_constraints present");

    let vc = extract_verification_conditions_with_file_context(&ast, func)
        .expect("extract verify_all_constraints VC");
    let report = vc.verify_with_report(VerificationReportOptions::new());
    assert!(
        matches!(report.result(), VerifyResult::Verified),
        "verify_all_constraints must verify under the report path; got {:?}",
        report.result()
    );
    let proof = report
        .proof()
        .expect("verified verify_all_constraints carries a proof certificate");
    assert!(
        proof.kernel_verified(),
        "verify_all_constraints UNSAT cert must be re-checked by trust-vc-kernel: {proof:?}"
    );
    assert!(
        proof.query_collapsed(),
        "fixture drift: the goal no longer folds to `false`; update the doc above: {proof:?}"
    );
}
