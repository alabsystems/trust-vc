// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Native deductive discharge of the AY pseudo-Boolean soundness contracts
// LIFTED ONTO THE REAL ay-pb TYPES.
//
// The proof source is the artifact committed to the `ay` repo at
// `crates/ay-pb/proofs/trust_vc/gate_and_eval_lemmas.rs`. Unlike the bare-i128
// fixture (`ay_native_gate_eval_lemmas.rs`), the eval_constraint lemmas here take
// an actual `PbConstraint` value and reproduce `eval_constraint`'s decision —
// the `match constraint.rel` over `PbRel::Ge`/`PbRel::Eq` and the
// `constraint.rhs` field read — so the obligation is literally about the real
// datatype defined in `crates/ay-pb/src/types.rs`. `verify_function_from_file`
// parses the file, collects the type defs into the source registry, lowers each
// function to typed IR (i128 => BV128; PbConstraint/PbRel => native datatypes;
// Vec<PbTerm> => Seq(Datatype)), encodes to `ay`, and refutes the negation.

use trust_vc_core::verify_function_from_file;
use trust_vc_core::VerifyResult;

/// The proof source. `tests/fixtures/ay_real_gate_eval_lemmas.rs` is a verbatim
/// copy of the artifact committed to the `ay` repo at
/// `crates/ay-pb/proofs/trust_vc/gate_and_eval_lemmas.rs` (kept in sync the same
/// way as the bare-i128 fixture). Override with `AY_PB_PROOF_SRC` to verify
/// directly against an `ay` checkout.
fn proof_source() -> String {
    std::env::var("AY_PB_PROOF_SRC").unwrap_or_else(|_| {
        format!(
            "{}/tests/fixtures/ay_real_gate_eval_lemmas.rs",
            env!("CARGO_MANIFEST_DIR")
        )
    })
}

fn discharge(name: &str) {
    let r = verify_function_from_file(&proof_source(), name);
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "{name} must be Verified, got {r:?}"
    );
}

/// E1: eval_constraint's Ge decision faithful on the REAL PbConstraint/PbRel.
#[test]
fn eval_constraint_ge_faithful_real_discharged() {
    discharge("eval_constraint_ge_faithful_real");
}

/// E2: eval_constraint's Eq decision faithful on the REAL PbConstraint/PbRel.
#[test]
fn eval_constraint_eq_faithful_real_discharged() {
    discharge("eval_constraint_eq_faithful_real");
}

/// E3: the match selects the correct branch (decision totality) on the real type.
#[test]
fn eval_constraint_decision_total_real_discharged() {
    discharge("eval_constraint_decision_total_real");
}

/// E4: eval_terms i128 accumulation is exact / non-wrapping (BV128).
#[test]
fn eval_terms_sum_no_overflow_discharged() {
    discharge("eval_terms_sum_no_overflow");
}

/// G1 (PRIORITY): OPTIMUM gate soundness — incumbent value lower-bounds every
/// feasible objective (parameter-Skolemized universal).
#[test]
fn optimum_gate_sound_discharged() {
    discharge("optimum_gate_sound");
}

/// G2: incumbent is achieved AND minimal => it is THE global optimum.
#[test]
fn optimum_achieved_and_minimal_discharged() {
    discharge("optimum_achieved_and_minimal");
}

/// The OPTIMUM gate lemma's UNSAT certificate is re-checked by the independent
/// `trust-vc-kernel` resolution checker (not merely trusted from ay).
#[cfg(feature = "proof-certificates")]
#[test]
fn optimum_gate_lemma_kernel_rechecked() {
    use trust_vc_core::ir::TrustVcType;
    use trust_vc_core::vc::{ProofObligation, VerificationContext};
    use trust_vc_core::VerificationReportOptions;

    let mut ctx = VerificationContext::new();
    for v in ["value", "floor", "obj_x"] {
        ctx.declare_var_typed(v, TrustVcType::parse_or_opaque("i128"));
    }
    ctx.push_obligation(ProofObligation::assume("guard", "value <= floor"));
    ctx.push_obligation(ProofObligation::assume("lb_sound", "floor <= obj_x"));
    ctx.push_obligation(ProofObligation::assert("optimum", "value <= obj_x"));

    let report = ctx.verify_with_report(VerificationReportOptions::new());
    assert!(matches!(report.result(), VerifyResult::Verified));
    let proof = report
        .proof()
        .expect("verified result carries a proof certificate");
    assert!(
        proof.kernel_verified(),
        "gate lemma UNSAT cert must be re-checked by trust-vc-kernel"
    );
}
