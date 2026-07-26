// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Native deductive discharge of the AY pseudo-Boolean soundness contracts.
//
// The fixture `tests/fixtures/ay_gate_and_eval_lemmas.rs` is a verbatim copy of
// the proof artifact committed to the `ay` repo at
// `crates/ay-pb/proofs/trust_vc/gate_and_eval_lemmas.rs`. Each `#[trust_vc::proof]`
// function carries `requires!/ensures!/assert!` contracts that mirror the i128
// arithmetic of a real ay-pb soundness function (the OPTIMUM upgrade gate in
// portfolio.rs and eval_constraint in solver.rs). `verify_function_from_file`
// parses the fixture, lowers each function to typed IR, encodes to `ay` (i128 =>
// BV128), and refutes the negation; `Verified` means ay returned UNSAT.

use trust_vc_core::verify_function_from_file;
use trust_vc_core::VerifyResult;

fn fixture() -> String {
    format!(
        "{}/tests/fixtures/ay_gate_and_eval_lemmas.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn discharge(name: &str) {
    let r = verify_function_from_file(&fixture(), name);
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "{name} must be Verified, got {r:?}"
    );
}

/// PRIORITY: OPTIMUM gate soundness — incumbent value lower-bounds every
/// feasible objective (parameter-Skolemized universal).
#[test]
fn optimum_gate_sound_discharged() {
    discharge("optimum_gate_sound");
}

/// Incumbent is achieved AND minimal => it is THE global optimum.
#[test]
fn optimum_achieved_and_minimal_discharged() {
    discharge("optimum_achieved_and_minimal");
}

/// eval_constraint i128 accumulation is exact / non-wrapping (BV128).
#[test]
fn eval_constraint_sum_no_overflow_discharged() {
    discharge("eval_constraint_sum_no_overflow");
}

/// eval_constraint's Ge decision is total/faithful on the i128 sum (BV128).
#[test]
fn eval_constraint_ge_faithful_discharged() {
    discharge("eval_constraint_ge_faithful");
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
