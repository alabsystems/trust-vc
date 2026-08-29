// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! DISCRIMINATOR, one test per verdict-producing lane that could export an
//! unsound `Verified` for a syntactic self-disequality `a != a`.
//!
//! Before the 2026-08-25 amendment the hypothesis-robust demote lived only in
//! `typed_assertions::finish_regular_assertion_step`, i.e. only on the
//! regular-assertion lane. `typed::verify_typed_step` — the shared lane for
//! `assert ... by` conclusions AND their scoped assertions, the
//! postcondition-forwarding pre-pass, loop invariants and loop `ensures`,
//! `recommends`, and the WF1 floor — had NO demote at all: its whole
//! post-processing is `apply_vacuity_probe_to_result`. Four of those lanes
//! EXPORT a `Verified` as an assumption for every later obligation.
//!
//! Each EXPLOIT returns 0 while claiming `result == 1`, so it can only verify if
//! the lane exported a contradiction. Each CONTROL is genuinely true and pins
//! the no-over-rejection direction.
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fx() -> String {
    format!(
        "{}/tests/data/reflexive_neq_export_sites.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verdict(func: &str) -> Result<VerifyResult, String> {
    let start = std::time::Instant::now();
    let result = verify_function_from_file(&fx(), func).map_err(|err| err.to_string());
    eprintln!("[{func}] {:.2}s {result:?}", start.elapsed().as_secs_f64());
    result
}

#[test]
fn assert_by_conclusion_must_not_export_a_reflexive_disequality() {
    let result = verdict("assert_by_conclusion_export_exploit");
    assert!(
        !matches!(result, Ok(VerifyResult::Verified)),
        "CARDINAL: `assert_by!(a != a, {{}})` is false by reflexivity. Verifying a \
         function that returns 0 while claiming `result == 1` means the by-block's \
         conclusion was exported into `verified_assert_by` as a global assumption. \
         Got: {result:?}"
    );
}

#[test]
fn assert_by_scoped_assertion_must_not_export_a_reflexive_disequality() {
    let result = verdict("assert_by_scoped_export_exploit");
    assert!(
        !matches!(result, Ok(VerifyResult::Verified)),
        "CARDINAL: a scoped `assert!(a != a)` inside a by-block is false by \
         reflexivity; verifying the exploit means it was exported into \
         `verified_assert_by_for_scope`. Got: {result:?}"
    );
}

#[test]
fn forwarding_prepass_must_not_export_a_reflexive_disequality() {
    let result = verdict("forwarding_prepass_export_exploit");
    assert!(
        !matches!(result, Ok(VerifyResult::Verified)),
        "CARDINAL: the postcondition-forwarding pre-pass must not forward \
         `a != a` as an assumption. Got: {result:?}"
    );
}

#[test]
fn regular_assertion_lane_still_refuses() {
    // The lane that was ALREADY closed — pinned so the amendment cannot regress
    // it while closing the others.
    let result = verdict("regular_assertion_lane_control");
    assert!(
        !matches!(result, Ok(VerifyResult::Verified)),
        "regression on the pre-existing regular-assertion demote. Got: {result:?}"
    );
}

#[test]
fn true_datatype_disequality_in_an_assert_by_still_verifies() {
    // NO OVER-REJECTION — the direction the new guard most endangers.
    // `is_syntactic_self_disequality` requires STRUCTURALLY IDENTICAL operands,
    // so `dbl(Succ(Zero)) != Zero` never enters the short circuit.
    let result = verdict("assert_by_conclusion_true_neq_control");
    assert!(
        matches!(result, Ok(VerifyResult::Verified)),
        "OVER-REJECTION: a genuinely true datatype `!=` conclusion must still \
         verify. Got: {result:?}"
    );
}
