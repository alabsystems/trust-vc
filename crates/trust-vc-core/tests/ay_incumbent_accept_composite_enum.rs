// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// NON-VACUOUS native-deductive verification of the OPTIMIZATION INCUMBENT
// accept-core soundness stated as ONE contract over the ACTUAL composite ENUM
// return `Verdict { Reject, Accept(i128) }`:
//
//     result == if feasible { Accept(exact recompute) } else { Reject }
//
// This is the combined obligation that was historically Unknown in the DT+BV
// route. The blocker was NOT the datatype theory itself but an ay incremental
// PUSH-SCOPE completeness gap: the negated postcondition, asserted inside a
// `(push)` frame, returned Unknown (fail-closed, never a false Verified) where
// the IDENTICAL formula decided at base scope / via the assumption mechanism is
// UNSAT. The trust-vc verify path now recovers from that fail-closed Unknown by
// re-solving the SAME query through `check_sat_assuming` (no push frame); see
// `encoder/verification/solve.rs` (#enum-incremental) and the pinned divergence
// in `tests/repro_enum_incremental.rs`.
//
// Companion to `ay_incumbent_accept_composite.rs` (the STRUCT form). The
// trust-vc verification ENGINE has no rustc_private dependency, so this runs on
// the Trust toolchain's unverified lane:
// `targo --unverified test --locked -p trust-vc-core --test ay_incumbent_accept_composite_enum`.
// Override the fixture with `AY_PB_PROOF_SRC`.

use trust_vc_core::verify_function_from_file;
use trust_vc_core::VerifyResult;

fn proof_source() -> String {
    std::env::var("AY_PB_PROOF_SRC").unwrap_or_else(|_| {
        format!(
            "{}/tests/fixtures/ay_incumbent_accept_composite_enum.rs",
            env!("CARGO_MANIFEST_DIR")
        )
    })
}

fn verify(name: &str) -> VerifyResult {
    verify_function_from_file(&proof_source(), name)
        .unwrap_or_else(|e| panic!("{name} should extract+verify, got error: {e}"))
}

/// The composite-return ENUM accept-decision PROVES its combined contract:
/// `result == if feasible { Accept(actual) } else { Reject }`.
#[test]
fn enum_composite_verified() {
    let v = verify("incumbent_accept_composite");
    assert!(
        matches!(v, VerifyResult::Verified),
        "enum composite accept-decision must PROVE its combined contract; got {v:?}"
    );
}

/// NON-VACUITY CONTROL: storing the unchecked `claimed` objective on the accept
/// path MUST be refuted with a concrete counterexample.
#[test]
fn enum_composite_wrong_refuted() {
    let v = verify("incumbent_accept_composite_wrong");
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "WRONG enum composite (stores unchecked claim) MUST be a Counterexample; got {v:?}"
    );
}

/// FRESH-INVALID CONTROL (off-by-one): the body stores the exact recompute but
/// the contract demands `Accept(actual + 1)`. MUST be Counterexample — guards
/// that the incremental-completeness fallback never vacuously verifies a
/// genuinely-invalid datatype obligation.
#[test]
fn enum_composite_offbyone_refuted() {
    let v = verify("incumbent_accept_composite_offbyone_wrong");
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "FRESH-INVALID enum composite (ensures Accept(actual+1)) MUST be a \
         Counterexample, never vacuously Verified; got {v:?}"
    );
}
