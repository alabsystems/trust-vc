// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// NON-VACUOUS native-deductive verification of the OPTIMIZATION INCUMBENT
// accept-core soundness stated as ONE contract over a COMPOSITE (struct) RETURN
// value — the decidable composite-return form (companion to the scalar-halves
// proof in `ay_incumbent_vig_realbody.rs`). The combined `#[ensures]` over
// `AcceptDecision { accepted, value }` asserts BOTH P1 (accept ⟺ the VIG
// `feasible` decision) and P2 (on the accept path the stored objective is the
// EXACT recompute, never a producer's unchecked claim).
//
// This fixture also pins the durable PATTERN for stating multi-field
// accept-decision soundness as a single composite obligation: build the struct
// ONCE from straight-line-bound fields (trivial constructor payloads), which the
// `ay` datatype-UF layer decides — sidestepping the `Ite`-over-distinct-
// constructors shape that returns `Unknown` (documented in
// `ay_incumbent_vig_realbody.rs`).
//
// The trust-vc verification ENGINE has no rustc_private dependency, so this
// runs in minutes on the Trust toolchain's unverified lane:
// `targo --unverified test --locked -p trust-vc-core --test ay_incumbent_accept_composite`.
// Override the fixture with `AY_PB_PROOF_SRC`.

use trust_vc_core::verify_function_from_file;
use trust_vc_core::VerifyResult;

fn proof_source() -> String {
    std::env::var("AY_PB_PROOF_SRC").unwrap_or_else(|_| {
        format!(
            "{}/tests/fixtures/ay_incumbent_accept_composite.rs",
            env!("CARGO_MANIFEST_DIR")
        )
    })
}

fn verify(name: &str) -> VerifyResult {
    verify_function_from_file(&proof_source(), name)
        .unwrap_or_else(|e| panic!("{name} should extract+verify, got error: {e}"))
}

/// The composite accept-decision PROVES its combined contract: `result.accepted
/// == feasible` AND `result.accepted ==> result.value == actual`.
#[test]
fn incumbent_accept_composite_verified() {
    let v = verify("incumbent_accept_composite");
    assert!(
        matches!(v, VerifyResult::Verified),
        "composite accept-decision must PROVE its combined contract; got {v:?}"
    );
}

/// NON-VACUITY CONTROL: storing the unchecked `claimed` objective on the accept
/// path (dropping the `claimed == actual` guard) MUST be refuted with a concrete
/// counterexample (`feasible = true`, `claimed != actual`).
#[test]
fn incumbent_accept_composite_wrong_refuted() {
    let v = verify("incumbent_accept_composite_wrong");
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "WRONG composite accept-decision (stores unchecked claim) MUST be \
         refuted with a counterexample; got {v:?}"
    );
}
