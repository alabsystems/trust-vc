// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// NON-VACUOUS native-deductive verification of the C3-1 SYMMETRY-CONVENTION-
// CONSISTENCY invariant — the bug fixed in `symmetry.rs` (`permutation_lex_
// leader_constraint` must emit the SAME keep-max convention as the always-on
// single-variable chain `lex_ge_constraint`, else a shared interchangeable pair
// is forced equal and the orbit is deleted -> false UNSAT). The lemmas prove the
// focused coefficient-pattern invariant the two emitters produce for a
// transposition; the keep-min controls (the pre-fix bug) are refuted with a
// concrete i128/BV128 counterexample. See the fixture header for the mechanism.
//
// `tests/fixtures/ay_symmetry_c3_lemmas.rs` is a verbatim copy of the artifact
// committed to the `ay` repo at `crates/ay-pb/proofs/trust_vc/`. Override the
// directory with `AY_PB_PROOF_DIR` to verify directly against an `ay` checkout.

use trust_vc_core::verify_function_from_file;
use trust_vc_core::VerifyResult;

fn proof_source() -> String {
    match std::env::var("AY_PB_PROOF_DIR") {
        Ok(dir) => format!("{dir}/symmetry_c3_lemmas.rs"),
        Err(_) => format!(
            "{}/tests/fixtures/ay_symmetry_c3_lemmas.rs",
            env!("CARGO_MANIFEST_DIR")
        ),
    }
}

fn verify(name: &str) -> VerifyResult {
    verify_function_from_file(&proof_source(), name)
        .unwrap_or_else(|e| panic!("{name} should extract+verify, got error: {e}"))
}

/// The keep-max convention keeps the orbit representative (x_hi=1, x_lo=0) on
/// BOTH the chain and the scalable transposition row — no orbit deletion. PROVES.
#[test]
fn c3_1_keepmax_keeps_orbit_representative_verified() {
    let v = verify("c3_1_keepmax_keeps_orbit_representative");
    assert!(
        matches!(v, VerifyResult::Verified),
        "keep-max orbit-representative survival must PROVE; got {v:?}"
    );
}

/// The keep-MIN (pre-fix) convention deletes the orbit representative — MUST be
/// refuted with a concrete (w_hi, w_lo) counterexample.
#[test]
fn c3_1_keepmin_keeps_orbit_representative_refuted() {
    let v = verify("c3_1_keepmin_keeps_orbit_representative");
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "keep-min orbit deletion MUST be refuted with a counterexample; got {v:?}"
    );
}

/// The keep-max scalable coefficient on the smaller index is positive — the same
/// sign convention as the single-variable chain's `+1`. PROVES.
#[test]
fn c3_1_keepmax_conventions_agree_verified() {
    let v = verify("c3_1_keepmax_conventions_agree");
    assert!(
        matches!(v, VerifyResult::Verified),
        "keep-max convention agreement must PROVE; got {v:?}"
    );
}

/// The keep-MIN scalable coefficient on the smaller index is negative — the
/// opposite of the chain (the C3-1 clash). MUST be refuted with a counterexample.
#[test]
fn c3_1_keepmin_conventions_agree_refuted() {
    let v = verify("c3_1_keepmin_conventions_agree");
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "keep-min convention clash MUST be refuted with a counterexample; got {v:?}"
    );
}
