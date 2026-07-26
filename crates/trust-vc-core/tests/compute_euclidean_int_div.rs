// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
//! Round-2 soundness audit (compute-fallback cluster): `int`/`nat` div/mod in the
//! ComputeEvaluator must be Euclidean, not Rust-truncating, or the compute
//! fallback manufactures a false `Verified` on negative-`int` div/mod goals.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn path() -> String {
    format!(
        "{}/tests/data/compute_euclidean_int_div.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}
fn v(f: &str) -> VerifyResult {
    verify_function_from_file(&path(), f).unwrap_or_else(|e| panic!("verify {f}: {e:?}"))
}

#[test]
fn truncated_int_div_mod_goals_do_not_verify() {
    for f in [
        "dq_neg_trunc_false",
        "dr_neg_trunc_false",
        "dr_neg8_trunc_false",
    ] {
        assert!(!matches!(v(f), VerifyResult::Verified),
            "UNSOUND: truncated-semantics goal {f} must NOT Verify (int div/mod is Euclidean), got {:?}", v(f));
    }
}

#[test]
fn euclidean_int_div_mod_goals_verify() {
    for f in [
        "dq_neg_eucl_true",
        "dr_neg_eucl_true",
        "dr_neg8_eucl_true",
        "pos_true",
    ] {
        assert!(
            matches!(v(f), VerifyResult::Verified),
            "Euclidean div/mod goal {f} must Verify, got {:?}",
            v(f)
        );
    }
}
