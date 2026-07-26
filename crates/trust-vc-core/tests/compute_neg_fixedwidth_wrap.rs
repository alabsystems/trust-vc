// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
//! Round-2 soundness audit (compute-fallback): fixed-width unary negation in the
//! ComputeEvaluator must wrap in two's complement, or the compute fallback
//! manufactures a false `Verified` on `-(i8::MIN) >= 0`.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn path() -> String {
    format!(
        "{}/tests/data/compute_neg_fixedwidth_wrap.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}
fn v(f: &str) -> VerifyResult {
    verify_function_from_file(&path(), f).unwrap_or_else(|e| panic!("verify {f}: {e:?}"))
}

#[test]
fn fixedwidth_min_negation_overflow_goals_do_not_verify() {
    for f in [
        "i8_min_neg_ge0_false",
        "i8_min_neg_eq0_false",
        "i16_min_neg_ge0_false",
    ] {
        assert!(
            !matches!(v(f), VerifyResult::Verified),
            "UNSOUND: fixed-width MIN-negation overflow goal {f} must NOT Verify, got {:?}",
            v(f)
        );
    }
}

#[test]
fn fixedwidth_negation_true_goals_verify() {
    for f in ["i8_min_neg_wraps_true", "i8_nonmin_neg_true"] {
        assert!(
            matches!(v(f), VerifyResult::Verified),
            "true negation goal {f} must Verify, got {:?}",
            v(f)
        );
    }
}
