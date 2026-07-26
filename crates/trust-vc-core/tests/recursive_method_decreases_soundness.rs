// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Stage-2 termination now analyzes recursive INHERENT METHODS (previously
//! `MemberTermInfo::from_source_fn` bailed on any receiver, so every guarded
//! recursive method was conservatively suppressed → over-rejection). This suite
//! pins BOTH directions: a method with a VALID decreasing measure publishes its
//! body axiom (`good(0) == 0` verifies), and a method whose #[decreases] measure
//! does NOT shrink stays suppressed (the `m(s,n) == m(s,n)+1` / assert!(false)
//! exploits must fail closed). Cache-off throughout.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn repro_path() -> String {
    format!(
        "{}/tests/data/recursive_method_decreases_soundness_repro.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}
fn verdict(func: &str) -> VerifyResult {
    trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
        verify_function_from_file(&repro_path(), func).unwrap_or_else(|e| VerifyResult::Error {
            message: e.to_string(),
        })
    })
}

#[test]
fn valid_method_measure_publishes_axiom() {
    assert!(
        matches!(verdict("good_base"), VerifyResult::Verified),
        "OVER-REJECTION: a recursive method with a VALID decreasing measure must \
         publish its body axiom so good(0) == 0 verifies"
    );
}

#[test]
fn bogus_same_arg_measure_is_suppressed() {
    // n -> n (no shrink): the `+1` makes it the 0 == 1 exploit.
    assert!(
        !matches!(verdict("exploit_bad_same"), VerifyResult::Verified),
        "CARDINAL: a method recursing on the SAME argument (measure does not \
         shrink) must NOT publish a usable axiom"
    );
    assert!(
        !matches!(verdict("exploit_bad_same_false"), VerifyResult::Verified),
        "CARDINAL: assert!(false) must not verify via the bogus-measure method axiom"
    );
}

#[test]
fn bogus_increasing_measure_is_suppressed() {
    // n -> n+1 (clearly non-terminating).
    assert!(
        !matches!(verdict("exploit_bad_inc"), VerifyResult::Verified),
        "CARDINAL: a method recursing on an INCREASING argument must NOT publish \
         a usable axiom"
    );
}
