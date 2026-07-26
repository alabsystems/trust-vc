// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Manifest validation regressions for named reveal groups.

mod common;

use trust_vc::spec;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod first_def {
    use super::spec;

    #[spec]
    #[trust_vc::opaque]
    pub fn left_member(x: u64) -> u64 {
        x + 1
    }

    trust_vc::reveal_group!(dup_bundle { left_member });
}

mod second_def {
    use super::spec;

    #[spec]
    #[trust_vc::opaque]
    pub fn right_member(x: u64) -> u64 {
        x + 2
    }

    trust_vc::reveal_group!(dup_bundle { right_member });
}

#[test]
fn test_duplicate_named_group_definitions_fail_closed() {
    let result = common::with_clean_verification(|| {
        verify_macro::set_proof_mode(true);
        trust_vc::reveal!(dup_bundle);
        verify_macro::set_proof_mode(false);
        VerificationPipeline::collect_from_macros().verify()
    });

    assert!(
        matches!(result, VerifyResult::Error { ref message } if message.contains("duplicate named reveal group `dup_bundle`")),
        "duplicate named reveal group definitions must surface as VerifyResult::Error, got: {result:?}"
    );
}
