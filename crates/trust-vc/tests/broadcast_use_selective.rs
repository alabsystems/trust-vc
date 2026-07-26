// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Proc-macro integration tests for grouped broadcast activation (#2414).

mod common;

use trust_vc::{broadcast, spec};
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

#[spec]
#[trust_vc::opaque]
fn grouped_identity(x: u64) -> u64 {
    x
}

#[spec]
#[trust_vc::opaque]
fn global_successor(x: u64) -> u64 {
    x + 1
}

#[trust_vc::broadcast_group(arith)]
#[broadcast]
#[trust_vc::trigger(grouped_identity(x))]
fn lemma_grouped_identity(x: u64) {
    trust_vc::ensures!(grouped_identity(x) == x);
}

#[broadcast]
#[trust_vc::trigger(global_successor(x))]
fn lemma_global_successor(x: u64) {
    trust_vc::ensures!(global_successor(x) == x + 1u64);
}

#[spec]
#[trust_vc::opaque]
fn named_group_identity(x: u64) -> u64 {
    x
}

#[spec]
#[trust_vc::opaque]
fn named_group_successor(x: u64) -> u64 {
    x + 1
}

#[trust_vc::broadcast_group(alpha_only)]
#[broadcast]
#[trust_vc::trigger(named_group_identity(x))]
fn lemma_named_group_identity(x: u64) {
    trust_vc::ensures!(named_group_identity(x) == x);
}

#[trust_vc::broadcast_group(beta_only)]
#[broadcast]
#[trust_vc::trigger(named_group_successor(x))]
fn lemma_named_group_successor(x: u64) {
    trust_vc::ensures!(named_group_successor(x) == x + 1u64);
}

trust_vc::reveal_group!(named_broadcast_bundle {
    lemma_named_group_identity,
    lemma_named_group_successor
});

fn verify_case<F>(case: F) -> VerifyResult
where
    F: FnOnce(),
{
    common::with_clean_verification(|| {
        verify_macro::set_proof_mode(true);
        case();
        verify_macro::set_proof_mode(false);
        VerificationPipeline::collect_from_macros().verify()
    })
}

#[test]
fn test_grouped_broadcast_without_import_fails() {
    let result = verify_case(|| {
        let _ = grouped_identity(0u64);
        let _ = global_successor(0u64);
        lemma_grouped_identity(0u64);
        lemma_global_successor(0u64);
        trust_vc::assert!(grouped_identity(3u64) == 3u64);
    });
    assert!(
        !matches!(result, VerifyResult::Verified),
        "grouped broadcast should stay inactive without broadcast_use, got: {:?}",
        result
    );
}

#[test]
fn test_grouped_broadcast_with_import_verifies() {
    let result = verify_case(|| {
        let _ = grouped_identity(0u64);
        let _ = global_successor(0u64);
        lemma_grouped_identity(0u64);
        lemma_global_successor(0u64);
        trust_vc::broadcast_use!(arith);
        trust_vc::assert!(grouped_identity(3u64) == 3u64);
        trust_vc::assert!(global_successor(3u64) == 4u64);
    });
    assert!(
        matches!(result, VerifyResult::Verified),
        "grouped broadcast should verify once imported, got: {:?}",
        result
    );
}

#[test]
fn test_ungrouped_broadcast_remains_global() {
    let result = verify_case(|| {
        let _ = grouped_identity(0u64);
        let _ = global_successor(0u64);
        lemma_grouped_identity(0u64);
        lemma_global_successor(0u64);
        trust_vc::assert!(global_successor(3u64) == 4u64);
    });
    assert!(
        matches!(result, VerifyResult::Verified),
        "ungrouped broadcast should remain globally active, got: {:?}",
        result
    );
}

#[test]
fn test_named_reveal_group_imports_member_broadcast_groups() {
    let result = verify_case(|| {
        let _ = named_group_identity(0u64);
        let _ = named_group_successor(0u64);
        lemma_named_group_identity(0u64);
        lemma_named_group_successor(0u64);
        trust_vc::broadcast_use!(named_broadcast_bundle);
        trust_vc::assert!(named_group_identity(3u64) == 3u64);
        trust_vc::assert!(named_group_successor(3u64) == 4u64);
    });
    assert!(
        matches!(result, VerifyResult::Verified),
        "named reveal groups should import member broadcast_group tags, got: {:?}",
        result
    );
}
