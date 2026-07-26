// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Cross-module regressions for manifest-backed named reveal/broadcast groups.

mod common;

use trust_vc::spec;
use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;

mod defs {
    use super::spec;

    #[spec]
    #[trust_vc::opaque]
    pub fn shared_alpha(x: u64) -> u64 {
        x + 1
    }

    #[spec]
    #[trust_vc::opaque]
    pub fn shared_beta(x: u64) -> u64 {
        x + 2
    }

    trust_vc::reveal_group!(shared_pair {
        shared_alpha,
        shared_beta
    });

    #[spec]
    #[trust_vc::opaque]
    pub fn grouped_identity(x: u64) -> u64 {
        x
    }

    #[spec]
    #[trust_vc::opaque]
    pub fn grouped_successor(x: u64) -> u64 {
        x + 1
    }

    #[trust_vc::broadcast_group(alpha_only)]
    #[trust_vc::broadcast]
    #[trust_vc::trigger(grouped_identity(x))]
    pub fn lemma_grouped_identity(x: u64) {
        trust_vc::ensures!(grouped_identity(x) == x);
    }

    #[trust_vc::broadcast_group(beta_only)]
    #[trust_vc::broadcast]
    #[trust_vc::trigger(grouped_successor(x))]
    pub fn lemma_grouped_successor(x: u64) {
        trust_vc::ensures!(grouped_successor(x) == x + 1u64);
    }

    trust_vc::reveal_group!(shared_broadcast_bundle {
        lemma_grouped_identity,
        lemma_grouped_successor
    });
}

#[test]
fn test_reveal_named_group_defined_in_other_module_registers_member_reveals() {
    let pipeline = common::with_clean_verification(|| {
        verify_macro::set_proof_mode(true);
        trust_vc::reveal!(shared_pair);
        verify_macro::set_proof_mode(false);
        VerificationPipeline::collect_from_macros()
    });

    let reveal_names = pipeline
        .context()
        .obligations()
        .iter()
        .filter(|obligation| obligation.kind() == ObligationKind::Reveal)
        .map(|obligation| obligation.name().to_string())
        .collect::<Vec<_>>();

    assert!(
        reveal_names == vec!["shared_alpha".to_string(), "shared_beta".to_string()],
        "cross-module reveal!(shared_pair) should register both member reveals, got: {reveal_names:?}"
    );
}

#[test]
fn test_broadcast_use_named_group_defined_in_other_module_registers_member_groups() {
    let pipeline = common::with_clean_verification(|| {
        verify_macro::set_proof_mode(true);
        trust_vc::broadcast_use!(shared_broadcast_bundle);
        verify_macro::set_proof_mode(false);
        VerificationPipeline::collect_from_macros()
    });

    let groups = pipeline.context().broadcast_use_groups();

    assert!(
        groups == ["shared_broadcast_bundle", "alpha_only", "beta_only"],
        "cross-module broadcast_use!(shared_broadcast_bundle) should register the manifest-backed group plus member broadcast groups, got: {groups:?}"
    );
}
