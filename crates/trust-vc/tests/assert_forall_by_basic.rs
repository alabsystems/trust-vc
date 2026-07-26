// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(clippy::identity_op)]

use trust_vc::assert_forall_by;
use trust_vc_core::ir::TrustVcType;
use trust_vc_core::vc::ObligationKind;

mod common;

#[allow(dead_code)]
fn forall_trigger_predicate(_: u32) -> bool {
    true
}

#[test]
fn test_assert_forall_by_collects_scoped_bound_vars() {
    common::with_clean_verification(|| {
        assert_forall_by!(|k: u32| k + 0u32 == k, {
            trust_vc::assume!(k + 0u32 == k);
        });

        let ctx = trust_vc_core::verify_macro::get_context()
            .expect("assert_forall_by should create a verification context");
        let obligation = ctx
            .obligations()
            .iter()
            .find(|obligation| obligation.kind() == ObligationKind::AssertBy)
            .expect("assert_forall_by should collect an AssertBy obligation");

        let bound_vars = ctx
            .forall_bound_vars()
            .get(obligation.name())
            .expect("AssertBy obligation should have scoped forall binders");
        assert_eq!(bound_vars.len(), 1);
        assert_eq!(bound_vars[0].name, "k");
        assert_eq!(bound_vars[0].ty, TrustVcType::Uint { width: 32 });

        let scoped = ctx
            .assert_by_scopes()
            .get(obligation.name())
            .expect("AssertBy obligation should have a scoped proof block");
        assert_eq!(scoped.len(), 1);
        assert_eq!(scoped[0].kind(), ObligationKind::Assume);
    });
}

#[test]
#[rustfmt::skip]
fn test_assert_forall_by_collects_trigger_patterns() {
    common::with_clean_verification(|| {
        assert_forall_by!(|k: u32| #[trigger] forall_trigger_predicate(k) && k + 0u32 == k, {
            trust_vc::assume!(k + 0u32 == k);
        });

        let ctx = trust_vc_core::verify_macro::get_context()
            .expect("assert_forall_by should create a verification context");
        let obligation = ctx
            .obligations()
            .iter()
            .find(|obligation| obligation.kind() == ObligationKind::AssertBy)
            .expect("assert_forall_by should collect an AssertBy obligation");

        let patterns = obligation
            .trigger_patterns()
            .expect("AssertBy obligation should preserve explicit trigger patterns");
        assert_eq!(patterns.len(), 1);
        assert_eq!(patterns[0].len(), 1);
        assert!(
            patterns[0][0].contains("forall_trigger_predicate"),
            "unexpected trigger pattern: {patterns:?}"
        );
    });
}

#[test]
#[rustfmt::skip]
fn test_assert_forall_by_collects_verus_inner_trigger_group() {
    common::with_clean_verification(|| {
        assert_forall_by!(assert forall |k: u32| #![trigger forall_trigger_predicate(k)] forall_trigger_predicate(k) && k + 0u32 == k by {
            trust_vc::assume!(k + 0u32 == k);
        });

        let ctx = trust_vc_core::verify_macro::get_context()
            .expect("assert forall should create a verification context");
        let obligation = ctx
            .obligations()
            .iter()
            .find(|obligation| obligation.kind() == ObligationKind::AssertBy)
            .expect("assert forall should collect an AssertBy obligation");

        let patterns = obligation
            .trigger_patterns()
            .expect("AssertBy obligation should preserve Verus inner trigger patterns");
        assert_eq!(patterns.len(), 1);
        assert_eq!(patterns[0].len(), 1);
        assert!(
            patterns[0][0].contains("forall_trigger_predicate"),
            "unexpected trigger pattern: {patterns:?}"
        );
        assert!(
            !obligation.condition().contains("#![trigger"),
            "inner trigger attribute must not leak into the asserted condition"
        );
    });
}

#[test]
fn test_assert_forall_by_verifies_simple_scoped_proof() {
    let _ = common::verify_should_pass(|| {
        assert_forall_by!(|k: u32| k + 0u32 == k, {
            trust_vc::assume!(k + 0u32 == k);
        });
    });
}

#[test]
fn test_assert_macro_accepts_verus_style_forall_by_tokens() {
    common::with_clean_verification(|| {
        trust_vc::assert!(forall |k: u32| k + 0u32 == k by {
            trust_vc::assume!(k + 0u32 == k);
        });

        let ctx = trust_vc_core::verify_macro::get_context()
            .expect("assert forall should create a verification context");
        let obligation = ctx
            .obligations()
            .iter()
            .find(|obligation| obligation.kind() == ObligationKind::AssertBy)
            .expect("assert forall should collect an AssertBy obligation");

        let bound_vars = ctx
            .forall_bound_vars()
            .get(obligation.name())
            .expect("AssertBy obligation should have scoped forall binders");
        assert_eq!(bound_vars.len(), 1);
        assert_eq!(bound_vars[0].name, "k");
        assert_eq!(bound_vars[0].ty, TrustVcType::Uint { width: 32 });
    });
}

#[test]
#[rustfmt::skip]
fn test_assert_macro_accepts_assert_forall_tokens_with_inner_trigger_group() {
    common::with_clean_verification(|| {
        trust_vc::assert!(assert forall |k: u32| #![trigger forall_trigger_predicate(k)] forall_trigger_predicate(k) && k + 0u32 == k by {
            trust_vc::assume!(k + 0u32 == k);
        });

        let ctx = trust_vc_core::verify_macro::get_context()
            .expect("assert forall should create a verification context");
        let obligation = ctx
            .obligations()
            .iter()
            .find(|obligation| obligation.kind() == ObligationKind::AssertBy)
            .expect("assert forall should collect an AssertBy obligation");

        let bound_vars = ctx
            .forall_bound_vars()
            .get(obligation.name())
            .expect("AssertBy obligation should have scoped forall binders");
        assert_eq!(bound_vars.len(), 1);
        assert_eq!(bound_vars[0].name, "k");
        assert_eq!(bound_vars[0].ty, TrustVcType::Uint { width: 32 });

        let patterns = obligation
            .trigger_patterns()
            .expect("AssertBy obligation should preserve Verus inner trigger patterns");
        assert_eq!(patterns.len(), 1);
        assert_eq!(patterns[0].len(), 1);
        assert!(
            patterns[0][0].contains("forall_trigger_predicate"),
            "unexpected trigger pattern: {patterns:?}"
        );
        assert!(
            !obligation.condition().contains("#![trigger"),
            "inner trigger attribute must not leak into the asserted condition"
        );
    });
}

#[test]
fn test_assert_forall_by_macro_accepts_assert_forall_tokens() {
    common::with_clean_verification(|| {
        assert_forall_by!(assert forall |k: u32| k + 0u32 == k by {
            trust_vc::assume!(k + 0u32 == k);
        });

        let ctx = trust_vc_core::verify_macro::get_context()
            .expect("assert_forall_by should create a verification context");
        let obligation = ctx
            .obligations()
            .iter()
            .find(|obligation| obligation.kind() == ObligationKind::AssertBy)
            .expect("assert forall should collect an AssertBy obligation");

        let scoped = ctx
            .assert_by_scopes()
            .get(obligation.name())
            .expect("AssertBy obligation should have a scoped proof block");
        assert_eq!(scoped.len(), 1);
        assert_eq!(scoped[0].kind(), ObligationKind::Assume);
    });
}
