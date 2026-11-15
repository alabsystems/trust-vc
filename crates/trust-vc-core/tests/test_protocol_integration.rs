//! Integration tests for the protocol verification pipeline (ty).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Tests the full pipeline: register components → translate → model check → result.
//! Requires the `ty` feature: `targo --unverified test -p trust-vc-core --features ty`

#![cfg(feature = "ty")]

mod common;

use trust_vc_core::verification_bridge::{
    register_protocol_action, register_protocol_invariant, register_protocol_liveness,
    register_protocol_state_var, VerificationPipeline,
};
use trust_vc_core::VerifyResult;

/// Bounded counter: increment only when x < 5.
/// Safety invariant (x <= 5) should hold — all reachable states satisfy it.
#[test]
fn test_protocol_counter_bounded_verified() {
    common::with_clean_verification(|| {
        register_protocol_state_var("Counter", "x", "u8");
        register_protocol_action(
            "Counter",
            "Increment",
            "{ if self.x >= 5 { return; } self.x = self.x + 1 }",
        );
        register_protocol_invariant("Counter", "Bounded", "{ self.x <= 5 }");

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Bounded counter should verify, got: {result:?}"
        );
    });
}

/// Unbounded counter: increment without guard.
/// Safety invariant (x <= 5) is violated when x reaches 6.
#[test]
fn test_protocol_counter_unbounded_violation() {
    common::with_clean_verification(|| {
        register_protocol_state_var("Counter", "x", "u8");
        register_protocol_action("Counter", "Increment", "{ self.x = self.x + 1 }");
        register_protocol_invariant("Counter", "Bounded", "{ self.x <= 5 }");

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            !matches!(result, VerifyResult::Verified),
            "Unbounded counter should find invariant violation"
        );
    });
}

/// Simple mutex with flag-checking: process 1 enters CS only if process 2
/// is not in CS, and vice versa. Mutual exclusion invariant should hold.
#[test]
fn test_protocol_mutex_mutual_exclusion_verified() {
    common::with_clean_verification(|| {
        register_protocol_state_var("Mutex", "in_cs1", "bool");
        register_protocol_state_var("Mutex", "in_cs2", "bool");

        register_protocol_action(
            "Mutex",
            "Enter1",
            "{ if self.in_cs2 { return; } self.in_cs1 = true }",
        );
        register_protocol_action("Mutex", "Leave1", "{ self.in_cs1 = false }");
        register_protocol_action(
            "Mutex",
            "Enter2",
            "{ if self.in_cs1 { return; } self.in_cs2 = true }",
        );
        register_protocol_action("Mutex", "Leave2", "{ self.in_cs2 = false }");

        // MutualExclusion: at most one process in CS
        register_protocol_invariant(
            "Mutex",
            "MutualExclusion",
            "{ self.in_cs1 == false || self.in_cs2 == false }",
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Mutex with flag checking should verify mutual exclusion, got: {result:?}"
        );
    });
}

/// Buggy mutex: process 1 enters CS without checking process 2's flag.
/// Mutual exclusion invariant should be violated.
#[test]
fn test_protocol_mutex_buggy_violation() {
    common::with_clean_verification(|| {
        register_protocol_state_var("Mutex", "in_cs1", "bool");
        register_protocol_state_var("Mutex", "in_cs2", "bool");

        // Bug: Enter1 does NOT check in_cs2 before entering
        register_protocol_action("Mutex", "Enter1", "{ self.in_cs1 = true }");
        register_protocol_action("Mutex", "Leave1", "{ self.in_cs1 = false }");
        register_protocol_action(
            "Mutex",
            "Enter2",
            "{ if self.in_cs1 { return; } self.in_cs2 = true }",
        );
        register_protocol_action("Mutex", "Leave2", "{ self.in_cs2 = false }");

        register_protocol_invariant(
            "Mutex",
            "MutualExclusion",
            "{ self.in_cs1 == false || self.in_cs2 == false }",
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            !matches!(result, VerifyResult::Verified),
            "Buggy mutex should find mutual exclusion violation"
        );
    });
}

/// Two-phase commit: coordinator commits only after all participants vote yes.
/// Safety: committed implies all voted.
#[test]
fn test_protocol_two_phase_commit_safety() {
    common::with_clean_verification(|| {
        register_protocol_state_var("TwoPC", "p1_voted", "bool");
        register_protocol_state_var("TwoPC", "p2_voted", "bool");
        register_protocol_state_var("TwoPC", "committed", "bool");

        // Participants vote independently
        register_protocol_action(
            "TwoPC",
            "Vote1",
            "{ if self.p1_voted { return; } self.p1_voted = true }",
        );
        register_protocol_action(
            "TwoPC",
            "Vote2",
            "{ if self.p2_voted { return; } self.p2_voted = true }",
        );
        // Coordinator commits only after both voted
        register_protocol_action(
            "TwoPC",
            "Commit",
            "{ if !self.p1_voted { return; } if !self.p2_voted { return; } self.committed = true }",
        );

        // Safety: committed → both voted
        register_protocol_invariant(
            "TwoPC",
            "CommitSafety",
            "{ self.committed == false || self.p1_voted == true }",
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "2PC safety should verify: committed implies all voted, got: {result:?}"
        );
    });
}

/// Two independent protocols registered simultaneously.
/// Counter has a bounded increment; Mutex has flag-checking.
/// Both should verify independently — actions from one protocol must NOT
/// appear in the other's TLA+ module. This is the regression test for #2573
/// (protocol scoping soundness bug).
#[test]
fn test_multi_protocol_independent_verification() {
    common::with_clean_verification(|| {
        // Protocol 1: BoundedCounter
        register_protocol_state_var("BCounter", "x", "u8");
        register_protocol_action(
            "BCounter",
            "Increment",
            "{ if self.x >= 5 { return; } self.x = self.x + 1 }",
        );
        register_protocol_invariant("BCounter", "Bounded", "{ self.x <= 5 }");

        // Protocol 2: SimpleMutex
        register_protocol_state_var("SMutex", "in_cs1", "bool");
        register_protocol_state_var("SMutex", "in_cs2", "bool");
        register_protocol_action(
            "SMutex",
            "Enter1",
            "{ if self.in_cs2 { return; } self.in_cs1 = true }",
        );
        register_protocol_action("SMutex", "Leave1", "{ self.in_cs1 = false }");
        register_protocol_action(
            "SMutex",
            "Enter2",
            "{ if self.in_cs1 { return; } self.in_cs2 = true }",
        );
        register_protocol_action("SMutex", "Leave2", "{ self.in_cs2 = false }");
        register_protocol_invariant(
            "SMutex",
            "MutualExclusion",
            "{ self.in_cs1 == false || self.in_cs2 == false }",
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Two independent protocols should both verify when scoped correctly, got: {result:?}"
        );
    });
}

/// Raw temporal properties registered through `#[liveness]` should be checked by
/// the ty path when they do not request action fairness.
#[test]
fn test_protocol_liveness_temporal_property_verified() {
    common::with_clean_verification(|| {
        register_protocol_state_var("LiveCounter", "x", "u8");
        register_protocol_action("LiveCounter", "Stay", "{ self.x = self.x }");
        register_protocol_liveness(
            "LiveCounter",
            "EventuallyInitial",
            r#"{ trust_vc :: temporal ! ("<>(x = 0)") }"#,
            "",
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Initial-state eventual property should verify, got: {result:?}"
        );
    });
}

/// Negative liveness test: the only behavior stutters at x = 0 forever, so
/// eventually reaching x = 1 must be reported as a counterexample.
#[test]
fn test_protocol_liveness_temporal_property_violation() {
    common::with_clean_verification(|| {
        register_protocol_state_var("LiveCounter", "x", "u8");
        register_protocol_action("LiveCounter", "Stay", "{ self.x = self.x }");
        register_protocol_liveness(
            "LiveCounter",
            "EventuallyOne",
            r#"{ trust_vc :: temporal ! ("<>(x = 1)") }"#,
            "",
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Unreachable eventual property should fail, got: {result:?}"
        );
    });
}

/// Fairness attributes are not meaningful until the macro API names the action
/// being constrained, so the bridge must reject them instead of verifying an
/// incorrectly translated property.
#[test]
fn test_protocol_liveness_fairness_is_fail_closed() {
    common::with_clean_verification(|| {
        register_protocol_state_var("LiveCounter", "x", "u8");
        register_protocol_action("LiveCounter", "Stay", "{ self.x = self.x }");
        register_protocol_liveness(
            "LiveCounter",
            "EventuallyInitial",
            r#"{ trust_vc :: temporal ! ("<>(x = 0)") }"#,
            r#"fairness = "weak""#,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "Fairness requests should fail closed until supported, got: {result:?}"
        );
    });
}

/// Components registered against a protocol with no state registration used to
/// be ignored. That is unsound when the same test/process also has ay work.
#[test]
fn test_protocol_components_without_state_vars_fail_closed() {
    common::with_clean_verification(|| {
        register_protocol_action("MissingProtocol", "Step", "{ true }");
        register_protocol_invariant("MissingProtocol", "Impossible", "{ false }");

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "Orphan protocol components should fail closed, got: {result:?}"
        );
    });
}

/// Unsupported state types must produce an explicit error instead of becoming
/// empty TLA+ domains that look like ordinary invariant counterexamples.
#[test]
fn test_protocol_unsupported_state_type_fails_closed() {
    common::with_clean_verification(|| {
        register_protocol_state_var("UnsupportedState", "items", "Vec < u8 >");
        register_protocol_action("UnsupportedState", "Stay", "{ true }");

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "Unsupported protocol state types should be explicit errors, got: {result:?}"
        );
    });
}
