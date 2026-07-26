//! Assert-by scope isolation tests (fixes #1547).
//! Proof-step localization tests (Part of #2652).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::*;
use crate::context_management::with_clean_thread_locals;
use crate::ir::TrustVcType;
use crate::vc::ObligationKind;

#[test]
fn test_assert_by_scope_isolation_assumption_does_not_leak() {
    // SOUNDNESS TEST: An assumption inside an assert_by proof block must NOT
    // be available for proving assertions outside the scope.
    //
    // Scenario: assume!(x > 100) inside assert_by proof block. After the
    // scope, an assertion requiring x > 100 should FAIL because the
    // assumption was scoped.
    //
    // Uses "int" type to route through LIA solver which has proper timeout
    // enforcement, unlike BV solver which ignores deadlines (#1605, #1623, #1650).
    use crate::vc::VerificationContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::MathInt);

    // Simulate assert_by with scoped assumption:
    //   assert_by!({
    //       assume!(x > 100);  // scoped
    //       x > 0              // condition to prove
    //   });
    //   assert!(x > 100);  // should FAIL — scoped assumption is gone
    let scoped = vec![crate::vc::ProofObligation::assume(
        "scoped_assume",
        "x > 100",
    )];
    ctx.add_assert_by("assert_by_scope_test", "x > 0", scoped);

    // Now add an assertion OUTSIDE the scope that requires the leaked assumption
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "should_fail_without_leak",
        "x > 100",
    ));

    let result = ctx.verify();
    // The assert_by should verify (scoped assumption helps prove x > 0).
    // But the outer assertion x > 100 should FAIL because the assumption
    // was scoped and didn't leak.
    assert!(
        matches!(result, crate::encoder::VerifyResult::Counterexample { .. }),
        "Outer assertion must FAIL when scoped assumption doesn't leak: {:?}",
        result
    );
}

#[test]
fn test_assert_by_proven_condition_available_as_assumption() {
    // The proven condition from assert_by! should be available as an
    // assumption for subsequent assertions in the outer context.
    //
    // assert_by!(x > 0, { assume!(x > 100); });
    // assert!(x > 0);  // should PASS — proven condition is available
    //
    // Uses "int" type to route through LIA solver which has proper timeout
    // enforcement, unlike BV solver which ignores deadlines (#1605, #1623, #1650).
    use crate::vc::VerificationContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::MathInt);

    let scoped = vec![crate::vc::ProofObligation::assume(
        "scoped_assume",
        "x > 100",
    )];
    ctx.add_assert_by("assert_by_proven", "x > 0", scoped);

    // This assertion should PASS because the proven condition (x > 0)
    // is now available as an assumption in the outer context
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "uses_proven_condition",
        "x > 0",
    ));

    let result = ctx.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "Proven condition must be available as assumption: {:?}",
        result
    );
}

#[test]
fn test_assert_by_scope_begin_end_integration() {
    // Test the begin/end scope functions that the macro expansion calls.
    // This verifies the thread-local scope tracking works correctly.
    with_clean_thread_locals(|| {
        // Collect a variable (auto-creates context)
        collect_variable("y".to_string(), "i32".to_string());

        // Begin assert_by scope
        begin_assert_by_scope("test_scope".to_string());

        // Inside scope: collect an assumption (simulates assume! in proof block)
        collect_obligation(
            ObligationKind::Assume,
            "proof_block_assume".to_string(),
            "y > 100".to_string(),
            None,
        );

        // End scope with condition
        end_assert_by_scope("y > 0".to_string(), Some("test.rs:42".to_string()));

        // Verify the context state
        let ctx = take_context().expect("Context should exist after scope operations");

        // Should have 1 obligation: AssertBy only (no _proven Assume, fixes #1642)
        assert_eq!(
            ctx.obligations.len(),
            1,
            "Expected 1 obligation (AssertBy only, no _proven Assume), got: {:?}",
            ctx.obligations
                .iter()
                .map(|o| (&o.name, &o.kind))
                .collect::<Vec<_>>()
        );

        // Should be AssertBy
        assert_eq!(ctx.obligations[0].kind, ObligationKind::AssertBy);
        assert_eq!(ctx.obligations[0].name, "test_scope");

        // Scoped obligations should be in assert_by_scopes
        let scoped = ctx.assert_by_scopes.get("test_scope");
        assert!(scoped.is_some(), "Scoped obligations should be stored");
        let scoped = scoped.unwrap();
        assert_eq!(scoped.len(), 1, "Should have 1 scoped obligation");
        assert_eq!(scoped[0].kind, ObligationKind::Assume);
        assert_eq!(scoped[0].name, "proof_block_assume");
    });
}

#[test]
fn test_assert_by_unprovable_condition_must_fail() {
    // DISCRIMINATING SOUNDNESS TEST: An assert_by with an UNPROVABLE
    // condition and EMPTY proof block must produce a Counterexample.
    //
    // This catches circular reasoning: if the encoder assumes the condition
    // being proven (via the _proven Assume obligation) during verification
    // of the AssertBy itself, the assertion would vacuously pass.
    //
    // Scenario: assert_by!(false, { /* no proof */ })
    // Expected: Counterexample — "false" cannot be proven from nothing.
    //
    // Uses "int" type to route through LIA solver which has proper timeout
    // enforcement, unlike BV solver which ignores deadlines (#1605, #1623).
    use crate::vc::VerificationContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::MathInt);

    // Empty proof block — no scoped assumptions to help prove the condition
    let scoped = vec![];
    ctx.add_assert_by("unprovable_assert_by", "false", scoped);

    let result = ctx.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Counterexample { .. }),
        "assert_by(false, {{}}) with empty proof block must FAIL — \
         if it passes, the encoder has circular reasoning (assumes what it proves): {:?}",
        result
    );
}

#[test]
fn test_assert_by_unrelated_condition_must_fail() {
    // DISCRIMINATING SOUNDNESS TEST: An assert_by where the proof block
    // does NOT support the assertion must fail.
    //
    // Scenario: assert_by!(y > 0, { assume!(x > 100); })
    //   The scoped assumption is about x, not y. The condition y > 0
    //   cannot be proven from x > 100 alone.
    //
    // Uses "int" type to route through LIA solver which has proper timeout
    // enforcement, unlike BV solver which ignores deadlines (#1605, #1623).
    use crate::vc::VerificationContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::MathInt);
    ctx.declare_var_typed("y", TrustVcType::MathInt);

    let scoped = vec![crate::vc::ProofObligation::assume(
        "scoped_about_x",
        "x > 100",
    )];
    ctx.add_assert_by("unrelated_proof", "y > 0", scoped);

    let result = ctx.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Counterexample { .. }),
        "assert_by(y > 0, {{ assume!(x > 100) }}) must FAIL — \
         proof block doesn't support assertion. If it passes, circular reasoning: {:?}",
        result
    );
}

#[test]
fn test_assert_by_scoped_assertion_must_verify_before_condition_is_trusted() {
    use crate::vc::VerificationContext;

    let mut ctx = VerificationContext::new();
    ctx.add_assert_by(
        "scoped_assertion_is_checked",
        "true",
        vec![crate::vc::ProofObligation::assert(
            "scoped_false_assert",
            "false",
        )],
    );

    let result = ctx.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Counterexample { .. }),
        "assertions inside assert_by proof blocks must be verified before the \
         enclosing condition is trusted: {:?}",
        result
    );
}

#[test]
fn test_multi_step_calc_step_condition_does_not_leak() {
    use crate::vc::VerificationContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::MathInt);

    ctx.add_assert_by(
        "calc_line_10_step_1",
        "x > 0",
        vec![crate::vc::ProofObligation::assume(
            "scoped_assume",
            "x > 100",
        )],
    );
    if let Some(last) = ctx.obligations.last_mut() {
        last.step_meta = Some(crate::vc::ProofStepMeta::new(
            "calc_line_10_step_1",
            "calc step 1 of 2",
        ));
    }

    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "outer_must_not_see_calc_step",
        "x > 0",
    ));

    let result = ctx.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Counterexample { .. }),
        "multi-step calc intermediates must not be available after the calc block: {:?}",
        result
    );
}

#[test]
fn test_multi_step_calc_conclusion_still_exports() {
    use crate::vc::VerificationContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::MathInt);

    ctx.add_assert_by(
        "calc_line_10_step_1",
        "x > 0",
        vec![crate::vc::ProofObligation::assume(
            "scoped_assume",
            "x > 100",
        )],
    );
    if let Some(last) = ctx.obligations.last_mut() {
        last.step_meta = Some(crate::vc::ProofStepMeta::new(
            "calc_line_10_step_1",
            "calc step 1 of 2",
        ));
    }

    ctx.add_assert_by(
        "calc_line_10_conclusion",
        "x > 0",
        vec![crate::vc::ProofObligation::assume(
            "calc_conclusion_step_1",
            "x > 0",
        )],
    );
    if let Some(last) = ctx.obligations.last_mut() {
        last.step_meta = Some(crate::vc::ProofStepMeta::new(
            "calc_line_10_conclusion",
            "calc conclusion",
        ));
    }

    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "outer_uses_calc_conclusion",
        "x > 0",
    ));

    let result = ctx.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "the final calc conclusion should remain available after the calc block: {:?}",
        result
    );
}

// ─── Proof-step localization tests (Part of #2652) ──────────────────────────

#[test]
fn test_begin_scope_with_label_sets_step_meta() {
    // begin_assert_by_scope_with_label should populate step_meta on the
    // resulting AssertBy obligation so display_name() returns the label
    // instead of the internal scope key.
    with_clean_thread_locals(|| {
        collect_variable("z".to_string(), "i32".to_string());

        begin_assert_by_scope_with_label(
            "calc_line_10_step_1".to_string(),
            Some("calc step 1 of 3".to_string()),
        );

        end_assert_by_scope("z > 0".to_string(), Some("test.rs:10:5".to_string()));

        let ctx = take_context().expect("Context should exist");
        assert_eq!(ctx.obligations.len(), 1);
        let ob = &ctx.obligations[0];
        assert_eq!(ob.kind, ObligationKind::AssertBy);
        assert_eq!(ob.name, "calc_line_10_step_1");

        let meta = ob.step_meta.as_ref().expect("step_meta should be set");
        assert_eq!(meta.key, "calc_line_10_step_1");
        assert_eq!(meta.label, "calc step 1 of 3");
    });
}

#[test]
fn test_begin_scope_without_label_has_no_step_meta() {
    // begin_assert_by_scope (no label) should NOT set step_meta.
    with_clean_thread_locals(|| {
        collect_variable("z".to_string(), "i32".to_string());
        begin_assert_by_scope("assert_by_line_42_col_5".to_string());
        end_assert_by_scope("z > 0".to_string(), None);

        let ctx = take_context().expect("Context should exist");
        assert_eq!(ctx.obligations.len(), 1);
        assert!(
            ctx.obligations[0].step_meta.is_none(),
            "plain begin_assert_by_scope should not set step_meta"
        );
    });
}

#[test]
fn test_calc_style_multiple_scopes_unique_keys() {
    // Simulate calc! expansion: 3 steps on the same line but with distinct
    // step indices. Each scope must get a unique key in assert_by_scopes.
    with_clean_thread_locals(|| {
        collect_variable("a".to_string(), "int".to_string());

        for step in 1..=3 {
            let key = format!("calc_line_20_step_{step}");
            let label = format!("calc step {step} of 3");
            begin_assert_by_scope_with_label(key, Some(label));
            end_assert_by_scope("a > 0".to_string(), Some("test.rs:20:1".to_string()));
        }

        let ctx = take_context().expect("Context should exist");

        // Should have exactly 3 AssertBy obligations with distinct scope keys
        assert_eq!(ctx.obligations.len(), 3);
        for (i, ob) in ctx.obligations.iter().enumerate() {
            let step = i + 1;
            assert_eq!(ob.kind, ObligationKind::AssertBy);
            assert_eq!(ob.name, format!("calc_line_20_step_{step}"));

            let meta = ob.step_meta.as_ref().expect("step_meta should be set");
            assert_eq!(meta.label, format!("calc step {step} of 3"));
        }

        // Each scope key must exist in assert_by_scopes
        for step in 1..=3 {
            assert!(
                ctx.assert_by_scopes
                    .contains_key(&format!("calc_line_20_step_{step}")),
                "scope key for step {step} must exist in assert_by_scopes"
            );
        }
    });
}

#[test]
fn test_calc_step_with_label_fails_shows_display_label() {
    // An assert_by with step_meta that FAILS should include the display
    // label in the counterexample obligation_name, not the internal key.
    use crate::vc::VerificationContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::MathInt);

    // Simulate calc step 2 of 3 that fails: "x > 100" is unprovable
    let scoped = vec![];
    ctx.add_assert_by("calc_line_10_step_2", "x > 100", scoped);

    // Manually set step_meta to match what the proc-macro expansion does
    if let Some(last) = ctx.obligations.last_mut() {
        last.step_meta = Some(crate::vc::ProofStepMeta::new(
            "calc_line_10_step_2",
            "calc step 2 of 3",
        ));
        last.location = Some("src/lib.rs:10:1".to_string());
    }

    let result = ctx.verify();
    match &result {
        crate::encoder::VerifyResult::Counterexample {
            obligation_name, ..
        } => {
            assert!(
                obligation_name.contains("calc step 2 of 3"),
                "counterexample obligation_name should contain display label, got: {obligation_name}"
            );
            assert!(
                !obligation_name.contains("calc_line_10_step_2"),
                "counterexample should NOT contain internal key, got: {obligation_name}"
            );
        }
        other => panic!("expected Counterexample for unprovable calc step, got: {other:?}"),
    }
}

#[test]
fn test_assert_by_with_label_verified_still_works() {
    // A provable assert_by with step_meta should still verify successfully.
    use crate::vc::VerificationContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::MathInt);

    let scoped = vec![crate::vc::ProofObligation::assume(
        "scoped_assume",
        "x > 100",
    )];
    ctx.add_assert_by("calc_line_5_step_1", "x > 0", scoped);

    if let Some(last) = ctx.obligations.last_mut() {
        last.step_meta = Some(crate::vc::ProofStepMeta::new(
            "calc_line_5_step_1",
            "calc step 1 of 2",
        ));
    }

    let result = ctx.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "provable calc step with step_meta should verify: {:?}",
        result
    );
}
