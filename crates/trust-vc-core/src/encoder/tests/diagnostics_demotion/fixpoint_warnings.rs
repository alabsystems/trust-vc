// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_full_assertion_path_warns_on_fixpoint_non_convergence() {
    let assertion_name = "full_path_fixpoint_non_convergence";
    let ctx = build_non_convergent_pipeline_context(assertion_name);

    let (result, warnings) = capture_warns(|| AYEncoder::verify(&ctx));

    expect_fail_closed(&result, "non-convergent body-axiom chain must not verify");
    let warning = warnings
        .iter()
        .find(|event| event.assertion.as_deref() == Some(assertion_name))
        .unwrap_or_else(|| {
            panic!(
                "expected non-convergence warning for '{}', captured warnings: {:?}",
                assertion_name, warnings
            )
        });
    assert_eq!(
        warning.message.as_deref(),
        Some("Ground pool fixpoint did not converge within round limit"),
        "full assertion path should emit the non-convergence warning"
    );
}

#[test]
fn test_full_assertion_path_stays_quiet_when_fixpoint_converges() {
    let assertion_name = "full_path_fixpoint_converged";
    let ctx = build_convergent_pipeline_context(assertion_name);

    let (result, warnings) = capture_warns(|| AYEncoder::verify(&ctx));

    expect_verified(&result, "convergent body axiom should verify cleanly");
    assert!(
        warnings
            .iter()
            .all(|event| event.assertion.as_deref() != Some(assertion_name)),
        "convergent full assertion path must not emit non-convergence warnings: {:?}",
        warnings
    );
}

/// Non-convergent ground pool + verified assertion = NO demotion (LOW risk).
#[test]
fn test_ground_fixpoint_non_convergence_verified_no_demotion() {
    let name = "reflexive_non_conv";
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(i32_spec_fn("f"));
    add_body_axiom_to_context(&mut ctx, "f(x) == f(x + 1) + 1");
    ctx.push_obligation(ProofObligation::assert(name, "f(0) == f(0)"));

    let (result, warnings) = capture_warns(|| AYEncoder::verify(&ctx));

    expect_verified(&result, "must verify");
    assert!(
        warnings.iter().any(|event| {
            event.assertion.as_deref() == Some(name)
                && event
                    .message
                    .as_deref()
                    .is_some_and(|message| message.contains("fixpoint did not converge"))
        }),
        "non-convergence warning must fire: {:?}",
        warnings
    );
}
