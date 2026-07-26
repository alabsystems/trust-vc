// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Integration tests for `trust_vc::closure!` contract macro (#1943).
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationPipeline.

use trust_vc_core::vc::VerificationMode;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

mod common;

// ── Postcondition tests ──────────────────────────────────────────────

#[test]
fn test_closure_ensures_postcondition_verified() {
    common::with_clean_verification(|| {
        let add1 = trust_vc::closure!(
            |x: i32|
            ensures(|res: i32| res == x + 1)
            x + 1
        );

        let result = add1(4);
        assert_eq!(result, 5);

        let pipeline = VerificationPipeline::collect_from_macros();
        let verify_result = pipeline.verify();
        assert!(
            matches!(verify_result, VerifyResult::Verified),
            "Closure postcondition `res == x + 1` should verify, got: {:?}",
            verify_result
        );
    });
}

#[test]
fn test_closure_ensures_false_postcondition_rejected() {
    let _ = common::verify_should_fail(|| {
        let bad_closure = trust_vc::closure!(
            |x: i32|
            ensures(|res: i32| res == x + 999)
            x + 1
        );

        bad_closure(4);
    });
}

#[test]
fn test_closure_counterexample_uses_source_param_and_result_names() {
    let result = common::verify_and_get_result(|| {
        let bad_closure = trust_vc::closure!(
            |item: i32|
            ensures(|res: i32| res == item + 999)
            item + 1
        );

        bad_closure(4);
    });

    match result {
        VerifyResult::Counterexample {
            model: Some(model), ..
        } => {
            assert!(
                model.contains("item = "),
                "counterexample should show the closure parameter name, got: {model}"
            );
            assert!(
                model.contains("res = "),
                "counterexample should show the ensures result binder, got: {model}"
            );
            assert!(
                !model.contains("__trust_vc_closure_arg0"),
                "counterexample should hide the raw closure parameter helper, got: {model}"
            );
            assert!(
                !model.contains("__trust_vc_closure_result"),
                "counterexample should hide the raw closure result helper, got: {model}"
            );
        }
        other => panic!("expected Counterexample with model, got {other:?}"),
    }
}

// ── Precondition tests ───────────────────────────────────────────────

#[test]
fn test_closure_requires_precondition_verified() {
    common::with_clean_verification(|| {
        let guarded = trust_vc::closure!(
            |x: i32|
            requires(x > 0)
            ensures(|res: i32| res > 0)
            x
        );

        let result = guarded(5);
        assert_eq!(result, 5);

        let pipeline = VerificationPipeline::collect_from_macros();
        let verify_result = pipeline.verify();
        assert!(
            matches!(verify_result, VerifyResult::Verified),
            "Closure with requires(x > 0) and ensures(res > 0) should verify, got: {:?}",
            verify_result
        );
    });
}

#[test]
fn test_option_and_then_contract_closure_precondition_verified() {
    common::with_clean_verification(|| {
        let step = trust_vc::closure!(
            |x: u32| -> Option<u32>
            requires(x < 1000u32)
            ensures(|res: Option<u32>| res == Option::<u32>::Some(x + 1u32))
            Option::<u32>::Some(x + 1u32)
        );

        let result = Some(2u32).and_then(step);
        assert_eq!(result, Some(3u32));

        let pipeline = VerificationPipeline::collect_from_macros();
        let verify_result = pipeline.verify();
        assert!(
            matches!(verify_result, VerifyResult::Verified),
            "Option::and_then closure contract precondition should verify in body mode, got: {:?}",
            verify_result
        );
    });
}

#[test]
fn test_option_and_then_contract_closure_precondition_rejected_at_call_site() {
    common::with_clean_verification(|| {
        let step = trust_vc::closure!(
            |x: u32| -> Option<u32>
            requires(x < 1000u32)
            ensures(|res: Option<u32>| res == Option::<u32>::Some(x + 1u32))
            Option::<u32>::Some(x + 1u32)
        );

        let result = Some(1000u32).and_then(step);
        assert_eq!(result, Some(1001u32));

        // #791: closures no longer expose a stable, externally-referenceable
        // `__trust_vc_closure_arg0` symbol (that shared name was the
        // cross-closure contamination hole). The call-site rejection no longer
        // needs a hand-injected fact about the argument: in CallSite mode the
        // closure's own `requires(x < 1000)` is *asserted* over its (now
        // per-closure-namespaced, unconstrained) parameter, so an arbitrary
        // call site cannot discharge it.
        let mut pipeline = VerificationPipeline::collect_from_macros();
        pipeline
            .context_mut()
            .set_verification_mode(VerificationMode::CallSite);
        let verify_result = pipeline.verify();
        assert!(
            matches!(
                verify_result,
                VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. }
            ),
            "Option::and_then closure precondition should be rejected in call-site mode, got: {:?}",
            verify_result
        );
    });
}

#[test]
fn test_option_ok_or_else_contract_closure_precondition_verified_at_call_site() {
    common::with_clean_verification(|| {
        let opt: Option<u32> = None;
        let result: Result<u32, u32> = opt.ok_or_else(trust_vc::closure!(
            || -> u32
            requires(true)
            ensures(|err: u32| err == 99u32)
            99u32
        ));
        assert_eq!(result, Err(99u32));

        let mut pipeline = VerificationPipeline::collect_from_macros();
        pipeline
            .context_mut()
            .set_verification_mode(VerificationMode::CallSite);
        let verify_result = pipeline.verify();
        assert!(
            matches!(verify_result, VerifyResult::Verified),
            "Option::ok_or_else fallback closure precondition should verify at call site, got: {:?}",
            verify_result
        );
    });
}

#[test]
fn test_option_ok_or_else_contract_closure_precondition_rejected_at_call_site() {
    common::with_clean_verification(|| {
        let opt: Option<u32> = None;
        let result: Result<u32, u32> = opt.ok_or_else(trust_vc::closure!(
            || -> u32
            requires(false)
            ensures(|err: u32| err == 99u32)
            99u32
        ));
        assert_eq!(result, Err(99u32));

        let mut pipeline = VerificationPipeline::collect_from_macros();
        pipeline
            .context_mut()
            .set_verification_mode(VerificationMode::CallSite);
        let verify_result = pipeline.verify();
        assert!(
            matches!(
                verify_result,
                VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. }
            ),
            "Option::ok_or_else fallback closure precondition should be rejected at call site, got: {:?}",
            verify_result
        );
    });
}

#[test]
fn test_option_unwrap_or_else_contract_closure_precondition_verified_at_call_site() {
    common::with_clean_verification(|| {
        let opt: Option<u32> = None;
        let result = opt.unwrap_or_else(trust_vc::closure!(
            || -> u32
            requires(true)
            ensures(|fallback: u32| fallback == 99u32)
            99u32
        ));
        assert_eq!(result, 99u32);

        let mut pipeline = VerificationPipeline::collect_from_macros();
        pipeline
            .context_mut()
            .set_verification_mode(VerificationMode::CallSite);
        let verify_result = pipeline.verify();
        assert!(
            matches!(verify_result, VerifyResult::Verified),
            "Option::unwrap_or_else fallback closure precondition should verify at call site, got: {:?}",
            verify_result
        );
    });
}

#[test]
fn test_option_unwrap_or_else_contract_closure_precondition_rejected_at_call_site() {
    common::with_clean_verification(|| {
        let opt: Option<u32> = None;
        let result = opt.unwrap_or_else(trust_vc::closure!(
            || -> u32
            requires(false)
            ensures(|fallback: u32| fallback == 99u32)
            99u32
        ));
        assert_eq!(result, 99u32);

        let mut pipeline = VerificationPipeline::collect_from_macros();
        pipeline
            .context_mut()
            .set_verification_mode(VerificationMode::CallSite);
        let verify_result = pipeline.verify();
        assert!(
            matches!(
                verify_result,
                VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. }
            ),
            "Option::unwrap_or_else fallback closure precondition should be rejected at call site, got: {:?}",
            verify_result
        );
    });
}

// ── Capture tests ────────────────────────────────────────────────────

#[test]
fn test_closure_captures_outer_variable() {
    common::with_clean_verification(|| {
        // Register captured variable `k` in the verification context.
        // In real code, surrounding trust_vc macros handle this; in a direct
        // test we register it manually (design: "surrounding proof/test code
        // already declares those locals through the current extraction path").
        trust_vc_core::verify_macro::collect_variable("k".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "k_value".to_string(),
            "k == 10".to_string(),
            Some("closure_contracts.rs:capture".to_string()),
        );

        let k = 10;
        let add_k = trust_vc::closure!(
            move |x: i32|
            ensures(|res: i32| res == x + 10)
            x + k
        );

        let result = add_k(3);
        assert_eq!(result, 13);

        let pipeline = VerificationPipeline::collect_from_macros();
        let verify_result = pipeline.verify();
        assert!(
            matches!(verify_result, VerifyResult::Verified),
            "Closure capturing outer `k=10` should verify, got: {:?}",
            verify_result
        );
    });
}

// ── Multi-parameter tests ────────────────────────────────────────────

#[test]
fn test_closure_two_parameters() {
    common::with_clean_verification(|| {
        let add = trust_vc::closure!(
            |a: i32, b: i32|
            ensures(|res: i32| res == a + b)
            a + b
        );

        let result = add(3, 7);
        assert_eq!(result, 10);

        let pipeline = VerificationPipeline::collect_from_macros();
        let verify_result = pipeline.verify();
        assert!(
            matches!(verify_result, VerifyResult::Verified),
            "Two-param closure `res == a + b` should verify, got: {:?}",
            verify_result
        );
    });
}

// ── Syntax-preservation regressions ──────────────────────────────────

#[test]
fn test_closure_struct_field_shorthand_preserved() {
    struct Point {
        x: i32,
        y: i32,
    }

    let project_x = trust_vc::closure!(
        |x: i32|
        ensures(|res: i32| res == x)
        {
            let point: Point = Point { x, y: x + 1 };
            let _ = point.y;
            point.x
        }
    );

    let result = project_x(4);
    assert_eq!(result, 4);
}

#[test]
fn test_closure_mut_parameter_supported() {
    let increment = trust_vc::closure!(
        |mut x: i32|
        ensures(|res: i32| res == x)
        {
            x += 1;
            x
        }
    );

    let result = increment(4);
    assert_eq!(result, 5);
}

// ── Iterator smoke test ──────────────────────────────────────────────

#[test]
fn test_closure_with_iterator_map() {
    common::with_clean_verification(|| {
        let double = trust_vc::closure!(
            |x: i32|
            ensures(|res: i32| res == x * 2)
            x * 2
        );

        let results: Vec<i32> = vec![1, 2, 3].into_iter().map(double).collect();
        assert_eq!(results, vec![2, 4, 6]);

        // Each call accumulates obligations; verification checks all of them.
        let pipeline = VerificationPipeline::collect_from_macros();
        let verify_result = pipeline.verify();
        assert!(
            matches!(verify_result, VerifyResult::Verified),
            "Iterator map with closure contract should verify, got: {:?}",
            verify_result
        );
    });
}

// ── Ensures-only (no requires) ───────────────────────────────────────

#[test]
fn test_closure_ensures_only_no_requires() {
    common::with_clean_verification(|| {
        let identity = trust_vc::closure!(
            |x: i32|
            ensures(|res: i32| res == x)
            x
        );

        let result = identity(42);
        assert_eq!(result, 42);

        let pipeline = VerificationPipeline::collect_from_macros();
        let verify_result = pipeline.verify();
        assert!(
            matches!(verify_result, VerifyResult::Verified),
            "Identity closure `res == x` should verify, got: {:?}",
            verify_result
        );
    });
}
