//! Broadcast trigger-inference mode tests that inspect emitted quantifier triggers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

fn inferred_trigger_counts(mode: crate::trigger_inference::TriggerInferenceMode) -> (usize, usize) {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_helper_function_typed(
        "f",
        crate::ir::TrustVcType::Bool,
        vec![("x".to_string(), crate::ir::TrustVcType::Int { width: 32 })],
    );
    ctx.declare_helper_function_typed(
        "g",
        crate::ir::TrustVcType::Bool,
        vec![("x".to_string(), crate::ir::TrustVcType::Int { width: 32 })],
    );

    let mut obligation =
        crate::vc::ProofObligation::broadcast_assume("broadcast_inferred", "f(x) && g(x)")
            .with_bound_vars(vec!["x".to_string()]);
    obligation.trigger_inference_mode = Some(mode);
    ctx.obligations.push(obligation);

    let prepared = crate::prepared_context::prepare_context(&ctx)
        .expect("broadcast should prepare with typed helpers");
    let obligation = prepared
        .obligations
        .first()
        .expect("prepared context should contain the broadcast obligation");

    let mut encoder = AYEncoder::new();
    for variable in &prepared.variables {
        encoder
            .declare_variable(variable)
            .expect("variable declaration should succeed");
    }
    for helper in &prepared.helper_function_contexts {
        encoder
            .register_function_context(helper)
            .expect("helper registration should succeed");
    }
    let all_var_terms: Vec<_> = encoder.variables.values().copied().collect();

    encoder
        .add_typed_broadcast(obligation, &all_var_terms)
        .expect("typed broadcast should encode");
    let assertions = encoder.solver.assertions();
    let quantified = *assertions
        .last()
        .expect("broadcast encoding should assert one quantified formula");
    let trigger_count = encoder
        .solver
        .quantifier_triggers(quantified)
        .expect("broadcast assertion should be quantified")
        .len();

    (
        trigger_count,
        encoder
            .state
            .ground_pool
            .pending_instantiation_count_for_tests(),
    )
}

#[test]
fn test_inferred_trigger_mode_controls_emitted_quantifier_triggers() {
    use crate::trigger_inference::TriggerInferenceMode;

    let (conservative_triggers, conservative_pending) =
        inferred_trigger_counts(TriggerInferenceMode::Conservative);
    let (aggressive_triggers, aggressive_pending) =
        inferred_trigger_counts(TriggerInferenceMode::Aggressive);

    assert_eq!(
        conservative_triggers, 1,
        "conservative mode should emit exactly one inferred trigger group"
    );
    assert_eq!(
        aggressive_triggers, 2,
        "aggressive mode should emit both inferred trigger groups"
    );
    assert_eq!(
        conservative_pending, 0,
        "inferred triggers should not fabricate eager-seed instantiations in conservative mode"
    );
    assert_eq!(
        aggressive_pending, 0,
        "inferred triggers should not fabricate eager-seed instantiations in aggressive mode"
    );
}
