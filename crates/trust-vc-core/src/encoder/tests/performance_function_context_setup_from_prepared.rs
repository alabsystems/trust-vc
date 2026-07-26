//! Composed scaling proofs for `setup_from_prepared`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

/// `setup_from_prepared` composes variable declaration, function-context
/// registration, and assumption/broadcast setup into each fresh encoder used by
/// typed verification. With a fixed number of obligations, growing the
/// prepared-variable set should therefore stay O(V), not O(V²).
#[test]
fn test_setup_from_prepared_mixed_context_scaling_linear() {
    let small = 10;
    let large = 40;
    let iterations = 160;

    let small_fixture = build_setup_from_prepared_fixture(small, 2, 2);
    let large_fixture = build_setup_from_prepared_fixture(large, 2, 2);

    let t_small = measure_median(
        || time_setup_from_prepared_fixture(&small_fixture, false, iterations),
        3,
    );
    let t_large = measure_median(
        || time_setup_from_prepared_fixture(&large_fixture, false, iterations),
        3,
    );

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large as f64 / small as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "setup_from_prepared variable scaling appears quadratic: \
         T(V={})={}us, T(V={})={}us, ratio={:.1}x, normalized={:.1}x. \
         Fresh encoder setup should stay O(V) when obligation count is fixed.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}

/// Broadcast setup in `setup_from_prepared` goes through the real typed
/// trigger path (`add_typed_broadcast` + `encode_trigger_typed`). With one
/// bound variable and fixed trigger shape, growing the broadcast batch should
/// stay O(B), not O(B²).
#[test]
fn test_setup_from_prepared_broadcast_batch_scaling_linear() {
    let small = 8;
    let large = 32;
    let iterations = 160;

    let small_fixture = build_setup_from_prepared_fixture(1, small, 0);
    let large_fixture = build_setup_from_prepared_fixture(1, large, 0);

    let t_small = measure_median(
        || time_setup_from_prepared_fixture(&small_fixture, false, iterations),
        3,
    );
    let t_large = measure_median(
        || time_setup_from_prepared_fixture(&large_fixture, false, iterations),
        3,
    );

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large as f64 / small as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "setup_from_prepared broadcast scaling appears quadratic: \
         T(B={})={}us, T(B={})={}us, ratio={:.1}x, normalized={:.1}x. \
         Trigger encoding should stay O(B) below the broadcast cap.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}

/// `setup_from_prepared` also replays proven `assert_by` facts and scoped
/// proof assumptions into each fresh encoder. With fixed variables, function
/// context, and no broadcasts, growing those extra assumption batches should
/// stay O(A), not O(A²).
#[test]
fn test_setup_from_prepared_extra_assumption_batch_scaling_linear() {
    let small = 8;
    let large = 32;
    let iterations = 180;

    let small_fixture = build_setup_from_prepared_fixture(2, 0, small);
    let large_fixture = build_setup_from_prepared_fixture(2, 0, large);

    let t_small = measure_median(
        || time_setup_from_prepared_fixture(&small_fixture, false, iterations),
        3,
    );
    let t_large = measure_median(
        || time_setup_from_prepared_fixture(&large_fixture, false, iterations),
        3,
    );

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large as f64 / small as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "setup_from_prepared extra-assumption scaling appears quadratic: \
         T(A={})={}us, T(A={})={}us, ratio={:.1}x, normalized={:.1}x. \
         verified_assert_by and scoped_assumptions replay should stay O(A).",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}

/// When `use_int_for_measures` is enabled, `setup_from_prepared` promotes each
/// variable to `MathInt` and adds a non-negative guard for unsigned inputs.
/// That extra pass should stay O(V), not O(V²).
#[test]
fn test_setup_from_prepared_measure_guard_scaling_linear() {
    let small = 20;
    let large = 80;
    let iterations = 180;

    let small_fixture = build_unsigned_measure_fixture(small);
    let large_fixture = build_unsigned_measure_fixture(large);

    let t_small = measure_median(
        || time_setup_from_prepared_fixture(&small_fixture, true, iterations),
        3,
    );
    let t_large = measure_median(
        || time_setup_from_prepared_fixture(&large_fixture, true, iterations),
        3,
    );

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large as f64 / small as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "setup_from_prepared measure-guard scaling appears quadratic: \
         T(V={})={}us, T(V={})={}us, ratio={:.1}x, normalized={:.1}x. \
         Int-measure promotion plus unsigned guards should stay O(V).",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}

struct SetupPreparedFixture {
    ctx: crate::prepared_context::PreparedVerificationContext,
    assumptions: Vec<crate::prepared_context::PreparedObligation>,
    broadcasts: Vec<crate::prepared_context::PreparedObligation>,
    verified_assert_by: Vec<crate::prepared_context::PreparedObligation>,
    scoped_assumptions: Vec<crate::prepared_context::PreparedObligation>,
}

fn time_setup_from_prepared_fixture(
    fixture: &SetupPreparedFixture,
    use_int_for_measures: bool,
    iterations: usize,
) -> u128 {
    let assumptions: Vec<&crate::prepared_context::PreparedObligation> =
        fixture.assumptions.iter().collect();
    let broadcasts: Vec<&crate::prepared_context::PreparedObligation> =
        fixture.broadcasts.iter().collect();
    let verified_assert_by: Vec<&crate::prepared_context::PreparedObligation> =
        fixture.verified_assert_by.iter().collect();
    let scoped_assumptions: Vec<&crate::prepared_context::PreparedObligation> =
        fixture.scoped_assumptions.iter().collect();

    let expected_functions = usize::from(fixture.ctx.function_context.is_some());

    let start = std::time::Instant::now();
    for _ in 0..iterations {
        let slices = crate::encoder::verification::VerificationSlices::new(
            &fixture.ctx,
            &assumptions,
            &broadcasts,
            &[],
            &verified_assert_by,
            &scoped_assumptions,
        );
        let encoder = AYEncoder::setup_from_prepared(&slices, use_int_for_measures, None)
            .expect("setup_from_prepared should succeed for performance fixtures");

        assert_eq!(
            encoder.variables.len(),
            fixture.ctx.variables.len(),
            "fresh encoder should register each prepared variable once"
        );
        assert_eq!(
            encoder.collection_lengths.len(),
            0,
            "scalar-only setup fixtures should not create collection length entries"
        );
        assert_eq!(
            encoder.fn_ctx.functions.len(),
            expected_functions,
            "n-ary function context should populate the function table once"
        );
        assert_eq!(
            encoder.fn_ctx.return_types.len(),
            expected_functions,
            "function return-type tracking should stay bounded per fresh encoder"
        );
        assert_eq!(
            encoder.state.broadcast_count,
            fixture.broadcasts.len(),
            "broadcast counter should reflect the exact prepared broadcast batch"
        );

        if use_int_for_measures {
            for var in &fixture.ctx.variables {
                assert_eq!(
                    encoder.var_types.get(&var.name),
                    Some(&crate::ir::TrustVcType::MathInt),
                    "measure mode should promote '{}' to MathInt",
                    var.name,
                );
            }
        }

        std::hint::black_box((
            encoder.variables.len(),
            encoder.fn_ctx.functions.len(),
            encoder.state.broadcast_count,
        ));
    }
    start.elapsed().as_micros()
}

fn build_setup_from_prepared_fixture(
    n_vars: usize,
    n_broadcasts: usize,
    n_extra_assumptions: usize,
) -> SetupPreparedFixture {
    let mut ctx = crate::vc::VerificationContext::new();
    for i in 0..n_vars {
        let ty = if i % 2 == 0 {
            crate::ir::TrustVcType::Int { width: 32 }
        } else {
            crate::ir::TrustVcType::Uint { width: 32 }
        };
        ctx.declare_var_typed(&format!("v_{i}"), ty);
    }

    ctx.push_obligation(crate::vc::ProofObligation::assume(
        "assume_nonneg",
        "v_0 >= 0",
    ));

    for i in 0..n_broadcasts {
        ctx.push_obligation(
            ProofObligation::broadcast_assume(format!("broadcast_{i}"), "f(v_0) >= 0")
                .with_bound_vars(vec!["v_0".to_string()])
                .with_trigger_patterns(vec![vec!["f(v_0)".to_string()]]),
        );
    }

    ctx.set_function_context(crate::vc::FunctionContext {
        name: "f".to_string(),
        params: vec![("arg".to_string(), crate::ir::TrustVcType::Int { width: 32 })],
        return_type: crate::ir::TrustVcType::Int { width: 32 },
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    let prepared =
        crate::prepared_context::prepare_context(&ctx).expect("prepare_context should succeed");
    let (assumptions, broadcasts): (
        Vec<crate::prepared_context::PreparedObligation>,
        Vec<crate::prepared_context::PreparedObligation>,
    ) = prepared
        .obligations
        .into_iter()
        .partition(|obligation| obligation.kind == crate::vc::ObligationKind::Assume);

    let verified_assert_by =
        clone_named_assumptions(&assumptions, n_extra_assumptions, "verified_assert_by");
    let scoped_assumptions =
        clone_named_assumptions(&assumptions, n_extra_assumptions, "scoped_assumption");

    SetupPreparedFixture {
        ctx: crate::prepared_context::PreparedVerificationContext {
            obligations: Vec::new(),
            variables: prepared.variables,
            function_context: prepared.function_context,
            trait_decls: prepared.trait_decls,
            trait_impl_decls: prepared.trait_impl_decls,
            trait_impl_method_bodies: prepared.trait_impl_method_bodies,
            trait_impl_method_ensures: prepared.trait_impl_method_ensures,
            conformance_exempt_methods: prepared.conformance_exempt_methods,
            verification_mode: prepared.verification_mode,
            overflow_behavior: prepared.overflow_behavior,
            div0_behavior: crate::vc::Div0Behavior::default(),
            bitshift_behavior: crate::vc::BitshiftBehavior::default(),
            broadcast_use_groups: prepared.broadcast_use_groups,
            assert_by_scopes: std::collections::HashMap::new(),
            assert_by_scope_revealed_fns: prepared.assert_by_scope_revealed_fns,
            forall_bound_vars: std::collections::HashMap::new(),
            loop_guards: std::collections::HashMap::new(),
            loop_modified_vars: std::collections::HashMap::new(),
            loop_body_transitions: std::collections::HashMap::new(),
            has_collection_context: prepared.has_collection_context,
            revealed_fns: std::collections::HashSet::new(),
            hidden_fns: prepared.hidden_fns,
            helper_function_contexts: Vec::new(),
            struct_types: Vec::new(),
            type_invariants: std::collections::HashMap::new(),
            invariant_mask: crate::vc::InvariantMask::default(),
            tracked_params: std::collections::HashSet::new(),
            rlimit_ms: None,
            demand_inline: crate::vc::DemandInlineConfig::new(),
            counterexample_var_meta: std::collections::HashMap::new(),
            skip_retry_cascade: false,
        },
        assumptions,
        broadcasts,
        verified_assert_by,
        scoped_assumptions,
    }
}

fn build_unsigned_measure_fixture(n_vars: usize) -> SetupPreparedFixture {
    let mut ctx = crate::vc::VerificationContext::new();
    for i in 0..n_vars {
        let ty = match i % 4 {
            0 => crate::ir::TrustVcType::Uint { width: 8 },
            1 => crate::ir::TrustVcType::Uint { width: 16 },
            2 => crate::ir::TrustVcType::Uint { width: 32 },
            _ => crate::ir::TrustVcType::Uint { width: 64 },
        };
        ctx.declare_var_typed(&format!("m_{i}"), ty);
    }

    let prepared =
        crate::prepared_context::prepare_context(&ctx).expect("prepare_context should succeed");
    SetupPreparedFixture {
        ctx: crate::prepared_context::PreparedVerificationContext {
            obligations: Vec::new(),
            variables: prepared.variables,
            function_context: prepared.function_context,
            trait_decls: prepared.trait_decls,
            trait_impl_decls: prepared.trait_impl_decls,
            trait_impl_method_bodies: prepared.trait_impl_method_bodies,
            trait_impl_method_ensures: prepared.trait_impl_method_ensures,
            conformance_exempt_methods: prepared.conformance_exempt_methods,
            verification_mode: prepared.verification_mode,
            overflow_behavior: prepared.overflow_behavior,
            div0_behavior: crate::vc::Div0Behavior::default(),
            bitshift_behavior: crate::vc::BitshiftBehavior::default(),
            broadcast_use_groups: prepared.broadcast_use_groups,
            assert_by_scopes: std::collections::HashMap::new(),
            assert_by_scope_revealed_fns: prepared.assert_by_scope_revealed_fns,
            forall_bound_vars: std::collections::HashMap::new(),
            loop_guards: std::collections::HashMap::new(),
            loop_modified_vars: std::collections::HashMap::new(),
            loop_body_transitions: std::collections::HashMap::new(),
            has_collection_context: prepared.has_collection_context,
            revealed_fns: std::collections::HashSet::new(),
            hidden_fns: prepared.hidden_fns,
            helper_function_contexts: Vec::new(),
            struct_types: Vec::new(),
            type_invariants: std::collections::HashMap::new(),
            invariant_mask: crate::vc::InvariantMask::default(),
            tracked_params: std::collections::HashSet::new(),
            rlimit_ms: None,
            demand_inline: crate::vc::DemandInlineConfig::new(),
            counterexample_var_meta: std::collections::HashMap::new(),
            skip_retry_cascade: false,
        },
        assumptions: Vec::new(),
        broadcasts: Vec::new(),
        verified_assert_by: Vec::new(),
        scoped_assumptions: Vec::new(),
    }
}

fn clone_named_assumptions(
    source: &[crate::prepared_context::PreparedObligation],
    count: usize,
    prefix: &str,
) -> Vec<crate::prepared_context::PreparedObligation> {
    if count == 0 {
        return Vec::new();
    }

    assert!(
        !source.is_empty(),
        "fixture must include at least one prepared assumption to clone"
    );

    (0..count)
        .map(|i| {
            let mut obligation = source[i % source.len()].clone();
            obligation.name = format!("{prefix}_{i}");
            obligation
        })
        .collect()
}
