//! Performance proofs for function-context registration hot paths.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `register_function_context` runs before solver work begins. These tests
//! guard the two registration branches that large real-world contexts stress:
//! wide function signatures (`declare_fun`) and many zero-arity helpers
//! (`declare_const`).

use super::*;

#[path = "performance_parser_constructor.rs"]
mod parser_constructor;
#[path = "performance_function_context_setup_from_prepared.rs"]
mod setup_from_prepared;

/// Maximum allowed ratio between T(4N) and T(N).
/// Linear = ~4x, quadratic = ~16x. We use 12x as the threshold.
const QUADRATIC_THRESHOLD: f64 = 12.0;

/// Minimum timing to avoid division by near-zero durations.
const MIN_MEASURABLE_US: u128 = 100;

/// `register_function_context` builds one domain sort per parameter before
/// declaring the uninterpreted function. With a fixed return type, wide
/// signatures should therefore scale O(P), not O(P²).
#[test]
fn test_register_function_context_param_scaling_linear() {
    let small = 25;
    let large = 100;
    let iterations = 300;

    let t_small = measure_median(
        || time_register_function_context_params(small, iterations),
        3,
    );
    let t_large = measure_median(
        || time_register_function_context_params(large, iterations),
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
        "function-context parameter scaling appears quadratic: \
         T(P={})={}us, T(P={})={}us, ratio={:.1}x, normalized={:.1}x. \
         register_function_context() should stay O(P) in parameter count.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}

/// The non-zero-arity branch also inserts one declaration per helper into the
/// `functions` and `function_return_types` tables. Registering N fixed-arity
/// helpers in one encoder should stay O(N), not regress to O(N²) as the
/// function set grows.
#[test]
fn test_register_n_ary_function_count_scaling_linear() {
    let small = 25;
    let large = 100;
    let iterations = 120;

    let t_small = measure_median(
        || time_register_n_ary_function_contexts(small, 2, iterations),
        3,
    );
    let t_large = measure_median(
        || time_register_n_ary_function_contexts(large, 2, iterations),
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
        "n-ary function registration appears quadratic: \
         T(F={})={}us, T(F={})={}us, ratio={:.1}x, normalized={:.1}x. \
         register_function_context() should stay O(F) in fixed-arity helper count.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}

/// The zero-arity branch inserts one constant per helper into `variables` and
/// `function_return_types`. Registering N helpers in one encoder should stay
/// O(N), not regress to O(N²) via repeated rescans or map churn.
#[test]
fn test_register_zero_arity_function_count_scaling_linear() {
    let small = 25;
    let large = 100;
    let iterations = 120;

    let t_small = measure_median(
        || time_register_zero_arity_function_contexts(small, iterations),
        3,
    );
    let t_large = measure_median(
        || time_register_zero_arity_function_contexts(large, iterations),
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
        "zero-arity function registration appears quadratic: \
         T(F={})={}us, T(F={})={}us, ratio={:.1}x, normalized={:.1}x. \
         register_function_context() should stay O(F) in helper count.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}

fn time_register_function_context_params(n_params: usize, iterations: usize) -> u128 {
    let func_ctx = build_n_ary_function_context(n_params);
    let mut total_elapsed = 0u128;

    for _ in 0..iterations {
        let mut encoder = AYEncoder::new();
        let start = std::time::Instant::now();
        encoder
            .register_function_context(&func_ctx)
            .expect("wide function registration should succeed");
        total_elapsed += start.elapsed().as_micros();
        assert!(
            encoder.fn_ctx.functions.contains_key(&func_ctx.name),
            "n-ary function should register in the function table"
        );
        assert_eq!(
            encoder.fn_ctx.return_types.get(&func_ctx.name),
            Some(&func_ctx.return_type),
            "return type table should track the registered function"
        );
        assert!(
            encoder.variables.is_empty(),
            "n-ary functions should not populate the zero-arity variable table"
        );
        std::hint::black_box(encoder.fn_ctx.functions.len());
    }

    total_elapsed
}

fn time_register_n_ary_function_contexts(
    n_functions: usize,
    n_params: usize,
    iterations: usize,
) -> u128 {
    let functions = build_n_ary_function_contexts(n_functions, n_params);
    let mut total_elapsed = 0u128;

    for _ in 0..iterations {
        let mut encoder = AYEncoder::new();
        let start = std::time::Instant::now();
        for func_ctx in &functions {
            encoder
                .register_function_context(func_ctx)
                .expect("fixed-arity function registration should succeed");
        }
        total_elapsed += start.elapsed().as_micros();
        assert_eq!(
            encoder.fn_ctx.functions.len(),
            n_functions,
            "n-ary helpers should populate the function table"
        );
        assert_eq!(
            encoder.fn_ctx.return_types.len(),
            n_functions,
            "return type table should track each registered n-ary helper"
        );
        assert!(
            encoder.variables.is_empty(),
            "n-ary helpers should not populate the zero-arity variable table"
        );
        std::hint::black_box(encoder.fn_ctx.functions.len());
    }

    total_elapsed
}

fn time_register_zero_arity_function_contexts(n_functions: usize, iterations: usize) -> u128 {
    let functions = build_zero_arity_function_contexts(n_functions);
    let mut total_elapsed = 0u128;

    for _ in 0..iterations {
        let mut encoder = AYEncoder::new();
        let start = std::time::Instant::now();
        for func_ctx in &functions {
            encoder
                .register_function_context(func_ctx)
                .expect("zero-arity helper registration should succeed");
        }
        total_elapsed += start.elapsed().as_micros();
        assert_eq!(
            encoder.variables.len(),
            n_functions,
            "zero-arity helpers should populate the variables table"
        );
        assert_eq!(
            encoder.fn_ctx.return_types.len(),
            n_functions,
            "zero-arity helpers should populate the return-type table"
        );
        assert!(
            encoder.fn_ctx.functions.is_empty(),
            "zero-arity helpers should not populate the function table"
        );
        std::hint::black_box(encoder.variables.len());
    }

    total_elapsed
}

fn build_n_ary_function_context(n_params: usize) -> crate::vc::FunctionContext {
    build_named_n_ary_function_context(format!("wide_helper_{}", n_params), n_params)
}

fn build_n_ary_function_contexts(
    n_functions: usize,
    n_params: usize,
) -> Vec<crate::vc::FunctionContext> {
    (0..n_functions)
        .map(|i| build_named_n_ary_function_context(format!("fixed_arity_helper_{i}"), n_params))
        .collect()
}

fn build_named_n_ary_function_context(name: String, n_params: usize) -> crate::vc::FunctionContext {
    crate::vc::FunctionContext {
        name,
        params: (0..n_params)
            .map(|i| {
                let ty = if i % 2 == 0 {
                    crate::ir::TrustVcType::Int { width: 32 }
                } else {
                    crate::ir::TrustVcType::Uint { width: 32 }
                };
                (format!("p{i}"), ty)
            })
            .collect(),
        return_type: crate::ir::TrustVcType::Int { width: 32 },
        is_recursive: true,
        mode: crate::mode::FunctionMode::Exec,
        trait_bounds: vec![],
    }
}

fn build_zero_arity_function_contexts(n_functions: usize) -> Vec<crate::vc::FunctionContext> {
    (0..n_functions)
        .map(|i| crate::vc::FunctionContext {
            name: format!("const_helper_{i}"),
            params: Vec::new(),
            return_type: crate::ir::TrustVcType::Int { width: 32 },
            is_recursive: false,
            mode: crate::mode::FunctionMode::Exec,
            trait_bounds: vec![],
        })
        .collect()
}
