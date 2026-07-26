//! Prepared trigger metadata and array axiom helper scaling tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from performance_hot_paths/mod.rs (#2145).

use super::*;

/// Trigger preparation should do the parse+lower work once at the prepared
/// context boundary. Scaling should stay linear in obligation count.
#[test]
fn test_trigger_preparation_scaling_linear() {
    let small = 25;
    let large = 100;

    let t_small = measure_median(
        || time_prepare_broadcasts(build_trigger_prepare_context(small)),
        3,
    );
    let t_large = measure_median(
        || time_prepare_broadcasts(build_trigger_prepare_context(large)),
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
        "prepared trigger lowering appears quadratic: \
         T({})={}μs, T({})={}μs, ratio={:.1}x, normalized={:.1}x. \
         trigger preparation should stay O(N) in obligation count.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}

/// After preparation, head-symbol and eager-seed reads should stay linear in
/// the number of prepared obligations and avoid repeated trigger reparsing.
#[test]
fn test_prepared_trigger_symbol_access_scaling_linear() {
    let small = 25;
    let large = 100;
    let iterations = 200;

    let small_prepared =
        crate::prepared_context::prepare_context(&build_trigger_prepare_context(small))
            .expect("small trigger context should prepare");
    let large_prepared =
        crate::prepared_context::prepare_context(&build_trigger_prepare_context(large))
            .expect("large trigger context should prepare");

    assert_eq!(
        small_prepared.obligations[0]
            .eager_seed_symbols()
            .iter()
            .map(|symbol| symbol.as_ref())
            .collect::<Vec<_>>(),
        vec!["helper_0"]
    );
    assert_eq!(
        large_prepared.obligations[large - 1]
            .trigger_head_symbols()
            .iter()
            .map(|symbol| symbol.as_ref())
            .collect::<Vec<_>>(),
        vec!["helper_99"]
    );

    let t_small = measure_median(
        || time_prepared_trigger_symbol_reads(&small_prepared.obligations, iterations),
        3,
    );
    let t_large = measure_median(
        || time_prepared_trigger_symbol_reads(&large_prepared.obligations, iterations),
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
        "prepared trigger symbol access appears quadratic: \
         T({})={}μs, T({})={}μs, ratio={:.1}x, normalized={:.1}x. \
         prepare-once/read-many trigger queries should stay O(N) in obligation count.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}

fn time_prepare_broadcasts(ctx: crate::vc::VerificationContext) -> u128 {
    let start = std::time::Instant::now();
    let prepared =
        crate::prepared_context::prepare_context(&ctx).expect("trigger context should prepare");
    std::hint::black_box(prepared.obligations.len());
    start.elapsed().as_micros()
}

fn time_prepared_trigger_symbol_reads(
    obligations: &[crate::prepared_context::PreparedObligation],
    iterations: usize,
) -> u128 {
    let start = std::time::Instant::now();
    let mut extracted_len = 0usize;

    for _ in 0..iterations {
        for obligation in obligations {
            extracted_len += obligation
                .trigger_head_symbols()
                .iter()
                .map(|symbol| symbol.len())
                .sum::<usize>();
            extracted_len += obligation
                .eager_seed_symbols()
                .iter()
                .map(|symbol| symbol.len())
                .sum::<usize>();
        }
    }

    std::hint::black_box(extracted_len);
    start.elapsed().as_micros()
}

fn build_trigger_prepare_context(n: usize) -> crate::vc::VerificationContext {
    let mut ctx = crate::vc::VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));

    for i in 0..n {
        let helper = format!("helper_{i}");
        ctx.declare_helper_function_typed(
            &helper,
            crate::ir::TrustVcType::Bool,
            vec![("x".to_string(), crate::ir::TrustVcType::Int { width: 32 })],
        );
        ctx.obligations.push(
            crate::vc::ProofObligation::broadcast_assume(format!("broadcast_{i}"), "x == x")
                .with_bound_vars(vec!["x".to_string()])
                .with_trigger_patterns(vec![vec![format!("{helper}(x)")]]),
        );
    }

    ctx
}

/// The `array_axioms.rs` helpers add a bounded amount of SMT structure per
/// collection operation: one quantified preservation axiom for store/update
/// and eight ground instantiations for `last()`. Repeating the helpers N times
/// should therefore scale linearly in N.
#[test]
fn test_array_axiom_helper_scaling_linear() {
    let small = 20;
    let large = 80;

    let t_small = measure_median(|| time_array_axiom_helper_batch(small), 3);
    let t_large = measure_median(|| time_array_axiom_helper_batch(large), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large as f64 / small as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "array axiom helper scaling appears quadratic: \
         T({})={}μs, T({})={}μs, ratio={:.1}x, normalized={:.1}x. \
         store/update/last helper generation should be O(N) in axiom count.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}

fn time_array_axiom_helper_batch(n_ops: usize) -> u128 {
    use ay_dpll::api::{ArraySort, Logic, Solver, Sort};

    let pw = crate::ir::pointer_width();
    let seq_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(pw),
        element_sort: Sort::bitvec(32),
    }));

    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let variables = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let start = std::time::Instant::now();
    for i in 0..n_ops {
        apply_array_axiom_helpers(&mut parser, &seq_sort, i, pw);
    }
    start.elapsed().as_micros()
}

fn apply_array_axiom_helpers(
    parser: &mut AstExpressionParser<'_>,
    seq_sort: &ay_dpll::api::Sort,
    i: usize,
    pw: u32,
) {
    let source = parser
        .solver
        .fresh_var(&format!("seq_source_{}", i), seq_sort.clone());
    let seq_result = parser
        .solver
        .fresh_var(&format!("seq_result_{}", i), seq_sort.clone());
    let elem_result = parser.solver.fresh_var(
        &format!("elem_result_{}", i),
        ay_dpll::api::Sort::bitvec(32),
    );
    let len_term = parser
        .solver
        .try_bv_const((i % 8 + 1) as i64, pw)
        .expect("len term");
    let idx_term = parser
        .solver
        .try_bv_const((i % 8) as i64, pw)
        .expect("idx term");

    parser
        .assert_store_preservation(seq_result, source, len_term, &format!("push_{}", i))
        .expect("store preservation");
    parser
        .assert_update_preservation(seq_result, source, idx_term)
        .expect("update preservation");
    parser
        .assert_last_ground_insts(source, len_term, elem_result)
        .expect("last ground instantiations");
}
