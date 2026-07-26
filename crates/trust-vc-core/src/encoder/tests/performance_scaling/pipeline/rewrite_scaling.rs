// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::*;
use super::super::{MIN_MEASURABLE_US, QUADRATIC_THRESHOLD};

/// `replace_vars_with_pre` scans the condition string once per variable.
/// With V variables and condition length L, cost should be O(V * L).
/// For fixed L, should be linear in V.
#[test]
fn test_replace_vars_with_pre_scales_linearly_in_variables() {
    use crate::vc::VariableDecl;

    let small = 10;
    let large = 40;

    let vars_small: Vec<VariableDecl> = (0..small)
        .map(|i| VariableDecl {
            bounded_len: false,
            name: format!("var_{}", i),
            ty: crate::ir::TrustVcType::Int { width: 32 },
        })
        .collect();

    let vars_large: Vec<VariableDecl> = (0..large)
        .map(|i| VariableDecl {
            bounded_len: false,
            name: format!("var_{}", i),
            ty: crate::ir::TrustVcType::Int { width: 32 },
        })
        .collect();

    let condition = "var_0 + var_1 + var_2 > 0";

    let t_small = measure_median(
        || {
            let start = std::time::Instant::now();
            for _ in 0..10_000 {
                let _ = super::super::verification::rewrite::replace_vars_with_pre(
                    condition,
                    &vars_small,
                );
            }
            start.elapsed().as_micros()
        },
        3,
    );

    let t_large = measure_median(
        || {
            let start = std::time::Instant::now();
            for _ in 0..10_000 {
                let _ = super::super::verification::rewrite::replace_vars_with_pre(
                    condition,
                    &vars_large,
                );
            }
            start.elapsed().as_micros()
        },
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
        "replace_vars_with_pre scaling appears quadratic: \
         T({})={}μs, T({})={}μs, ratio={:.1}x, normalized={:.1}x",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}
