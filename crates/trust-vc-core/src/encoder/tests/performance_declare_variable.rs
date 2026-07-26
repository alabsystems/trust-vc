//! Performance proofs for `declare_variable` hot paths.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `declare_variable` runs once per variable in every fresh encoder created by
//! `setup_from_prepared`. For scalar variables, the cost is a single
//! `declare_const` + two HashMap inserts. For collection types (Seq, Set, Map),
//! additional solver calls create length terms, non-negative constraints, and
//! (for Map) domain membership arrays. These tests guard that the per-variable
//! setup stays O(N) in variable count and does not regress to O(N²) via
//! repeated map rescans or solver state accumulation.

use super::*;

/// Maximum allowed ratio between T(4N) and T(N).
/// Linear = ~4x, quadratic = ~16x. We use 12x as the threshold.
const QUADRATIC_THRESHOLD: f64 = 12.0;

/// Minimum timing to avoid division by near-zero durations.
const MIN_MEASURABLE_US: u128 = 100;

/// Declaring N scalar (Int/Uint) variables in one encoder should stay O(N).
/// Each scalar declaration is one `declare_const` + two HashMap inserts
/// (`variables` and `var_types`). No solver assertions are generated.
#[test]
fn test_declare_scalar_variables_scaling_linear() {
    let small = 30;
    let large = 120;
    let iterations = 200;

    let t_small = measure_median(|| time_declare_scalar_variables(small, iterations), 3);
    let t_large = measure_median(|| time_declare_scalar_variables(large, iterations), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large as f64 / small as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "scalar variable declaration appears quadratic: \
         T(V={})={}us, T(V={})={}us, ratio={:.1}x, normalized={:.1}x. \
         declare_variable() for scalars should stay O(V).",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}

/// Declaring N Seq<i32> variables should stay O(N). Each Seq declaration
/// involves: `declare_const` for the array, `declare_const` for the length
/// term, `bv_const(0)` + `bvuge` + `assert_term` for the length >= 0
/// constraint. That is 5 solver interactions per variable — a high constant
/// factor but still O(1) per variable, so O(N) total.
#[test]
fn test_declare_seq_variables_scaling_linear() {
    let small = 20;
    let large = 80;
    let iterations = 100;

    let t_small = measure_median(
        || time_declare_collection_variables(small, iterations, CollectionShape::Seq),
        3,
    );
    let t_large = measure_median(
        || time_declare_collection_variables(large, iterations, CollectionShape::Seq),
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
        "Seq variable declaration appears quadratic: \
         T(V={})={}us, T(V={})={}us, ratio={:.1}x, normalized={:.1}x. \
         declare_variable() for Seq should stay O(V).",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}

/// Declaring N Map<i32, i32> variables should stay O(N). Map declaration is
/// the most expensive branch: it performs everything Seq does PLUS creates a
/// domain membership array (`Array(BV32, Bool)`) via an additional
/// `declare_const`. That is 6+ solver interactions per variable. This test
/// guards that the per-variable cost stays bounded and does not interact
/// with accumulated encoder state.
#[test]
fn test_declare_map_variables_scaling_linear() {
    let small = 20;
    let large = 80;
    let iterations = 80;

    let t_small = measure_median(
        || time_declare_collection_variables(small, iterations, CollectionShape::Map),
        3,
    );
    let t_large = measure_median(
        || time_declare_collection_variables(large, iterations, CollectionShape::Map),
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
        "Map variable declaration appears quadratic: \
         T(V={})={}us, T(V={})={}us, ratio={:.1}x, normalized={:.1}x. \
         declare_variable() for Map should stay O(V).",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}

/// Mixed declaration: N/3 scalars + N/3 Seq + N/3 Map. This exercises the
/// three code paths interleaved in one encoder, catching any cross-path
/// interaction that makes accumulated state grow super-linearly.
#[test]
fn test_declare_mixed_variables_scaling_linear() {
    let small = 30;
    let large = 120;
    let iterations = 80;

    let t_small = measure_median(|| time_declare_mixed_variables(small, iterations), 3);
    let t_large = measure_median(|| time_declare_mixed_variables(large, iterations), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large as f64 / small as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "mixed variable declaration appears quadratic: \
         T(V={})={}us, T(V={})={}us, ratio={:.1}x, normalized={:.1}x. \
         declare_variable() for mixed types should stay O(V).",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}

// -- Helpers --

#[derive(Clone, Copy)]
enum CollectionShape {
    Seq,
    Map,
}

fn time_declare_scalar_variables(n_vars: usize, iterations: usize) -> u128 {
    let vars: Vec<crate::vc::VariableDecl> = (0..n_vars)
        .map(|i| crate::vc::VariableDecl {
            bounded_len: false,
            name: format!("v_{i}"),
            ty: if i % 2 == 0 {
                crate::ir::TrustVcType::Int { width: 32 }
            } else {
                crate::ir::TrustVcType::Uint { width: 64 }
            },
        })
        .collect();

    let start = std::time::Instant::now();
    for _ in 0..iterations {
        let mut encoder = AYEncoder::new();
        for var in &vars {
            encoder
                .declare_variable(var)
                .expect("scalar variable declaration should succeed");
        }
        assert_eq!(
            encoder.variables.len(),
            n_vars,
            "all scalar variables should be in the variables table"
        );
        assert!(
            encoder.collection_lengths.is_empty(),
            "scalar variables should not create collection length entries"
        );
        std::hint::black_box(encoder.variables.len());
    }
    start.elapsed().as_micros()
}

fn time_declare_collection_variables(
    n_vars: usize,
    iterations: usize,
    shape: CollectionShape,
) -> u128 {
    let vars: Vec<crate::vc::VariableDecl> = (0..n_vars)
        .map(|i| crate::vc::VariableDecl {
            bounded_len: false,
            name: format!("c_{i}"),
            ty: match shape {
                CollectionShape::Seq => {
                    crate::ir::TrustVcType::Seq(Box::new(crate::ir::TrustVcType::Int { width: 32 }))
                }
                CollectionShape::Map => crate::ir::TrustVcType::Map(
                    Box::new(crate::ir::TrustVcType::Int { width: 32 }),
                    Box::new(crate::ir::TrustVcType::Int { width: 32 }),
                ),
            },
        })
        .collect();

    let start = std::time::Instant::now();
    for _ in 0..iterations {
        let mut encoder = AYEncoder::new();
        for var in &vars {
            encoder
                .declare_variable(var)
                .expect("collection variable declaration should succeed");
        }
        assert_eq!(
            encoder.collection_lengths.len(),
            n_vars,
            "each collection variable should create a length entry"
        );
        match shape {
            CollectionShape::Seq => {
                let expected_variables = if cfg!(feature = "native-seq") {
                    n_vars * 2
                } else {
                    n_vars
                };
                assert_eq!(
                    encoder.variables.len(),
                    expected_variables,
                    "Seq variables should populate the variables table plus native shadows when enabled"
                );
            }
            CollectionShape::Map => {
                // Map declares both the variable itself and a {name}_dom entry
                assert_eq!(
                    encoder.variables.len(),
                    n_vars * 2,
                    "Map variables should populate variables + domain entries"
                );
            }
        }
        std::hint::black_box(encoder.collection_lengths.len());
    }
    start.elapsed().as_micros()
}

fn time_declare_mixed_variables(n_vars: usize, iterations: usize) -> u128 {
    let third = n_vars / 3;
    let vars: Vec<crate::vc::VariableDecl> = (0..n_vars)
        .map(|i| {
            if i < third {
                crate::vc::VariableDecl {
                    bounded_len: false,
                    name: format!("s_{i}"),
                    ty: crate::ir::TrustVcType::Int { width: 32 },
                }
            } else if i < third * 2 {
                crate::vc::VariableDecl {
                    bounded_len: false,
                    name: format!("q_{i}"),
                    ty: crate::ir::TrustVcType::Seq(Box::new(crate::ir::TrustVcType::Int {
                        width: 32,
                    })),
                }
            } else {
                crate::vc::VariableDecl {
                    bounded_len: false,
                    name: format!("m_{i}"),
                    ty: crate::ir::TrustVcType::Map(
                        Box::new(crate::ir::TrustVcType::Int { width: 32 }),
                        Box::new(crate::ir::TrustVcType::Int { width: 32 }),
                    ),
                }
            }
        })
        .collect();

    let n_collections = n_vars - third;
    let n_maps = n_vars - third * 2;

    let start = std::time::Instant::now();
    for _ in 0..iterations {
        let mut encoder = AYEncoder::new();
        for var in &vars {
            encoder
                .declare_variable(var)
                .expect("mixed variable declaration should succeed");
        }
        assert_eq!(
            encoder.collection_lengths.len(),
            n_collections,
            "collection variables should populate length entries"
        );
        let seq_shadow_entries = if cfg!(feature = "native-seq") {
            third
        } else {
            0
        };
        // variables = scalars + seqs + maps + map_dom entries (+ native-seq shadows)
        assert_eq!(
            encoder.variables.len(),
            n_vars + n_maps + seq_shadow_entries,
            "variables table should include all vars, Map domain entries, and native-seq shadows"
        );
        std::hint::black_box(encoder.variables.len());
    }
    start.elapsed().as_micros()
}
