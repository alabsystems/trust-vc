// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_expand_ext_eq() {
    let lhs = quote! { a.field };
    let rhs = quote! { b.field };

    let result = expand_ext_eq(lhs, rhs);

    let result_str = result.to_string();
    // Should generate extensional equality check
    assert!(result_str.contains("ext_eq"));
    assert!(result_str.contains("a . field"));
    assert!(result_str.contains("b . field"));
}

#[test]
fn test_expand_ext_ne() {
    let lhs = quote! { vec1 };
    let rhs = quote! { vec2 };

    let result = expand_ext_ne(lhs, rhs);

    let result_str = result.to_string();
    // Should generate extensional inequality check
    assert!(result_str.contains("__trust_vc_ext_ne"));
    assert!(result_str.contains("vec1"));
    assert!(result_str.contains("vec2"));
    assert!(result_str.contains("!="));
}

// ========================================================================
// #2066: Qualified-path mode validation via crate index
// ========================================================================

#[test]
fn test_validate_qualified_self_path_rejects_exec_calling_proof_2066() {
    crate::mode::clear_compile_time_mode_registry();
    let block: syn::Block = syn::parse_quote! {{
        self::proof_helper(x);
        x
    }};

    let index = crate::mode_index::CrateModeIndex::from_entries(&[
        (&["proof_helper"], crate::mode::FunctionMode::Proof),
        (&["exec_caller"], crate::mode::FunctionMode::Exec),
    ]);

    let errors = crate::validate_function_calls_for_mode(
        crate::mode::FunctionMode::Exec,
        &block,
        None,
        Some(&index),
        &[], // top-level caller
    );
    assert!(
        !errors.is_empty(),
        "self::proof_helper() from exec should be rejected (#2066)"
    );
}

#[test]
fn test_validate_qualified_crate_path_rejects_proof_calling_exec_2066() {
    crate::mode::clear_compile_time_mode_registry();
    let block: syn::Block = syn::parse_quote! {{
        crate::runtime::touch(x);
    }};

    let index = crate::mode_index::CrateModeIndex::from_entries(&[(
        &["runtime", "touch"],
        crate::mode::FunctionMode::Exec,
    )]);

    let errors = crate::validate_function_calls_for_mode(
        crate::mode::FunctionMode::Proof,
        &block,
        None,
        Some(&index),
        &[], // top-level caller
    );
    assert!(
        !errors.is_empty(),
        "crate::runtime::touch() from proof should be rejected (#2066)"
    );
}

#[test]
fn test_validate_qualified_multi_segment_rejects_exec_calling_spec_2066() {
    crate::mode::clear_compile_time_mode_registry();
    let block: syn::Block = syn::parse_quote! {{
        specs::helper(x)
    }};

    let index = crate::mode_index::CrateModeIndex::from_entries(&[(
        &["specs", "helper"],
        crate::mode::FunctionMode::Spec,
    )]);

    let errors = crate::validate_function_calls_for_mode(
        crate::mode::FunctionMode::Exec,
        &block,
        None,
        Some(&index),
        &[], // top-level caller
    );
    assert!(
        !errors.is_empty(),
        "specs::helper() from exec should be rejected (#2066)"
    );
}

#[test]
fn test_validate_qualified_crate_path_allows_proof_calling_spec_2066() {
    crate::mode::clear_compile_time_mode_registry();
    let block: syn::Block = syn::parse_quote! {{
        crate::specs::helper(x)
    }};

    let index = crate::mode_index::CrateModeIndex::from_entries(&[(
        &["specs", "helper"],
        crate::mode::FunctionMode::Spec,
    )]);

    let errors = crate::validate_function_calls_for_mode(
        crate::mode::FunctionMode::Proof,
        &block,
        None,
        Some(&index),
        &[], // top-level caller
    );
    assert!(
        errors.is_empty(),
        "crate::specs::helper() from proof should be allowed (#2066)"
    );
}

#[test]
fn test_validate_leading_colon_paths_skipped_2066() {
    crate::mode::clear_compile_time_mode_registry();
    let block: syn::Block = syn::parse_quote! {{
        ::trust_vc_core::verify_macro::something();
    }};

    let index = crate::mode_index::CrateModeIndex::from_entries(&[]);

    let errors = crate::validate_function_calls_for_mode(
        crate::mode::FunctionMode::Proof,
        &block,
        None,
        Some(&index),
        &[],
    );
    assert!(
        errors.is_empty(),
        "leading :: paths (external crates) should be skipped (#2066)"
    );
}

// ============================================================
// Performance: merge_catalog dedup scaling in trait_registry
// ============================================================

/// Generate Rust source containing `n` trait definitions with `#[trust_vc::trait_spec]`.
fn generate_trait_source(n: usize, prefix: &str) -> String {
    let mut source = String::with_capacity(n * 80);
    for i in 0..n {
        use std::fmt::Write;
        let _ = write!(
            source,
            "#[trust_vc::trait_spec]\ntrait {prefix}T{i} {{ fn m(&self) -> i32; }}\n"
        );
    }
    source
}

/// Time K calls to `register_traits_from_source` with N-trait source.
/// First call fills the registry; subsequent K-1 calls trigger O(N²) dedup.
fn time_merge_catalog_dedup(n_traits: usize, k_calls: usize, prefix: &str) -> u128 {
    let source = generate_trait_source(n_traits, prefix);
    let start = std::time::Instant::now();
    for i in 0..k_calls {
        let _ = crate::trait_registry::register_traits_from_source(
            &format!("perf_{prefix}_{i}.rs"),
            &source,
        );
    }
    start.elapsed().as_micros()
}

/// `merge_catalog` (trait_registry.rs:58-67) uses `Vec::contains` for dedup,
/// which is O(N×M) where N = incoming traits and M = registered traits.
/// When called K times with the same N-trait source, total dedup work is
/// O(K × N²).
///
/// This test verifies the overall `register_traits_from_source` path scales
/// proportionally to source size (dominated by syn parsing at O(N), not by
/// the quadratic dedup term). A ratio > 12x (for 4x input scale) would
/// indicate the quadratic dedup term has become dominant and Vec::contains
/// should be replaced with HashSet.
///
/// Re: performance_proofs phase audit, P1-838.
#[test]
fn test_merge_catalog_dedup_scaling_not_quadratic_dominant() {
    const SMALL_N: usize = 20;
    const LARGE_N: usize = 80;
    const K_CALLS: usize = 10;
    const QUADRATIC_THRESHOLD: f64 = 12.0;
    const MIN_MEASURABLE_US: u128 = 100;

    crate::trait_registry::clear_registered_traits();

    // Warmup (JIT, page faults)
    let _ = time_merge_catalog_dedup(SMALL_N, 1, "wu");
    crate::trait_registry::clear_registered_traits();

    // Measure small N
    let t_small = time_merge_catalog_dedup(SMALL_N, K_CALLS, "sm");
    crate::trait_registry::clear_registered_traits();

    // Measure large N
    let t_large = time_merge_catalog_dedup(LARGE_N, K_CALLS, "lg");
    crate::trait_registry::clear_registered_traits();

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    assert!(
        ratio < QUADRATIC_THRESHOLD,
        "merge_catalog dedup appears quadratic-dominant: \
         T(N={SMALL_N})={t_small}μs, T(N={LARGE_N})={t_large}μs, \
         ratio={ratio:.1}x (threshold {QUADRATIC_THRESHOLD}x for 4x scale). \
         Vec::contains in merge_catalog may need HashSet replacement.",
    );
}
