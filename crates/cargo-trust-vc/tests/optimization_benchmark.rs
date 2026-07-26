// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Optimization benchmark suite: measures the optimization impact of verified
//! hints across real-world patterns.
//!
//! All tests are deterministic (counting hints/transforms, not timing).
//! The suite covers bounds-check elimination, null-check elimination,
//! overflow elimination (via unreachable-branch), dead-branch elimination,
//! combined real-world patterns, and regression benchmarks.
//!
//! These benchmarks exercise the full hint pipeline:
//!   `ProvenFact` -> `generate_hints` -> `OptimizationHint` -> classification
//!
//! The core pipeline has three hint categories:
//!   - `BoundsElimination`: expressions with bounds keywords + comparison ops
//!   - `NullCheckElimination`: expressions with is_some/is_none/!= None/!= null
//!   - `UnreachableBranch`: everything else (overflow, dead branch, general)

use trust_vc_core::proven_facts::{
    emit_hint_annotations, format_report, generate_hints, to_json, OptimizationHintKind,
    ProvenFact, ProvenFactKind, ProvenFactsReport,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn make_fact(
    kind: ProvenFactKind,
    expression: &str,
    location: Option<&str>,
    step_label: &str,
) -> ProvenFact {
    ProvenFact::new(kind, expression, location.map(str::to_string), step_label)
}

/// Count hints of a specific kind in a hint vector.
fn count_hints(facts: &[ProvenFact], target: OptimizationHintKind) -> usize {
    generate_hints(facts)
        .iter()
        .filter(|h| h.hint_kind() == target)
        .count()
}

// ===========================================================================
// 1. Bounds check elimination benchmarks
// ===========================================================================

#[test]
fn bench_bounds_array_access_proven_in_bounds() {
    // Pattern: array access with proven `i < arr.len()` invariant.
    // Expected: BoundsElimination hint -> get_unchecked.
    let facts = vec![make_fact(
        ProvenFactKind::Invariant,
        "i < arr.len()",
        Some("src/array.rs:15:9"),
        "array_access_bound",
    )];
    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::BoundsElimination
    );

    let annotations = emit_hint_annotations(&hints);
    assert!(
        annotations.contains("get_unchecked"),
        "should emit get_unchecked for proven in-bounds access"
    );
    assert!(
        annotations.contains("bounds check can be elided"),
        "should note bounds check elision"
    );
}

#[test]
fn bench_bounds_loop_invariant_all_iterations() {
    // Pattern: loop with proven invariant `idx < buf.len()` across N iterations.
    // Simulates N loop iterations where each access is bounds-checked.
    // All should produce BoundsElimination hints.
    let mut facts = Vec::new();
    for i in 0..100 {
        facts.push(make_fact(
            ProvenFactKind::Invariant,
            "idx < buf.len()",
            Some(&format!("src/loop.rs:{}:9", 10 + i)),
            &format!("loop_bound_iter_{i}"),
        ));
    }

    let bounds_count = count_hints(&facts, OptimizationHintKind::BoundsElimination);
    assert_eq!(
        bounds_count, 100,
        "all 100 loop iterations should produce bounds elimination hints"
    );

    let report = ProvenFactsReport::from_facts(&facts);
    assert_eq!(report.bounds_elimination_hints(), 100);
    assert_eq!(report.unreachable_branch_hints(), 0);
    assert_eq!(report.null_check_elimination_hints(), 0);
}

#[test]
fn bench_bounds_slice_operations_with_proven_length() {
    // Pattern: slice operations with multiple proven length relationships.
    let facts = vec![
        make_fact(
            ProvenFactKind::Precondition,
            "start < slice.len()",
            Some("src/slice.rs:5:1"),
            "slice_start_bound",
        ),
        make_fact(
            ProvenFactKind::Precondition,
            "end <= slice.len()",
            Some("src/slice.rs:6:1"),
            "slice_end_bound",
        ),
        make_fact(
            ProvenFactKind::Assertion,
            "index < capacity",
            Some("src/slice.rs:12:5"),
            "slice_cap_check",
        ),
        make_fact(
            ProvenFactKind::Invariant,
            "offset <= size",
            Some("src/slice.rs:20:9"),
            "slice_offset_bound",
        ),
    ];

    let bounds_count = count_hints(&facts, OptimizationHintKind::BoundsElimination);
    assert_eq!(
        bounds_count, 4,
        "all four slice operations should produce bounds elimination hints"
    );

    let report = ProvenFactsReport::from_facts(&facts);
    assert_eq!(report.total_facts(), 4);
    assert_eq!(report.bounds_elimination_hints(), 4);
}

#[test]
fn bench_bounds_compound_range_expression() {
    // Pattern: compound bounds expression `x >= 0 && x < arr.len()`.
    let facts = vec![make_fact(
        ProvenFactKind::Assertion,
        "x >= 0 && x < arr.len()",
        Some("src/range.rs:8:5"),
        "compound_bound",
    )];

    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::BoundsElimination
    );
}

// ===========================================================================
// 2. Null check elimination benchmarks
// ===========================================================================

#[test]
fn bench_null_option_guaranteed_some() {
    // Pattern: Option guaranteed Some -> unwrap_unchecked hint.
    let facts = vec![make_fact(
        ProvenFactKind::Precondition,
        "arg.is_some()",
        Some("src/api.rs:15:1"),
        "option_some_pre",
    )];

    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::NullCheckElimination
    );

    let annotations = emit_hint_annotations(&hints);
    assert!(
        annotations.contains("unwrap_unchecked"),
        "should emit unwrap_unchecked for proven Some"
    );
    assert!(
        annotations.contains("null/Option check can be elided"),
        "should note null check elision"
    );
}

#[test]
fn bench_null_check_multiple_patterns() {
    // Pattern: various null-check expression patterns that should all
    // classify as NullCheckElimination.
    let patterns = [
        ("value.is_some()", "is_some_check"),
        ("ptr != None", "not_none_check"),
        ("ptr != null", "not_null_check"),
        ("handle != std::ptr::null()", "not_std_null_check"),
    ];

    let facts: Vec<ProvenFact> = patterns
        .iter()
        .enumerate()
        .map(|(i, (expr, label))| {
            make_fact(
                ProvenFactKind::Precondition,
                expr,
                Some(&format!("src/null.rs:{}:1", i + 1)),
                label,
            )
        })
        .collect();

    let null_count = count_hints(&facts, OptimizationHintKind::NullCheckElimination);
    assert_eq!(
        null_count,
        facts.len(),
        "all null-check patterns should produce NullCheckElimination hints"
    );

    let report = ProvenFactsReport::from_facts(&facts);
    assert_eq!(report.null_check_elimination_hints(), facts.len());
}

#[test]
fn bench_null_result_guaranteed_ok() {
    // Pattern: Result guaranteed Ok -> the core pipeline classifies is_ok()
    // as UnreachableBranch (not NullCheckElimination), because is_ok() is
    // not in the core null-check pattern list.
    let facts = vec![make_fact(
        ProvenFactKind::Postcondition,
        "result.is_ok()",
        Some("src/io.rs:30:1"),
        "io_ok_post",
    )];

    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    // Core classifies is_ok() as UnreachableBranch (not NullCheckElimination)
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::UnreachableBranch,
        "core pipeline classifies is_ok() as unreachable branch"
    );
}

// ===========================================================================
// 3. Overflow elimination benchmarks
// ===========================================================================

#[test]
fn bench_overflow_addition_proven_non_overflow() {
    // Pattern: addition with proven non-overflow.
    // Core classifies as UnreachableBranch (no separate overflow category).
    let facts = vec![make_fact(
        ProvenFactKind::Assertion,
        "no_overflow(a + b)",
        Some("src/math.rs:20:5"),
        "add_no_overflow",
    )];

    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::UnreachableBranch,
        "overflow assertions map to UnreachableBranch in core pipeline"
    );
    assert!(hints[0].safety_justification().contains("add_no_overflow"));
}

#[test]
fn bench_overflow_multiplication_proven_bounds() {
    // Pattern: multiplication with proven bounds -> unchecked_mul.
    let facts = vec![make_fact(
        ProvenFactKind::Assertion,
        "a * b <= MAX",
        Some("src/math.rs:30:5"),
        "mul_bound",
    )];

    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::UnreachableBranch
    );

    let annotations = emit_hint_annotations(&hints);
    assert!(
        annotations.contains("unreachable_unchecked"),
        "overflow proof should emit unreachable_unchecked"
    );
}

#[test]
fn bench_overflow_subtraction_no_underflow() {
    // Pattern: subtraction with proven no underflow.
    let facts = vec![make_fact(
        ProvenFactKind::Assertion,
        "checked_sub does not overflow",
        Some("src/math.rs:40:5"),
        "sub_no_underflow",
    )];

    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::UnreachableBranch
    );
}

#[test]
fn bench_overflow_increment_within_range() {
    // Pattern: x + 1 <= MAX (common increment pattern).
    let facts = vec![make_fact(
        ProvenFactKind::Assertion,
        "x + 1 <= MAX",
        Some("src/counter.rs:10:5"),
        "inc_safe",
    )];

    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    // Contains arithmetic + range bound but no bounds keywords, so UnreachableBranch
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::UnreachableBranch
    );
}

// ===========================================================================
// 4. Dead branch elimination benchmarks
// ===========================================================================

#[test]
fn bench_dead_branch_proven_condition_true() {
    // Pattern: if/else with proven condition -> unreachable_unchecked for dead branch.
    let facts = vec![make_fact(
        ProvenFactKind::Assertion,
        "x > 0",
        Some("src/branch.rs:10:5"),
        "positive_guard",
    )];

    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::UnreachableBranch
    );

    let annotations = emit_hint_annotations(&hints);
    assert!(annotations.contains("unreachable_unchecked"));
    assert!(annotations.contains("else branch is dead code"));
}

#[test]
fn bench_dead_branch_enum_discriminant_proven() {
    // Pattern: match arm with proven discriminant -> other arms unreachable.
    let facts = vec![make_fact(
        ProvenFactKind::Postcondition,
        "result == Status::Success",
        Some("src/status.rs:25:5"),
        "status_success",
    )];

    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::UnreachableBranch
    );
}

#[test]
fn bench_dead_branch_boolean_constant_proven() {
    // Pattern: boolean expression proven always true.
    let facts = vec![
        make_fact(
            ProvenFactKind::Assertion,
            "flag == true",
            Some("src/config.rs:5:5"),
            "flag_always_true",
        ),
        make_fact(
            ProvenFactKind::Assertion,
            "enabled && !disabled",
            Some("src/config.rs:10:5"),
            "config_active",
        ),
    ];

    let unreachable_count = count_hints(&facts, OptimizationHintKind::UnreachableBranch);
    assert_eq!(
        unreachable_count, 2,
        "both boolean proofs should produce unreachable branch hints"
    );
}

#[test]
fn bench_dead_branch_postcondition_implies_unreachable() {
    // Pattern: proven postcondition means the negation branch is unreachable.
    let facts = vec![make_fact(
        ProvenFactKind::Postcondition,
        "result == old(x) + 1",
        None,
        "inc_ensures",
    )];

    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1);
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::UnreachableBranch
    );
    assert!(hints[0].safety_justification().contains("inc_ensures"));
}

// ===========================================================================
// 5. Combined optimization benchmarks: real-world patterns
// ===========================================================================

#[test]
fn bench_combined_binary_search() {
    // Binary search pattern: multiple bounds checks + comparison proofs.
    let facts = vec![
        // Loop invariant: low <= high
        make_fact(
            ProvenFactKind::Invariant,
            "low < arr.len()",
            Some("src/search.rs:10:9"),
            "bs_low_bound",
        ),
        make_fact(
            ProvenFactKind::Invariant,
            "high <= arr.len()",
            Some("src/search.rs:11:9"),
            "bs_high_bound",
        ),
        // Mid calculation: mid = (low + high) / 2
        make_fact(
            ProvenFactKind::Assertion,
            "mid < arr.len()",
            Some("src/search.rs:13:9"),
            "bs_mid_bound",
        ),
        // Comparison result
        make_fact(
            ProvenFactKind::Assertion,
            "arr[mid] == target",
            Some("src/search.rs:15:9"),
            "bs_found",
        ),
        // Return value postcondition
        make_fact(
            ProvenFactKind::Postcondition,
            "result.is_some() ==> arr[result.unwrap()] == target",
            None,
            "bs_ensures",
        ),
    ];

    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 5, "binary search should produce 5 hints");

    let report = ProvenFactsReport::from_facts(&facts);
    assert_eq!(
        report.bounds_elimination_hints(),
        3,
        "binary search has 3 bounds elimination hints (low, high, mid)"
    );
    // "arr[mid] == target" -> UnreachableBranch (no bounds keywords)
    // "result.is_some() ==> ..." -> NullCheckElimination (contains is_some())
    assert_eq!(
        report.unreachable_branch_hints(),
        1,
        "binary search has 1 unreachable branch hint (arr[mid] == target)"
    );
    assert_eq!(
        report.null_check_elimination_hints(),
        1,
        "binary search has 1 null check hint (postcondition contains is_some())"
    );
    assert_eq!(report.total_facts(), 5);
}

#[test]
fn bench_combined_sorting_algorithm() {
    // Sorting pattern: bounds checks + comparisons + postconditions.
    let facts = vec![
        // Loop bounds
        make_fact(
            ProvenFactKind::Invariant,
            "i < arr.len()",
            Some("src/sort.rs:10:9"),
            "sort_i_bound",
        ),
        make_fact(
            ProvenFactKind::Invariant,
            "j < arr.len()",
            Some("src/sort.rs:11:9"),
            "sort_j_bound",
        ),
        // Swap preconditions
        make_fact(
            ProvenFactKind::Precondition,
            "i < arr.len()",
            Some("src/sort.rs:15:9"),
            "swap_i_bound",
        ),
        make_fact(
            ProvenFactKind::Precondition,
            "j < arr.len()",
            Some("src/sort.rs:16:9"),
            "swap_j_bound",
        ),
        // Sorted postcondition
        make_fact(
            ProvenFactKind::Postcondition,
            "forall k: 0..result.len()-1 :: result[k] <= result[k+1]",
            None,
            "sorted_post",
        ),
        // Length preservation
        make_fact(
            ProvenFactKind::Postcondition,
            "result.len() == old(arr).len()",
            None,
            "len_preserved",
        ),
    ];

    let report = ProvenFactsReport::from_facts(&facts);
    assert_eq!(report.total_facts(), 6);
    // 4 loop/swap bounds + "forall k: 0..result.len()-1 :: result[k] <= result[k+1]"
    // The forall postcondition has ".len()" + "<=" -> BoundsElimination
    assert_eq!(report.bounds_elimination_hints(), 5);
    // "result.len() == old(arr).len()" has .len() but == (not < / <= / >=) -> Unreachable
    assert_eq!(report.unreachable_branch_hints(), 1);
    assert_eq!(report.invariants(), 2);
    assert_eq!(report.preconditions(), 2);
    assert_eq!(report.postconditions(), 2);
}

#[test]
fn bench_combined_hash_map_operations() {
    // Hash map pattern: null checks + bounds checks + overflow protection.
    let facts = vec![
        // Bucket index in bounds
        make_fact(
            ProvenFactKind::Assertion,
            "bucket_idx < buckets.len()",
            Some("src/map.rs:20:5"),
            "bucket_bound",
        ),
        // Entry exists
        make_fact(
            ProvenFactKind::Precondition,
            "entry.is_some()",
            Some("src/map.rs:25:5"),
            "entry_some",
        ),
        // Capacity check
        make_fact(
            ProvenFactKind::Assertion,
            "count < capacity",
            Some("src/map.rs:30:5"),
            "cap_check",
        ),
        // No rehash overflow
        make_fact(
            ProvenFactKind::Assertion,
            "new_cap >= old_cap",
            Some("src/map.rs:35:5"),
            "rehash_growth",
        ),
        // Load factor bound
        make_fact(
            ProvenFactKind::Invariant,
            "load <= capacity",
            Some("src/map.rs:40:9"),
            "load_factor",
        ),
    ];

    let report = ProvenFactsReport::from_facts(&facts);
    assert_eq!(report.total_facts(), 5);
    // bucket_idx, count, load all have bounds keywords + comparison
    assert_eq!(
        report.bounds_elimination_hints(),
        3,
        "hash map has 3 bounds elimination hints"
    );
    assert_eq!(
        report.null_check_elimination_hints(),
        1,
        "hash map has 1 null check elimination hint"
    );
    assert_eq!(
        report.unreachable_branch_hints(),
        1,
        "hash map has 1 unreachable branch hint (rehash_growth)"
    );
}

#[test]
fn bench_combined_strength_distribution() {
    // Measure total hints generated and verify Critical vs Strong vs Moderate
    // distribution across a mixed workload.
    let facts = vec![
        // Critical: bounds checks (BoundsElimination)
        make_fact(ProvenFactKind::Invariant, "i < arr.len()", None, "c1"),
        make_fact(ProvenFactKind::Precondition, "index < capacity", None, "c2"),
        make_fact(ProvenFactKind::Assertion, "offset <= size", None, "c3"),
        // Strong: null checks (NullCheckElimination)
        make_fact(ProvenFactKind::Precondition, "val.is_some()", None, "s1"),
        make_fact(ProvenFactKind::Assertion, "ptr != None", None, "s2"),
        // Strong: overflow (UnreachableBranch in core)
        make_fact(ProvenFactKind::Assertion, "no_overflow(a + b)", None, "s3"),
        // Moderate: range/constant (UnreachableBranch in core)
        make_fact(ProvenFactKind::Assertion, "x > 0", None, "m1"),
        make_fact(ProvenFactKind::Assertion, "flag == true", None, "m2"),
        // Informational: general postcondition (UnreachableBranch in core)
        make_fact(
            ProvenFactKind::Postcondition,
            "result == old(x) + 1",
            None,
            "i1",
        ),
        make_fact(
            ProvenFactKind::Postcondition,
            "result == old(seq).push(val)",
            None,
            "i2",
        ),
    ];

    let report = ProvenFactsReport::from_facts(&facts);
    assert_eq!(report.total_facts(), 10);

    // Core pipeline distribution:
    // BoundsElimination: 3 (i < arr.len(), index < capacity, offset <= size)
    // NullCheckElimination: 2 (val.is_some(), ptr != None)
    // UnreachableBranch: 5 (no_overflow, x > 0, flag, two postconditions)
    assert_eq!(report.bounds_elimination_hints(), 3);
    assert_eq!(report.null_check_elimination_hints(), 2);
    assert_eq!(report.unreachable_branch_hints(), 5);

    // Total hints = total facts (1:1 mapping)
    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 10);
}

#[test]
fn bench_combined_vector_push_loop() {
    // Real-world pattern: push loop with capacity pre-allocation.
    let facts = vec![
        // Pre-allocated capacity
        make_fact(
            ProvenFactKind::Precondition,
            "n <= vec.capacity",
            Some("src/vec.rs:5:1"),
            "pre_alloc",
        ),
        // Loop index bound
        make_fact(
            ProvenFactKind::Invariant,
            "i < n",
            Some("src/vec.rs:10:9"),
            "push_idx_bound",
        ),
        // Length invariant: we don't exceed capacity
        make_fact(
            ProvenFactKind::Invariant,
            "vec.len() <= capacity",
            Some("src/vec.rs:11:9"),
            "len_within_cap",
        ),
        // Postcondition: final length
        make_fact(
            ProvenFactKind::Postcondition,
            "vec.len() == n",
            None,
            "final_len",
        ),
    ];

    let report = ProvenFactsReport::from_facts(&facts);
    assert_eq!(report.total_facts(), 4);
    // "n <= vec.capacity" has "capacity" + "<=" -> bounds
    // "vec.len() <= capacity" has both ".len()" and "capacity" with "<=" -> bounds
    assert_eq!(report.bounds_elimination_hints(), 2);
    // "i < n" lacks bounds keywords -> unreachable
    // "vec.len() == n" has .len() but no < / <= / >= -> unreachable
    assert_eq!(report.unreachable_branch_hints(), 2);
}

// ===========================================================================
// 6. Regression benchmarks: exact expected hint counts
// ===========================================================================

#[test]
fn regression_single_bounds_check_produces_exactly_one_hint() {
    let facts = vec![make_fact(
        ProvenFactKind::Invariant,
        "i < arr.len()",
        Some("src/lib.rs:10:9"),
        "loop_bound",
    )];

    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 1, "exactly one hint expected");
    assert_eq!(
        hints[0].hint_kind(),
        OptimizationHintKind::BoundsElimination
    );
    assert_eq!(hints[0].expression(), "i < arr.len()");
    assert_eq!(hints[0].source_location(), Some("src/lib.rs:10:9"));
    assert!(hints[0].safety_justification().contains("loop_bound"));
}

#[test]
fn regression_all_transform_kinds_deterministic_classification() {
    // Each expression must classify to its expected kind. This is the
    // regression test that pins the classification behavior.
    let test_cases: Vec<(&str, OptimizationHintKind)> = vec![
        // BoundsElimination patterns
        ("i < arr.len()", OptimizationHintKind::BoundsElimination),
        ("index < capacity", OptimizationHintKind::BoundsElimination),
        ("offset <= size", OptimizationHintKind::BoundsElimination),
        (
            "x >= 0 && x < arr.len()",
            OptimizationHintKind::BoundsElimination,
        ),
        ("bound < arr.len()", OptimizationHintKind::BoundsElimination),
        // NullCheckElimination patterns
        ("val.is_some()", OptimizationHintKind::NullCheckElimination),
        ("!val.is_none()", OptimizationHintKind::NullCheckElimination),
        ("ptr != None", OptimizationHintKind::NullCheckElimination),
        ("ptr != null", OptimizationHintKind::NullCheckElimination),
        // UnreachableBranch patterns (general / overflow / range / const)
        ("x > 0", OptimizationHintKind::UnreachableBranch),
        ("flag == true", OptimizationHintKind::UnreachableBranch),
        (
            "result == old(x) + 1",
            OptimizationHintKind::UnreachableBranch,
        ),
        (
            "no_overflow(a + b)",
            OptimizationHintKind::UnreachableBranch,
        ),
        ("a * b <= MAX", OptimizationHintKind::UnreachableBranch),
    ];

    for (expr, expected_kind) in &test_cases {
        let facts = vec![make_fact(
            ProvenFactKind::Assertion,
            expr,
            None,
            "regression",
        )];
        let hints = generate_hints(&facts);
        assert_eq!(
            hints.len(),
            1,
            "expression {expr:?} should produce exactly one hint"
        );
        assert_eq!(
            hints[0].hint_kind(),
            *expected_kind,
            "expression {expr:?} should classify as {expected_kind:?}"
        );
    }
}

#[test]
fn regression_mixed_facts_exact_report_counts() {
    // Pin the exact counts for a known mixed fact set.
    let facts = vec![
        make_fact(ProvenFactKind::Assertion, "x > 0", None, "s1"),
        make_fact(ProvenFactKind::Invariant, "i < arr.len()", None, "s2"),
        make_fact(ProvenFactKind::Precondition, "val.is_some()", None, "s3"),
        make_fact(
            ProvenFactKind::Postcondition,
            "result == old(x) + 1",
            None,
            "s4",
        ),
        make_fact(ProvenFactKind::Assertion, "ptr != None", None, "s5"),
    ];

    let report = ProvenFactsReport::from_facts(&facts);
    assert_eq!(report.total_facts(), 5);
    assert_eq!(report.assertions(), 2);
    assert_eq!(report.preconditions(), 1);
    assert_eq!(report.postconditions(), 1);
    assert_eq!(report.invariants(), 1);
    assert_eq!(report.bounds_elimination_hints(), 1);
    assert_eq!(report.null_check_elimination_hints(), 2);
    assert_eq!(report.unreachable_branch_hints(), 2);
}

#[test]
fn regression_json_output_structure_exact_counts() {
    // Verify the JSON output contains exact expected values.
    let facts = vec![
        make_fact(ProvenFactKind::Invariant, "i < buf.len()", None, "b1"),
        make_fact(ProvenFactKind::Precondition, "opt.is_some()", None, "n1"),
        make_fact(ProvenFactKind::Assertion, "x > 0", None, "u1"),
    ];

    let json = to_json(&facts);
    let parsed: serde_json::Value = serde_json::from_str(&json).expect("JSON output must be valid");

    assert_eq!(parsed["summary"]["total_facts"], 3);
    assert_eq!(parsed["summary"]["assertions"], 1);
    assert_eq!(parsed["summary"]["preconditions"], 1);
    assert_eq!(parsed["summary"]["invariants"], 1);
    assert_eq!(parsed["summary"]["postconditions"], 0);
    assert_eq!(parsed["summary"]["bounds_elimination_hints"], 1);
    assert_eq!(parsed["summary"]["null_check_elimination_hints"], 1);
    assert_eq!(parsed["summary"]["unreachable_branch_hints"], 1);

    let hints_arr = parsed["hints"].as_array().unwrap();
    assert_eq!(hints_arr.len(), 3);

    // Verify each hint's kind in order
    assert_eq!(hints_arr[0]["hint_kind"], "bounds_elimination");
    assert_eq!(hints_arr[1]["hint_kind"], "null_check_elimination");
    assert_eq!(hints_arr[2]["hint_kind"], "unreachable_branch");
}

#[test]
fn regression_format_report_exact_layout() {
    // Pin the report format for a known set of facts.
    let facts = vec![
        make_fact(
            ProvenFactKind::Assertion,
            "x > 0",
            Some("src/lib.rs:42:5"),
            "pos_check",
        ),
        make_fact(
            ProvenFactKind::Invariant,
            "i < arr.len()",
            Some("src/loop.rs:10:9"),
            "loop_bound",
        ),
    ];

    let report = format_report(&facts);

    // Header
    assert!(report.contains("Proven Facts Summary"));
    assert!(report.contains("===================="));

    // Summary counts
    assert!(report.contains("Total proven facts: 2"));
    assert!(report.contains("Assertions:     1"));
    assert!(report.contains("Invariants:     1"));
    assert!(report.contains("Preconditions:  0"));
    assert!(report.contains("Postconditions: 0"));

    // Optimization hints
    assert!(report.contains("Optimization Hints:"));
    assert!(report.contains("Unreachable branches:     1"));
    assert!(report.contains("Bounds eliminations:      1"));
    assert!(report.contains("Null check eliminations:  0"));

    // Details section
    assert!(report.contains("Details:"));
    assert!(report.contains("1. [assertion] `x > 0` at src/lib.rs:42:5 (step: pos_check)"));
    assert!(
        report.contains("2. [invariant] `i < arr.len()` at src/loop.rs:10:9 (step: loop_bound)")
    );
}

#[test]
fn regression_annotations_contain_expected_unsafe_patterns() {
    // Pin the annotation text for each hint kind.
    let facts = vec![
        make_fact(ProvenFactKind::Assertion, "x > 0", Some("a.rs:1:1"), "s1"),
        make_fact(
            ProvenFactKind::Invariant,
            "i < arr.len()",
            Some("b.rs:2:1"),
            "s2",
        ),
        make_fact(
            ProvenFactKind::Precondition,
            "val.is_some()",
            Some("c.rs:3:1"),
            "s3",
        ),
    ];

    let hints = generate_hints(&facts);
    let annotations = emit_hint_annotations(&hints);

    // UnreachableBranch annotation
    assert!(annotations.contains("unreachable_unchecked"));
    assert!(annotations.contains("else branch is dead code"));

    // BoundsElimination annotation
    assert!(annotations.contains("get_unchecked"));
    assert!(annotations.contains("bounds check can be elided"));

    // NullCheckElimination annotation
    assert!(annotations.contains("unwrap_unchecked"));
    assert!(annotations.contains("null/Option check can be elided"));

    // Location headers
    assert!(annotations.contains("At a.rs:1:1"));
    assert!(annotations.contains("At b.rs:2:1"));
    assert!(annotations.contains("At c.rs:3:1"));
}

// ===========================================================================
// Additional benchmarks: scaling and edge cases
// ===========================================================================

#[test]
fn bench_scaling_100_facts_all_bounds() {
    // Benchmark: 100 bounds-check facts -> all should produce BoundsElimination.
    let facts: Vec<ProvenFact> = (0..100)
        .map(|i| {
            make_fact(
                ProvenFactKind::Invariant,
                &format!("idx_{i} < arr.len()"),
                Some(&format!("src/gen.rs:{i}:9")),
                &format!("bound_{i}"),
            )
        })
        .collect();

    let report = ProvenFactsReport::from_facts(&facts);
    assert_eq!(report.total_facts(), 100);
    assert_eq!(report.bounds_elimination_hints(), 100);
    assert_eq!(report.null_check_elimination_hints(), 0);
    assert_eq!(report.unreachable_branch_hints(), 0);
}

#[test]
fn bench_scaling_100_facts_mixed_distribution() {
    // Benchmark: 100 mixed facts with known distribution.
    let mut facts = Vec::new();
    for i in 0..100 {
        let (expr, kind) = match i % 5 {
            0 => (format!("idx_{i} < arr.len()"), ProvenFactKind::Invariant),
            1 => (format!("val_{i}.is_some()"), ProvenFactKind::Precondition),
            2 => (format!("ptr_{i} != None"), ProvenFactKind::Assertion),
            3 => (format!("x_{i} > 0"), ProvenFactKind::Assertion),
            _ => (
                format!("result_{i} == old(x)"),
                ProvenFactKind::Postcondition,
            ),
        };
        facts.push(make_fact(
            kind,
            &expr,
            Some(&format!("src/gen.rs:{i}:1")),
            &format!("step_{i}"),
        ));
    }

    let report = ProvenFactsReport::from_facts(&facts);
    assert_eq!(report.total_facts(), 100);

    // 20 bounds (idx < arr.len())
    assert_eq!(report.bounds_elimination_hints(), 20);
    // 20 null (is_some) + 20 null (!= None) = 40
    assert_eq!(report.null_check_elimination_hints(), 40);
    // 20 unreachable (x > 0) + 20 unreachable (result == old(x)) = 40
    assert_eq!(report.unreachable_branch_hints(), 40);
}

#[test]
fn bench_empty_facts_zero_hints() {
    // Edge case: no facts -> no hints.
    let facts: Vec<ProvenFact> = Vec::new();
    let hints = generate_hints(&facts);
    assert!(hints.is_empty());

    let report = ProvenFactsReport::from_facts(&facts);
    assert_eq!(report.total_facts(), 0);
    assert_eq!(report.bounds_elimination_hints(), 0);
    assert_eq!(report.null_check_elimination_hints(), 0);
    assert_eq!(report.unreachable_branch_hints(), 0);
}

#[test]
fn bench_whitespace_handling_does_not_change_classification() {
    // Edge case: leading/trailing whitespace should not affect classification.
    let pairs = vec![
        ("  i < arr.len()  ", OptimizationHintKind::BoundsElimination),
        (
            "  val.is_some()  ",
            OptimizationHintKind::NullCheckElimination,
        ),
        ("  x > 0  ", OptimizationHintKind::UnreachableBranch),
    ];

    for (expr, expected) in &pairs {
        let facts = vec![make_fact(ProvenFactKind::Assertion, expr, None, "ws_test")];
        let hints = generate_hints(&facts);
        assert_eq!(
            hints[0].hint_kind(),
            *expected,
            "whitespace-padded expression {expr:?} should classify as {expected:?}"
        );
    }
}

#[test]
fn bench_duplicate_facts_produce_duplicate_hints() {
    // Edge case: duplicate facts are not deduplicated (1:1 mapping).
    let fact = make_fact(
        ProvenFactKind::Invariant,
        "i < arr.len()",
        Some("src/loop.rs:5:1"),
        "same_fact",
    );
    let facts = vec![fact.clone(), fact.clone(), fact];

    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 3, "duplicate facts produce duplicate hints");

    let report = ProvenFactsReport::from_facts(&facts);
    assert_eq!(report.bounds_elimination_hints(), 3);
}

#[test]
fn bench_safety_justification_always_references_step_label() {
    // Verify that every hint's safety justification references its step label.
    let facts = vec![
        make_fact(
            ProvenFactKind::Invariant,
            "i < arr.len()",
            None,
            "unique_label_alpha",
        ),
        make_fact(
            ProvenFactKind::Precondition,
            "val.is_some()",
            None,
            "unique_label_beta",
        ),
        make_fact(
            ProvenFactKind::Assertion,
            "x > 0",
            None,
            "unique_label_gamma",
        ),
    ];

    let hints = generate_hints(&facts);
    assert_eq!(hints.len(), 3);

    assert!(
        hints[0]
            .safety_justification()
            .contains("unique_label_alpha"),
        "bounds hint should cite its step label"
    );
    assert!(
        hints[1]
            .safety_justification()
            .contains("unique_label_beta"),
        "null hint should cite its step label"
    );
    assert!(
        hints[2]
            .safety_justification()
            .contains("unique_label_gamma"),
        "unreachable hint should cite its step label"
    );
}
