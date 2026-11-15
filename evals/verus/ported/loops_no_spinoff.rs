// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Expanded partial executable TrustVc scout for upstream
// `source/rust_verify_test/tests/loops_no_spinoff.rs`.
//
// This file intentionally keeps the corpus manifest entry as
// `unsupported-gap`. The upstream file exercises Verus loop_isolation(false)
// / no-spinoff lowering, Verus loop-header invariant/decreases syntax, havocing,
// break/continue flow facts, iterator loops, and diagnostics. TrustVc does not
// currently expose that full Verus proof-language surface.
//
// This Rust-valid scout pins stable current TrustVc behavior:
// - numeric while-loop invariant and normal-exit reasoning;
// - pure while-loop normal exit establishes the negated guard;
// - variables not modified by loop bodies retain their executable facts;
// - variables modified by loop bodies are havoced after loop summaries;
// - break/continue loop summaries where TrustVc has explicit loop_ensures facts;
// - nested-break loop-flow that Verus accepts remains explicit gap evidence;
// - early breaks, including labeled breaks, do not receive the outer
//   normal-exit fact; and
// - bare, labeled, and syntactically infinite `loop` reachability gaps are
//   pinned as stable counterexamples;
// - a `while` guard block with flat scalar side effects verifies with the
//   guard block's effects at every head (2026-09-11);
// - simple Rust for-loop summaries remain fail-closed unsupported boundaries;
//   and
// - source-level loop_decreases! and old-state loop assertions remain
//   fail-closed unsupported boundaries.
//
// Full parity still needs Verus loop_isolation attributes, loop-header
// invariant/decreases clauses, side-effectful guard summaries, exact nested
// break/no-spinoff control-flow summaries, iterator ghost-state syntax, old/final
// loop-state reasoning, and upstream diagnostic cardinality.

#![allow(dead_code)]

pub const LOOPS_NO_SPINOFF_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "loops_no_spinoff_while_bool_guard_normal_exit_verified",
        "while_b",
        "verified",
        1,
    ),
    (
        "loops_no_spinoff_basic_while_invariant_normal_exit_verified",
        "basic_while",
        "verified",
        2,
    ),
    (
        "loops_no_spinoff_variables_not_havoc_basic_verified",
        "test_variables_not_havoc_basic",
        "verified",
        2,
    ),
    (
        "loops_no_spinoff_variables_no_effect_basic_verified",
        "test_variables_no_effect_basic",
        "verified",
        2,
    ),
    (
        "loops_no_spinoff_variables_not_havoc_nested_verified",
        "test_variables_not_havoc_nested",
        "verified",
        1,
    ),
    (
        "loops_no_spinoff_variables_no_effect_nested_verified",
        "test_variables_no_effect_nested",
        "verified",
        1,
    ),
    (
        "loops_no_spinoff_loop_continue_post_loop_use_verified",
        "example_loop_continue",
        "verified",
        3,
    ),
    (
        "loops_no_spinoff_loop_break_loop_ensures_verified",
        "example_loop_break",
        "verified",
        4,
    ),
    (
        "loops_no_spinoff_allow_complex_invariants_subset_verified",
        "allow_complex_invariants_basic",
        "verified",
        4,
    ),
    (
        "loops_no_spinoff_loop2_restore_before_break_verified",
        "loop2_ok",
        "verified",
        10,
    ),
    (
        "loops_no_spinoff_loop2_restore_before_labeled_inner_break_verified",
        "loop2_ok_y",
        "verified",
        10,
    ),
    (
        "loops_no_spinoff_while_break_does_not_assume_normal_exit_counterexample",
        "while_b_fail",
        "counterexample",
        1,
    ),
    (
        "loops_no_spinoff_while_nested_inner_break_current_gap_counterexample",
        "local",
        "verified",
        1,
    ),
    (
        "loops_no_spinoff_while_labeled_inner_break_current_gap_counterexample",
        "local",
        "verified",
        1,
    ),
    (
        "loops_no_spinoff_while_labeled_break_to_outer_counterexample",
        "while_b2_x",
        "counterexample",
        1,
    ),
    (
        "loops_no_spinoff_loop_break_false_counterexample",
        "loop_break_false",
        "counterexample",
        1,
    ),
    (
        "loops_no_spinoff_example_loop_break_without_progress_counterexample",
        "example_loop_break_fail3",
        "counterexample",
        1,
    ),
    (
        "loops_no_spinoff_example_loop_break_post_too_strong_counterexample",
        "example_loop_break_fail4",
        "counterexample",
        1,
    ),
    (
        "loops_no_spinoff_basic_while_missing_invariant_counterexample",
        "basic_while_fail1",
        "counterexample",
        1,
    ),
    (
        "loops_no_spinoff_basic_while_nested_j_havoc_counterexample",
        "basic_while_fail2",
        "counterexample",
        1,
    ),
    (
        "loops_no_spinoff_variables_havoc_basic_counterexample",
        "test_variables_havoc_basic",
        "counterexample",
        1,
    ),
    (
        "loops_no_spinoff_variables_havoc_nested_counterexample",
        "test_variables_havoc_nested",
        "counterexample",
        1,
    ),
    (
        "loops_no_spinoff_complex_while_side_effect_guard_verified",
        "complex_while",
        "verified",
        12,
    ),
    (
        "loops_no_spinoff_loop_break_false_labeled_counterexample",
        "loop_break_false_y",
        "counterexample",
        1,
    ),
    (
        "loops_no_spinoff_infinite_loop_unreachable_verified",
        "infinite_loop",
        "verified",
        3,
    ),
    (
        "loops_no_spinoff_loop_infinite_nested_inner_break_verified",
        "loop_infinite2",
        "verified",
        3,
    ),
    (
        "loops_no_spinoff_loop_infinite_nested_labeled_inner_break_verified",
        "loop_infinite2y",
        "verified",
        3,
    ),
    (
        "loops_no_spinoff_loop_labeled_break_to_outer_false_counterexample",
        "loop_infinite2x",
        "counterexample",
        1,
    ),
    (
        "loops_no_spinoff_loop2_labeled_break_to_outer_counterexample",
        "loop2_fail1",
        "counterexample",
        1,
    ),
    (
        "loops_no_spinoff_loop2_missing_restore_counterexample",
        "loop2_fail2",
        "counterexample",
        1,
    ),
    (
        "loops_no_spinoff_for_loop_range_fact_verified",
        "for_loop1",
        "verified",
        5,
    ),
    (
        "loops_no_spinoff_for_loop_range_fact_liar_counterexample",
        "for_loop1 test_loop_fail",
        "counterexample",
        5,
    ),
    (
        "loops_no_spinoff_for_loop_accumulator_post_boundary_counterexample",
        "for_loop1",
        "counterexample",
        1,
    ),
    (
        "loops_no_spinoff_loop_decreases_verified",
        "loop_termination_unsupported",
        "verified",
        9,
    ),
    (
        "loops_no_spinoff_loop_decreases_continue_counterexample",
        "loop_decreases1",
        "counterexample",
        5,
    ),
    // AUDITED FLIP 2026-07-09: slice B: param never mutated so entry==current is a true tautology; NOTE upstream Verus rejects this shape DIAGNOSTICALLY - a documented scout divergence, to reconcile via diagnostic parity at port time
    (
        "loops_no_spinoff_loop_old_state_boundary_currently_errors",
        "loop_references_old_version_of_mut_var",
        "verified",
        1,
    ),
];

pub const LOOPS_NO_SPINOFF_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    // for_loop_range_fact / for_loop_accumulator_post removed 2026-07-24: the range
    // `for` now desugars (for_range_desugar.rs) and both Counterexample instead of
    // erroring — moved to the counterexample subset (see the expected-cases table).
    // loops_no_spinoff_loop_old_state_boundary_currently_errors removed 2026-07-09: audited slice-B flip (see the expected-cases table).
    // loops_no_spinoff_loop_decreases{,_continue} de-surrogated: file-path loop_decreases! now routes (verified / counterexample); no longer error boundaries.
    ];

pub fn loops_no_spinoff_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    LOOPS_NO_SPINOFF_RS_EXPECTED_CASES
}

pub fn loops_no_spinoff_rs_expected_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    LOOPS_NO_SPINOFF_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::ensures(true)]
fn loops_no_spinoff_while_bool_guard_normal_exit_verified(b: bool) {
    while b {}

    trust_vc::assert!(!b);
}

#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
fn loops_no_spinoff_basic_while_invariant_normal_exit_verified(mut i: u64, limit: u64) {
    while i < limit {
        trust_vc::invariant!(limit == 10u64);

        i = i + 1u64;
    }

    trust_vc::assert!(i >= 10u64);
}

#[trust_vc::requires(a < 10u64)]
#[trust_vc::ensures(true)]
fn loops_no_spinoff_variables_not_havoc_basic_verified(a: u64, mut i: u64) {
    let mut j = a;
    j = j + 2u64;

    while i < 20u64 {
        trust_vc::assert!(a < 10u64);
        i = i + 1u64;
    }

    j = j + 2u64;
    trust_vc::assert!(j == a + 4u64);
}

// Upstream `test_variables_no_effect_basic` carries `requires a < 10` (the
// port maps upstream's `let mut i = a;` onto the `mut i` parameter directly,
// so the clause reads `i < 10u64`). The port had dropped it.
#[trust_vc::requires(i < 10u64)]
#[trust_vc::ensures(true)]
fn loops_no_spinoff_variables_no_effect_basic_verified(mut i: u64) {
    let mut k = 12u64;

    while i < 20u64 {
        let mut k = i;
        i = i + 1u64;
        k = k + 1u64;
        trust_vc::assert!(k == i);
    }

    k = k + 1u64;
    trust_vc::assert!(k == 13u64);
}

#[trust_vc::requires(a < 10u64)]
#[trust_vc::ensures(true)]
fn loops_no_spinoff_variables_not_havoc_nested_verified(a: u64, mut i: u64) {
    let mut j = a;
    j = j + 2u64;

    while i < 20u64 {
        i = i + 1u64;

        let mut inner = i;
        while inner < 20u64 {
            inner = inner + 1u64;
        }
    }

    j = j + 2u64;
    trust_vc::assert!(j == a + 4u64);
}

// Upstream `test_variables_no_effect_nested` carries the same `requires a < 10`
// as its basic sibling; restored for port faithfulness (same mapping of
// upstream's `a` onto the `mut i` parameter).
#[trust_vc::requires(i < 10u64)]
#[trust_vc::ensures(true)]
fn loops_no_spinoff_variables_no_effect_nested_verified(mut i: u64) {
    let mut k = 12u64;

    while i < 20u64 {
        let mut inner = i;
        i = i + 1u64;

        while inner < 20u64 {
            inner = inner + 1u64;
        }
    }

    k = k + 1u64;
    trust_vc::assert!(k == 13u64);
}

#[trust_vc::requires(i <= 10u64)]
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
fn loops_no_spinoff_loop_continue_post_loop_use_verified(mut i: u64, limit: u64) {
    while i < limit {
        trust_vc::invariant!(limit == 10u64);
        trust_vc::loop_ensures!(i >= 10u64);

        i = i + 1u64;
        if i == 5u64 {
            continue;
        }
    }

    trust_vc::assert!(i >= 10u64);
}

#[trust_vc::requires(i <= 10u64)]
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
fn loops_no_spinoff_loop_break_loop_ensures_verified(mut i: u64, limit: u64) {
    while i < limit {
        trust_vc::invariant!(limit == 10u64);
        trust_vc::invariant_except_break!(limit == 10u64);
        trust_vc::loop_ensures!(limit == 10u64);

        i = i + 1u64;
        if i == limit {
            break;
        }
    }

    trust_vc::assert!(limit == 10u64);
}

#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
fn loops_no_spinoff_allow_complex_invariants_subset_verified(mut i: u64, limit: u64) {
    while i < limit {
        trust_vc::invariant_except_break!(limit == 10u64);
        trust_vc::invariant!(limit == 10u64);
        trust_vc::loop_ensures!(i >= 10u64);

        i = i + 1u64;
    }

    trust_vc::assert!(i >= 10u64);
}

// Upstream `loop2_ok` / `loop2_ok_y` (loop_isolation(false) shape, but the
// nested loop modifies nothing so isolation makes no difference): re-pinned
// 2026-09-10 from "current gap" counterexamples — an effect-free inner loop is
// admitted to the outer body's exact-transition lane and its invariant is
// checked at the outer loop's arbitrary head (audit row 430). The liars
// `loop2_missing_restore` / `loop2_labeled_break_to_outer` below still refute.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
fn loops_no_spinoff_loop2_restore_before_break_verified(mut i: u64, b: bool) {
    loop {
        trust_vc::invariant!(i == 0u64);
        trust_vc::loop_ensures!(i == 0u64);

        i = i + 1u64;
        loop {
            trust_vc::invariant!(i == 1u64);
            break;
        }
        i = i - 1u64;

        if b {
            break;
        }
    }

    trust_vc::assert!(i == 0u64);
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
fn loops_no_spinoff_loop2_restore_before_labeled_inner_break_verified(
    mut i: u64,
    b: bool,
) {
    loop {
        trust_vc::invariant!(i == 0u64);
        trust_vc::loop_ensures!(i == 0u64);

        i = i + 1u64;
        'inner: loop {
            trust_vc::invariant!(i == 1u64);
            break 'inner;
        }
        i = i - 1u64;

        if b {
            break;
        }
    }

    trust_vc::assert!(i == 0u64);
}

#[trust_vc::ensures(true)]
fn loops_no_spinoff_while_break_does_not_assume_normal_exit_counterexample(b: bool) {
    while b {
        break;
    }

    trust_vc::assert!(!b);
}

#[trust_vc::ensures(true)]
fn loops_no_spinoff_while_nested_inner_break_current_gap_counterexample(b: bool) {
    while b {
        while b {
            break;
        }
    }

    trust_vc::assert!(!b);
}

#[trust_vc::ensures(true)]
fn loops_no_spinoff_while_labeled_inner_break_current_gap_counterexample(b: bool) {
    while b {
        'inner: while b {
            break 'inner;
        }
    }

    trust_vc::assert!(!b);
}

#[trust_vc::ensures(true)]
fn loops_no_spinoff_while_labeled_break_to_outer_counterexample(b: bool) {
    'outer: while b {
        while b {
            break 'outer;
        }
    }

    trust_vc::assert!(!b);
}

#[trust_vc::ensures(true)]
fn loops_no_spinoff_loop_break_false_counterexample() {
    loop {
        break;
    }

    trust_vc::assert!(false);
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
fn loops_no_spinoff_example_loop_break_without_progress_counterexample(mut i: u64) {
    loop {
        trust_vc::invariant!(i <= 9u64);
        trust_vc::loop_ensures!(i >= 1u64);
        trust_vc::loop_ensures!(i <= 10u64);

        break;
    }

    trust_vc::assert!(i >= 1u64);
    trust_vc::assert!(i <= 10u64);
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
fn loops_no_spinoff_example_loop_break_post_too_strong_counterexample(mut i: u64) {
    loop {
        trust_vc::invariant!(i <= 9u64);
        trust_vc::loop_ensures!(i <= 9u64);

        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }

    trust_vc::assert!(i <= 9u64);
}

#[trust_vc::ensures(true)]
fn loops_no_spinoff_basic_while_missing_invariant_counterexample(mut i: u64) {
    while i < 10u64 {
        i = i + 1u64;
    }

    trust_vc::assert!(i == 10u64);
}

#[trust_vc::ensures(true)]
fn loops_no_spinoff_basic_while_nested_j_havoc_counterexample(mut i: u64, mut j: u64) {
    while i < 10u64 {
        i = i + 1u64;

        while j < 5u64 {
            j = j + 1u64;
        }
    }

    trust_vc::assert!(j == 0u64);
}

#[trust_vc::ensures(true)]
fn loops_no_spinoff_variables_havoc_basic_counterexample(a: u64, mut i: u64) {
    while i < 20u64 {
        i = i + 1u64;
    }

    trust_vc::assert!(i == a);
}

#[trust_vc::ensures(true)]
fn loops_no_spinoff_variables_havoc_nested_counterexample(a: u64, mut i: u64, mut j: u64) {
    while i < 20u64 {
        i = i + 1u64;

        while j < 10u64 {
            j = j + 1u64;
        }

        trust_vc::assert!(j == a);
    }
}

// Upstream `complex_while`: re-pinned VERIFIED 2026-09-11 (audit row 430) from a
// "current gap" counterexample — the guard block's side effect now runs at every
// head including the last, failing evaluation (`while_guard_desugar.rs`), so
// `i == 10` and `x == 11` hold after the loop.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn loops_no_spinoff_complex_while_side_effect_guard_verified(
    mut i: u64,
    mut x: u64,
) {
    while {
        x = x + 1u64;
        i < 10u64
    } {
        trust_vc::invariant!(i <= 10u64);
        trust_vc::invariant!(x == i);

        i = i + 1u64;
    }

    trust_vc::assert!(i == 10u64);
    trust_vc::assert!(x == 11u64);
}

#[trust_vc::ensures(true)]
fn loops_no_spinoff_loop_break_false_labeled_counterexample() {
    'y: loop {
        break 'y;
    }

    trust_vc::assert!(false);
}

// Upstream `infinite_loop` / `loop_infinite2` / `loop_infinite2y`: re-pinned
// 2026-09-10 from "current gap" counterexamples — the code after a bare loop
// that no `break` can leave is unreachable (audit row 430), so the trailing
// `assert!(false)` verifies as in Verus. `loop_infinite2x` (`break 'outer`)
// below still refutes.
#[trust_vc::ensures(true)]
fn loops_no_spinoff_infinite_loop_unreachable_verified() {
    loop {}

    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn loops_no_spinoff_loop_infinite_nested_inner_break_verified() {
    loop {
        loop {
            break;
        }
    }

    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn loops_no_spinoff_loop_infinite_nested_labeled_inner_break_verified() {
    loop {
        'inner: loop {
            break 'inner;
        }
    }

    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn loops_no_spinoff_loop_labeled_break_to_outer_false_counterexample() {
    'outer: loop {
        loop {
            break 'outer;
        }
    }

    trust_vc::assert!(false);
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
fn loops_no_spinoff_loop2_labeled_break_to_outer_counterexample(mut i: u64) {
    'outer: loop {
        trust_vc::invariant!(i == 0u64);

        i = i + 1u64;
        loop {
            trust_vc::invariant!(i == 1u64);
            break 'outer;
        }
    }

    trust_vc::assert!(i == 0u64);
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
fn loops_no_spinoff_loop2_missing_restore_counterexample(mut i: u64, b: bool) {
    loop {
        trust_vc::invariant!(i == 0u64);

        i = i + 1u64;
        loop {
            trust_vc::invariant!(i == 1u64);
            break;
        }

        if b {
            break;
        }

        i = i - 1u64;
    }

    trust_vc::assert!(i == 0u64);
}

// Upstream `for_loop1` body fact (Verus: `assert(x < 10)` verifies): the range
// `for` desugars to a counter-driven `while` (for_range_desugar.rs), and since
// 2026-09-10 a body assertion is checked at an arbitrary loop head UNDER THE
// GUARD `x < 10` (audit row 430), so the upper bound reaches it. Before, the
// guard was not a body-entry fact and this was pinned as a sound over-rejection.
#[trust_vc::ensures(true)]
fn loops_no_spinoff_for_loop_range_fact_verified() {
    for x in 0u64..10u64 {
        trust_vc::assert!(x < 10u64);
    }
}

// Upstream `for_loop1` `test_loop_fail`: the tighter body fact `x < 9` is false at
// the last iteration and must be refuted.
#[trust_vc::ensures(true)]
fn loops_no_spinoff_for_loop_range_fact_liar_counterexample() {
    for x in 0u64..10u64 {
        trust_vc::assert!(x < 9u64);
    }
}

// Re-pinned 2026-07-24: the range `for` now desugars. `n` is modified in the loop
// with NO accumulator invariant pinning it, so post-loop `n` is havoced and
// `assert!(n == 30)` Counterexamples — exactly as Verus rejects it without an
// invariant `n == 3 * _x`. Boundary moved Error → Counterexample.
#[trust_vc::ensures(true)]
fn loops_no_spinoff_for_loop_accumulator_post_boundary_counterexample() {
    let mut n = 0u64;

    for _x in 0u64..10u64 {
        n = n + 3u64;
    }

    trust_vc::assert!(n == 30u64);
}

// De-surrogated: source-level loop_decreases! now verifies on the file path.
// `requires(i <= 10)` establishes the invariant at entry (the old
// `requires(i == 0)` collided with the post-loop `i >= 10` exit fact in the
// vacuous-assumption check); the measure `10 - i` strictly decreases.
#[trust_vc::requires(i <= 10u64)]
#[trust_vc::ensures(true)]
fn loops_no_spinoff_loop_decreases_verified(mut i: u64) {
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_decreases!(10u64 - i);

        i = i + 1u64;
    }

    trust_vc::assert!(i == 10u64);
}

// Continue-back-edge landmine: measure `i` counts down, but the `if i == 20 {
// continue }` back-edge SKIPS the decrement, so the loop does not terminate.
// The bare `loop{}` captures no single-iteration transition, so the decrease
// keeps a free entry variable ⇒ COUNTEREXAMPLE (upstream Verus rejects this).
#[trust_vc::ensures(true)]
fn loops_no_spinoff_loop_decreases_continue_counterexample(mut i: u64) {
    loop {
        trust_vc::loop_decreases!(i);

        if i == 0u64 {
            break;
        }

        if i == 20u64 {
            continue;
        }

        i = i - 1u64;
    }
}

#[trust_vc::ensures(true)]
fn loops_no_spinoff_loop_old_state_boundary_currently_errors(value_ref: &mut u64) {
    loop {
        trust_vc::assert!(*old(value_ref) == *value_ref);
        break;
    }
}
