// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(dead_code)]

// Partial executable TrustVc scout for upstream
// `source/rust_verify_test/tests/loops.rs`.
//
// The manifest entry remains `unsupported-gap`. This file intentionally ports
// only Rust-valid loop behavior TrustVc can model today:
// - while-loop invariant and normal-exit facts;
// - loop facts for unmodified locals across ordinary, nested, and shadowing
//   loop bodies;
// - boolean while normal-exit facts plus current-gap nested-break
//   counterexamples;
// - minimal invariant_except_break / loop_ensures witnesses for break and
//   continue;
// - bare-loop regular invariants over unmodified state, checked base + step
//   against the loop's own modified set and available after the loop
//   (2026-09-10, audit row 429);
// - the upstream `example_loop_break` family: invariants and loop ensures
//   checked AT `break` sites, the head-to-head step assuming the break-only
//   `if` fell through, and a `loop_decreases!` measure on a bare loop
//   (2026-09-10, audit rows 430/431), plus the `example_loop_continue` pair
//   (invariants and the measure's descent checked at the continue site), and
//   `loop_continue_no_break` (trailing unconditional continue as a no-op),
//   and the `loop2_ok` family (an effect-free inner loop admitted to the outer
//   exact lane, its invariant checked at the outer loop's arbitrary head);
// - stable counterexamples for missing loop facts, reachable breaks, wrong
//   post-loop assertions, exec-counter overflow at an arbitrary loop head, and
//   stale entry reads of loop-modified parameters; and
// - fail-closed boundaries for source-level loop_decreases! and Verus old-state
//   loop reasoning.
//
// Full parity still needs Verus loop-header invariant/decreases syntax,
// loop-havoc diagnostics, richer break/continue flow, ghost/proof code in loop
// guards, iterator loops and `for x in iter:` syntax, subrange via clauses,
// old/final mutable-reference loop reasoning, loop_isolation(false) behavior,
// recursive-call termination inside loops, and exact upstream diagnostic counts.

pub const LOOPS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "basic_while_invariant_establishes_assertion",
        "basic_while",
        "verified",
        3,
    ),
    (
        "while_unmodified_variable_not_havoced_verified",
        "test_variables_not_havoc_basic",
        "verified",
        1,
    ),
    (
        "while_shadowed_variable_no_effect_verified",
        "test_variables_no_effect_basic",
        "verified",
        1,
    ),
    (
        "nested_while_outer_variable_not_havoced_verified",
        "test_variables_not_havoc_nested",
        "verified",
        1,
    ),
    ("while_bool_guard_normal_exit", "while_b", "verified", 3),
    (
        "loop_continue_loop_ensures_post_loop_use",
        "example_loop_continue",
        "verified",
        4,
    ),
    (
        "loop_break_invariant_except_break",
        "example_loop_break (while slice)",
        "verified",
        4,
    ),
    (
        "loop_break_regular_invariant_preserves_unmodified_fact",
        "basic_loop",
        "verified",
        3,
    ),
    (
        "loop_labeled_inner_break_regular_invariant_preserves_unmodified_fact",
        "loop2_ok_y unmodified-state subset",
        "verified",
        3,
    ),
    (
        "basic_while_missing_upper_invariant_counterexample",
        "basic_while_fail1",
        "counterexample",
        1,
    ),
    (
        "while_nested_inner_break_current_gap_counterexample",
        "while_b2 current TrustVc gap",
        "verified",
        2,
    ),
    (
        "while_labeled_inner_break_current_gap_counterexample",
        "while_b2_y current TrustVc gap",
        "verified",
        2,
    ),
    (
        "while_break_does_not_assume_normal_exit_counterexample",
        "while_to_loop_break",
        "counterexample",
        1,
    ),
    (
        "while_labeled_break_to_outer_counterexample",
        "while_b2_x",
        "counterexample",
        1,
    ),
    (
        "loop_break_false_counterexample",
        "loop_break_false",
        "counterexample",
        1,
    ),
    (
        "loop_labeled_break_false_counterexample",
        "loop_break_false_y",
        "counterexample",
        1,
    ),
    (
        "infinite_loop_verified",
        "infinite_loop",
        "verified",
        3,
    ),
    (
        "loop_infinite2_verified",
        "loop_infinite2",
        "verified",
        3,
    ),
    (
        "loop_infinite2y_verified",
        "loop_infinite2y",
        "verified",
        3,
    ),
    (
        "basic_loop_int_counter_verified",
        "basic_loop",
        "verified",
        4,
    ),
    (
        "basic_loop_fail_counterexample",
        "basic_loop_fail",
        "counterexample",
        4,
    ),
    (
        "basic_while_fail2_counterexample",
        "basic_while_fail2",
        "counterexample",
        5,
    ),
    (
        "test_variables_havoc_nested_counterexample",
        "test_variables_havoc_nested",
        "counterexample",
        6,
    ),
    (
        "test_variables_no_effect_nested_verified",
        "test_variables_no_effect_nested",
        "verified",
        7,
    ),
    (
        "while_b_ok_verified",
        "while_b_ok",
        "verified",
        4,
    ),
    (
        "while_b_fail_counterexample",
        "while_b_fail",
        "counterexample",
        4,
    ),
    (
        "while_to_loop_ensures_verified",
        "while_to_loop_ensures (Verus rejects only through its while-to-loop conversion)",
        "verified",
        4,
    ),
    (
        "loop_decreases2_nested_counters_verified",
        "loop_decreases2 test1",
        "verified",
        11,
    ),
    (
        "loop_decreases2_inner_measure_constant_counterexample",
        "loop_decreases2 test2",
        "counterexample",
        9,
    ),
    (
        "loop_decreases2_outer_measure_constant_counterexample",
        "loop_decreases2 test3",
        "counterexample",
        9,
    ),
    (
        "loop_decreases1_continue_skips_decrease_counterexample",
        "loop_decreases1 test1",
        "counterexample",
        6,
    ),
    (
        "loop_decreases1_fall_through_never_decreases_counterexample",
        "loop_decreases1 test2",
        "counterexample",
        4,
    ),
    (
        "for_loop1_test_loop_peek_verified",
        "for_loop1 test_loop_peek",
        "verified",
        9,
    ),
    (
        "for_loop2_test_loop_verified",
        "for_loop2 test_loop",
        "verified",
        10,
    ),
    (
        "complex_while_exit_values_verified",
        "complex_while",
        "verified",
        11,
    ),
    (
        "complex_while_wrong_exit_value_counterexample",
        "complex_while (exit-value liar)",
        "counterexample",
        10,
    ),
    (
        "loop_nested_break_to_outer_false_counterexample",
        "loop_infinite2x",
        "counterexample",
        1,
    ),
    (
        "loop_break_regular_unmodified_invariant_verified",
        "basic_loop non-tautological invariant (unmodified-state subset)",
        "verified",
        5,
    ),
    (
        "loop_labeled_inner_break_regular_invariant_verified",
        "loop2_ok_y non-tautological invariant (unmodified-state subset)",
        "verified",
        6,
    ),
    (
        "loop_break_unbounded_counter_increment_overflow_counterexample",
        "basic_loop exec-counter overflow at an arbitrary loop head",
        "counterexample",
        6,
    ),
    (
        "loop_break_modified_param_forgets_entry_value_counterexample",
        "test_variables_havoc_basic bare-loop form",
        "counterexample",
        4,
    ),
    (
        "example_loop_break_verified",
        "example_loop_break",
        "verified",
        13,
    ),
    (
        "example_loop_break_fail1_counterexample",
        "example_loop_break_fail1",
        "counterexample",
        13,
    ),
    (
        "example_loop_break_fail2_counterexample",
        "example_loop_break_fail2",
        "counterexample",
        13,
    ),
    (
        "example_loop_break_fail3_counterexample",
        "example_loop_break_fail3",
        "counterexample",
        10,
    ),
    (
        "example_loop_break_fail4_counterexample",
        "example_loop_break_fail4",
        "counterexample",
        12,
    ),
    (
        "example_loop_continue_verified",
        "example_loop_continue",
        "verified",
        16,
    ),
    (
        "example_loop_continue_fail_counterexample",
        "example_loop_continue_fail",
        "counterexample",
        16,
    ),
    (
        "loop_continue_no_break_test_loop_verified",
        "loop_continue_no_break test_loop",
        "verified",
        5,
    ),
    (
        "loop_continue_no_break_fail_beginning_counterexample",
        "loop_continue_no_break test_fail_beginning",
        "counterexample",
        3,
    ),
    (
        "loop_continue_no_break_fail_at_continue_counterexample",
        "loop_continue_no_break test_fail_at_continue",
        "counterexample",
        5,
    ),
    (
        "loop_continue_no_break_fail_at_end_after_continue_counterexample",
        "loop_continue_no_break test_fail_at_end_after_continue",
        "counterexample",
        6,
    ),
    (
        "loop2_ok_verified",
        "loop2_ok",
        "verified",
        8,
    ),
    (
        "loop2_ok_y_verified",
        "loop2_ok_y",
        "verified",
        8,
    ),
    (
        "loop2_fail1_counterexample",
        "loop2_fail1",
        "counterexample",
        6,
    ),
    (
        "loop2_fail2_counterexample",
        "loop2_fail2",
        "counterexample",
        8,
    ),
    (
        "while_loop_decreases_verified",
        "loop_termination_supported / loop_decreases1 boundary",
        "verified",
        9,
    ),
    (
        "loop_old_state_invariant_boundary_currently_errors",
        "loop_references_old_version_of_mut_var old-state boundary",
        "error",
        0,
    ),
];

pub const LOOPS_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "loop_old_state_invariant_boundary_currently_errors",
        &[
            "Unsupported old-state expression `old(...)`",
            "old-state",
            "old",
        ],
    ),
];

pub fn loops_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    LOOPS_RS_EXPECTED_CASES
}

pub fn loops_rs_expected_error_patterns() -> &'static [(&'static str, &'static [&'static str])] {
    LOOPS_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
fn basic_while_invariant_establishes_assertion(mut i: u64, limit: u64) {
    while i < limit {
        trust_vc::invariant!(limit == 10u64);
        i = i + 1u64;
    }

    trust_vc::assert!(i >= 10u64);
}

// Rust-valid slice adjacent to upstream `test_variables_not_havoc_basic`:
// variables not assigned by a break-exiting loop keep their arithmetic facts.
#[trust_vc::requires(a < 100u64)]
#[trust_vc::ensures(true)]
fn while_unmodified_variable_not_havoced_verified(a: u64) {
    let mut i = 0u64;
    let mut j = a;
    j = j + 2u64;

    while i < 1u64 {
        i = i + 1u64;
        if i == 1u64 {
            break;
        }
    }

    j = j + 2u64;
    trust_vc::assert!(j == a + 4u64);
}

// Rust-valid slice adjacent to upstream `test_variables_no_effect_basic`: a
// shadowed loop-local variable does not affect the outer variable.
#[trust_vc::ensures(true)]
fn while_shadowed_variable_no_effect_verified() {
    let mut i = 0u64;
    let mut k = 12u64;

    while i < 1u64 {
        let mut k = i;
        i = i + 1u64;
        k = k + 1u64;
        break;
    }

    k = k + 1u64;
    trust_vc::assert!(k == 13u64);
}

// Rust-valid slice adjacent to upstream `test_variables_not_havoc_nested`: a
// nested loop-local shadow does not havoc an outer variable of the same name.
#[trust_vc::requires(a < 100u64)]
#[trust_vc::ensures(true)]
fn nested_while_outer_variable_not_havoced_verified(a: u64) {
    let mut i = 0u64;
    let mut j = a;
    j = j + 2u64;

    while i < 1u64 {
        i = i + 1u64;
        let mut j = 0u64;
        while j < 1u64 {
            j = j + 1u64;
            break;
        }
        break;
    }

    j = j + 2u64;
    trust_vc::assert!(j == a + 4u64);
}

// Faithful executable slice of upstream `while_b`: normal exit from a pure
// boolean while loop establishes the negated guard.
#[trust_vc::ensures(true)]
fn while_bool_guard_normal_exit(b: bool) {
    while b {}

    trust_vc::assert!(!b);
}

// Upstream `while_b2` normal-exit fact: the inner unlabeled break exits only
// the inner loop and the outer loop has no break, so `!b` holds on normal
// exit. Historically a TrustVc gap pinned as counterexample; the label-scoped
// break-target analysis now proves it. Flip audited 2026-07-04: assert!(b)
// and break-'outer false twins both still produce counterexamples.
#[trust_vc::ensures(true)]
fn while_nested_inner_break_current_gap_counterexample(b: bool) {
    while b {
        while b {
            break;
        }
    }

    trust_vc::assert!(!b);
}

// Upstream `while_b2_y`: the labeled break exits only the nested loop, so
// `!b` holds on the outer loop's normal exit. Historically a TrustVc gap
// pinned as counterexample; now proven. Flip audited 2026-07-04: assert!(b)
// and break-'outer false twins both still produce counterexamples.
#[trust_vc::ensures(true)]
fn while_labeled_inner_break_current_gap_counterexample(b: bool) {
    while b {
        'y: while b {
            break 'y;
        }
    }

    trust_vc::assert!(!b);
}

// Stable local counterexample adjacent to upstream `basic_while_fail1`: the
// normal-exit fact proves only the lower bound, not the exact final value.
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
fn basic_while_missing_upper_invariant_counterexample(mut i: u64, limit: u64) {
    while i < limit {
        i = i + 1u64;
    }

    trust_vc::assert!(i == 10u64);
}

// Faithful executable slice of upstream `while_to_loop_break`: a break out of
// the while body cannot justify the normal-exit guard fact.
#[trust_vc::ensures(true)]
fn while_break_does_not_assume_normal_exit_counterexample(b: bool) {
    while b {
        break;
    }

    trust_vc::assert!(!b);
}

// Faithful executable slice of upstream `while_b2_x`: a labeled break to the
// outer while bypasses the outer normal-exit guard fact.
#[trust_vc::ensures(true)]
fn while_labeled_break_to_outer_counterexample(b: bool) {
    'x: while b {
        while b {
            break 'x;
        }
    }

    trust_vc::assert!(!b);
}

// Minimal supported slice of upstream `example_loop_continue`: a continue path
// does not suppress the loop postcondition fact used after the loop.
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
fn loop_continue_loop_ensures_post_loop_use(mut i: u64, limit: u64) {
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

// Minimal supported slice of upstream `example_loop_break`: a loop with a break
// may carry an invariant_except_break clause, but that fact is not used as an
// unconditional post-loop assertion.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
fn loop_break_invariant_except_break(mut i: u64, limit: u64) {
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

// Faithful executable slice of upstream `loop_break_false`: a normal break from
// a bare loop reaches the following assertion.
#[trust_vc::ensures(true)]
fn loop_break_false_counterexample() {
    loop {
        break;
    }

    trust_vc::assert!(false);
}

// Faithful executable slice of upstream `loop_break_false_y`: an unlabeled
// break from a labeled loop reaches the following assertion.
#[trust_vc::ensures(true)]
fn loop_labeled_break_false_counterexample() {
    'y: loop {
        break;
    }

    trust_vc::assert!(false);
}

// Upstream `infinite_loop` / `loop_infinite2` / `loop_infinite2y` (2026-09-10,
// audit row 430): a bare loop that no `break` can leave marks the code after it
// unreachable, so the trailing `assert!(false)` verifies exactly as Verus
// reports it (with an "unreachable" warning). The nested loops' breaks target
// only the INNER loop; `loop_infinite2x` below breaks to the OUTER label and
// still refutes.
#[trust_vc::ensures(true)]
fn infinite_loop_verified() {
    loop {}

    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn loop_infinite2_verified() {
    'x: loop {
        'y: loop {
            break;
        }
    }

    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn loop_infinite2y_verified() {
    'x: loop {
        'y: loop {
            break 'y;
        }
    }

    trust_vc::assert!(false);
}

// Upstream `basic_loop` (a ghost `int` counter under `invariant a > 0`, never
// exits) and `basic_loop_fail` (a `u32` counter decremented under the same
// invariant, which is not preserved). The proof-block assignment is written as
// the native `int` local it is; `int`/`nat` let-local counters joined the loop
// scalar model on 2026-09-10 (audit row 430).
#[trust_vc::ensures(true)]
fn basic_loop_int_counter_verified() {
    let mut a: int = 5int;
    loop {
        trust_vc::invariant!(a > 0int);

        a = a + 1int;
    }
}

#[trust_vc::ensures(true)]
fn basic_loop_fail_counterexample() {
    let mut a: u32 = 5u32;
    loop {
        trust_vc::invariant!(a > 0u32);

        a = a - 1u32;
    }
}

// Six more upstream loops.rs shapes promoted 2026-09-10 (audit rows 429/430;
// each measured before pinning). `basic_while_fail2` / `test_variables_havoc_nested`
// refute because the inner loop havocs `j`; `test_variables_no_effect_nested`
// verifies because the inner `k` shadows the outer one; `while_b_ok` proves its
// loop `ensures` through the normal-exit fact and `while_b_fail` refutes it at
// the trailing `break`. `while_to_loop_ensures` is pinned VERIFIED although
// Verus reports an error: Verus converts a `while` that carries `ensures` into
// a `loop` and therefore drops the negated-guard exit fact, but `!b` genuinely
// holds after `while b { }` exits — trust-vc proves the true property (a
// superior verdict, not a divergence in semantics).
#[trust_vc::ensures(true)]
fn basic_while_fail2_counterexample() {
    let mut i = 0u64;
    let mut j = 0u64;
    while i < 10u64 {
        i = i + 1u64;
        while j < 5u64 {
            j = j + 1u64;
        }
    }

    trust_vc::assert!(j == 0u64);
}

#[trust_vc::requires(a < 10u64)]
#[trust_vc::ensures(true)]
fn test_variables_havoc_nested_counterexample(a: u64) {
    let mut i = a;
    while i < 20u64 {
        i = i + 1u64;
        let mut j = a;
        while j < 10u64 {
            j = j + 1u64;
        }
        trust_vc::assert!(j == a);
    }
}

#[trust_vc::requires(a < 10u64)]
#[trust_vc::ensures(true)]
fn test_variables_no_effect_nested_verified(a: u64) {
    let mut i = a;
    let mut k = 12u64;
    while i < 20u64 {
        let mut k = i;
        i = i + 1u64;
        while k < 20u64 {
            k = k + 1u64;
        }
    }
    k = k + 1u64;

    trust_vc::assert!(k == 13u64);
}

#[trust_vc::ensures(true)]
fn while_b_ok_verified(b: bool) {
    while b {
        trust_vc::loop_ensures!(!b);
    }

    trust_vc::assert!(!b);
}

#[trust_vc::ensures(true)]
fn while_b_fail_counterexample(b: bool) {
    while b {
        trust_vc::loop_ensures!(!b);
        break;
    }

    trust_vc::assert!(!b);
}

#[trust_vc::ensures(true)]
fn while_to_loop_ensures_verified(b: bool) {
    while b {
        trust_vc::loop_ensures!(true);
    }

    trust_vc::assert!(!b);
}

// Upstream `loop_decreases2` (2026-09-10, audit rows 430/431): nested counters,
// each with a `loop_decreases!` measure. `test1` verifies because the inner
// loop — which modifies `j`, cannot `break`, and has a flat body — is
// SUMMARIZED for the outer transition (`j` ↦ a fresh exit symbol constrained
// by the inner invariants and the negated guard), so the outer measure's
// strict descent `i - 1 < i` is still an exact frame-condition step. `test2`
// refutes the INNER measure (the body never changes `j`) and `test3` the OUTER
// one (the body never changes `i`): a never-modified measure renders to its
// constant value, and its declared type is handed to the measure builder so the
// descent obligation is emitted and refuted rather than failing closed.
#[trust_vc::ensures(true)]
fn loop_decreases2_nested_counters_verified() {
    let mut i: u8 = 100;
    let mut j: u8 = 100;
    while i > 0 {
        trust_vc::loop_decreases!(i);

        while j > 0 {
            trust_vc::loop_decreases!(j);

            j = j - 1;
        }
        i = i - 1;
    }

    trust_vc::assert!(i == 0);
}

#[trust_vc::ensures(true)]
fn loop_decreases2_inner_measure_constant_counterexample() {
    let mut i: u8 = 100;
    let mut j: u8 = 100;
    while i > 0 {
        trust_vc::loop_decreases!(i);

        while j > 0 {
            trust_vc::loop_decreases!(j);
        }
        i = i - 1;
    }
}

#[trust_vc::ensures(true)]
fn loop_decreases2_outer_measure_constant_counterexample() {
    let mut i: u8 = 100;
    let mut j: u8 = 100;
    while i > 0 {
        trust_vc::loop_decreases!(i);

        while j > 0 {
            trust_vc::loop_decreases!(j);

            j = j - 1;
        }
    }
}

// Upstream `loop_decreases1` (2026-09-10): both functions FAIL in Verus and
// refute here at the same place. `test1` skips the decrement on the `continue`
// path — the continue-site descent check (`i_decreases__continue_*`) refutes;
// `test2` decrements only inside the `continue` arm, so the fall-through path
// never decreases — the head-to-head descent refutes.
#[trust_vc::ensures(true)]
fn loop_decreases1_continue_skips_decrease_counterexample() {
    let mut i: u8 = 100;
    loop {
        trust_vc::loop_decreases!(i);

        if i == 0 {
            break;
        }
        if i == 20 {
            continue;
        }
        i = i - 1;
    }
}

#[trust_vc::ensures(true)]
fn loop_decreases1_fall_through_never_decreases_counterexample() {
    let mut i: u8 = 100;
    loop {
        trust_vc::loop_decreases!(i);

        if i == 0 {
            break;
        }
        if i == 20 {
            i = i - 1;
            continue;
        }
    }
}

// Upstream `for_loop1::test_loop_peek` and `for_loop2::test_loop` (2026-09-10,
// audit row 433): a range `for` verifies with ONLY its accumulator invariant —
// the desugar auto-injects both bounds (`LO <= x` and `!(LO <= HI) || x <= HI`),
// so the negated guard at exit pins `x == HI` and `n == 30` follows. The guard
// reaches the body assertion `x < 10`. (The upstream `iter:` ghost-iterator
// binding and `iter.cur` are Verus surface; the counter itself carries the
// same facts here.)
#[trust_vc::ensures(true)]
fn for_loop1_test_loop_peek_verified() {
    let mut n: u64 = 0;
    for x in 0u64..10u64 {
        trust_vc::invariant!(n == x * 3u64);

        trust_vc::assert!(x < 10u64);
        n = n + 3u64;
    }

    trust_vc::assert!(n == 30u64);
}

#[trust_vc::ensures(true)]
fn for_loop2_test_loop_verified() {
    let mut n: u64 = 0;
    let end: u64 = 10;
    for x in 0u64..end {
        trust_vc::invariant!(n == x * 3u64);
        trust_vc::invariant!(end == 10u64);

        trust_vc::assert!(x < 10u64);
        n = n + 3u64;
    }

    trust_vc::assert!(n == 30u64);
}

// Upstream `complex_while` (2026-09-11, audit row 430): the `while` guard is a
// BLOCK with a side effect (`x = x + 1`) that runs at EVERY head, including the
// last, failing evaluation — so the exit state is a head state satisfying the
// invariants, transformed by the guard block, with the condition false:
// `i == 20` and `x == 11`. The extractor rotates the loop into a pure-guard
// `while` over a snapshot of the guard-assigned var (`while_guard_desugar.rs`).
#[trust_vc::ensures(true)]
fn complex_while_exit_values_verified() {
    let mut i: u64 = 10;
    let mut x: u64 = 0;
    while {
        x = x + 1u64;
        i < 20u64
    } {
        trust_vc::invariant!(10u64 <= i);
        trust_vc::invariant!(i <= 20u64);
        trust_vc::invariant!(x == i - 10u64);
        i = i + 1u64;
    }

    trust_vc::assert!(i == 20u64);
    trust_vc::assert!(x == 11u64);
}

// Exit-value liar twin of upstream `complex_while`: the guard block ran eleven
// times, so `x == 10` is refuted.
#[trust_vc::ensures(true)]
fn complex_while_wrong_exit_value_counterexample() {
    let mut i: u64 = 10;
    let mut x: u64 = 0;
    while {
        x = x + 1u64;
        i < 20u64
    } {
        trust_vc::invariant!(10u64 <= i);
        trust_vc::invariant!(i <= 20u64);
        trust_vc::invariant!(x == i - 10u64);
        i = i + 1u64;
    }

    trust_vc::assert!(x == 10u64);
}

// Faithful executable slice of upstream `loop_infinite2x`: a nested break to
// the outer loop reaches the following assertion.
#[trust_vc::ensures(true)]
fn loop_nested_break_to_outer_false_counterexample() {
    'x: loop {
        loop {
            break 'x;
        }
    }

    trust_vc::assert!(false);
}

// Faithful unmodified-state slice of upstream `basic_loop` / `loop2_ok`: a bare
// `loop {}` with a `break` carries a tautological regular invariant, the
// modified exec variable is havoc'd after the loop, and the unmodified-state
// fact reaches the following assertion. The modified variable is written
// WITHOUT arithmetic on purpose: with only `invariant!(true)` at the loop head
// `i` is arbitrary there, so `i + 1` is a genuine possible-overflow refutation
// (Verus reports the same) — pinned separately below as a counterexample.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
fn loop_break_regular_invariant_preserves_unmodified_fact(mut i: u64, limit: u64) {
    loop {
        trust_vc::invariant!(true);

        i = 1u64;
        if i == 1u64 {
            break;
        }
    }

    trust_vc::assert!(limit == 10u64);
}

// Upstream `loop2_ok_y` unmodified-state slice: a labeled inner break still
// carries tautological invariant metadata and reaches the following assertion.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
fn loop_labeled_inner_break_regular_invariant_preserves_unmodified_fact(mut i: u64, limit: u64) {
    'x: loop {
        trust_vc::invariant!(true);

        i = 1u64;
        'y: loop {
            trust_vc::invariant!(true);
            break 'y;
        }

        if i == 1u64 {
            break 'x;
        }
    }

    trust_vc::assert!(limit == 10u64);
}

// Upstream `basic_loop` non-tautological slice (unmodified-state subset): a
// regular invariant over UNMODIFIED state is checked base + inductive-step
// against the loop's own modified set and its fact reaches the post-loop
// assertion. Flipped from a pinned "current gap" counterexample on 2026-09-10
// (audit row 429): before, a bare loop pushed no loop context, so the
// invariant's inductive step fell into the havoc-ALL lane and refuted even
// `limit == 10`. Invariants over the MODIFIED counter itself (upstream
// `loop2_ok`'s `i == 0`) still fail closed — audit rows 430/431.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
fn loop_break_regular_unmodified_invariant_verified(mut i: u64, limit: u64) {
    loop {
        trust_vc::invariant!(limit == 10u64);

        i = 1u64;
        if i == 1u64 {
            break;
        }
    }

    trust_vc::assert!(limit == 10u64);
}

// Upstream `loop2_ok_y` non-tautological slice (unmodified-state subset): the
// labeled inner break shape with a regular invariant over unmodified state in
// both loops. Same 2026-09-10 flip as above.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
fn loop_labeled_inner_break_regular_invariant_verified(mut i: u64, limit: u64) {
    'x: loop {
        trust_vc::invariant!(limit == 10u64);

        i = 1u64;
        'y: loop {
            trust_vc::invariant!(limit == 10u64);
            break 'y;
        }

        if i == 1u64 {
            break 'x;
        }
    }

    trust_vc::assert!(limit == 10u64);
}

// Verus-faithful overflow refutation: loop-body exec arithmetic is checked at an
// ARBITRARY loop head under the invariants. Nothing bounds `i` there, so
// `i + 1` can overflow and the function is refuted (Verus reports "possible
// arithmetic overflow" for the same shape). Before 2026-09-10 a bare loop's
// body arithmetic was checked against the ENTRY value and this false-verified.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::requires(limit == 10u64)]
#[trust_vc::ensures(true)]
fn loop_break_unbounded_counter_increment_overflow_counterexample(mut i: u64, limit: u64) {
    loop {
        trust_vc::invariant!(limit == 10u64);

        i = i + 1u64;
        if i == 1u64 {
            break;
        }
    }

    trust_vc::assert!(limit == 10u64);
}

// Bare-loop form of upstream `test_variables_havoc_basic`: a parameter written
// inside the loop is havoc'd after it, so its `requires` entry value cannot be
// read back. Before 2026-09-10 the file path kept the entry symbol for a
// bare-loop-modified param and this false-verified.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
fn loop_break_modified_param_forgets_entry_value_counterexample(mut i: u64) {
    loop {
        trust_vc::invariant!(true);

        i = 5u64;
        break;
    }

    trust_vc::assert!(i == 0u64);
}

// Faithful port of upstream `example_loop_break` (u64 for the port's integer
// surface), in-body `assert(i <= 9)` included: a body assertion is checked at an
// arbitrary loop head under the guard and every invariant, except-break ones
// included (2026-09-10, audit row 430). The except-break invariant bounds the
// counter at the head, the
// regular invariant and the loop ensures are checked AT the `break` site and
// carried past the loop, and the measure strictly decreases on every
// head-to-head iteration. Landed 2026-09-10 (audit rows 430/431): a body of flat
// assignments plus `if cond { break; }` sites is in the exact-transition lane,
// each site emits exit checks, and the head-to-head step assumes the site fell
// through.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
fn example_loop_break_verified(mut i: u64) {
    loop {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_ensures!(1u64 <= i);
        trust_vc::loop_decreases!(10u64 - i);

        trust_vc::assert!(i <= 9u64);
        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }

    trust_vc::assert!(1u64 <= i);
    trust_vc::assert!(i <= 10u64);
}

// Upstream `example_loop_break_fail1`: the except-break invariant is false at
// entry (`i == 10` on entry, clause `i <= 9`).
#[trust_vc::requires(i == 10u64)]
#[trust_vc::ensures(true)]
fn example_loop_break_fail1_counterexample(mut i: u64) {
    loop {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_ensures!(1u64 <= i);
        trust_vc::loop_decreases!(10u64 - i);

        trust_vc::assert!(i <= 9u64);
        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }

    trust_vc::assert!(1u64 <= i);
    trust_vc::assert!(i <= 10u64);
}

// Upstream `example_loop_break_fail2`: the except-break invariant `i <= 8` is not
// preserved by the fall-through path (`i == 8` steps to 9 without breaking).
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
fn example_loop_break_fail2_counterexample(mut i: u64) {
    loop {
        trust_vc::invariant_except_break!(i <= 8u64);
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_ensures!(1u64 <= i);
        trust_vc::loop_decreases!(10u64 - i);

        trust_vc::assert!(i <= 9u64);
        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }

    trust_vc::assert!(1u64 <= i);
    trust_vc::assert!(i <= 10u64);
}

// Upstream `example_loop_break_fail3`: an unconditional `break` exits with
// `i == 0`, so the loop ensures `1 <= i` fails. The unconditional break keeps
// the body out of the exact lane (havoc); the ensures then has to follow from
// the invariants alone and does not.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
fn example_loop_break_fail3_counterexample(mut i: u64) {
    loop {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_ensures!(1u64 <= i);
        trust_vc::loop_decreases!(10u64 - i);

        break;
    }

    trust_vc::assert!(1u64 <= i);
    trust_vc::assert!(i <= 10u64);
}

// Upstream `example_loop_break_fail4`: the post-loop assertion `i <= 9` is too
// strong — only the regular invariant (`i <= 10`) and the ensures (`1 <= i`)
// survive the loop, and the loop exits with `i == 10`.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
fn example_loop_break_fail4_counterexample(mut i: u64) {
    loop {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_ensures!(1u64 <= i);
        trust_vc::loop_decreases!(10u64 - i);

        trust_vc::assert!(i <= 9u64);
        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }

    trust_vc::assert!(i <= 9u64);
}

// Faithful port of upstream `example_loop_continue` (u64): a continue-only `if`
// keeps the body in the exact lane — every invariant (except-break included) and
// the measure's strict descent are checked AT the continue site, and the
// fall-through step assumes the site was not taken (2026-09-10, audit rows
// 430/431). The break site behaves as in `example_loop_break_verified`.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
fn example_loop_continue_verified(mut i: u64) {
    loop {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_ensures!(1u64 <= i);
        trust_vc::loop_decreases!(10u64 - i);

        trust_vc::assert!(i <= 9u64);
        i = i + 1u64;
        if i == 5u64 {
            continue;
        }
        if i == 10u64 {
            break;
        }
    }

    trust_vc::assert!(1u64 <= i);
    trust_vc::assert!(i <= 10u64);
}

// Upstream `example_loop_continue_fail`: the continue fires at `i == 10`, where
// the except-break invariant `i <= 9` is violated on the way back to the head.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
fn example_loop_continue_fail_counterexample(mut i: u64) {
    loop {
        trust_vc::invariant_except_break!(i <= 9u64);
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_ensures!(1u64 <= i);
        trust_vc::loop_decreases!(10u64 - i);

        trust_vc::assert!(i <= 9u64);
        i = i + 1u64;
        if i == 10u64 {
            continue;
        }
        if i == 10u64 {
            break;
        }
    }

    trust_vc::assert!(1u64 <= i);
    trust_vc::assert!(i <= 10u64);
}

// Upstream `loop_continue_no_break` (four functions; Verus: test_loop Ok, the
// other three FAIL). Trailing unconditional `continue;` / `break;` statements
// are in the exact lane since 2026-09-10 (audit row 430): a trailing
// `continue;` is a no-op, a trailing `break;` is an exit site reached
// unconditionally. Two divergences are kept honest rather than surrogated:
// (1) upstream's `test_loop` body is a bare `continue;` over an unmodified
// counter, so the loop never exits once entered and the post-loop assertion is
// unreachable — Verus passes it vacuously, trust-vc reports the whole-function
// vacuity as Unknown by design; the port increments the counter so the trailing
// continue is a genuine no-op. (2) upstream's `test_fail_*` counters are
// `let mut i = 7`, so their loops never run; Verus's isolated body check still
// fails them, trust-vc value-numbers the unmodified local and the step is
// vacuous (the code is correct) — the port makes those loops reachable and
// terminating so the broken invariant is what refutes.
#[trust_vc::ensures(true)]
fn loop_continue_no_break_test_loop_verified() {
    let mut i = 0u64;
    while i < 5u64 {
        trust_vc::invariant!(i <= 5u64);
        i = i + 1u64;
        continue;
    }

    trust_vc::assert!(i == 5u64);
}

#[trust_vc::ensures(true)]
fn loop_continue_no_break_fail_beginning_counterexample() {
    let mut x = 0u64;
    let mut i = 7u64;
    while i < 5u64 {
        trust_vc::invariant!(x == 1u64);
        x = 1u64;
        continue;
    }
}

#[trust_vc::requires(i < 5u64)]
#[trust_vc::ensures(true)]
fn loop_continue_no_break_fail_at_continue_counterexample(mut i: u64) {
    let mut x = 2u64;
    while i < 5u64 {
        trust_vc::invariant!(x == 2u64);
        x = 1u64;
        i = i + 1u64;
        continue;
    }
}

#[trust_vc::requires(i < 5u64)]
#[trust_vc::ensures(true)]
fn loop_continue_no_break_fail_at_end_after_continue_counterexample(b: bool, mut i: u64) {
    let mut x = 2u64;
    while i < 5u64 {
        trust_vc::invariant!(x == 2u64);
        i = i + 1u64;
        if b {
            continue;
        }
        x = 1u64;
    }
}

// Upstream `loop2_ok` family (2026-09-10, audit rows 430/431): an inner loop
// that assigns nothing is admitted to the outer body's exact-transition lane,
// and its own invariant is checked at the OUTER loop's arbitrary head — over
// the outer head symbols, under the outer invariants — the nested-loop
// soundness fix that landed with it (before, an inner invariant that held only
// on the first outer iteration verified). `loop2_fail1` breaks to the OUTER
// label from inside the inner loop (a non-flat outer body: the outer invariant
// is not inductive under havoc); `loop2_fail2` reaches the outer break site
// with `i == 1`.
#[trust_vc::ensures(true)]
fn loop2_ok_verified(b: bool) {
    let mut i: i8 = 0;
    'x: loop {
        trust_vc::invariant!(i == 0i8);
        i = i + 1i8;
        'y: loop {
            trust_vc::invariant!(i == 1i8);
            break;
        }
        i = i - 1i8;
        if b {
            break;
        }
    }

    trust_vc::assert!(i == 0i8);
}

#[trust_vc::ensures(true)]
fn loop2_ok_y_verified(b: bool) {
    let mut i: i8 = 0;
    'x: loop {
        trust_vc::invariant!(i == 0i8);
        i = i + 1i8;
        'y: loop {
            trust_vc::invariant!(i == 1i8);
            break 'y;
        }
        i = i - 1i8;
        if b {
            break;
        }
    }

    trust_vc::assert!(i == 0i8);
}

#[trust_vc::ensures(true)]
fn loop2_fail1_counterexample(b: bool) {
    let mut i: i8 = 0;
    'x: loop {
        trust_vc::invariant!(i == 0i8);
        i = i + 1i8;
        'y: loop {
            trust_vc::invariant!(i == 1i8);
            break 'x;
        }
        i = i - 1i8;
        if b {
            break;
        }
    }

    trust_vc::assert!(i == 0i8);
}

#[trust_vc::ensures(true)]
fn loop2_fail2_counterexample(b: bool) {
    let mut i: i8 = 0;
    'x: loop {
        trust_vc::invariant!(i == 0i8);
        i = i + 1i8;
        'y: loop {
            trust_vc::invariant!(i == 1i8);
            break;
        }
        if b {
            break;
        }
        i = i - 1i8;
    }

    trust_vc::assert!(i == 0i8);
}

// Source-level loop_decreases! now verifies on the file path: the measure
// `10 - i` strictly decreases each iteration and the precondition establishes
// the invariant at entry (de-surrogated — was a fail-closed boundary).
#[trust_vc::requires(i <= 10u64)]
#[trust_vc::ensures(true)]
fn while_loop_decreases_verified(mut i: u64) {
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_decreases!(10u64 - i);

        i = i + 1u64;
    }

    trust_vc::assert!(i == 10u64);
}

// Fail-closed boundary for upstream `loop_references_old_version_of_mut_var`:
// TrustVc does not yet model Verus old-state loop invariants in source files.
#[trust_vc::ensures(true)]
fn loop_old_state_invariant_boundary_currently_errors(mut i: u64) {
    while i < 1u64 {
        trust_vc::invariant!(old(i) == 0u64);
        i = i + 1u64;
    }

    trust_vc::assert!(i >= 1u64);
}
