// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream Verus
// `source/rust_verify_test/tests/mut_refs_loops.rs`.
//
// The manifest entry remains `unsupported-gap`. This file intentionally ports
// only Rust-valid mutable-reference loop behavior that TrustVc can model today:
// - direct local `&mut` writes inside a bare `loop` body;
// - direct local `&mut` writes inside a `while` body;
// - direct pre-borrowed local `&mut` writes before loop/while/for exit paths;
// - direct local `&mut` writes inside `continue`, nested-loop, and `for` body
//   shapes;
// - direct local `&mut` writes inside nested while plus loop/while body shapes
//   after a pre-loop alias reassignment;
// - direct local `&mut` writes before labeled `continue` from nested loop/while
//   shapes;
// - direct pre-borrowed local `&mut` writeback from a loop-return path;
// - direct pre-borrowed local `&mut` writeback after a loop-break path;
// - direct aliased `&mut` parameter writeback from loop-return, single-break,
//   repeated-break, and nested-break paths;
// - stable wrong-value counterexamples after those writes;
// - fail-closed boundaries for Verus-only `has_resolved`/`final` loop
//   reasoning, `after_borrow` loop invariants, direct parameter-derived
//   mutable-reference writeback, nested reassigned-alias loop bodies,
//   tuple-projected mutable-reference writes, leaked-reference reassignment,
//   closure loop bodies, and mutable-reference calls in loop conditions.
//
// Full parity still needs Verus `has_resolved`, `after_borrow`, `final`,
// loop-isolation-sensitive borrow resolution, for-loop desugaring parity,
// mutable-reference condition calls, future/proph post-state reasoning, tuple
// mutable-reference projections, closure loop captures, nontermination
// attributes, and exact diagnostic counts.

#![allow(dead_code)]

pub const MUT_REFS_LOOPS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "mut_refs_loop_body_local_write_verified",
        "control_flow_loops",
        "verified",
        2,
    ),
    (
        "mut_refs_while_body_local_write_verified",
        "control_flow_while_loops",
        "verified",
        2,
    ),
    (
        "mut_refs_loop_preborrow_write_before_loop_exit_verified",
        "control_flow_loops",
        "verified",
        2,
    ),
    (
        "mut_refs_while_preborrow_write_before_loop_exit_verified",
        "control_flow_while_loops",
        "verified",
        2,
    ),
    (
        "mut_refs_for_preborrow_write_before_loop_exit_verified",
        "for_loops",
        "verified",
        2,
    ),
    (
        "mut_refs_loop_body_local_write_continue_verified",
        "control_flow_loops",
        "verified",
        2,
    ),
    (
        "mut_refs_while_body_local_write_continue_verified",
        "control_flow_while_loops",
        "verified",
        2,
    ),
    (
        "mut_refs_for_body_local_write_verified",
        "for_loops",
        "verified",
        2,
    ),
    (
        "mut_refs_nested_loop_local_write_labeled_break_verified",
        "control_flow_loops_nested",
        "verified",
        2,
    ),
    (
        "mut_refs_while_nested_loop_local_write_labeled_break_verified",
        "control_flow_while_loops_nested",
        "verified",
        2,
    ),
    (
        "mut_refs_nested_loop_local_write_labeled_continue_verified",
        "control_flow_loops_nested",
        "verified",
        2,
    ),
    (
        "mut_refs_while_nested_loop_local_write_labeled_continue_verified",
        "control_flow_while_loops_nested",
        "verified",
        2,
    ),
    (
        "mut_refs_loop_reassigned_alias_before_loop_body_verified",
        "control_flow_loops_nested",
        "verified",
        2,
    ),
    (
        "mut_refs_while_reassigned_alias_before_loop_body_verified",
        "control_flow_while_loops_nested",
        "verified",
        2,
    ),
    (
        "mut_refs_loop_preborrow_writeback_return_verified",
        "future_preserved_in_loop",
        "verified",
        2,
    ),
    (
        "mut_refs_loop_preborrow_break_then_writeback_verified",
        "future_preserved_in_loop",
        "verified",
        2,
    ),
    (
        "mut_refs_loop_parameter_alias_writeback_return_verified",
        "future_preserved_in_loop",
        "verified",
        2,
    ),
    (
        "mut_refs_loop_parameter_alias_break_then_writeback_verified",
        "future_preserved_in_loop",
        "verified",
        2,
    ),
    (
        "mut_refs_loop_parameter_alias_two_breaks_writeback_verified",
        "future_preserved_in_loop_fails3",
        "verified",
        2,
    ),
    (
        "mut_refs_loop_parameter_alias_nested_break_writeback_verified",
        "future_preserved_in_loop_fails4",
        "verified",
        2,
    ),
    (
        "mut_refs_loop_body_wrong_written_value_counterexample",
        "control_flow_loops",
        "counterexample",
        1,
    ),
    (
        "mut_refs_loop_preborrow_write_before_loop_wrong_value_counterexample",
        "control_flow_loops",
        "counterexample",
        1,
    ),
    (
        "mut_refs_loop_preborrow_wrong_writeback_counterexample",
        "future_preserved_in_loop",
        "counterexample",
        1,
    ),
    (
        "mut_refs_loop_preborrow_break_wrong_writeback_counterexample",
        "future_preserved_in_loop",
        "counterexample",
        1,
    ),
    (
        "mut_refs_for_body_wrong_written_value_counterexample",
        "for_loops",
        "counterexample",
        1,
    ),
    (
        "mut_refs_loop_preborrow_two_breaks_wrong_writeback_counterexample",
        "future_preserved_in_loop_fails3",
        "counterexample",
        1,
    ),
    (
        "mut_refs_loop_reassigned_alias_before_loop_wrong_written_value_counterexample",
        "control_flow_loops_nested",
        "counterexample",
        1,
    ),
    (
        "mut_refs_loop_has_resolved_boundary_currently_errors",
        "control_flow_loops",
        "error",
        0,
    ),
    (
        "mut_refs_loop_after_borrow_invariant_boundary_currently_errors",
        "control_flow_loops",
        "error",
        0,
    ),
    (
        "mut_refs_loop_final_post_state_boundary_currently_errors",
        "future_preserved_in_loop",
        "error",
        0,
    ),
    (
        "mut_refs_loop_parameter_writeback_boundary_verified",
        "future_preserved_in_loop",
        "verified",
        2,
    ),
    (
        "mut_refs_loop_nested_reassigned_alias_boundary_currently_errors",
        "control_flow_loops_nested",
        "error",
        0,
    ),
    (
        "mut_refs_while_nested_reassigned_alias_boundary_currently_errors",
        "control_flow_while_loops_nested",
        "error",
        0,
    ),
    (
        "mut_refs_loop_tuple_field_writeback_boundary_currently_errors",
        "future_preserved_in_loop",
        "error",
        0,
    ),
    (
        "mut_refs_loop_nested_tuple_mut_ref_write_boundary_currently_errors",
        "future_preserved_in_loop_nested",
        "error",
        0,
    ),
    (
        "mut_refs_loop_parameter_reassignment_leak_boundary_currently_errors",
        "future_preserved_in_loop_fails1",
        "error",
        0,
    ),
    (
        "mut_refs_loop_closure_mut_ref_body_boundary_currently_errors",
        "closure_future_preserved_in_loop",
        "error",
        0,
    ),
    (
        "mut_refs_loop_mut_ref_condition_call_currently_errors",
        "while_loops_with_mutation_in_condition",
        "error",
        0,
    ),
];

pub fn mut_refs_loops_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    MUT_REFS_LOOPS_RS_EXPECTED_CASES
}

pub const MUT_REFS_LOOPS_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "mut_refs_loop_has_resolved_boundary_currently_errors",
        &["has_resolved", "unknown return type"],
    ),
    (
        "mut_refs_loop_after_borrow_invariant_boundary_currently_errors",
        &["after_borrow", "unknown return type", "Failed to lower"],
    ),
    (
        "mut_refs_loop_final_post_state_boundary_currently_errors",
        &[
            "Failed to parse assert!() expression",
            "expected an expression",
            "final",
        ],
    ),
    (
        "mut_refs_loop_nested_reassigned_alias_boundary_currently_errors",
        &[
            "assignment through a dereferenced reference is unsupported",
            "* x_ref",
        ],
    ),
    (
        "mut_refs_while_nested_reassigned_alias_boundary_currently_errors",
        &[
            "assignment through a dereferenced reference is unsupported",
            "* x_ref",
        ],
    ),
    (
        "mut_refs_loop_tuple_field_writeback_boundary_currently_errors",
        &[
            "assignment through a mutable-reference projection is unsupported",
            "tuple-field",
            "pair_ref . 0",
            "field '0'",
        ],
    ),
    (
        "mut_refs_loop_nested_tuple_mut_ref_write_boundary_currently_errors",
        &[
            "assignment through a dereferenced reference is unsupported",
            "* pair . 0",
        ],
    ),
    (
        "mut_refs_loop_parameter_reassignment_leak_boundary_currently_errors",
        &[
            "assignment through a dereferenced reference is unsupported",
            "* aliased_ref",
        ],
    ),
    (
        "mut_refs_loop_closure_mut_ref_body_boundary_currently_errors",
        &[
            "assignment through a dereferenced reference is unsupported",
            "update",
            "value_ref",
        ],
    ),
    (
        "mut_refs_loop_mut_ref_condition_call_currently_errors",
        &["unresolved variable `value`", "Failed to lower obligation"],
    ),
];

pub fn mut_refs_loops_rs_expected_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    MUT_REFS_LOOPS_RS_EXPECTED_ERROR_PATTERNS
}

fn mut_refs_loops_condition(_value_ref: &mut u64) -> bool {
    true
}

fn mut_refs_loops_leak_ref<'a>() -> &'a mut u64 {
    loop {}
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_body_local_write_verified(run: bool) {
    loop {
        if !run {
            break;
        }

        let mut x = 0u64;
        let x_ref: &mut u64 = &mut x;

        *x_ref = 20u64;

        trust_vc::assert!(x == 20u64);
        trust_vc::assert!(*x_ref == 20u64);
        break;
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_while_body_local_write_verified(run: bool) {
    while run {
        let mut x = 0u64;
        let x_ref: &mut u64 = &mut x;

        *x_ref = 20u64;

        trust_vc::assert!(x == 20u64);
        trust_vc::assert!(*x_ref == 20u64);
        break;
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_preborrow_write_before_loop_exit_verified(run: bool) {
    let mut x = 0u64;
    let x_ref: &mut u64 = &mut x;

    *x_ref = 20u64;

    loop {
        if run {
            break;
        }

        break;
    }

    trust_vc::assert!(x == 20u64);
    trust_vc::assert!(*x_ref == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_while_preborrow_write_before_loop_exit_verified(run: bool) {
    let mut x = 0u64;
    let x_ref: &mut u64 = &mut x;

    *x_ref = 20u64;

    while run {
        trust_vc::assert!(*x_ref == 20u64);
        break;
    }

    trust_vc::assert!(x == 20u64);
    trust_vc::assert!(*x_ref == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_for_preborrow_write_before_loop_exit_verified() {
    let mut x = 0u64;
    let x_ref: &mut u64 = &mut x;

    *x_ref = 20u64;

    for _i in 0u64..10u64 {
        trust_vc::assert!(*x_ref == 20u64);
        break;
    }

    trust_vc::assert!(x == 20u64);
    trust_vc::assert!(*x_ref == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_body_local_write_continue_verified(run: bool) {
    loop {
        if !run {
            break;
        }

        let mut x = 0u64;
        let x_ref: &mut u64 = &mut x;

        *x_ref = 20u64;

        trust_vc::assert!(x == 20u64);
        trust_vc::assert!(*x_ref == 20u64);
        continue;
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_while_body_local_write_continue_verified(run: bool) {
    while run {
        let mut x = 0u64;
        let x_ref: &mut u64 = &mut x;

        *x_ref = 20u64;

        trust_vc::assert!(x == 20u64);
        trust_vc::assert!(*x_ref == 20u64);
        continue;
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_for_body_local_write_verified() {
    for _i in 0u64..10u64 {
        let mut x = 0u64;
        let x_ref: &mut u64 = &mut x;

        *x_ref = 20u64;

        trust_vc::assert!(x == 20u64);
        trust_vc::assert!(*x_ref == 20u64);
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_nested_loop_local_write_labeled_break_verified(run: bool) {
    'outer: loop {
        if !run {
            break;
        }

        loop {
            let mut x = 0u64;
            let x_ref: &mut u64 = &mut x;

            loop {
                *x_ref = 20u64;

                trust_vc::assert!(x == 20u64);
                trust_vc::assert!(*x_ref == 20u64);
                break 'outer;
            }
        }
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_while_nested_loop_local_write_labeled_break_verified(run: bool) {
    'outer: while run {
        while run {
            while run {
                let mut x = 0u64;
                let x_ref: &mut u64 = &mut x;

                *x_ref = 20u64;

                trust_vc::assert!(x == 20u64);
                trust_vc::assert!(*x_ref == 20u64);
                break 'outer;
            }

            break;
        }

        break;
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_nested_loop_local_write_labeled_continue_verified(run: bool) {
    'outer: loop {
        if !run {
            break;
        }

        loop {
            let mut x = 0u64;
            let x_ref: &mut u64 = &mut x;

            loop {
                *x_ref = 20u64;

                trust_vc::assert!(x == 20u64);
                trust_vc::assert!(*x_ref == 20u64);
                continue 'outer;
            }
        }
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_while_nested_loop_local_write_labeled_continue_verified(run: bool) {
    'outer: while run {
        loop {
            let mut x = 0u64;
            let x_ref: &mut u64 = &mut x;

            while run {
                *x_ref = 20u64;

                trust_vc::assert!(x == 20u64);
                trust_vc::assert!(*x_ref == 20u64);
                continue 'outer;
            }

            break;
        }
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_reassigned_alias_before_loop_body_verified(run: bool) {
    let mut x = 0u64;
    let mut y = 10u64;
    let mut x_ref: &mut u64 = &mut x;

    x_ref = &mut y;

    loop {
        if !run {
            break;
        }

        *x_ref = 20u64;

        trust_vc::assert!(y == 20u64);
        break;
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_while_reassigned_alias_before_loop_body_verified(run: bool) {
    let mut x = 0u64;
    let mut y = 10u64;
    let mut x_ref: &mut u64 = &mut x;

    x_ref = &mut y;

    while run {
        *x_ref = 20u64;

        trust_vc::assert!(y == 20u64);
        break;
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_body_wrong_written_value_counterexample() {
    loop {
        let mut x = 0u64;
        let x_ref: &mut u64 = &mut x;

        *x_ref = 20u64;

        trust_vc::assert!(x == 21u64);
        break;
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_preborrow_write_before_loop_wrong_value_counterexample() {
    let mut x = 0u64;
    let x_ref: &mut u64 = &mut x;

    *x_ref = 20u64;

    loop {
        break;
    }

    trust_vc::assert!(x == 21u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_preborrow_writeback_return_verified() {
    let mut value = 0u64;
    let value_ref: &mut u64 = &mut value;

    loop {
        *value_ref = 5u64;

        trust_vc::assert!(*value_ref == 5u64);
        trust_vc::assert!(value == 5u64);
        return;
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_preborrow_break_then_writeback_verified() {
    let mut value = 0u64;
    let value_ref: &mut u64 = &mut value;

    loop {
        *value_ref = 20u64;
        break;
    }

    *value_ref = 5u64;

    trust_vc::assert!(*value_ref == 5u64);
    trust_vc::assert!(value == 5u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_parameter_alias_writeback_return_verified(value_ref: &mut u64) {
    let aliased_ref: &mut u64 = value_ref;

    loop {
        *aliased_ref = 5u64;

        trust_vc::assert!(*aliased_ref == 5u64);
        trust_vc::assert!(value_ref == 5u64);
        return;
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_parameter_alias_break_then_writeback_verified(value_ref: &mut u64) {
    let aliased_ref: &mut u64 = value_ref;

    loop {
        *aliased_ref = 20u64;
        break;
    }

    *aliased_ref = 5u64;

    trust_vc::assert!(*aliased_ref == 5u64);
    trust_vc::assert!(value_ref == 5u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_parameter_alias_two_breaks_writeback_verified(value_ref: &mut u64) {
    let aliased_ref: &mut u64 = value_ref;

    loop {
        *aliased_ref = 20u64;
        break;
    }

    loop {
        *aliased_ref = 30u64;
        break;
    }

    *aliased_ref = 5u64;

    trust_vc::assert!(*aliased_ref == 5u64);
    trust_vc::assert!(value_ref == 5u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_parameter_alias_nested_break_writeback_verified(value_ref: &mut u64, run: bool) {
    let aliased_ref: &mut u64 = value_ref;

    loop {
        *aliased_ref = 20u64;
        if run {
            break;
        }

        loop {
            *aliased_ref = 30u64;
            break;
        }

        break;
    }

    *aliased_ref = 5u64;

    trust_vc::assert!(*aliased_ref == 5u64);
    trust_vc::assert!(value_ref == 5u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_preborrow_wrong_writeback_counterexample() {
    let mut value = 0u64;
    let value_ref: &mut u64 = &mut value;

    loop {
        *value_ref = 5u64;

        trust_vc::assert!(value == 6u64);
        return;
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_preborrow_break_wrong_writeback_counterexample() {
    let mut value = 0u64;
    let value_ref: &mut u64 = &mut value;

    loop {
        *value_ref = 20u64;
        break;
    }

    *value_ref = 5u64;

    trust_vc::assert!(value == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_for_body_wrong_written_value_counterexample() {
    for _i in 0u64..10u64 {
        let mut x = 0u64;
        let x_ref: &mut u64 = &mut x;

        *x_ref = 20u64;

        trust_vc::assert!(x == 21u64);
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_preborrow_two_breaks_wrong_writeback_counterexample() {
    let mut value = 0u64;
    let value_ref: &mut u64 = &mut value;

    loop {
        *value_ref = 20u64;
        break;
    }

    loop {
        *value_ref = 30u64;
        break;
    }

    *value_ref = 5u64;

    trust_vc::assert!(value == 30u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_reassigned_alias_before_loop_wrong_written_value_counterexample() {
    let mut x = 0u64;
    let mut y = 10u64;
    let mut x_ref: &mut u64 = &mut x;

    x_ref = &mut y;

    loop {
        *x_ref = 20u64;

        trust_vc::assert!(y == 21u64);
        break;
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_has_resolved_boundary_currently_errors(run: bool) {
    let mut x = 0u64;
    let x_ref: &mut u64 = &mut x;

    *x_ref = 20u64;

    while run {
        trust_vc::assert!(has_resolved(x_ref));
        break;
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_after_borrow_invariant_boundary_currently_errors(run: bool) {
    let mut x = 0u64;
    let x_ref: &mut u64 = &mut x;

    *x_ref = 20u64;

    while run {
        trust_vc::invariant!(after_borrow(x) == x);
        *x_ref = 20u64;
        break;
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_final_post_state_boundary_currently_errors(value_ref: &mut u64) {
    trust_vc::assert!(final(value_ref) == value_ref);
}

// De-surrogated 2026-07-18 (scalar `&mut` deref-write support): a direct
// parameter mutable-reference write inside a loop body now verifies;
// discriminator-certified genuine (falsified variant Counterexamples).
#[trust_vc::ensures(true)]
fn mut_refs_loop_parameter_writeback_boundary_verified(value_ref: &mut u64) {
    loop {
        *value_ref = 5u64;

        trust_vc::assert!(*value_ref == 5u64);
        return;
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_nested_reassigned_alias_boundary_currently_errors(run: bool) {
    let mut x = 0u64;
    let mut y = 10u64;
    let mut x_ref: &mut u64 = &mut x;

    loop {
        if !run {
            break;
        }

        loop {
            x_ref = &mut y;

            loop {
                *x_ref = 20u64;
                trust_vc::assert!(y == 20u64);
                break;
            }

            break;
        }

        break;
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_while_nested_reassigned_alias_boundary_currently_errors(run: bool) {
    let mut x = 0u64;
    let mut y = 10u64;
    let mut x_ref: &mut u64 = &mut x;

    while run {
        while run {
            x_ref = &mut y;

            while run {
                *x_ref = 20u64;
                trust_vc::assert!(y == 20u64);
                break;
            }

            break;
        }

        break;
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_tuple_field_writeback_boundary_currently_errors(pair_ref: &mut (u64, u64)) {
    loop {
        pair_ref.0 = 20u64;
        break;
    }

    pair_ref.0 = 5u64;
    pair_ref.1 = 6u64;

    trust_vc::assert!(pair_ref.0 == 5u64);
    trust_vc::assert!(pair_ref.1 == 6u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_nested_tuple_mut_ref_write_boundary_currently_errors(pair: (&mut u64, &mut u64)) {
    loop {
        *pair.0 = 5u64;
        return;
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_parameter_reassignment_leak_boundary_currently_errors(value_ref: &mut u64) {
    let mut aliased_ref: &mut u64 = value_ref;

    aliased_ref = mut_refs_loops_leak_ref();

    loop {
        *aliased_ref = 5u64;
        return;
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_closure_mut_ref_body_boundary_currently_errors() {
    let update = |value_ref: &mut u64| loop {
        *value_ref = 5u64;
        return;
    };

    let mut value = 0u64;
    update(&mut value);

    trust_vc::assert!(value == 5u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_loop_mut_ref_condition_call_currently_errors() {
    let mut value = 0u64;
    let value_ref: &mut u64 = &mut value;

    while mut_refs_loops_condition(value_ref) {
        trust_vc::assert!(value == 0u64);
        break;
    }
}
