// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Partial executable TrustVc scout for upstream mut_refs_patterns.rs.
//
// This intentionally keeps the corpus manifest entry as `unsupported-gap`.
// It covers only Rust-valid by-value tuple-struct, simple enum, and literal
// pattern reads from the same upstream lanes, adjacent direct
// mutable-reference reads/writes, including multi-field tuple structs and one
// irrefutable by-value let-else pattern. It also pins reachable
// by-value/mutable-reference counterexamples and unsupported pattern
// boundaries.
// Mutable-reference pattern bindings, pattern-bound writes, plain tuple
// destructuring, nested tuple subpatterns/place projections, explicit `ref mut`
// binders, `@` binders, const/range patterns under mutable references,
// if-let parity, custom-enum let-else parity,
// let-else mut-ref parity, match guard/or-pattern combinations with
// mutable-reference binders, resolution helpers, and ghost/tracked/proof-mode
// diagnostics remain unsupported.

#![allow(dead_code)]

use trust_vc_types::{Ghost, Tracked};

pub type MutRefsPatternsExpectedCase = (&'static str, &'static str, &'static str, usize);

pub const MUT_REFS_PATTERNS_RS_UPSTREAM_ACTIVE_CASES: &[&str] = &[
    "basic_match_mut_ref",
    "basic_let_stmt_mut_ref",
    "match_on_a_field_place_via_dot",
    "match_on_a_field_via_underscore",
    "let_decl_on_a_field_place",
    "match_explicit_ref_mut_binding",
    "let_explicit_ref_mut_binding",
    "ref_mut_inside_immut_ref",
    "ref_mut_inside_immut_ref_no_lifetime",
    "ref_mut_inside_at_binder",
    "match_complex_mut_ref_combos",
    "complex_nesting_enum_1_variant",
    "let_decl_complex_nesting_enum_1_variant",
    "complex_nesting_enum_2_variant",
    "mut_ref_to_struct_with_immut_refs",
    "let_decl_mut_ref_to_struct_with_immut_refs",
    "mut_ref_to_enum_with_immut_refs",
    "struct_mut_refs_immut_refs",
    "enum_mut_refs_immut_refs",
    "struct_immut_refs_mut_refs",
    "enum_immut_refs_mut_refs",
    "enum_immut_refs_mut_refs2",
    "ref_mut_binding_and_nothing_else",
    "enum_take_mut_refs_to_same_var_in_both_branches",
    "mut_ref_with_range_and_const_patterns",
    "binders_in_pattern_copy_vs_no_copy",
    "binders_in_pattern_ghost_vs_no_ghost",
    "no_resolve_ghost_binders",
    "mut_ref_ghost_binder_forbidden",
    "mut_ref_ghost_atbinder_forbidden",
    "mut_ref_tracked_binder_forbidden",
    "mut_ref_tracked_atbinder_forbidden",
    "mut_ref_tracked_unwrap",
    "mut_ref_ghost_unwrap",
    "mut_ref_ghost_binder_forbidden_mut_ref_field",
    "mut_ref_ghost_binder_forbidden_ghost_type",
    "mut_ref_ghost_binder_forbidden_trk_type",
    "mut_ref_ghost_match_ok_when_no_binder",
    "partial_move_from_enum_with_mut_ref",
    "partial_move_from_pair_with_mut_ref",
    "mut_refs_with_if_let",
    "side_effects_in_match_arg",
    "enum_conditional_resolution",
    "enum_conditional_resolution_with_mut_refs",
    "enum_conditional_resolution_with_mut_refs_and_moves",
    "enum_conditional_resolution_nested",
    "enum_conditional_resolution_nested_with_mut_refs",
    "partial_move_out_of_enum",
    "partial_move_out_of_enum_no_lifetime",
    "partial_move_out_of_enum2",
    "partial_move_out_of_enum3",
    "not_support_pattern_mut_ref_binding_with_guard",
    "not_support_pattern_mut_ref_binding_with_or_pat",
    "not_support_let_pattern_mut_ref_binding_with_or_pat",
    "test_match_guards",
    "test_or_patterns",
    "decl_test_or_patterns",
    "or_patterns_with_conditional_moves",
    "or_patterns_with_conditional_moves2",
    "or_patterns_with_moves_in_same_place",
    "let_else_cfg_reachability",
    "basic_let_else_mut_ref",
    "let_else_on_a_field_place_via_dot",
    "let_else_match_on_a_field_via_underscore",
    "let_else_explicit_ref_mut_binding",
    "let_else_ref_mut_inside_immut_ref",
    "let_else_ref_mut_inside_immut_ref_no_lifetime",
    "let_else_ref_mut_inside_at_binder",
    "let_else_complex_mut_ref_combos",
    "let_else_complex_nesting_enum_1_variant",
    "two_mut_ref_borrows_from_enum",
    "two_mut_ref_borrows_from_enum_no_lifetime",
];

pub fn upstream_mut_refs_patterns_rs_active_cases() -> &'static [&'static str] {
    MUT_REFS_PATTERNS_RS_UPSTREAM_ACTIVE_CASES
}

pub const MUT_REFS_PATTERNS_RS_EXPECTED_CASES: &[MutRefsPatternsExpectedCase] = &[
    (
        "mut_refs_patterns_direct_mut_ref_write_verified",
        "basic_match_mut_ref direct mutable-reference write baseline",
        "verified",
        2,
    ),
    (
        "mut_refs_patterns_tuple_pattern_then_mut_ref_write_verified",
        "basic_let_stmt_mut_ref tuple pattern followed by direct mutable-reference write",
        "verified",
        2,
    ),
    (
        "mut_refs_patterns_let_tuple_struct_value_read_verified",
        "basic_let_stmt_mut_ref::test_foo irrefutable tuple pattern read",
        "verified",
        1,
    ),
    (
        "mut_refs_patterns_let_tuple_struct_pair_value_read_verified",
        "irrefutable multi-field tuple-struct pattern read",
        "verified",
        2,
    ),
    (
        "mut_refs_patterns_match_tuple_struct_value_read_verified",
        "basic_match_mut_ref::test_foo by-value tuple-struct match read",
        "verified",
        1,
    ),
    (
        "mut_refs_patterns_match_tuple_struct_pair_value_read_verified",
        "basic_match_mut_ref by-value multi-field tuple-struct match read",
        "verified",
        2,
    ),
    (
        "mut_refs_patterns_scalar_literal_match_arm_verified",
        "mut_ref_with_range_and_const_patterns scalar literal arm subset",
        "verified",
        1,
    ),
    (
        "mut_refs_patterns_match_option_some_value_read_verified",
        "basic_match_mut_ref::test_opt by-value enum match read",
        "verified",
        1,
    ),
    (
        "mut_refs_patterns_match_option_none_value_read_verified",
        "basic_match_mut_ref::test_opt by-value None arm read",
        "verified",
        1,
    ),
    (
        "mut_refs_patterns_let_one_variant_enum_value_read_verified",
        "let_explicit_ref_mut_binding by-value one-variant enum let read",
        "verified",
        1,
    ),
    (
        "mut_refs_patterns_let_else_tuple_struct_value_read_verified",
        "basic_let_else_mut_ref::test_foo by-value tuple-struct let-else read",
        "verified",
        1,
    ),
    (
        "mut_refs_patterns_match_option_some_arm_counterexample",
        "basic_match_mut_ref::test_opt_fails1 reachable by-value Some arm",
        "counterexample",
        1,
    ),
    (
        "mut_refs_patterns_match_option_none_arm_counterexample",
        "basic_match_mut_ref::test_opt_fails1 reachable by-value None arm",
        "counterexample",
        1,
    ),
    (
        "mut_refs_patterns_match_tuple_struct_pair_arm_counterexample",
        "basic_match_mut_ref multi-field tuple-struct false arm",
        "counterexample",
        1,
    ),
    (
        "mut_refs_patterns_let_else_option_some_arm_counterexample",
        "basic_let_else_mut_ref::test_opt_fails1 by-value enum let-else false arm",
        "counterexample",
        1,
    ),
    (
        "mut_refs_patterns_direct_mut_ref_wrong_post_counterexample",
        "basic_match_mut_ref direct mutable-reference stale-value assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_patterns_tuple_pattern_then_mut_ref_false_tail_counterexample",
        "basic_let_stmt_mut_ref tuple pattern followed by mutable-reference false tail",
        "counterexample",
        1,
    ),
    (
        "mut_refs_patterns_scalar_literal_match_arm_counterexample",
        "mut_ref_with_range_and_const_patterns scalar literal false arm subset",
        "counterexample",
        1,
    ),
    (
        "mut_refs_patterns_mut_ref_const_range_match_currently_blocked",
        "mut_ref_with_range_and_const_patterns mutable-reference const/range pattern boundary",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_plain_tuple_let_verified",
        "let_decl_on_a_field_place plain tuple let-pattern boundary",
        "verified",
        3,
    ),
    (
        "mut_refs_patterns_nested_tuple_subpattern_currently_blocked",
        "nested tuple subpattern inside tuple-struct pattern",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_match_field_place_dot_currently_blocked",
        "match_on_a_field_place_via_dot mutable-reference field-place match",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_match_field_place_tuple_currently_blocked",
        "match_on_a_field_via_underscore tuple field-place match",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_match_mut_ref_read_currently_blocked",
        "basic_match_mut_ref::test_foo mutable-reference match pattern read",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_match_enum_mut_ref_payload_read_currently_blocked",
        "basic_match_mut_ref by-value enum carrying mutable-reference payload",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_match_mut_ref_update_currently_blocked",
        "basic_match_mut_ref::test_foo pattern-bound write",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_let_mut_ref_read_currently_blocked",
        "basic_let_stmt_mut_ref::test_foo mutable-reference let pattern read",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_let_mut_ref_update_currently_blocked",
        "basic_let_stmt_mut_ref::test_foo pattern-bound write",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_explicit_ref_mut_binder_currently_blocked",
        "match_explicit_ref_mut_binding explicit ref mut binder",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_ref_mut_scalar_match_read_currently_blocked",
        "ref_mut_binding_and_nothing_else read-only match ref mut binding",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_ref_mut_scalar_let_read_currently_blocked",
        "ref_mut_binding_and_nothing_else read-only let ref mut binding",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_ref_mut_scalar_match_false_currently_blocked",
        "ref_mut_binding_and_nothing_else read-only match false witness",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_explicit_ref_mut_binder_read_currently_blocked",
        "match_explicit_ref_mut_binding read-only explicit ref mut binder",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_scalar_ref_mut_update_currently_blocked",
        "ref_mut_binding_and_nothing_else pattern-bound scalar write",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_at_binder_currently_blocked",
        "ref_mut_inside_at_binder at-binder pattern boundary",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_if_let_option_value_currently_blocked",
        "mut_refs_with_if_let by-value if-let pattern boundary",
        "verified",
        1,
    ),
    (
        "mut_refs_patterns_if_let_mut_ref_read_currently_blocked",
        "mut_refs_with_if_let mutable-reference if-let pattern read",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_if_let_ref_mut_binding_currently_blocked",
        "mut_refs_with_if_let explicit ref mut if-let binding",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_let_else_option_some_value_currently_blocked",
        "basic_let_else_mut_ref::test_opt by-value enum let-else read",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_let_else_mut_ref_read_currently_blocked",
        "basic_let_else_mut_ref::test_opt mutable-reference let-else read",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_let_else_field_place_currently_blocked",
        "let_else_on_a_field_place_via_dot mutable-reference field-place let-else",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_ref_mut_inside_immut_ref_currently_blocked",
        "ref_mut_inside_immut_ref Rust shared-reference ref mut rejection",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_ref_mut_guard_currently_blocked",
        "not_support_pattern_mut_ref_binding_with_guard",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_ref_mut_or_pattern_currently_blocked",
        "not_support_pattern_mut_ref_binding_with_or_pat or-pattern boundary",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_let_or_pattern_ref_mut_currently_blocked",
        "not_support_let_pattern_mut_ref_binding_with_or_pat or-pattern boundary",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_has_resolved_currently_blocked",
        "has_resolved resolution predicate boundary",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_mut_ref_current_local_borrow_verified",
        "mut_ref_current resolution helper boundary",
        "verified",
        1,
    ),
    (
        "mut_refs_patterns_mut_ref_current_local_borrow_wrong_value_counterexample",
        "mut_ref_current resolution helper boundary",
        "counterexample",
        1,
    ),
    (
        "mut_refs_patterns_mut_ref_future_currently_blocked",
        "mut_ref_future helper boundary",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_after_borrow_currently_blocked",
        "after_borrow resolution helper boundary",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_proof_ref_mut_binding_currently_blocked",
        "mut_ref_ghost_binder_forbidden proof-mode ref mut binder diagnostic",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_ghost_ref_mut_binding_currently_blocked",
        "mut_ref_ghost_binder_forbidden_ghost_type diagnostic",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_tracked_ref_mut_binding_currently_blocked",
        "mut_ref_tracked_binder_forbidden tracked-mode diagnostic",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_side_effects_add1_two_state_verified",
        "side_effects_in_match_arg::add1 two-state mut_ref_current/mut_ref_future contract",
        "verified",
        1,
    ),
    (
        "mut_refs_patterns_side_effects_statement_call_verified",
        "side_effects_in_match_arg statement-position call applies the two-state ensures",
        "verified",
        1,
    ),
    (
        "mut_refs_patterns_side_effects_let_tuple_call_verified",
        "side_effects_in_match_arg::test3 tuple-destructured call result",
        "verified",
        1,
    ),
    (
        "mut_refs_patterns_side_effects_let_tuple_false_counterexample",
        "side_effects_in_match_arg::test3_fails tuple-destructured call result",
        "counterexample",
        1,
    ),
    (
        "mut_refs_patterns_side_effects_let_tuple_wrong_value_counterexample",
        "side_effects_in_match_arg::test3 tuple-destructured call result, wrong post value",
        "counterexample",
        1,
    ),
];

pub fn mut_refs_patterns_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    MUT_REFS_PATTERNS_RS_EXPECTED_CASES
}

struct PatternFoo(u64);
struct PatternPair(u64, u64);
struct PatternNested((u64, u64));

enum PatternOption {
    Some(u64),
    None,
}

enum PatternOneVariant {
    Some(u64),
}

enum PatternRefOption<'a> {
    Some(&'a mut u64),
    None,
}

enum PatternEither {
    Left(u64),
    Right(u64),
}

const PATTERN_CONST: u64 = 24u64;

#[trust_vc::ensures(true)]
fn mut_refs_patterns_direct_mut_ref_write_verified() {
    let mut value = 3u64;
    let value_ref: &mut u64 = &mut value;

    *value_ref = 20u64;

    trust_vc::assert!(value == 20u64);
    trust_vc::assert!(*value_ref == 20u64);
}

#[trust_vc::ensures(true)]
#[trust_vc::requires(o.0 == 20u64)]
fn mut_refs_patterns_let_tuple_struct_value_read_verified(o: PatternFoo) {
    let PatternFoo(i) = o;
    trust_vc::assert!(i == 20u64);
}

#[trust_vc::ensures(true)]
#[trust_vc::requires(o.0 == 20u64)]
fn mut_refs_patterns_tuple_pattern_then_mut_ref_write_verified(o: PatternFoo) {
    let PatternFoo(i) = o;
    let mut value = i;
    let value_ref: &mut u64 = &mut value;

    *value_ref = 30u64;

    trust_vc::assert!(i == 20u64);
    trust_vc::assert!(value == 30u64);
    trust_vc::assert!(*value_ref == 30u64);
}

#[trust_vc::ensures(true)]
#[trust_vc::requires(o.0 == 20u64)]
#[trust_vc::requires(o.1 == 30u64)]
fn mut_refs_patterns_let_tuple_struct_pair_value_read_verified(o: PatternPair) {
    let PatternPair(left, right) = o;
    trust_vc::assert!(left == 20u64);
    trust_vc::assert!(right == 30u64);
}

#[trust_vc::ensures(result == 20u64)]
#[trust_vc::requires(o.0 == 20u64)]
fn mut_refs_patterns_match_tuple_struct_value_read_verified(o: PatternFoo) -> u64 {
    match o {
        PatternFoo(i) => i,
    }
}

#[trust_vc::ensures(result == 50u64)]
#[trust_vc::requires(o.0 == 20u64)]
#[trust_vc::requires(o.1 == 30u64)]
fn mut_refs_patterns_match_tuple_struct_pair_value_read_verified(o: PatternPair) -> u64 {
    match o {
        PatternPair(left, right) => left + right,
    }
}

#[trust_vc::ensures(result)]
fn mut_refs_patterns_scalar_literal_match_arm_verified() -> bool {
    match 24u64 {
        24u64 => true,
        _ => false,
    }
}

#[trust_vc::ensures(result == 20u64)]
fn mut_refs_patterns_match_option_some_value_read_verified() -> u64 {
    match PatternOption::Some(20u64) {
        PatternOption::Some(i) => i,
        PatternOption::None => 0u64,
    }
}

#[trust_vc::ensures(result == 0u64)]
fn mut_refs_patterns_match_option_none_value_read_verified() -> u64 {
    match PatternOption::None {
        PatternOption::Some(i) => i,
        PatternOption::None => 0u64,
    }
}

#[trust_vc::ensures(true)]
#[trust_vc::requires(o.get_Some_0() == 20u64)]
fn mut_refs_patterns_let_one_variant_enum_value_read_verified(o: PatternOneVariant) {
    let PatternOneVariant::Some(i) = o;

    trust_vc::assert!(i == 20u64);
}

#[allow(irrefutable_let_patterns)]
#[trust_vc::ensures(true)]
#[trust_vc::requires(o.0 == 20u64)]
fn mut_refs_patterns_let_else_tuple_struct_value_read_verified(o: PatternFoo) {
    let PatternFoo(i) = o else {
        return;
    };

    trust_vc::assert!(i == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_let_else_option_some_value_currently_blocked() {
    let PatternOption::Some(i) = PatternOption::Some(20u64) else {
        return;
    };

    trust_vc::assert!(i == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_ref_mut_scalar_match_read_currently_blocked() {
    let mut value = 20u64;

    match value {
        ref mut i => {
            trust_vc::assert!(*i == 20u64);
        }
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_ref_mut_scalar_let_read_currently_blocked() {
    let mut value = 20u64;
    let ref mut i = value;

    trust_vc::assert!(*i == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_explicit_ref_mut_binder_read_currently_blocked() {
    let mut o = PatternFoo(20u64);

    match o {
        PatternFoo(ref mut i) => {
            trust_vc::assert!(*i == 20u64);
        }
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_match_option_some_arm_counterexample() {
    match PatternOption::Some(20u64) {
        PatternOption::Some(_) => {
            trust_vc::assert!(false);
        }
        PatternOption::None => {}
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_match_option_none_arm_counterexample() {
    match PatternOption::None {
        PatternOption::Some(_) => {}
        PatternOption::None => {
            trust_vc::assert!(false);
        }
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_match_tuple_struct_pair_arm_counterexample() {
    match PatternPair(20u64, 30u64) {
        PatternPair(_, _) => {
            trust_vc::assert!(false);
        }
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_let_else_option_some_arm_counterexample() {
    let PatternOption::Some(_) = PatternOption::Some(20u64) else {
        return;
    };

    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_direct_mut_ref_wrong_post_counterexample() {
    let mut value = 3u64;
    let value_ref: &mut u64 = &mut value;

    *value_ref = 20u64;

    trust_vc::assert!(value == 3u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_tuple_pattern_then_mut_ref_false_tail_counterexample() {
    let PatternFoo(i) = PatternFoo(20u64);
    let mut value = i;
    let value_ref: &mut u64 = &mut value;

    *value_ref = 30u64;

    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_scalar_literal_match_arm_counterexample() {
    match 24u64 {
        24u64 => {
            trust_vc::assert!(false);
        }
        _ => {}
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_mut_ref_const_range_match_currently_blocked() {
    let mut pair = (24u64, 7u64);
    let pair_ref: &mut (u64, u64) = &mut pair;

    let accepted = match pair_ref {
        (PATTERN_CONST, 3u64..=14u64) => true,
        _ => false,
    };

    trust_vc::assert!(accepted);
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_ref_mut_scalar_match_false_currently_blocked() {
    let mut value = 20u64;

    match value {
        ref mut i => {
            trust_vc::assert!(*i == 20u64);
            trust_vc::assert!(false);
        }
    }
}

// De-surrogated 2026-07-18 (ROOT-D pattern-binding rework): a plain tuple
// `let (left, right) = pair` destructuring now verifies;
// discriminator-certified genuine (falsified variant Counterexamples).
#[trust_vc::ensures(true)]
fn mut_refs_patterns_plain_tuple_let_verified() {
    let pair = (20u64, 30u64);
    let (left, right) = pair;

    trust_vc::assert!(left == 20u64);
    trust_vc::assert!(right == 30u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_nested_tuple_subpattern_currently_blocked(o: PatternNested) {
    let PatternNested((i, _)) = o;
    trust_vc::assert!(i == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_match_field_place_dot_currently_blocked(cond: bool) {
    let mut x = 3u64;
    let mut y = 4u64;
    let option = if cond {
        PatternRefOption::Some(&mut x)
    } else {
        PatternRefOption::None
    };
    let pair = (option, &mut y);

    match pair.0 {
        PatternRefOption::Some(i) => {
            trust_vc::assert!(*i == 3u64);
            *i = 20u64;
        }
        PatternRefOption::None => {
            trust_vc::assert!(y == 4u64);
        }
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_match_field_place_tuple_currently_blocked(cond: bool) {
    let mut x = 3u64;
    let mut y = 4u64;
    let option = if cond {
        PatternRefOption::Some(&mut x)
    } else {
        PatternRefOption::None
    };
    let pair = (option, &mut y);

    match pair {
        (PatternRefOption::Some(i), _) => {
            trust_vc::assert!(*i == 3u64);
            *i = 20u64;
        }
        (PatternRefOption::None, _) => {
            trust_vc::assert!(y == 4u64);
        }
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_match_mut_ref_read_currently_blocked() {
    let mut o = PatternFoo(20u64);
    let o_ref: &mut PatternFoo = &mut o;

    match o_ref {
        PatternFoo(i) => {
            trust_vc::assert!(*i == 20u64);
        }
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_match_enum_mut_ref_payload_read_currently_blocked() {
    let mut value = 20u64;
    let option = PatternRefOption::Some(&mut value);

    match option {
        PatternRefOption::Some(i) => {
            trust_vc::assert!(*i == 20u64);
        }
        PatternRefOption::None => {}
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_match_mut_ref_update_currently_blocked() {
    let mut o = PatternFoo(20u64);
    let o_ref: &mut PatternFoo = &mut o;

    match o_ref {
        PatternFoo(i) => {
            trust_vc::assert!(*i == 20u64);
            *i = 30u64;
        }
    }

    trust_vc::assert!(o.0 == 30u64);
}

#[trust_vc::ensures(true)]
#[trust_vc::requires(o.0 == 20u64)]
fn mut_refs_patterns_at_binder_currently_blocked(o: PatternFoo) {
    let whole @ PatternFoo(i) = o;

    trust_vc::assert!(i == 20u64);
    trust_vc::assert!(whole.0 == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_let_mut_ref_read_currently_blocked() {
    let mut o = PatternFoo(20u64);
    let o_ref: &mut PatternFoo = &mut o;
    let PatternFoo(i) = o_ref;

    trust_vc::assert!(*i == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_let_mut_ref_update_currently_blocked() {
    let mut o = PatternFoo(20u64);
    let o_ref: &mut PatternFoo = &mut o;
    let PatternFoo(i) = o_ref;

    trust_vc::assert!(*i == 20u64);
    *i = 30u64;

    trust_vc::assert!(o.0 == 30u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_explicit_ref_mut_binder_currently_blocked() {
    let mut o = PatternFoo(20u64);

    match o {
        PatternFoo(ref mut i) => {
            trust_vc::assert!(*i == 20u64);
            *i = 30u64;
        }
    }

    trust_vc::assert!(o.0 == 30u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_scalar_ref_mut_update_currently_blocked() {
    let mut value = 20u64;

    match value {
        ref mut i => {
            trust_vc::assert!(*i == 20u64);
            *i = 30u64;
        }
    }

    trust_vc::assert!(value == 30u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_if_let_option_value_currently_blocked() {
    let o = PatternOption::Some(20u64);

    if let PatternOption::Some(i) = o {
        trust_vc::assert!(i == 20u64);
    } else {
        trust_vc::assert!(false);
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_if_let_mut_ref_read_currently_blocked() {
    let mut o = PatternOption::Some(20u64);
    let o_ref: &mut PatternOption = &mut o;

    if let PatternOption::Some(i) = o_ref {
        trust_vc::assert!(*i == 20u64);
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_if_let_ref_mut_binding_currently_blocked() {
    let mut o = PatternOption::Some(20u64);

    if let PatternOption::Some(ref mut i) = o {
        trust_vc::assert!(*i == 20u64);
        *i = 30u64;
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_let_else_mut_ref_read_currently_blocked() {
    let mut o = PatternOption::Some(20u64);
    let o_ref: &mut PatternOption = &mut o;
    let PatternOption::Some(i) = o_ref else {
        return;
    };

    trust_vc::assert!(*i == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_let_else_field_place_currently_blocked(cond: bool) {
    let mut x = 3u64;
    let mut y = 4u64;
    let option = if cond {
        PatternRefOption::Some(&mut x)
    } else {
        PatternRefOption::None
    };
    let pair = (option, &mut y);

    let PatternRefOption::Some(i) = pair.0 else {
        return;
    };

    trust_vc::assert!(*i == 3u64);
    *i = 20u64;
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_ref_mut_inside_immut_ref_currently_blocked() {
    let o = PatternOption::Some(20u64);
    let o_ref: &PatternOption = &o;

    match o_ref {
        PatternOption::Some(ref mut i) => {
            trust_vc::assert!(*i == 20u64);
        }
        PatternOption::None => {}
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_ref_mut_guard_currently_blocked() {
    let mut value = 20u64;

    match value {
        ref mut i if *i == 20u64 => {
            trust_vc::assert!(*i == 20u64);
        }
        _ => {}
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_ref_mut_or_pattern_currently_blocked() {
    let mut value = PatternEither::Left(20u64);

    match value {
        PatternEither::Left(ref mut i) | PatternEither::Right(ref mut i) => {
            trust_vc::assert!(*i == 20u64);
        }
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_let_or_pattern_ref_mut_currently_blocked() {
    let mut value = (20u64, true);
    let (ref mut i, false | true) = value;

    trust_vc::assert!(*i == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_has_resolved_currently_blocked() {
    let value = 20u64;

    trust_vc::assert!(has_resolved(value));
}

// `mut_ref_current(P)` on a LOCAL `&mut` borrow reads the CURRENT value behind
// the borrow, which is exactly what `*P` reads. Pinned in both directions so the
// op can never drift onto some other state.
#[trust_vc::ensures(true)]
fn mut_refs_patterns_mut_ref_current_local_borrow_verified() {
    let mut value = 20u64;
    let value_ref: &mut u64 = &mut value;

    trust_vc::assert!(mut_ref_current(value_ref) == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_mut_ref_current_local_borrow_wrong_value_counterexample() {
    let mut value = 20u64;
    let value_ref: &mut u64 = &mut value;

    trust_vc::assert!(mut_ref_current(value_ref) == 21u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_mut_ref_future_currently_blocked() {
    let mut value = 20u64;
    let value_ref: &mut u64 = &mut value;

    trust_vc::assert!(mut_ref_future(value_ref) == 20u64);
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_after_borrow_currently_blocked() {
    let mut value = 20u64;
    let value_ref: &mut u64 = &mut value;

    trust_vc::assert!(after_borrow(value_ref) == 20u64);
}

#[trust_vc::proof]
fn mut_refs_patterns_proof_ref_mut_binding_currently_blocked() {
    let mut value = 20u64;

    match value {
        ref mut i => {
            trust_vc::assert!(*i == 20u64);
        }
    }
}

#[trust_vc::ensures(true)]
fn mut_refs_patterns_ghost_ref_mut_binding_currently_blocked(g: Ghost<PatternFoo>) {
    match g {
        Ghost(PatternFoo(ref mut i)) => {
            trust_vc::assert!(*i == 20u64);
        }
    }
}

#[trust_vc::proof]
fn mut_refs_patterns_tracked_ref_mut_binding_currently_blocked(t: Tracked<u64>) {
    let value = t.get();
    trust_vc::assert!(value == value);

    match t {
        Tracked(ref mut i) => {
            trust_vc::assert!(*i == *i);
        }
    }
}

// ---------------------------------------------------------------------------
// upstream `side_effects_in_match_arg`
//
// Upstream writes the callee's contract in the `&mut` TWO-STATE VOCABULARY —
// `requires mut_ref_current(b) < 100`, `ensures mut_ref_future(b) ==
// mut_ref_current(b) + 1` — and then calls it in several positions, asserting
// `i == 1` after each. Two separate things had to change before any of it could
// be ported:
//
// 1. The vocabulary spelling VERIFIED at the callee's definition but no caller
//    could instantiate it: the callee `ensures` reached IR lowering with
//    `mut_ref_future(..)` unresolved and the whole caller failed to lower. The
//    plain synonym (`ensures b == ...`) instantiated soundly, so the two
//    spellings were synonyms at the definition and not at the call site.
// 2. Binding the result DROPPED the postcondition: `add1(&mut i);` applied it
//    and `let (r, t) = add1(&mut i);` — upstream's own `test3` — did not, so the
//    havoc variable came back unconstrained and `i == 1` was refuted.
//
// DEVIATION, recorded rather than hidden: upstream's `add1` returns
// `(Blah, Blah)` for a local `enum Blah`. A tuple of enums has no sort in this
// engine's result model (`Context contains variables with unrecognized types
// ... 'result' (type: (Blah, Blah))`), which is an independent type-modelling
// gap, so the port returns a scalar tuple. Everything that the two fixes are
// about — the contract vocabulary, the call positions, the destructuring
// binding form, and upstream's asserted verdicts — is carried over unchanged.
//
// `test1` / `test2` (the call in `match` scrutinee position) and the two
// `_fails` match-arm cases are NOT ported: they need the enum-tuple return.

#[trust_vc::requires(mut_ref_current(b) < 100u64)]
#[trust_vc::ensures(mut_ref_future(b) == mut_ref_current(b) + 1u64)]
fn mut_refs_patterns_side_effects_add1_two_state_verified(b: &mut u64) -> (u64, u64) {
    *b = *b + 1u64;
    (3u64, 4u64)
}

// The neighbouring shape that already worked — the other half of the decisive
// pair. One line apart from the `let (r, t) = ...` form below.
#[trust_vc::ensures(true)]
fn mut_refs_patterns_side_effects_statement_call_verified() {
    let mut i = 0u64;
    mut_refs_patterns_side_effects_add1_two_state_verified(&mut i);

    trust_vc::assert!(i == 1u64);
}

// upstream `test3`
#[trust_vc::ensures(true)]
fn mut_refs_patterns_side_effects_let_tuple_call_verified() {
    let mut i = 0u64;
    let (_r, _t) = mut_refs_patterns_side_effects_add1_two_state_verified(&mut i);

    trust_vc::assert!(i == 1u64);
}

// upstream `test3_fails`: the same body plus upstream's own marked
// `assert(false)`, which upstream counts among the file's 5 expected failures.
#[trust_vc::ensures(true)]
fn mut_refs_patterns_side_effects_let_tuple_false_counterexample() {
    let mut i = 0u64;
    let (_r, _t) = mut_refs_patterns_side_effects_add1_two_state_verified(&mut i);

    trust_vc::assert!(i == 1u64);
    trust_vc::assert!(false);
}

// LIAR TWIN of `test3`: the postcondition says the referent is `0 + 1`, so `2`
// must refute. Without it the verified pin could pass on a vacuous hypothesis
// (resolving the FINAL endpoint to the ENTRY value would assume `b == b + 1`)
// rather than on the callee's actual promise.
#[trust_vc::ensures(true)]
fn mut_refs_patterns_side_effects_let_tuple_wrong_value_counterexample() {
    let mut i = 0u64;
    let (_r, _t) = mut_refs_patterns_side_effects_add1_two_state_verified(&mut i);

    trust_vc::assert!(i == 2u64);
}
