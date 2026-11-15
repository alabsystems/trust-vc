// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS PIN: an obligation may ASSUME a no-overflow fact only when that
//! fact was CHECKED.
//!
//! `AYEncoder::verify_assertion_typed` re-encodes the goal's own no-overflow
//! predicates and asserts them into the solver (the "Assert+Assume" pattern,
//! #2516) on the strength of "they were already verified in a separate
//! encoder". They were verified only when the overflow CHECK ran — and the
//! check is deliberately suppressed for `by(bit_vector)` (bit-vector math
//! WRAPS), for `by(nonlinear_arith)` (mathematical integers), and for
//! spec-predicate obligations (`requires`/`ensures`/`recommends`/`calc!` steps
//! /`__call_requires_*`, which are mathematical `int` in Verus).
//!
//! For exactly those obligations the assume fired anyway. With a `u32` pinned
//! at `u32::MAX`, the assumed `y + 1 <= u32::MAX` CONTRADICTS the hypothesis,
//! so every goal that mentions `y + 1u32` became vacuously true. The witness
//! that makes it undeniable is not a semantics argument at all:
//! `assert_by_bit_vector!(y + 1u32 == 7u32)` verified, and so did
//! `y + 1u32 == 0u32 && 1u32 == 2u32`.
//!
//! The visible SHAPE was an operator-dependent split — `y + 1u32 == 0u32` (true
//! only under WRAPPING) and `y + 1u32 > y` (true only under LOSSLESS integer
//! arithmetic) both verified of the same subterm. Both were vacuous. These pins
//! therefore cover the whole enumerated class: every comparison operator, both
//! signednesses, four widths, the shifts, mixed widths through a cast, a
//! subterm shared between two comparisons in one assertion, and the
//! non-bit-vector lanes the same gate governs.

use std::fs;
use std::path::Path;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verdict(tag: &str, code: &str) -> VerifyResult {
    let dir = Path::new("target/overflow_assume_only_what_is_checked");
    fs::create_dir_all(dir).expect("fixture dir");
    let path = dir.join(format!("{tag}.rs"));
    fs::write(&path, code).expect("write fixture");
    verify_function_from_file(path.to_str().expect("utf-8 path"), "f")
        .unwrap_or_else(|err| panic!("{tag} should extract: {err}"))
}

/// An EXEC (non-`proof`) function - the lane where `overflow_behavior` is on,
/// which is what made the unchecked assume reachable - with `y` pinned and one
/// `by(bit_vector)` goal.
fn bv_goal(tag: &str, param: &str, pin: &str, goal: &str) -> VerifyResult {
    let code = format!(
        "fn f({param}) {{\n    trust_vc::assume!({pin});\n    trust_vc::assert_by_bit_vector!({goal});\n}}\n"
    );
    verdict(tag, &code)
}

#[track_caller]
fn assert_verified(tag: &str, param: &str, pin: &str, goal: &str) {
    let result = bv_goal(tag, param, pin, goal);
    assert!(
        matches!(result, VerifyResult::Verified),
        "`{goal}` under `{pin}` is TRUE of wrapping bit-vector arithmetic and must \
         verify, got {result:?}"
    );
}

#[track_caller]
fn assert_refuted(tag: &str, param: &str, pin: &str, goal: &str) {
    let result = bv_goal(tag, param, pin, goal);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "`{goal}` under `{pin}` is FALSE of wrapping bit-vector arithmetic and must \
         refute, got {result:?}"
    );
}

const U32_MAX_PIN: &str = "y == 0xffff_ffffu32";

// ---------------------------------------------------------------------------
// THE WITNESS, and the proof that it was vacuity rather than a second reading
// ---------------------------------------------------------------------------

/// `1u32 == 2u32` is false in every model. A goal that conjoins it with a term
/// mentioning `y + 1u32` can only verify if the HYPOTHESES are contradictory.
#[test]
fn a_bit_vector_goal_mentioning_overflowing_arithmetic_is_not_vacuous() {
    assert_refuted(
        "vacuity_false_conjunct",
        "y: u32",
        U32_MAX_PIN,
        "y + 1u32 == 0u32 && 1u32 == 2u32",
    );
}

/// The blunt one: `y + 1u32` is `0` under wrapping and `4294967296` under
/// lossless integer arithmetic. It is `7` under neither.
#[test]
fn a_bit_vector_sum_is_not_equal_to_an_arbitrary_wrong_value() {
    assert_refuted(
        "vacuity_wrong_value",
        "y: u32",
        U32_MAX_PIN,
        "y + 1u32 == 7u32",
    );
}

/// The two reported witnesses CONJOINED. `y + 1u32 == 0u32` is the wrapping
/// reading, `y + 1u32 > y` the lossless one; no single reading satisfies both.
#[test]
fn the_two_readings_of_one_subterm_are_never_both_available() {
    assert_refuted(
        "conjoined_readings",
        "y: u32",
        U32_MAX_PIN,
        "y + 1u32 == 0u32 && y + 1u32 > y",
    );
}

/// The positive form of the same property: read consistently, EXACTLY ONE of
/// the two claims holds, so their disequality is a theorem.
#[test]
fn exactly_one_reading_of_the_shared_subterm_holds() {
    assert_verified(
        "exactly_one_reading",
        "y: u32",
        U32_MAX_PIN,
        "(y + 1u32 == 0u32) != (y + 1u32 > y)",
    );
}

// ---------------------------------------------------------------------------
// EVERY COMPARISON OPERATOR against the same subterm `y + 1u32` at u32::MAX.
// Wrapping: `y + 1u32` is 0. So `== 0`, `< y`, `<= y` hold; `!= 0`, `> y`,
// `>= y` do not.
// ---------------------------------------------------------------------------

#[test]
fn every_comparison_operator_reads_the_same_subterm_the_same_way() {
    assert_verified("op_eq", "y: u32", U32_MAX_PIN, "y + 1u32 == 0u32");
    assert_verified("op_lt", "y: u32", U32_MAX_PIN, "y + 1u32 < y");
    assert_verified("op_le", "y: u32", U32_MAX_PIN, "y + 1u32 <= y");
    assert_refuted("op_ne", "y: u32", U32_MAX_PIN, "y + 1u32 != 0u32");
    assert_refuted("op_gt", "y: u32", U32_MAX_PIN, "y + 1u32 > y");
    assert_refuted("op_ge", "y: u32", U32_MAX_PIN, "y + 1u32 >= y");
}

// ---------------------------------------------------------------------------
// The other arithmetic that wraps, each with its REFUTED twin.
// ---------------------------------------------------------------------------

#[test]
fn subtraction_below_zero_wraps_under_every_operator() {
    assert_verified(
        "sub_eq",
        "y: u32",
        "y == 0u32",
        "y - 1u32 == 0xffff_ffffu32",
    );
    assert_verified("sub_gt", "y: u32", "y == 0u32", "y - 1u32 > y");
    assert_refuted("sub_lt", "y: u32", "y == 0u32", "y - 1u32 < y");
    assert_refuted("sub_wrong", "y: u32", "y == 0u32", "y - 1u32 == 7u32");
}

#[test]
fn multiplication_past_the_top_bit_wraps_under_every_operator() {
    assert_verified(
        "mul_eq",
        "y: u32",
        "y == 0x8000_0000u32",
        "y * 2u32 == 0u32",
    );
    assert_refuted("mul_gt", "y: u32", "y == 0x8000_0000u32", "y * 2u32 > y");
    assert_refuted(
        "mul_wrong",
        "y: u32",
        "y == 0x8000_0000u32",
        "y * 2u32 == 7u32",
    );
}

#[test]
fn a_left_shift_out_of_the_word_is_zero_under_every_operator() {
    assert_verified(
        "shl_eq",
        "y: u32",
        "y == 0x8000_0000u32",
        "(y << 1u32) == 0u32",
    );
    assert_refuted("shl_gt", "y: u32", "y == 0x8000_0000u32", "(y << 1u32) > y");
}

// ---------------------------------------------------------------------------
// WIDTHS and SIGNEDNESS.
// ---------------------------------------------------------------------------

#[test]
fn the_same_reading_holds_at_every_width() {
    assert_verified("u8_eq", "y: u8", "y == 0xffu8", "y + 1u8 == 0u8");
    assert_refuted("u8_gt", "y: u8", "y == 0xffu8", "y + 1u8 > y");
    assert_verified("u16_eq", "y: u16", "y == 0xffffu16", "y + 1u16 == 0u16");
    assert_refuted("u16_gt", "y: u16", "y == 0xffffu16", "y + 1u16 > y");
    assert_verified(
        "u64_eq",
        "y: u64",
        "y == 0xffff_ffff_ffff_ffffu64",
        "y + 1u64 == 0u64",
    );
    assert_refuted(
        "u64_gt",
        "y: u64",
        "y == 0xffff_ffff_ffff_ffffu64",
        "y + 1u64 > y",
    );
}

#[test]
fn signed_overflow_wraps_to_the_minimum_under_every_operator() {
    assert_verified(
        "i32_eq",
        "y: i32",
        "y == 2147483647i32",
        "y + 1i32 == -2147483648i32",
    );
    assert_verified("i32_lt", "y: i32", "y == 2147483647i32", "y + 1i32 < y");
    assert_refuted("i32_gt", "y: i32", "y == 2147483647i32", "y + 1i32 > y");
    assert_refuted(
        "i32_ne",
        "y: i32",
        "y == 2147483647i32",
        "y + 1i32 != -2147483648i32",
    );
}

/// MIXED WIDTHS. Widened to `u64` first, `y + 1` does NOT overflow, so the
/// lossless-looking answer is the CORRECT one here — the pin is that the width
/// of the operation decides, not the operator.
#[test]
fn a_widened_subterm_is_read_at_its_own_width() {
    assert_verified(
        "cast_gt",
        "y: u32",
        U32_MAX_PIN,
        "(y as u64) + 1u64 > (y as u64)",
    );
    assert_refuted(
        "cast_eq0",
        "y: u32",
        U32_MAX_PIN,
        "(y as u64) + 1u64 == 0u64",
    );
}

// ---------------------------------------------------------------------------
// NO OVER-REJECTION: goals that are genuine bit-vector theorems, including ones
// whose arithmetic is exactly what used to carry the unchecked assumption, must
// still verify.
// ---------------------------------------------------------------------------

#[test]
fn genuine_bit_vector_theorems_still_verify() {
    for (tag, goal) in [
        ("ovr_and", "(y & y) == y"),
        ("ovr_or", "(y | y) == y"),
        ("ovr_xor", "(y ^ y) == 0u32"),
        ("ovr_add_zero", "y + 0u32 == y"),
        ("ovr_mask", "(y & 0xffu32) < 0x100u32"),
        ("ovr_double_not", "y == !(!y)"),
    ] {
        let code = format!("fn f(y: u32) {{\n    trust_vc::assert_by_bit_vector!({goal});\n}}\n");
        let result = verdict(tag, &code);
        assert!(
            matches!(result, VerifyResult::Verified),
            "`{goal}` is a bit-vector theorem for every `y` and must still verify, got {result:?}"
        );
    }
}

/// CROSS-LANE CONSISTENCY. The only thing that distinguished the two readings
/// was whether the enclosing function was `#[trust_vc::proof]` - a proof
/// function has overflow checking off, so no predicate was manufactured and
/// nothing unchecked was assumed, while an EXEC function got the contradictory
/// hypothesis. A `by(bit_vector)` goal is bit-vector math either way, so the
/// two lanes must agree on every goal.
#[test]
fn the_exec_lane_and_the_proof_lane_agree_on_every_bit_vector_goal() {
    for (tag, goal) in [
        ("xl_eq0", "y + 1u32 == 0u32"),
        ("xl_ne0", "y + 1u32 != 0u32"),
        ("xl_gt", "y + 1u32 > y"),
        ("xl_ge", "y + 1u32 >= y"),
        ("xl_lt", "y + 1u32 < y"),
        ("xl_le", "y + 1u32 <= y"),
        ("xl_wrong", "y + 1u32 == 7u32"),
        ("xl_conj", "y + 1u32 == 0u32 && y + 1u32 > y"),
        ("xl_shared", "(y + 1u32 == 0u32) != (y + 1u32 > y)"),
    ] {
        let exec = format!(
            "fn f(y: u32) {{\n    trust_vc::assume!({U32_MAX_PIN});\n    trust_vc::assert_by_bit_vector!({goal});\n}}\n"
        );
        let proof = format!(
            "#[trust_vc::proof]\nfn f(y: u32) {{\n    trust_vc::assume!({U32_MAX_PIN});\n    trust_vc::assert_by_bit_vector!({goal});\n}}\n"
        );
        let exec = verdict(&format!("{tag}_exec"), &exec);
        let proof = verdict(&format!("{tag}_proof"), &proof);
        assert_eq!(
            std::mem::discriminant(&exec),
            std::mem::discriminant(&proof),
            "`{goal}` must get the same verdict in an exec function and in a \
             `#[trust_vc::proof]` function; got {exec:?} vs {proof:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// THE SAME GATE OUTSIDE `by(bit_vector)`. Spec-predicate obligations
// (`requires`/`ensures`/`__call_requires_*`) also have their overflow check
// suppressed, so they were assuming the same unchecked fact.
// ---------------------------------------------------------------------------

/// A caller-side precondition whose clause mentions arithmetic that overflows
/// at the caller's argument value. `1u32 == 2u32` makes the clause false in
/// every model, so the call must be REJECTED.
#[test]
fn a_caller_side_precondition_is_not_discharged_by_an_unchecked_no_overflow_fact() {
    let code = "\
#[trust_vc::requires(z + 1u32 == 0u32 && 1u32 == 2u32)]
fn callee(z: u32) {}

#[trust_vc::requires(y == 0xffff_ffffu32)]
fn f(y: u32) {
    callee(y);
}
";
    let result = verdict("spec_call_requires", code);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "a precondition containing `1u32 == 2u32` can never be satisfied and the call \
         must be rejected, got {result:?}"
    );
}

/// REFUTED twin for the lane above: the SAME call with a satisfiable
/// precondition must still be accepted, so the fix rejects the false clause and
/// not the lane.
#[test]
fn a_satisfiable_caller_side_precondition_still_discharges() {
    let code = "\
#[trust_vc::requires(z == 0xffff_ffffu32)]
fn callee(z: u32) {}

#[trust_vc::requires(y == 0xffff_ffffu32)]
fn f(y: u32) {
    callee(y);
}
";
    let result = verdict("spec_call_requires_ok", code);
    assert!(
        matches!(result, VerifyResult::Verified),
        "a satisfiable precondition must still discharge, got {result:?}"
    );
}
