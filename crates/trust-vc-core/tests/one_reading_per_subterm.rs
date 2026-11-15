// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS PIN: one subterm, one reading — ACROSS lanes as well as inside
//! one.
//!
//! trust-vc solves obligations in two arithmetic universes and uses the same
//! term for a fixed-width subterm in both. `by(nonlinear_arith)` and the
//! `decreases` measure lane declare every `uN`/`iN` variable as an unbounded
//! ay `Int` (so the integer theory can handle `*`, `/`, `%` symbolically);
//! every other lane declares it as a `BitVec(N)`, where the same arithmetic
//! WRAPS. A fact established in one universe was asserted, unchanged, into a
//! solve running the other — and at a boundary value the two readings
//! CONTRADICT, so the hypothesis set went unsatisfiable and everything after
//! it verified vacuously.
//!
//! The reported witness, VERIFIED before the gate:
//!
//! ```text
//! fn f(y: u32) {
//!     trust_vc::assume!(y == 0xffff_ffffu32);
//!     trust_vc::assert_by_nonlinear!(y + 1u32 > y);   // TRUE of math int
//!     trust_vc::assert!(1u32 == 2u32);                // ← VERIFIED
//! }
//! ```
//!
//! and seven more of the same shape: `-` at zero, `*` past the top bit,
//! `u8`/`u32`/`u64`, `i32` at `MAX`, and the false conclusion written as a
//! `postcondition` rather than a body assert.
//!
//! THE BAR these pins hold, in both directions:
//!
//! * a fact proved under the math-int reading may not be assumed under the
//!   fixed-width one (`nonlinear_conclusion_*`);
//! * a fact given under the fixed-width reading may not be assumed under the
//!   math-int one (`fixed_width_hypothesis_*`) — `requires(a + b == c)` is
//!   satisfied by a wrapping caller and must not license `c >= b`;
//! * neither reading is WEAKENED to buy the above: every lane still proves its
//!   own true claims (`still_verifies_*`), and a spec-only `int`/`nat` fact —
//!   which both universes read identically — still crosses freely.
//!
//! Each positive pin carries its refuted twin, and each refutation pin carries
//! the verifying claim that shows the lane is not simply switched off.

use std::fs;
use std::path::Path;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verdict_of(tag: &str, code: &str, func: &str) -> VerifyResult {
    let dir = Path::new("target/one_reading_per_subterm");
    fs::create_dir_all(dir).expect("fixture dir");
    let path = dir.join(format!("{tag}.rs"));
    fs::write(&path, code).expect("write fixture");
    verify_function_from_file(path.to_str().expect("utf-8 path"), func)
        .unwrap_or_else(|err| panic!("{tag} should extract: {err}"))
}

fn verdict(tag: &str, code: &str) -> VerifyResult {
    verdict_of(tag, code, "f")
}

/// Same bar as [`assert_verified`], for a fixture whose subject is the CALLEE
/// rather than the caller.
#[track_caller]
fn assert_verified_fn(tag: &str, code: &str, func: &str, why: &str) {
    let result = verdict_of(tag, code, func);
    assert!(
        matches!(result, VerifyResult::Verified),
        "{why}\n--- fixture {tag} ({func}) ---\n{code}--- got ---\n{result:?}"
    );
}

#[track_caller]
fn assert_refuted(tag: &str, code: &str, why: &str) {
    let result = verdict(tag, code);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "{why}\n--- fixture {tag} ---\n{code}--- got ---\n{result:?}"
    );
}

#[track_caller]
fn assert_verified(tag: &str, code: &str, why: &str) {
    let result = verdict(tag, code);
    assert!(
        matches!(result, VerifyResult::Verified),
        "{why}\n--- fixture {tag} ---\n{code}--- got ---\n{result:?}"
    );
}

/// `fn f` pinned at a boundary value, one `by(nonlinear_arith)` conclusion that
/// is true ONLY of lossless arithmetic, then `1u32 == 2u32` — which is false in
/// every model of every reading, so it can verify only if the hypotheses are
/// contradictory.
fn nonlinear_then_false(param: &str, pin: &str, nl_goal: &str) -> String {
    format!(
        "fn f({param}) {{\n    trust_vc::assume!({pin});\n    \
         trust_vc::assert_by_nonlinear!({nl_goal});\n    \
         trust_vc::assert!(1u32 == 2u32);\n}}\n"
    )
}

// ---------------------------------------------------------------------------
// Direction 1 — a math-int conclusion must not reach a fixed-width solve
// ---------------------------------------------------------------------------

/// THE REPORTED WITNESS. `y + 1u32 > y` holds of mathematical integers and
/// fails of `u32` at `u32::MAX`; the conclusion must not be re-assumed where
/// the second reading applies.
#[test]
fn a_nonlinear_conclusion_does_not_make_a_later_assert_vacuous() {
    assert_refuted(
        "nl_add_u32",
        &nonlinear_then_false("y: u32", "y == 0xffff_ffffu32", "y + 1u32 > y"),
        "`1u32 == 2u32` is false in every model; it can only verify if a \
         math-int conclusion contradicted the fixed-width hypotheses",
    );
}

/// Subtraction below zero, the mirror of the addition witness.
#[test]
fn a_nonlinear_subtraction_conclusion_does_not_make_a_later_assert_vacuous() {
    assert_refuted(
        "nl_sub_u32",
        &nonlinear_then_false("y: u32", "y == 0u32", "y - 1u32 < y"),
        "`y - 1u32 < y` is a math-int theorem and a `u32` falsehood at zero",
    );
}

/// Multiplication past the top bit.
#[test]
fn a_nonlinear_multiplication_conclusion_does_not_make_a_later_assert_vacuous() {
    assert_refuted(
        "nl_mul_u32",
        &nonlinear_then_false("y: u32", "y == 0x8000_0000u32", "y * 2u32 > y"),
        "`y * 2u32 > y` is a math-int theorem and a `u32` falsehood past the top bit",
    );
}

/// The same reading rule at every width the corpus uses.
#[test]
fn the_reading_rule_holds_at_every_width() {
    for (tag, param, pin, goal) in [
        ("nl_u8", "y: u8", "y == 255u8", "y + 1u8 > y"),
        ("nl_u16", "y: u16", "y == 65535u16", "y + 1u16 > y"),
        ("nl_u32", "y: u32", "y == 0xffff_ffffu32", "y + 1u32 > y"),
        (
            "nl_u64",
            "y: u64",
            "y == 0xffff_ffff_ffff_ffffu64",
            "y + 1u64 > y",
        ),
    ] {
        assert_refuted(
            tag,
            &nonlinear_then_false(param, pin, goal),
            "a math-int conclusion must not contradict the fixed-width hypotheses at any width",
        );
    }
}

/// Signed types, at `iN::MAX`.
#[test]
fn the_reading_rule_holds_for_signed_types() {
    for (tag, param, pin, goal) in [
        ("nl_i8", "y: i8", "y == 127i8", "y + 1i8 > y"),
        ("nl_i32", "y: i32", "y == 2147483647i32", "y + 1i32 > y"),
        (
            "nl_i64",
            "y: i64",
            "y == 9223372036854775807i64",
            "y + 1i64 > y",
        ),
    ] {
        assert_refuted(
            tag,
            &nonlinear_then_false(param, pin, goal),
            "a signed math-int conclusion must not contradict the fixed-width hypotheses",
        );
    }
}

/// The false conclusion as a `postcondition` rather than a body assert — the
/// same leak through the contract channel.
#[test]
fn a_postcondition_after_a_nonlinear_conclusion_is_not_vacuous() {
    assert_refuted(
        "nl_postcondition",
        "#[trust_vc::requires(y == 0xffff_ffffu32)]\n\
         #[trust_vc::ensures(1u32 == 2u32)]\n\
         fn f(y: u32) {\n    trust_vc::assert_by_nonlinear!(y + 1u32 > y);\n}\n",
        "an unsatisfiable postcondition must not be discharged by a math-int conclusion",
    );
}

// ---------------------------------------------------------------------------
// Direction 2 — a fixed-width hypothesis must not reach a math-int solve
// ---------------------------------------------------------------------------

/// A `requires` clause is SPEC code, so `a + b == c` is a statement about
/// INTEGERS on both sides of the call (`crate::spec_arith`). The soundness
/// property is therefore not "the callee may not conclude `c >= b`" — over the
/// integers that conclusion is valid, and Verus draws it too — but that the
/// WRAPPING CALLER can never establish the clause in the first place.
///
/// Pinned end to end, because a one-sided reading is exactly the false-verify
/// shape: the caller that wraps is REFUTED at the call site, an honest caller
/// still gets through, and the callee's own conclusion is measured.
#[test]
fn a_wrapping_caller_cannot_establish_a_spec_arithmetic_precondition() {
    const CALLEE: &str = "#[trust_vc::requires(a + b == c)]\n\
         fn g(a: u32, b: u32, c: u32) {\n    \
         trust_vc::assert_by_nonlinear!(c >= b);\n}\n\n";
    assert_refuted(
        "bv_req_wrapping_caller",
        &format!("{CALLEE}fn f() {{\n    g(1u32, 0xffff_ffffu32, 0u32);\n}}\n"),
        "`a = 1, b = u32::MAX, c = 0` wraps; over the integers it does NOT satisfy \
         `a + b == c`, so the call site must refute",
    );
    assert_verified(
        "bv_req_honest_caller",
        &format!("{CALLEE}fn f() {{\n    g(1u32, 2u32, 3u32);\n}}\n"),
        "a caller whose arguments satisfy the clause over the integers must still \
         get through — the gate is a reading, not an off-switch",
    );
    assert_verified_fn(
        "bv_req_into_nl",
        CALLEE,
        "g",
        "over the integers `a + b == c` with `b >= 0` entails `c >= b`; that is what \
         spec arithmetic MEANS, and Verus proves it too",
    );
    // LIAR TWIN for that conclusion: `c > b` is false of the integers at
    // `b = 0`, and no reading rescues it.
    assert_refuted(
        "bv_req_into_nl_twin",
        "#[trust_vc::requires(a + b == c)]\n\
         fn f(a: u32, b: u32, c: u32) {\n    \
         trust_vc::assert_by_nonlinear!(c > b);\n}\n",
        "`a = b = c = 0` satisfies the clause over the integers and refutes `c > b`",
    );
}

/// A `requires` only a WRAPPING model satisfies is, read as the spec code it
/// is, CONTRADICTORY — and a contradictory hypothesis set must never publish a
/// `Verified`.
///
/// Both halves are pinned, because either alone would be a false-verify
/// generator: the callee answers `VacuousTruth` rather than `Verified`, and no
/// caller — arbitrary or pinned at the boundary value — can discharge the
/// clause.
#[test]
fn a_precondition_no_caller_can_satisfy_never_publishes_a_verified() {
    const CALLEE: &str = "#[trust_vc::requires(z + 1u32 == 0u32)]\n\
         fn g(z: u32) {\n    trust_vc::assert_by_nonlinear!(1u32 == 2u32);\n}\n\n";
    let callee = verdict_of("bv_req_vacuous_nl", CALLEE, "g");
    assert!(
        matches!(
            callee,
            VerifyResult::Unknown {
                category: trust_vc_core::UnknownCategory::VacuousTruth,
                ..
            }
        ),
        "`z + 1u32 == 0u32` is unsatisfiable over the integers for a `u32`; the \
         contradiction must be REPORTED, never published as a proof — got {callee:?}"
    );
    assert_refuted(
        "bv_req_vacuous_arbitrary_caller",
        &format!("{CALLEE}fn f(w: u32) {{\n    g(w);\n}}\n"),
        "no `u32` satisfies `z + 1 == 0` over the integers, so every call must refute",
    );
    assert_refuted(
        "bv_req_vacuous_max_caller",
        &format!("{CALLEE}fn f() {{\n    g(0xffff_ffffu32);\n}}\n"),
        "not even the value that satisfies the WRAPPING reading may discharge it",
    );
}

/// THE CORRECTED CROSS-READING WITNESS, END TO END.
///
/// `encoder::verification::arith_reading` admits a fixed-width fact into the
/// `Int` lane GUARDED by `MIN <= sub <= MAX` for each `+`/`-`/`*` in it. The
/// guard builder emits no bound for a `Neg`, so when a negation DOMINATES
/// every node it does bound — `z == -(x + y)` — the guard can hold while the
/// two readings of the asserted term differ (`2147483648` over `Int`,
/// `i32::MIN` fixed-width, at `x + y == i32::MIN`).
///
/// The bar is the only one that matters: whatever the engine does with such a
/// hypothesis, it may never publish a proof from it.
///
/// MEASURED HERE at this branch HEAD, this fixture is fail-closed and the
/// verdict is a `Counterexample` on the nonlinear assert (a model-less one) —
/// NOT the `Unknown`/`VacuousTruth` that the round-6 review reported for its
/// own probe of the same shape; the review also measured its probe's verdict
/// as byte-identical at the merge base, which is not re-measured here. Both
/// probes agree on the only thing the pin asserts, and on the conclusion:
/// the retry skip in `arith_reading::every_fact_crosses_into` is
/// CONSERVATISM against a guard whose incompleteness is real, not a patch for
/// a live hole.
#[test]
fn a_dominating_negation_hypothesis_is_fail_closed() {
    let result = verdict(
        "dominating_negation_cross_reading",
        "fn f(x: i32, y: i32, z: i32) {\n    trust_vc::assume!(z == -(x + y));\n    \
         trust_vc::assert_by_nonlinear!(1i32 == 2i32);\n}\n",
    );
    assert!(
        !matches!(result, VerifyResult::Verified),
        "a hypothesis whose two readings can disagree inside its own guard must \
         never license a proof of `1 == 2` — got {result:?}"
    );
}

/// THE SAME WITNESS, PINNED TO THE BOUNDARY — the discriminating half, added
/// by the round-7 review.
///
/// The fixture above leaves `x` and `y` free, and the `Guarded` rewrite asserts
/// `range ==> fact`, so a solver can satisfy that hypothesis simply by letting
/// `x + y` leave `i32` range: the incomplete guard never bites, and the
/// `Counterexample` it returns is consistent with the guard being SUFFICIENT
/// and with it being INCOMPLETE alike. It is a non-regression witness, not an
/// exploit attempt.
///
/// This one removes the escape. A comparison against a non-wrapping negative
/// literal is `Identical` and crosses `AsIs`, so the first two facts pin
/// `x + y` to exactly `i32::MIN`; the guard's premise then HOLDS, the `Int`
/// reading of `-(x + y)` is `2147483648`, and the int lane's own type-range
/// invariant for `z` (`i32::MIN <= z <= i32::MAX`) refutes it. That is the
/// contradictory hypothesis set `arith_reading::every_fact_crosses_into`
/// describes, reached WITHOUT a broadcast lemma or a trait-postcondition axiom
/// — so `assertion::vacuity_probe_result`, whose
/// `context_publishes_unverified_axiom` gate excludes a plain `assume!`, is not
/// what stands between this shape and a published proof.
///
/// MEASURED at this branch HEAD: fail-closed, and precisely —
/// `Unknown { category: VacuousTruth }`, "Assumptions are contradictory". The
/// engine reports the contradiction instead of proving from it, which is what
/// entitles the disclosure on `every_fact_crosses_into` to say the guard's
/// incompleteness is real but not currently exploitable. Not re-measured at the
/// merge base, where `arith_reading` does not exist at all.
#[test]
fn a_dominating_negation_pinned_to_the_boundary_is_fail_closed() {
    let result = verdict(
        "dominating_negation_pinned_to_boundary",
        "fn f(x: i32, y: i32, z: i32) {\n    trust_vc::assume!(x == -2147483647i32);\n    \
         trust_vc::assume!(y == -1i32);\n    trust_vc::assume!(z == -(x + y));\n    \
         trust_vc::assert_by_nonlinear!(1i32 == 2i32);\n}\n",
    );
    assert!(
        !matches!(result, VerifyResult::Verified),
        "the guard's premise HOLDS at `x + y == i32::MIN` and the two readings of \
         `-(x + y)` differ there, so this hypothesis set is contradictory — it must \
         never license a proof of `1 == 2`; got {result:?}"
    );
}

/// The body-`assume!` spelling of the same hypothesis.
#[test]
fn a_wrapping_body_assumption_does_not_make_the_nonlinear_lane_vacuous() {
    assert_refuted(
        "bv_assume_vacuous_nl",
        "fn f(z: u32) {\n    trust_vc::assume!(z + 1u32 == 0u32);\n    \
         trust_vc::assert_by_nonlinear!(1u32 == 2u32);\n}\n",
        "an `assume!` is read in the lane that was given it, not re-read over `Int`",
    );
}

// ---------------------------------------------------------------------------
// The two readings must never COMBINE
// ---------------------------------------------------------------------------

/// Both claims are true — each of its OWN lane's reading of `y + 1u32`. That
/// is allowed (it is what `by(bit_vector)` and `by(nonlinear_arith)` mean).
/// What must never happen is the two becoming available to ONE solve, where
/// they are jointly contradictory and prove anything.
#[test]
fn the_two_readings_of_one_subterm_never_combine() {
    let pair = "fn f(y: u32) {\n    trust_vc::assume!(y == 0xffff_ffffu32);\n    \
                trust_vc::assert_by_nonlinear!(y + 1u32 > y);\n    \
                trust_vc::assert_by_bit_vector!(y + 1u32 == 0u32);\n";
    assert_refuted(
        "pair_then_false_default",
        &format!("{pair}    trust_vc::assert!(1u32 == 2u32);\n}}\n"),
        "the math-int and the fixed-width reading of `y + 1u32` must not be jointly available",
    );
    assert_refuted(
        "pair_then_false_bv",
        &format!("{pair}    trust_vc::assert_by_bit_vector!(1u32 == 2u32);\n}}\n"),
        "nor jointly available to the bit-vector lane",
    );
    assert_refuted(
        "pair_then_false_nl",
        &format!("{pair}    trust_vc::assert_by_nonlinear!(1u32 == 2u32);\n}}\n"),
        "nor jointly available to the nonlinear lane",
    );
}

/// The same pair with the falsehood in the contract channel.
#[test]
fn the_two_readings_never_combine_through_a_postcondition() {
    assert_refuted(
        "pair_postcondition",
        "#[trust_vc::requires(y == 0xffff_ffffu32)]\n\
         #[trust_vc::ensures(1u32 == 2u32)]\n\
         fn f(y: u32) {\n    trust_vc::assert_by_nonlinear!(y + 1u32 > y);\n    \
         trust_vc::assert_by_bit_vector!(y + 1u32 == 0u32);\n}\n",
        "the postcondition channel must not see both readings either",
    );
}

// ---------------------------------------------------------------------------
// OVER-REJECTION: neither lane is switched off to buy the above
// ---------------------------------------------------------------------------

/// The nonlinear lane still proves its own claim about a boundary value.
#[test]
fn still_verifies_the_nonlinear_claim_itself() {
    assert_verified(
        "keep_nl_claim",
        "fn f(y: u32) {\n    trust_vc::assume!(y == 0xffff_ffffu32);\n    \
         trust_vc::assert_by_nonlinear!(y + 1u32 > y);\n}\n",
        "`by(nonlinear_arith)` reads `y + 1u32` losslessly; that is the lane's purpose",
    );
}

/// The bit-vector lane still proves the true WRAPPING claim about the same
/// subterm.
#[test]
fn still_verifies_the_wrapping_claim_itself() {
    assert_verified(
        "keep_bv_claim",
        "fn f(y: u32) {\n    trust_vc::assume!(y == 0xffff_ffffu32);\n    \
         trust_vc::assert_by_bit_vector!(y + 1u32 == 0u32);\n}\n",
        "`by(bit_vector)` reads `y + 1u32` as wrapping; that is the lane's purpose",
    );
}

/// A same-reading conclusion still carries forward: a `by(bit_vector)` fact is
/// still available to the fixed-width lane that follows it.
#[test]
fn still_carries_a_same_reading_conclusion_forward() {
    assert_verified(
        "keep_bv_carry",
        "fn f(y: u32) {\n    trust_vc::assert_by_bit_vector!(y & 0u32 == 0u32);\n    \
         trust_vc::assert!(y & 0u32 == 0u32);\n}\n",
        "the gate must fire only when the two lanes READ the fact differently",
    );
}

/// A cross-lane conclusion with NO width-sensitive arithmetic still carries
/// forward — both universes read a bare comparison identically.
#[test]
fn still_carries_an_arithmetic_free_cross_lane_conclusion_forward() {
    assert_verified(
        "keep_cross_no_arith",
        "fn f(y: u32) {\n    trust_vc::assume!(y < 100u32);\n    \
         trust_vc::assert_by_nonlinear!(y < 200u32);\n    \
         trust_vc::assert!(y < 200u32);\n}\n",
        "`y < 200u32` means the same thing in both universes and must still cross",
    );
}

/// An arithmetic-free hypothesis still reaches the nonlinear lane, so the
/// ordinary `assert(a * b <= …) by(nonlinear_arith) requires a < …, b < …`
/// shape keeps working.
#[test]
fn still_admits_arithmetic_free_hypotheses_into_the_nonlinear_lane() {
    assert_verified(
        "keep_nl_bounds",
        "#[trust_vc::requires(a < 100u32)]\n#[trust_vc::requires(b < 100u32)]\n\
         fn f(a: u32, b: u32) {\n    trust_vc::assert_by_nonlinear!(a * b <= 9801u32);\n}\n",
        "bare bounds carry no fixed-width arithmetic and must still reach the nonlinear lane",
    );
}

/// A SPEC-only `int` fact crosses freely: `int` is the same object in both
/// universes, so the gate must not touch it. This is the pin that keeps the
/// gate from degenerating into "no fact ever crosses".
#[test]
fn still_carries_a_spec_int_conclusion_across_lanes() {
    assert_verified(
        "keep_spec_int",
        "fn f(y: u32) {\n    trust_vc::assume!(y < 100u32);\n    \
         trust_vc::assert_by_nonlinear!(y < 100u32);\n    \
         trust_vc::assert!(y < 100u32);\n}\n",
        "a fact with no fixed-width arithmetic in it reads identically in both universes",
    );
}

/// An unpinned boundary is not needed for the gate to hold, and the ordinary
/// program is unaffected: with no contradictory reading available the false
/// assert is refuted exactly as it always was.
#[test]
fn an_ordinary_program_is_unaffected() {
    assert_refuted(
        "control_no_lane",
        "fn f(y: u32) {\n    trust_vc::assume!(y == 0xffff_ffffu32);\n    \
         trust_vc::assert!(1u32 == 2u32);\n}\n",
        "the baseline refutation this whole file is measured against",
    );
}
