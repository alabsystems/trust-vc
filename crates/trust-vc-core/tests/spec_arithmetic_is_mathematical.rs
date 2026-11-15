// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! PIN: a `requires` clause is SPEC code, so its arithmetic is MATHEMATICAL —
//! and it is the same arithmetic on BOTH SIDES OF THE CALL.
//!
//! In Verus, spec-mode `+`, `-`, `*` on a fixed-width `uN`/`iN` are the
//! operations on integers; wrapping is spelled out (`add`/`sub`/`mul`,
//! `wrapping_*`). trust-vc lowered them to fixed-width IR everywhere, so four
//! measured shapes — each a theorem of Verus's spec semantics — REFUTED:
//!
//! ```text
//! #[trust_vc::requires(z + 1u32 > z)]   fn g(z: u32) {…}   g(w)  ← at w = MAX
//! #[trust_vc::requires(z + 1u32 >= 1u32)] …                      ← same model
//! #[trust_vc::requires(m == n - 1u32)]  … assert_by_nonlinear!(n >= 1u32)
//!                                                          ← at m = 0, n = 0
//! #[trust_vc::requires(d == a + b + c)] … assert_by_nonlinear!(d >= a)
//!                                        ← at a = 1, b = 0, c = MAX, d = 0
//! ```
//!
//! The repair is at the IR level (`trust_vc_core::spec_arith`) and it is keyed
//! on the CHANNEL, not the direction: the caller's `__call_requires_*`
//! discharge and the callee's `precondition` assumption are rewritten by the
//! same pass at the same boundary. Repairing only the caller would have
//! completed an end-to-end FALSE VERIFIED — the callee would still derive the
//! fixed-width boundary fact from a clause the caller proved over the integers.
//!
//! EVERY positive pin here carries a liar twin whose claim is false OF THE
//! INTEGERS, so a reading that simply accepted everything would fail this file.
//! The complementary direction — that `assume!`, a body `assert!` and
//! `by(bit_vector)` still read WRAPPING, and that a wrapping caller can never
//! discharge a spec clause — is pinned in `one_reading_per_subterm.rs`.

use std::fs;
use std::path::Path;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verdict(tag: &str, code: &str, func: &str) -> VerifyResult {
    let dir = Path::new("target/spec_arithmetic_is_mathematical");
    fs::create_dir_all(dir).expect("fixture dir");
    let path = dir.join(format!("{tag}.rs"));
    fs::write(&path, code).expect("write fixture");
    verify_function_from_file(path.to_str().expect("utf-8 path"), func)
        .unwrap_or_else(|err| panic!("{tag} should extract: {err}"))
}

#[track_caller]
fn assert_verified(tag: &str, code: &str, func: &str, why: &str) {
    let result = verdict(tag, code, func);
    assert!(
        matches!(result, VerifyResult::Verified),
        "{why}\n--- fixture {tag} ({func}) ---\n{code}--- got ---\n{result:?}"
    );
}

#[track_caller]
fn assert_refuted(tag: &str, code: &str, func: &str, why: &str) {
    let result = verdict(tag, code, func);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "{why}\n--- fixture {tag} ({func}) ---\n{code}--- got ---\n{result:?}"
    );
}

/// A caller of `#[requires(clause)]` with an unconstrained argument.
fn call_site(clause: &str) -> String {
    format!(
        "#[trust_vc::requires({clause})]\nfn g(z: u32) {{\n    \
         trust_vc::assert!(true);\n}}\n\nfn f(w: u32) {{\n    g(w);\n}}\n"
    )
}

// ---------------------------------------------------------------------------
// The four measured shapes
// ---------------------------------------------------------------------------

/// SHAPE 1. `z + 1 > z` is a theorem of the integers, so any argument
/// discharges it. Under the fixed-width reading it failed at `w = u32::MAX`.
#[test]
fn a_successor_precondition_is_dischargeable_by_any_argument() {
    assert_verified(
        "successor_gt",
        &call_site("z + 1u32 > z"),
        "f",
        "`z + 1 > z` holds of every integer; a caller must not have to prove a \
         wrapping falsehood",
    );
}

/// LIAR TWIN: the same shape with a claim that is FALSE of the integers is
/// still refuted, at the call site, so shape 1 is not "accept every clause".
#[test]
fn a_precondition_false_of_the_integers_is_still_refuted() {
    assert_refuted(
        "successor_lt_twin",
        &call_site("z + 1u32 < z"),
        "f",
        "`z + 1 < z` is false of every integer and must refute at the call site",
    );
}

/// SHAPE 2. The same reading through a different comparison.
#[test]
fn a_successor_lower_bound_precondition_is_dischargeable() {
    assert_verified(
        "successor_ge_one",
        &call_site("z + 1u32 >= 1u32"),
        "f",
        "`z + 1 >= 1` holds of every `u32` read as an integer",
    );
}

/// LIAR TWIN for shape 2: `z + 1 >= 2` needs `z >= 1`, which an arbitrary
/// caller does not have.
#[test]
fn a_successor_lower_bound_that_needs_a_hypothesis_is_refuted() {
    assert_refuted(
        "successor_ge_two_twin",
        &call_site("z + 1u32 >= 2u32"),
        "f",
        "`z + 1 >= 2` is false at `z = 0` and must refute",
    );
}

/// SHAPE 3. The CALLEE side: with `m: u32` non-negative, `m == n - 1` entails
/// `n >= 1`. Under the fixed-width reading the clause was satisfied by the
/// wrapping model `m = u32::MAX, n = 0`, so the guard dropped it and the
/// nonlinear goal refuted at `m = 0, n = 0`.
#[test]
fn a_predecessor_precondition_entails_its_lower_bound() {
    assert_verified(
        "predecessor_bound",
        "#[trust_vc::requires(m == n - 1u32)]\nfn f(m: u32, n: u32) {\n    \
         trust_vc::assert_by_nonlinear!(n >= 1u32);\n}\n",
        "f",
        "`m >= 0` and `m == n - 1` over the integers force `n >= 1`",
    );
}

/// LIAR TWIN: one step further is not entailed — `m = 0, n = 1` satisfies the
/// clause over the integers and refutes `n >= 2`.
#[test]
fn a_predecessor_precondition_does_not_entail_more_than_it_says() {
    assert_refuted(
        "predecessor_bound_twin",
        "#[trust_vc::requires(m == n - 1u32)]\nfn f(m: u32, n: u32) {\n    \
         trust_vc::assert_by_nonlinear!(n >= 2u32);\n}\n",
        "f",
        "`m = 0, n = 1` satisfies the clause over the integers and refutes `n >= 2`",
    );
}

/// SHAPE 4. A three-term sum: over the integers `d == a + b + c` with
/// `b, c >= 0` entails `d >= a`. The fixed-width reading refuted it at
/// `a = 1, b = 0, c = u32::MAX, d = 0`.
#[test]
fn a_sum_precondition_entails_each_summand_as_a_lower_bound() {
    assert_verified(
        "sum_bound",
        "#[trust_vc::requires(d == a + b + c)]\nfn f(a: u32, b: u32, c: u32, d: u32) {\n    \
         trust_vc::assert_by_nonlinear!(d >= a);\n}\n",
        "f",
        "over the integers a sum of non-negatives is at least each summand",
    );
}

/// LIAR TWIN: the STRICT bound does not follow — `b = c = 0` is a model of the
/// clause over the integers with `d == a`.
#[test]
fn a_sum_precondition_does_not_entail_a_strict_bound() {
    assert_refuted(
        "sum_bound_twin",
        "#[trust_vc::requires(d == a + b + c)]\nfn f(a: u32, b: u32, c: u32, d: u32) {\n    \
         trust_vc::assert_by_nonlinear!(d > a);\n}\n",
        "f",
        "`b = c = 0` satisfies the clause over the integers and refutes `d > a`",
    );
}

// ---------------------------------------------------------------------------
// The same reading reaches the DEFAULT lane, not only `by(nonlinear_arith)`
// ---------------------------------------------------------------------------

/// The rewrite is on the clause, so the ordinary lane sees it too.
#[test]
fn the_default_lane_reads_the_same_clause_the_same_way() {
    assert_verified(
        "predecessor_bound_default_lane",
        "#[trust_vc::requires(m == n - 1u32)]\nfn f(m: u32, n: u32) {\n    \
         trust_vc::assert!(n >= 1u32);\n}\n",
        "f",
        "one clause, one meaning — the lane does not get to pick a reading",
    );
}

/// LIAR TWIN in the default lane.
#[test]
fn the_default_lane_still_refutes_what_the_clause_does_not_say() {
    assert_refuted(
        "predecessor_bound_default_twin",
        "#[trust_vc::requires(m == n - 1u32)]\nfn f(m: u32, n: u32) {\n    \
         trust_vc::assert!(n >= 2u32);\n}\n",
        "f",
        "`m = 0, n = 1` refutes `n >= 2` in the default lane too",
    );
}

// ---------------------------------------------------------------------------
// A QUANTIFIED clause — the shape that used to die in the encoder
// ---------------------------------------------------------------------------

/// A `requires` whose fixed-width arithmetic sits under a binder reads as
/// mathematical like any other, and reaches a VERDICT.
#[test]
fn a_quantified_precondition_reads_as_mathematical_too() {
    assert_verified(
        "quantified_clause",
        "#[trust_vc::requires(forall|i: u32| a + i >= a)]\nfn f(a: u32) {\n    \
         trust_vc::assert_by_nonlinear!(a >= 0u32);\n}\n",
        "f",
        "a quantified clause must reach a verdict, not an internal encoder error",
    );
}

/// LIAR TWIN: the goal is still decided on its merits.
#[test]
fn a_quantified_precondition_does_not_make_the_nonlinear_lane_vacuous() {
    assert_refuted(
        "quantified_clause_twin",
        "#[trust_vc::requires(forall|i: u32| a + i >= a)]\nfn f(a: u32) {\n    \
         trust_vc::assert_by_nonlinear!(1u32 == 2u32);\n}\n",
        "f",
        "`1u32 == 2u32` is false in every model and must refute under a quantified \
         hypothesis exactly as it does without one",
    );
}

// ---------------------------------------------------------------------------
// MAJOR 2: a quantified FIXED-WIDTH hypothesis reaches a verdict
// ---------------------------------------------------------------------------

/// `assume!` keeps the fixed-width reading (pinned in
/// `one_reading_per_subterm.rs`), so a quantified `assume!` is exactly the fact
/// the int-lane range guard has to handle. Its guard is hoisted to the TOP of
/// the fact, where the binder's `i` does not exist, and the unscoped walker
/// emitted one anyway: the assumption failed to encode and the int-lane branch
/// PROPAGATED that as a hard `VerifyResult::Error`.
///
/// Measured at the unscoped walker with the error propagating:
/// `Error { message: "encode typed assumption: Failed to encode assumption
/// 'assumption_0': encode expression: undefined variable `i` — ensure it is
/// declared as a function parameter, let-binding, or quantifier-bound variable
/// visible in the current specification scope" }` — an internal encoder message
/// blaming the user's source for a legitimate program.
#[test]
fn a_quantified_fixed_width_hypothesis_reaches_a_verdict() {
    assert_verified(
        "quantified_assume",
        "fn f(a: u32) {\n    trust_vc::assume!(forall|i: u32| a + i >= a);\n    \
         trust_vc::assert_by_nonlinear!(a >= 0u32);\n}\n",
        "f",
        "a quantified fixed-width hypothesis must be DROPPED on the way into the \
         other reading, never turned into an encoder error",
    );
}

/// LIAR TWIN, and the reason dropping is the fail-closed answer: the dropped
/// hypothesis must not make the lane vacuous.
#[test]
fn dropping_a_quantified_hypothesis_does_not_make_the_lane_vacuous() {
    assert_refuted(
        "quantified_assume_twin",
        "fn f(a: u32) {\n    trust_vc::assume!(forall|i: u32| a + i >= a);\n    \
         trust_vc::assert_by_nonlinear!(1u32 == 2u32);\n}\n",
        "f",
        "a hypothesis fewer can only make a goal HARDER; `1u32 == 2u32` must still refute",
    );
}

// ---------------------------------------------------------------------------
// A spec NEGATION is mathematical too — and on both sides of the call
// ---------------------------------------------------------------------------
//
// `TrustVcExpr::Neg` carries no `ty` field, so the rewrite that moved `+`/`-`/
// `*` to `MathInt` did not reach through it: the operand was BV-negated
// (wrapping) and only then bridged. `iN::MIN` is the ONE value at which the two
// readings of a negation disagree — `-(i32::MIN)` is `2147483648` over the
// integers and `i32::MIN` in two's complement — so both roles of a clause
// containing `-z` were still reading it the fixed-width way.

/// The CALLER half. `-z >= 0` is true of `z = i32::MIN` over the integers, and
/// Verus reads spec `-z` mathematically, so this program is Verus-valid.
/// Measured REFUTED before this repair.
#[test]
fn a_spec_negation_is_mathematical_at_the_signed_minimum() {
    assert_verified(
        "negation_at_min",
        "#[trust_vc::requires(-z >= 0i32)]\nfn g(z: i32) {\n    trust_vc::assert!(true);\n}\n\n\
         fn f() {\n    g(-2147483648i32);\n}\n",
        "f",
        "`-(i32::MIN)` is `2147483648` over the integers, so `-z >= 0` holds and the \
         caller must be able to discharge it",
    );
}

/// The same shape with a rewritten `+ 0i32` sitting next to the negation. It is
/// the DISCRIMINATOR for "the rewrite does not reach THROUGH a `Neg`": the sum
/// moved to `MathInt` and the program still refuted, which is how the gap was
/// located.
#[test]
fn a_negation_beside_rewritten_arithmetic_is_mathematical_too() {
    assert_verified(
        "negation_beside_sum",
        "#[trust_vc::requires(-z + 0i32 >= 0i32)]\nfn g(z: i32) {\n    trust_vc::assert!(true);\n}\n\n\
         fn f() {\n    g(-2147483648i32);\n}\n",
        "f",
        "moving the `+ 0i32` to the integers is not enough while the negation under it \
         still wraps",
    );
}

/// LIAR TWIN: the clause still says something. `-1 >= 0` is false of the
/// integers and must refute at the call site.
#[test]
fn a_negation_precondition_false_of_the_integers_is_refuted() {
    assert_refuted(
        "negation_at_min_twin",
        "#[trust_vc::requires(-z >= 0i32)]\nfn g(z: i32) {\n    trust_vc::assert!(true);\n}\n\n\
         fn f() {\n    g(1i32);\n}\n",
        "f",
        "`-1 >= 0` is false of the integers and must refute",
    );
}

/// THE CALLEE HALF, and the reason a caller-only repair would have been a FALSE
/// VERIFIED. Under the wrapping reading the clause `-z >= 0` EXCLUDES
/// `z == i32::MIN` (because `-(i32::MIN)` wraps back to `i32::MIN < 0`), so the
/// callee could DERIVE `z != i32::MIN` from it — measured `Verified` at the
/// merge base AND at this branch's previous head. With the caller now
/// discharging the clause for `g(i32::MIN)`, keeping that derivation would have
/// completed an end-to-end false Verified. It must refute.
#[test]
fn a_negation_precondition_does_not_exclude_the_signed_minimum() {
    assert_refuted(
        "negation_excludes_min_twin",
        "#[trust_vc::requires(-z >= 0i32)]\nfn g(z: i32) {\n    \
         trust_vc::assert!(z != -2147483648i32);\n}\n",
        "g",
        "read mathematically the clause admits `z = i32::MIN`, so the callee must not \
         be able to rule it out",
    );
}

/// The callee side of the same clause, positively: what it DOES entail.
#[test]
fn a_negation_precondition_entails_its_own_sign_bound() {
    assert_verified(
        "negation_entails_sign",
        "#[trust_vc::requires(-z < 0i32)]\nfn g(z: i32) {\n    trust_vc::assert!(z > 0i32);\n}\n",
        "g",
        "over the integers `-z < 0` is exactly `z > 0`; the wrapping reading admitted \
         `z = i32::MIN` and refuted it",
    );
}

/// LIAR TWIN for the callee side: `z = 0` satisfies `-z >= 0` over the
/// integers, so the strict bound does not follow.
#[test]
fn a_negation_precondition_does_not_entail_a_strict_bound() {
    assert_refuted(
        "negation_entails_sign_twin",
        "#[trust_vc::requires(-z >= 0i32)]\nfn g(z: i32) {\n    trust_vc::assert!(z < 0i32);\n}\n",
        "g",
        "`z = 0` satisfies the clause over the integers and refutes `z < 0`",
    );
}

/// The narrowest width, where the boundary is easiest to hit by hand.
#[test]
fn a_spec_negation_is_mathematical_at_the_i8_minimum() {
    assert_verified(
        "negation_at_i8_min",
        "#[trust_vc::requires(-z >= 0i8)]\nfn g(z: i8) {\n    trust_vc::assert!(true);\n}\n\n\
         fn f() {\n    g(-128i8);\n}\n",
        "f",
        "`-(i8::MIN)` is `128` over the integers",
    );
}

/// LIAR TWIN at `i8`.
#[test]
fn a_negation_precondition_at_i8_still_refutes_a_positive_argument() {
    assert_refuted(
        "negation_at_i8_twin",
        "#[trust_vc::requires(-z >= 0i8)]\nfn g(z: i8) {\n    trust_vc::assert!(true);\n}\n\n\
         fn f() {\n    g(1i8);\n}\n",
        "f",
        "`-1 >= 0` is false of the integers at `i8` too",
    );
}

/// A clause that is UNSATISFIABLE over the integers but satisfiable in two's
/// complement (`-z == z` holds at `z = i32::MIN`) must never publish a
/// `Verified` — the vacuity vector the mathematical reading opens.
#[test]
fn a_negation_clause_unsatisfiable_over_the_integers_is_never_verified() {
    let result = verdict(
        "negation_vacuous",
        "#[trust_vc::requires(-z == z)]\n#[trust_vc::requires(z != 0i32)]\nfn g(z: i32) {\n    \
         trust_vc::assert!(1i32 == 2i32);\n}\n",
        "g",
    );
    assert!(
        !matches!(result, VerifyResult::Verified),
        "`-z == z && z != 0` has no integer model, so nothing may verify under it; got \
         {result:?}"
    );
}

// ---------------------------------------------------------------------------
// A refuted call precondition keeps its COUNTEREXAMPLE
// ---------------------------------------------------------------------------

/// The return binding is an EXIT-point fact, so a call-site `requires`
/// discharge at a body program point must not see it
/// (`typed_assertions::forward_visible_assumptions`). When it did, and the
/// returned expression was a CALL returning an integer, the solve carried a
/// BV-sorted uninterpreted result next to the clause's `Int` arithmetic and ay
/// answered `unknown (incomplete)`: the user lost the counterexample and got a
/// `NotProved{Incompleteness}` instead. Fail-closed, but a verdict-quality
/// regression — and pre-existing at the merge base for any clause written with
/// an explicit `int`.
#[test]
fn a_refuted_call_precondition_still_refutes_when_the_result_is_returned() {
    assert_refuted(
        "returned_call_refutes",
        "#[trust_vc::requires(z + 1u32 < z)]\nfn h(z: u32) -> u32 {\n    0u32\n}\n\n\
         fn f(w: u32) -> u32 {\n    h(w)\n}\n",
        "f",
        "`z + 1 < z` is false of every integer and must produce a COUNTEREXAMPLE, not \
         an incompleteness, when the call's result is the caller's return value",
    );
}

/// The same through a `let`, which is the other measured spelling.
#[test]
fn a_refuted_call_precondition_still_refutes_through_a_returned_binding() {
    assert_refuted(
        "returned_binding_refutes",
        "#[trust_vc::requires(z + 1u32 < z)]\nfn h(z: u32) -> u32 {\n    0u32\n}\n\n\
         fn f(w: u32) -> u32 {\n    let r = h(w);\n    r\n}\n",
        "f",
        "binding the call's result and returning it must not cost the counterexample \
         either",
    );
}

/// LIAR TWIN: the same shape with a clause that IS dischargeable still
/// verifies, so the repair is not "refute every returned call".
#[test]
fn a_dischargeable_call_precondition_still_verifies_when_the_result_is_returned() {
    assert_verified(
        "returned_call_verifies",
        "#[trust_vc::requires(z + 1u32 > z)]\nfn h(z: u32) -> u32 {\n    0u32\n}\n\n\
         fn f(w: u32) -> u32 {\n    h(w)\n}\n",
        "f",
        "`z + 1 > z` holds of every integer; dropping the exit-point return binding \
         must not cost a true claim",
    );
}

/// And the postcondition — the one obligation that legitimately NAMES `result`
/// — still sees the binding it needs. Without this the repair could have been
/// "delete the return binding", which would make every `ensures(result == …)`
/// unprovable. The `requires` bound keeps the `ensures` channel — which still
/// reads WRAPPING, and is pinned that way in `one_reading_per_subterm.rs` —
/// clear of its own overflow obligation, so what this measures is the binding's
/// visibility and nothing else.
#[test]
fn the_postcondition_still_sees_the_return_binding() {
    assert_verified(
        "postcondition_sees_return",
        "#[trust_vc::requires(x < 100u32)]\n#[trust_vc::ensures(result == x + 1u32)]\n\
         fn f(x: u32) -> u32 {\n    x + 1u32\n}\n",
        "f",
        "an `ensures` is checked at function exit and must still see \
         `result == <return expression>`",
    );
}
