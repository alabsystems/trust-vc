// SPDX-License-Identifier: Apache-2.0
// Probe: a tuple-struct payload LITERAL refinement (`Just(0)`) must NOT be dropped.
// Non-Option variant names (Just/Nothing) are used on purpose so the generic
// `(m).is_Just()` tester is exercised (no Option<> special-casing).
enum Maybe {
    Just(u64),
    Nothing,
}

// TARGET -- correct verdict is NOT Verified (Counterexample). Faithfully, arm 1
// `Just(0)` matches ONLY m == Just(0); arm 2 `Just(v)` is reached for every
// Just(v) with v != 0, where `assert!(v == 0)` is FALSE. The obligation
// collector's arm_pattern_match_condition lowers `Just(0)` via
// pattern_match_condition_for_scoped_value to the bare variant test `(m).is_Just()`
// (the `0` element is discarded), so arm 1's selection condition widens to
// is_Just, prior_negations becomes `!((m).is_Just())`, arm 2's path condition
// collapses to `(m).is_Just() && !((m).is_Just())` == false, and add_assertion
// guards `v == 0` as `!(false) || (v==0)` == true. A Verified is the breach.
#[trust_vc::ensures(true)]
fn payload_literal_refinement_must_not_drop(m: Maybe) {
    match m {
        Maybe::Just(0) => {}
        Maybe::Just(v) => {
            trust_vc::assert!(v == 0u64);
        }
        Maybe::Nothing => {}
    }
}

// POSITIVE control -- a true arm-assert over the projected payload must verify,
// confirming the match-arm obligation machinery parses/runs (so the target's
// verdict is not a parse artifact).
#[trust_vc::ensures(true)]
fn payload_true_assert_verifies(m: Maybe) {
    match m {
        Maybe::Just(v) => {
            trust_vc::assert!(v == v);
        }
        Maybe::Nothing => {}
    }
}
