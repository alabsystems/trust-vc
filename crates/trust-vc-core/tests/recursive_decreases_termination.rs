// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Soundness battery for the recursive spec-function termination gate.
//!
//! A recursive spec function's defining axiom is trusted only when its
//! `#[decreases]` measure is PROVEN to strictly decrease. A bogus (non-shrinking
//! or ill-founded) measure must fail closed at EVERY integer type — bit-vector
//! AND `int`/`nat` — never letting a false goal verify. A correctly-decreasing
//! measure must still verify its true goals.
//!
//! See `crates/trust-vc-core/src/spec_function_catalog.rs`
//! (`recursion_suppresses_axiom` / `member_edges_decrease`).

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn path() -> String {
    format!(
        "{}/tests/data/recursive_decreases_termination.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verdict(func: &str) -> VerifyResult {
    verify_function_from_file(&path(), func)
        .unwrap_or_else(|err| panic!("extract/verify {func} failed: {err:?}"))
}

/// Bogus / ill-founded decreases measures must NEVER verify. A `Verified` here is
/// the catastrophic soundness failure this gate exists to prevent.
#[test]
fn bogus_decreases_never_proves_false() {
    for func in [
        // self-recursion at every integer type (BV and int/nat)
        "bogus_u64_proves_false",
        "bogus_u64_proves_literal_false",
        "bogus_u32_proves_false",
        "bogus_usize_proves_false",
        "bogus_int_proves_false",
        "bogus_nat_proves_false",
        // mutual recursion
        "mutual_proves_false",
        // constant / unrelated measure
        "const_measure_proves_false",
        // measure grows instead of shrinking
        "grow_proves_false",
        // nat-saturating recursion with no base case
        "nat_no_base_proves_false",
        // missing decreases stays fail-closed (unchanged behavior)
        "missing_proves_false",
    ] {
        let result = verdict(func);
        assert!(
            !matches!(result, VerifyResult::Verified),
            "UNSOUND: {func} verified a false goal via an untrusted recursive axiom \
             (bogus #[decreases] measure). Verdict: {result:?}"
        );
    }
}

/// The catastrophic cases must be DEFINITE fail-closed (Counterexample or Error),
/// not a masking `Unknown`/`VacuousTruth`. This also pins the historical
/// bit-vector-vs-`int` asymmetry shut: every type now reaches the same verdict.
#[test]
fn bogus_decreases_fails_closed_definitely() {
    for func in [
        "bogus_u64_proves_false",
        "bogus_u32_proves_false",
        "bogus_usize_proves_false",
        "bogus_int_proves_false",
        "bogus_nat_proves_false",
        "mutual_proves_false",
        "const_measure_proves_false",
        "nat_no_base_proves_false",
    ] {
        let result = verdict(func);
        assert!(
            matches!(
                result,
                VerifyResult::Counterexample { .. } | VerifyResult::Error { .. }
            ),
            "{func} must fail closed definitely (Counterexample/Error), got {result:?}"
        );
    }
}

/// Correctly-decreasing recursive spec functions must still verify true goals:
/// scalar `n - 1`, lexicographic (Ackermann), `Seq` length, and decreasing mutual
/// recursion. Over-suppressing these would defeat recursion entirely.
#[test]
fn correct_decreases_still_verifies() {
    for func in [
        "good_true_goal",
        "ack_true_goal",
        "seq_len_true_goal",
        "mutual_decreasing_true_goal",
    ] {
        let result = verdict(func);
        assert!(
            matches!(result, VerifyResult::Verified),
            "correctly-decreasing recursion {func} must verify its true goal, got {result:?}"
        );
    }
}

/// The defining axiom for a correctly-decreasing function must be FAITHFUL, not
/// vacuous: a false goal about it must still be a Counterexample.
#[test]
fn correct_decreases_axiom_is_faithful_not_vacuous() {
    let result = verdict("mutual_decreasing_false_goal");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "count_down_b(0) == 1 is false and must be a Counterexample (faithful axiom), got {result:?}"
    );
}
