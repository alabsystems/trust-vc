// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS regression (round-4 "quantifiers" finding): a TRIGGERLESS universal
//! whose body is a CONJUNCTION containing an inner EXISTENTIAL plus a ground
//! conjunct false-`Verified`.
//!
//! Refuting `forall|i| (exists|j| phi(i,j)) && psi(i)` in the single-solve path
//! frees the top-level witness `i` and rewrites `refute(P && Q)` into
//! `refute(P) || refute(Q)`. The inner triggerless exists refutes to a REAL
//! quantified disjunct (`not(exists j. j > i)` == `forall j. j <= i`) while the
//! ground conjunct refutes to a free-variable disjunct carrying the
//! counterexample (`i <= 1000`). ay decides the resulting mixed
//! (quantified-disjunct OR ground-disjunct) goal UNSOUNDLY — spurious UNSAT —
//! swallowing the ground counterexample, so the genuinely-false universal was
//! reported `Verified`.
//!
//! The fix verifies each conjunct's universal `forall|i| Cₖ` as a SEPARATE query
//! (the exact distribution `∀x.(A∧B) ⟺ (∀x.A)∧(∀x.B)`), so every sub-query is
//! EITHER a pure quantifier refutation OR a pure ground refutation — never the
//! mixed shape. It must therefore:
//!   * FAIL (never Verify) for every genuinely-false universal of this shape, and
//!   * STILL Verify every genuinely-true universal (no over-rejection), including
//!     a true forall-with-inner-exists, a true forall with a #[trigger], and a
//!     plain true universal.

use std::sync::atomic::{AtomicU64, Ordering};
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SOURCE: &str = r#"
// ======================================================================
// GENUINELY FALSE universals of the bug shape -> must NEVER Verify.
// ======================================================================

// CEX i=0: exists j>0 holds (j=1) but 0 > 1000 is false, so body false.
#[trust_vc::ensures(true)]
fn false_exists_gt_and_gt1000() {
    trust_vc::assert!(forall|i: int| (exists|j: int| j > i) && i > 1000);
}

#[trust_vc::ensures(true)]
fn false_exists_gt_and_gt0() {
    trust_vc::assert!(forall|i: int| (exists|j: int| j > i) && i > 0);
}

// Order-independent: the ground conjunct comes first.
#[trust_vc::ensures(true)]
fn false_order_swapped() {
    trust_vc::assert!(forall|i: int| i > 1000 && (exists|j: int| j > i));
}

// Nested `&& true` in front of the exists must not change the verdict.
#[trust_vc::ensures(true)]
fn false_exists_and_true_and_gt1000() {
    trust_vc::assert!(forall|i: int| ((exists|j: int| j > i) && true) && i > 1000);
}

// Equality inner-exists variant.
#[trust_vc::ensures(true)]
fn false_exists_eq_and_eq5() {
    trust_vc::assert!(forall|i: int| (exists|j: int| j == i) && i == 5);
}

// Body universally false (i==5 && i==7 has no witness, does not const-fold).
#[trust_vc::ensures(true)]
fn false_exists_eq_and_eq5_and_eq7() {
    trust_vc::assert!(forall|i: int| (exists|j: int| j == i) && i == 5 && i == 7);
}

// nat bound variable variant.
#[trust_vc::ensures(true)]
fn false_nat_exists_eq_and_eq5() {
    trust_vc::assert!(forall|i: nat| (exists|j: nat| j == i) && (i as int) == 5);
}

// ======================================================================
// GENUINELY TRUE universals -> must STILL Verify (no over-rejection).
// ======================================================================

// True forall-with-inner-exists: the ground conjunct `i == i` always holds.
#[trust_vc::ensures(true)]
fn true_exists_gt_and_refl() {
    trust_vc::assert!(forall|i: int| (exists|j: int| j > i) && i == i);
}

// True forall-with-inner-exists with a constant-true ground conjunct.
#[trust_vc::ensures(true)]
fn true_exists_gt_and_zerozero() {
    trust_vc::assert!(forall|i: int| (exists|j: int| j > i) && (0 == 0));
}

// Plain true forall with an inner exists (single conjunct — unaffected path).
#[trust_vc::ensures(true)]
fn true_plain_exists() {
    trust_vc::assert!(forall|i: int| exists|j: int| j > i);
}

// True forall whose body conjunction mixes an inner exists with a true ground
// arithmetic fact over the bound var.
#[trust_vc::ensures(true)]
fn true_exists_and_ground_true() {
    trust_vc::assert!(forall|i: int| (exists|j: int| j > i) && i + 1 > i);
}

// True forall carrying an explicit #[trigger] (the triggered path must be
// unchanged — its conjunction body must still verify).
#[trust_vc::ensures(true)]
fn true_triggered_conjunction(s: Seq<int>) {
    trust_vc::assert!(forall|k: int| 0 <= k < s.len() ==> #[trigger] s.index(k) == s.index(k));
}

// ======================================================================
// NEIGHBORS that must keep their existing (correct) verdicts.
// ======================================================================

// Plain false universal with a conjunction body but NO inner quantifier -> CEX.
#[trust_vc::ensures(true)]
fn false_plain_conj() {
    trust_vc::assert!(forall|i: int| i == i && i > 1000);
}

// Implication form (not a conjunction body) -> CEX, unchanged path.
#[trust_vc::ensures(true)]
fn false_implication_form() {
    trust_vc::assert!(forall|i: int| (exists|j: int| j > i) ==> i > 1000);
}

// Inner FORALL (not exists) in the conjunction -> CEX, unchanged.
#[trust_vc::ensures(true)]
fn false_inner_forall_conj() {
    trust_vc::assert!(forall|i: int| (forall|k: int| k == k) && i > 1000);
}
"#;

static SEQ: AtomicU64 = AtomicU64::new(0);

fn verify(func: &str) -> VerifyResult {
    let path = std::env::temp_dir().join(format!(
        "trust_vc_quantconj_{}_{}.rs",
        std::process::id(),
        SEQ.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, SOURCE).expect("write temp source");
    let result = verify_function_from_file(path.to_str().unwrap(), func)
        .unwrap_or_else(|e| panic!("{func} should verify-from-file without error: {e}"));
    let _ = std::fs::remove_file(&path);
    result
}

#[test]
fn false_quantified_conjunction_never_verifies() {
    for f in [
        "false_exists_gt_and_gt1000",
        "false_exists_gt_and_gt0",
        "false_order_swapped",
        "false_exists_and_true_and_gt1000",
        "false_exists_eq_and_eq5",
        "false_exists_eq_and_eq5_and_eq7",
        "false_nat_exists_eq_and_eq5",
        "false_plain_conj",
        "false_implication_form",
        "false_inner_forall_conj",
    ] {
        let result = verify(f);
        assert!(
            !matches!(result, VerifyResult::Verified),
            "{f}: a genuinely-false triggerless universal whose conjunction body \
             carries an inner existential must NEVER verify, got {result:?}"
        );
    }
}

#[test]
fn false_quantified_conjunction_is_a_decisive_counterexample() {
    // Soundness witness: the swallowed ground conjunct is genuinely refuted (a
    // concrete counterexample), not merely demoted to Unknown.
    for f in [
        "false_exists_gt_and_gt1000",
        "false_order_swapped",
        "false_exists_eq_and_eq5",
    ] {
        assert!(
            matches!(verify(f), VerifyResult::Counterexample { .. }),
            "{f}: should expose a decisive counterexample, got {:?}",
            verify(f)
        );
    }
}

#[test]
fn true_quantified_conjunction_still_verifies() {
    // No over-rejection: a genuinely-true universal of the same shape (and the
    // triggered / single-quantifier neighbors) must continue to Verify.
    for f in [
        "true_exists_gt_and_refl",
        "true_exists_gt_and_zerozero",
        "true_plain_exists",
        "true_exists_and_ground_true",
        "true_triggered_conjunction",
    ] {
        assert!(
            matches!(verify(f), VerifyResult::Verified),
            "{f}: a genuinely-true universal must STILL verify (no over-rejection), \
             got {:?}",
            verify(f)
        );
    }
}
