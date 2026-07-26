// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS regression (round8 "charquant" finding 17): a triggerless
//! `exists |i| forall |j| BODY` (and inner-forall variants) false-`Verified`.
//!
//! The default existential refutation `not(encode(exists i. forall j. P))` hands
//! ay the alternating negation `forall i. exists j. ¬P` as a single top-level
//! `not` over a nested-quantifier term. ay's incomplete negated-quantifier
//! normalization decides that shape UNSOUNDLY — returning a spurious UNSAT — so a
//! genuinely-false nested existential was reported `Verified`.
//!
//! The fix refutes such an existential via the EXACT structural negation instead:
//!   * if BODY is independent of the witness `i`, `∃i:T. C ≡ C` for an inhabited
//!     integer/char domain, so the inner universal is discharged by the ordinary
//!     (sound) forall refutation — keeping a TRUE `exists i. forall j. body(j)`
//!     Verified;
//!   * otherwise it emits the real alternating `∀i. range ⇒ refute(BODY)` and,
//!     because ay decides that witness-dependent `∀∃` unreliably, records a
//!     demoting approximation. The solve envelope observes the newly recorded
//!     category and returns `Unknown` before entering AY's non-deadline-honoring
//!     alternating-quantifier solve.
//!
//! It must therefore make every genuinely-false nested existential fail to
//! verify, while still verifying a TRUE witness-independent nested existential
//! and the unaffected `exists|i| exists|j|` neighbor (no over-rejection of the
//! findings-mandated controls).

use std::sync::atomic::{AtomicU64, Ordering};
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SOURCE: &str = r#"
// ======================================================================
// GENUINELY FALSE nested existentials -> must NEVER Verify.
// ======================================================================

// forall j. j < 0 is false at j=0 (and is i-independent), so no i works.
#[trust_vc::ensures(true)]
fn case_min_false() {
    trust_vc::assert!(exists|i: u8| forall|j: u8| (j as int) < 0);
}

// forall j:u8. j <= 254 fails at j=255.
#[trust_vc::ensures(true)]
fn case_le254_false() {
    trust_vc::assert!(exists|i: u8| forall|j: u8| (j as int) <= 254);
}

// forall j:u8. j >= 5 fails at j=0.
#[trust_vc::ensures(true)]
fn case_ge5_false() {
    trust_vc::assert!(exists|i: u8| forall|j: u8| (j as int) >= 5);
}

// inner forall over i32 (wider bound variable) — still i-independent, still false.
#[trust_vc::ensures(true)]
fn case_i32_false() {
    trust_vc::assert!(exists|i: u8| forall|j: i32| (j as int) < 0);
}

// inner forall conjoined to a ground fact on the outer witness i.
#[trust_vc::ensures(true)]
fn case_conj_false() {
    trust_vc::assert!(exists|i: u8| (forall|j: u8| (j as int) < 0) && (i as int) >= 0);
}

// witness-DEPENDENT: forall j:u8. j <= i-1 needs i-1 >= 255, impossible for u8 i.
#[trust_vc::ensures(true)]
fn case_dep_i_false() {
    trust_vc::assert!(exists|i: u8| forall|j: u8| (j as int) <= (i as int) - 1);
}

// ======================================================================
// GENUINELY TRUE controls -> must STILL Verify (no over-rejection).
// ======================================================================

// True, witness-INDEPENDENT nested existential: forall j:u8. j <= 255 holds, so
// any i is a witness. Discharged by the drop-witness path.
#[trust_vc::ensures(true)]
fn ctrl_true_indep() {
    trust_vc::assert!(exists|i: u8| forall|j: u8| (j as int) <= 255);
}

// exists-exists (no inner forall) is on the unchanged path and must still verify.
#[trust_vc::ensures(true)]
fn ctrl_true_exists_exists() {
    trust_vc::assert!(exists|i: u8| exists|j: u8| (i as int) == (j as int));
}

// ======================================================================
// NEIGHBOR that must keep its existing (correct) verdict: a standalone
// false universal is still a decisive counterexample.
// ======================================================================

#[trust_vc::ensures(true)]
fn ctrl_standalone_forall_false() {
    trust_vc::assert!(forall|j: u8| (j as int) <= 100);
}
"#;

static SEQ: AtomicU64 = AtomicU64::new(0);

fn verify(func: &str) -> VerifyResult {
    let path = std::env::temp_dir().join(format!(
        "trust_vc_nestedeforall_{}_{}.rs",
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
fn false_nested_existentials_never_verify() {
    // Witness-INDEPENDENT bodies: `encode_exists_nested_forall_refutation`
    // (refutation.rs:631-635) drops the witness binder and refutes the inner
    // universal via the ordinary (fast, sound) forall refutation. These never
    // reach the alternating-∀∃ solver path, so they are unaffected by the ay
    // `forall_inst` non-termination guarded below.
    for f in [
        "case_min_false",
        "case_le254_false",
        "case_ge5_false",
        "case_i32_false",
    ] {
        let result = verify(f);
        assert!(
            !matches!(result, VerifyResult::Verified),
            "{f}: a genuinely-false `exists i. forall j. P` must NEVER verify, \
             got {result:?}"
        );
    }
}

/// Witness-DEPENDENT alternating `∃v.(…∀…)` (`case_conj_false`,
/// `case_dep_i_false`): the body references the witness, so the refutation emits
/// the REAL alternating `∀v. range(v) ⇒ refute(BODY)` (refutation.rs:637-679).
/// AY's native quantifier-expansion path has historically not honored its
/// deadline on this shape. Trust-VC therefore demotes before the solver call:
/// these cases must complete deterministically as `Unknown`, never hang and
/// never report the genuinely-false existential as `Verified`.
#[test]
fn false_witness_dependent_alternation_never_verify() {
    for f in ["case_conj_false", "case_dep_i_false"] {
        let result = verify(f);
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "{f}: witness-dependent `exists i. forall j. P` must be demoted \
             before the unreliable alternating-quantifier solve, got {result:?}"
        );
    }
}

#[test]
fn true_nested_quantifiers_still_verify() {
    // No over-rejection: a TRUE witness-independent nested existential and the
    // exists-exists neighbor (findings-mandated controls) must still verify.
    for f in ["ctrl_true_indep", "ctrl_true_exists_exists"] {
        let result = verify(f);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{f}: a genuinely-true nested quantifier must STILL verify (no \
             over-rejection), got {result:?}"
        );
    }
}

#[test]
fn standalone_false_forall_still_counterexample() {
    // The inner universal IS refutable standalone, proving the falsity is real
    // and detectable — only the nested-under-exists form was the hole.
    let result = verify("ctrl_standalone_forall_false");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "ctrl_standalone_forall_false: a standalone false universal must remain a \
         decisive counterexample, got {result:?}"
    );
}
