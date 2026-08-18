// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Gate on the `Seq::from_fn` / `Seq::new` quantified pointwise axiom.
//!
//! `encode_seq_from_fn` asserts a pointwise axiom into the CONTEXT:
//!   `forall idx : BV(pointer_width). idx < len ==> result[idx] == f(idx)`
//! plus GROUND instances of the *same* body at concrete `k in 0..seed_count`,
//! each guarded by the *same* `k < len` term.
//!
//! When the length is a literal `n <= seed_count`, the seeds already cover every
//! index the guard admits, so the quantified axiom is entailed by the seeds and
//! carries zero logical content — but it still forces every REFUTATION (a SAT
//! query) to construct a model satisfying a quantifier over the whole
//! `2^pointer_width` index domain. Two bugs came out of that:
//!
//! 1. At 64-bit, `Seq::new` refutations blew past the solver budget and returned
//!    `Unknown{Timeout}` instead of a counterexample.
//! 2. At 32-bit, the assumption context went degenerate and every goal reading
//!    an ELEMENT "verified" — a cardinal false-verify, masked by
//!    `combine_dual_width_results` everywhere the 64-bit arm happened to refute.
//!    (Measured at the pre-fix tree: a wrong concrete element, a different
//!    generator AND a 3-vs-2 length mismatch all returned `Verified` at
//!    `size_of usize == 4`.)
//!
//! `seq_from_fn_seeds_cover_all_indices` now suppresses the redundant axiom.
//! This file pins BOTH sides of that gate:
//!   * the CHEAP DISCRIMINATORS still fire (a length mismatch and a wrong
//!     concrete element refute), *at 32-bit specifically*, where nothing else in
//!     the suite can see them; and
//!   * the axiom is still asserted when the seeds do NOT cover the range (a
//!     literal length past the seed window), so the gate did not silently become
//!     "never emit the axiom".

use std::fs;
use std::path::Path;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(code: &str, name: &str) -> VerifyResult {
    let dir = Path::new("target/seq_from_fn_ground_seed_axiom_gate");
    fs::create_dir_all(dir).unwrap();
    let f = dir.join(format!("{name}.rs"));
    fs::write(&f, code).unwrap();
    verify_function_from_file(f.to_str().unwrap(), name)
        .unwrap_or_else(|e| panic!("{name} should extract+verify: {e}"))
}

fn assert_refuted(code: &str, name: &str) {
    let r = verify(code, name);
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "{name}: a false claim must be REFUTED with a counterexample \
         (never a false Verified, never an Unknown/Timeout), got {r:?}"
    );
}

fn assert_verified(code: &str, name: &str) {
    let r = verify(code, name);
    assert!(
        matches!(r, VerifyResult::Verified),
        "{name}: a TRUE claim must still VERIFY (the ground seeds / the retained \
         quantified axiom must discharge it), got {r:?}"
    );
}

// ---------------------------------------------------------------------------
// The cheap discriminators, pinned AT 32-BIT.
//
// These programs are pointer-width-polymorphic, so the normal entry point runs
// them at both widths and `combine_dual_width_results` surfaces the 64-bit
// counterexample. Pinning `global size_of usize == 4` is what keeps the 32-bit
// arm honest on its own: before the gate, all three of these VERIFIED at 32-bit.
// ---------------------------------------------------------------------------

/// Length mismatch (`subrange(s,1,4)` has length 3, the RHS has length 2). The
/// goal carries the ground conjunct `3 == 2`, so this is refutable without any
/// element reasoning at all — a pure length discriminator.
#[test]
fn seq_new_length_mismatch_refutes_at_32bit() {
    assert_refuted(
        r#"
global size_of usize == 4;
#[trust_vc::ensures(true)]
fn seq_new_length_mismatch_refutes_at_32bit() {
    let s = Seq::<i32>::new(5usize, |i: usize| (i as i32) * 10i32);
    trust_vc::assert!(
        s.subrange(1usize, 4usize)
            =~= Seq::<i32>::new(2usize, |i: usize| ((i + 1) as i32) * 10i32)
    );
}
"#,
        "seq_new_length_mismatch_refutes_at_32bit",
    );
}

/// A ground-false conjunct next to a TRUE one: `s.len() == 5 && 3 == 2`. If the
/// assumption context is consistent this cannot verify, so it is a standing
/// consistency probe on the `Seq::new` context. (Measured: this one already
/// refuted before the gate — the pre-gate 32-bit breakage needed an element
/// SELECT in the goal to surface — so it is a guard, not a discriminator.)
#[test]
fn seq_new_ground_false_conjunct_refutes_at_32bit() {
    assert_refuted(
        r#"
global size_of usize == 4;
#[trust_vc::ensures(true)]
fn seq_new_ground_false_conjunct_refutes_at_32bit() {
    let s = Seq::<i32>::new(5usize, |i: usize| (i as i32) * 10i32);
    trust_vc::assert!(s.len() == 5int && 3int == 2int);
}
"#,
        "seq_new_ground_false_conjunct_refutes_at_32bit",
    );
}

/// A wrong concrete element (`s.index(2)` is 20, not 21) must refute at 32-bit.
#[test]
fn seq_new_wrong_concrete_element_refutes_at_32bit() {
    assert_refuted(
        r#"
global size_of usize == 4;
#[trust_vc::ensures(true)]
fn seq_new_wrong_concrete_element_refutes_at_32bit() {
    let s = Seq::<i32>::new(5usize, |i: usize| (i as i32) * 10i32);
    trust_vc::assert!(s.index(2usize) == 21i32);
}
"#,
        "seq_new_wrong_concrete_element_refutes_at_32bit",
    );
}

/// A different generator (`*10` vs `*11`) must refute at 32-bit.
#[test]
fn seq_new_different_generator_refutes_at_32bit() {
    assert_refuted(
        r#"
global size_of usize == 4;
#[trust_vc::ensures(true)]
fn seq_new_different_generator_refutes_at_32bit() {
    let s = Seq::<i32>::new(5usize, |i: usize| (i as i32) * 10i32);
    trust_vc::assert!(s =~= Seq::<i32>::new(5usize, |i: usize| (i as i32) * 11i32));
}
"#,
        "seq_new_different_generator_refutes_at_32bit",
    );
}

/// Completeness at 32-bit: dropping the (entailed) axiom must not cost a TRUE
/// concrete-index goal — the ground seeds still pin the value.
#[test]
fn seq_new_true_concrete_element_verifies_at_32bit() {
    assert_verified(
        r#"
global size_of usize == 4;
#[trust_vc::ensures(true)]
fn seq_new_true_concrete_element_verifies_at_32bit() {
    let s = Seq::<i32>::new(5usize, |i: usize| (i as i32) * 10i32);
    trust_vc::assert!(s.index(1usize) == 10i32);
}
"#,
        "seq_new_true_concrete_element_verifies_at_32bit",
    );
}

// ---------------------------------------------------------------------------
// NARROWNESS: the axiom is still emitted when the seeds do NOT cover the range.
//
// Both of these read an index OUTSIDE the ground-seed window, so they can only
// discharge through the quantified pointwise axiom. If the gate ever widened to
// "always suppress", these go red.
// ---------------------------------------------------------------------------

/// A LITERAL length past the seed window (`20 > SEQ_FROM_FN_GROUND_SEED_LIMIT`,
/// so the seeds only cover `0..15`) reading index 18 — only the retained
/// quantified axiom can discharge this.
#[test]
fn seq_new_literal_len_past_seed_window_keeps_axiom() {
    assert_verified(
        r#"
global size_of usize == 8;
#[trust_vc::ensures(true)]
fn seq_new_literal_len_past_seed_window_keeps_axiom() {
    let s = Seq::<i32>::new(20usize, |i: usize| (i as i32) * 10i32);
    trust_vc::assert!(s.index(18usize) == 180i32);
}
"#,
        "seq_new_literal_len_past_seed_window_keeps_axiom",
    );
}
