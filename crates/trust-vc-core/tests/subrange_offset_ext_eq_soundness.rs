// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Soundness guards for extensional equality over an OFFSET `subrange` of a
//! known-element source (push-chain / `seq!` literal).
//!
//! Regression: a VALID offset-subrange extensional equality such as
//! `seq[1..4] =~= [b, c, d]` was REFUTED with a false counterexample. The
//! `=~=` operator lowers to `len(a) == len(b) && forall i. a.index(i) ==
//! b.index(i)`, and `subrange(src, a, b).index(i)` for a SYMBOLIC `i` is encoded
//! through a fresh shifted-array whose defining axiom the solver does not
//! reliably instantiate at the goal-quantifier's skolem index — leaving the
//! body under-constrained so the solver fabricated a model where a valid
//! equality is refuted.
//!
//! The fix unrolls the quantifier to a finite conjunction of CONCRETE-index
//! element equalities when both operands have a statically-known equal length.
//! At a concrete index the subrange element law resolves directly, so the
//! equality is decided soundly.
//!
//! These tests pin BOTH soundness directions:
//!   * a VALID offset-subrange equality VERIFIES (no false counterexample), and
//!   * a genuinely-DIFFERENT one (wrong value, wrong length, wrong element law)
//!     still REFUTES (no false `Verified`).

use std::fs;
use std::path::Path;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(code: &str, name: &str) -> VerifyResult {
    let dir = Path::new("target/subrange_offset_ext_eq_soundness");
    fs::create_dir_all(dir).unwrap();
    let f = dir.join(format!("{name}.rs"));
    fs::write(&f, code).unwrap();
    verify_function_from_file(f.to_str().unwrap(), name)
        .unwrap_or_else(|e| panic!("{name} should extract+verify: {e}"))
}

fn assert_verified(code: &str, name: &str) {
    let r = verify(code, name);
    assert!(
        matches!(r, VerifyResult::Verified),
        "{name}: a VALID offset-subrange extensional equality must VERIFY \
         (never a false counterexample), got {r:?}"
    );
}

fn assert_refuted(code: &str, name: &str) {
    let r = verify(code, name);
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "{name}: a genuinely-different/false claim must be REFUTED with a \
         counterexample (never a false Verified), got {r:?}"
    );
}

// ---------------------------------------------------------------------------
// Direction (i): VALID offset-subrange equality must VERIFY.
// ---------------------------------------------------------------------------

#[test]
fn offset_subrange_ext_eq_push_inline_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn offset_subrange_ext_eq_push_inline_verifies() {
    trust_vc::assert!(
        Seq::<i32>::empty().push(10i32).push(20i32).push(30i32).push(40i32).push(50i32)
            .subrange(1usize, 4usize)
            =~= Seq::<i32>::empty().push(20i32).push(30i32).push(40i32)
    );
}
"#,
        "offset_subrange_ext_eq_push_inline_verifies",
    );
}

#[test]
fn offset_subrange_ext_eq_let_bound_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn offset_subrange_ext_eq_let_bound_verifies() {
    let s2 = Seq::<i32>::empty().push(10i32).push(20i32).push(30i32).push(40i32).push(50i32);
    let s3 = s2.subrange(1usize, 4usize);
    let s4 = Seq::<i32>::empty().push(20i32).push(30i32).push(40i32);
    trust_vc::assert!(s3 =~= s4);
}
"#,
        "offset_subrange_ext_eq_let_bound_verifies",
    );
}

#[test]
fn offset_subrange_plain_eq_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn offset_subrange_plain_eq_verifies() {
    trust_vc::assert!(
        Seq::<i32>::empty().push(10i32).push(20i32).push(30i32).push(40i32).push(50i32)
            .subrange(1usize, 4usize)
            == Seq::<i32>::empty().push(20i32).push(30i32).push(40i32)
    );
}
"#,
        "offset_subrange_plain_eq_verifies",
    );
}

#[test]
fn offset_subrange_strict_eq_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn offset_subrange_strict_eq_verifies() {
    trust_vc::assert!(
        Seq::<i32>::empty().push(10i32).push(20i32).push(30i32).push(40i32).push(50i32)
            .subrange(1usize, 4usize)
            === Seq::<i32>::empty().push(20i32).push(30i32).push(40i32)
    );
}
"#,
        "offset_subrange_strict_eq_verifies",
    );
}

#[test]
fn offset_subrange_assert_seqs_equal_macro_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn offset_subrange_assert_seqs_equal_macro_verifies() {
    trust_vc::assert_seqs_equal!(
        trust_vc_types::seq![0i32, 10i32, 20i32, 30i32, 40i32].subrange(1usize, 4usize)
            == trust_vc_types::seq![10i32, 20i32, 30i32]
    );
}
"#,
        "offset_subrange_assert_seqs_equal_macro_verifies",
    );
}

/// Direction (i), regression guard for prefix (offset 0) subranges (#2/#6 class):
/// the zero-offset case must keep verifying.
#[test]
fn prefix_subrange_ext_eq_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn prefix_subrange_ext_eq_verifies() {
    trust_vc::assert!(
        Seq::<i32>::empty().push(10i32).push(20i32).push(30i32).push(40i32).push(50i32)
            .subrange(0usize, 3usize)
            =~= Seq::<i32>::empty().push(10i32).push(20i32).push(30i32)
    );
}
"#,
        "prefix_subrange_ext_eq_verifies",
    );
}

/// Offset subrange longer than the standalone subrange's small ground-instance
/// window — exercises element resolution at higher concrete indices.
#[test]
fn long_offset_subrange_ext_eq_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn long_offset_subrange_ext_eq_verifies() {
    trust_vc::assert!(
        Seq::<i32>::empty().push(0i32).push(11i32).push(22i32).push(33i32)
            .push(44i32).push(55i32).push(66i32).push(77i32)
            .subrange(1usize, 8usize)
            =~= Seq::<i32>::empty().push(11i32).push(22i32).push(33i32)
                .push(44i32).push(55i32).push(66i32).push(77i32)
    );
}
"#,
        "long_offset_subrange_ext_eq_verifies",
    );
}

/// The TRUE subrange element law `subrange(s, a, b).index(i) == s.index(a + i)`
/// must hold for an offset view (here `subrange(1,4).index(0) == s.index(1)`).
#[test]
fn offset_subrange_element_law_correct_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn offset_subrange_element_law_correct_verifies() {
    trust_vc::assert!(
        Seq::<i32>::empty().push(10i32).push(20i32).push(30i32).push(40i32).push(50i32)
            .subrange(1usize, 4usize).index(0usize)
            == Seq::<i32>::empty().push(10i32).push(20i32).push(30i32).push(40i32).push(50i32)
                .index(1usize)
    );
}
"#,
        "offset_subrange_element_law_correct_verifies",
    );
}

// ---------------------------------------------------------------------------
// Direction (ii): genuinely-different / false claims must still REFUTE.
// ---------------------------------------------------------------------------

#[test]
fn different_value_offset_subrange_ext_eq_refuted() {
    assert_refuted(
        r#"
#[trust_vc::ensures(true)]
fn different_value_offset_subrange_ext_eq_refuted() {
    trust_vc::assert!(
        Seq::<i32>::empty().push(10i32).push(20i32).push(30i32).push(40i32).push(50i32)
            .subrange(1usize, 4usize)
            =~= Seq::<i32>::empty().push(20i32).push(30i32).push(99i32)
    );
}
"#,
        "different_value_offset_subrange_ext_eq_refuted",
    );
}

#[test]
fn different_length_offset_subrange_ext_eq_refuted() {
    assert_refuted(
        r#"
#[trust_vc::ensures(true)]
fn different_length_offset_subrange_ext_eq_refuted() {
    trust_vc::assert!(
        Seq::<i32>::empty().push(10i32).push(20i32).push(30i32).push(40i32).push(50i32)
            .subrange(1usize, 4usize)
            =~= Seq::<i32>::empty().push(20i32).push(30i32)
    );
}
"#,
        "different_length_offset_subrange_ext_eq_refuted",
    );
}

/// A WRONG element-law claim (`subrange(s,1,4).index(0) == s.index(0)` instead
/// of `s.index(1)`) must NOT verify.
#[test]
fn offset_subrange_element_law_wrong_refuted() {
    assert_refuted(
        r#"
#[trust_vc::ensures(true)]
fn offset_subrange_element_law_wrong_refuted() {
    trust_vc::assert!(
        Seq::<i32>::empty().push(10i32).push(20i32).push(30i32).push(40i32).push(50i32)
            .subrange(1usize, 4usize).index(0usize)
            == Seq::<i32>::empty().push(10i32).push(20i32).push(30i32).push(40i32).push(50i32)
                .index(0usize)
    );
}
"#,
        "offset_subrange_element_law_wrong_refuted",
    );
}
