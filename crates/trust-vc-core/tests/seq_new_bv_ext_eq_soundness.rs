// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Soundness guards for extensional equality over a `Seq::new` (`Seq::from_fn`)
//! with FIXED-WIDTH (BV) element types — directly and through a `subrange` view.
//!
//! Regression: a VALID `Seq::new(i32)` extensional equality reached through a
//! `subrange` view — e.g. `s.subrange(1, 4) =~= Seq::new(3, |i| ((i+1) as i32)*10)`
//! — was REFUTED with a false counterexample. `=~=` lowers (for equal concrete
//! lengths) to a finite conjunction of concrete-index element equalities. A
//! direct `Seq::new(i32)` element read `result.index(k)` resolves because the
//! quantified `from_fn` pointwise axiom e-matches the literal select. Through a
//! `subrange`, the element read becomes `shifted[k] == result[bvadd(k, offset)]`
//! (the shifted-array ground instance), and the `from_fn` axiom was not
//! instantiated at that compound `bvadd` source index — leaving the element
//! under-constrained so a valid equality was refuted.
//!
//! The fix extends the `from_fn` GROUND-instance seeding (previously gated to
//! non-BV `int`/`nat`/`real` element sorts) to fixed-width (BV) element sorts:
//! `result[k] == f(k)` is asserted at concrete `k in 0..min(len, window)`, each
//! guarded by `k < len`. The literal seed connects to the shifted view by BV
//! congruence, resolving the subrange element at a concrete index. The seeded
//! value is the EXACT generator value `f(k)`, coerced to the declared element
//! width/sign, so both soundness directions are preserved.
//!
//! These tests pin BOTH soundness directions:
//!   * a VALID `Seq::new(BV)` equality (direct + subranged) VERIFIES, and
//!   * a genuinely-DIFFERENT one (wrong generator value, wrong concrete element,
//!     wrong length) still REFUTES (no false `Verified`).

use std::fs;
use std::path::Path;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(code: &str, name: &str) -> VerifyResult {
    let dir = Path::new("target/seq_new_bv_ext_eq_soundness");
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
        "{name}: a VALID Seq::new(BV) extensional equality must VERIFY \
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
// Direction (i): VALID Seq::new(BV) equality must VERIFY.
// ---------------------------------------------------------------------------

/// Direct `Seq::new(i32)` ext-eq (control: already verified pre-fix via the
/// literal-select e-match; must keep verifying).
#[test]
fn seq_new_i32_ext_eq_direct_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn seq_new_i32_ext_eq_direct_verifies() {
    let s = Seq::<i32>::new(5usize, |i: usize| (i as i32) * 10i32);
    trust_vc::assert!(s =~= Seq::<i32>::new(5usize, |i: usize| (i as i32) * 10i32));
}
"#,
        "seq_new_i32_ext_eq_direct_verifies",
    );
}

/// The core regression: a `subrange` view of a `Seq::new(i32)` against an
/// equivalent `Seq::new(i32)`. Was a false counterexample; must VERIFY.
#[test]
fn seq_new_i32_ext_eq_subrange_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn seq_new_i32_ext_eq_subrange_verifies() {
    let s = Seq::<i32>::new(5usize, |i: usize| (i as i32) * 10i32);
    trust_vc::assert!(
        s.subrange(1usize, 4usize)
            =~= Seq::<i32>::new(3usize, |i: usize| ((i + 1) as i32) * 10i32)
    );
}
"#,
        "seq_new_i32_ext_eq_subrange_verifies",
    );
}

/// A prefix (offset-0) subrange of a `Seq::new(i32)` — must also verify.
#[test]
fn seq_new_i32_ext_eq_prefix_subrange_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn seq_new_i32_ext_eq_prefix_subrange_verifies() {
    let s = Seq::<i32>::new(5usize, |i: usize| (i as i32) * 10i32);
    trust_vc::assert!(
        s.subrange(0usize, 3usize)
            =~= Seq::<i32>::new(3usize, |i: usize| (i as i32) * 10i32)
    );
}
"#,
        "seq_new_i32_ext_eq_prefix_subrange_verifies",
    );
}

/// A concrete-index read of a `Seq::new(i32)` must pin the TRUE generator value.
#[test]
fn seq_new_i32_index_pins_true_value_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn seq_new_i32_index_pins_true_value_verifies() {
    let s = Seq::<i32>::new(5usize, |i: usize| (i as i32) * 10i32);
    trust_vc::assert!(s.index(2usize) == 20i32);
}
"#,
        "seq_new_i32_index_pins_true_value_verifies",
    );
}

/// A concrete-index read THROUGH a subrange must pin the shifted generator value
/// (`subrange(s,1,4).index(1) == f(2) == 20`).
#[test]
fn seq_new_i32_subrange_index_pins_shifted_value_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn seq_new_i32_subrange_index_pins_shifted_value_verifies() {
    let s = Seq::<i32>::new(5usize, |i: usize| (i as i32) * 10i32);
    trust_vc::assert!(s.subrange(1usize, 4usize).index(1usize) == 20i32);
}
"#,
        "seq_new_i32_subrange_index_pins_shifted_value_verifies",
    );
}

/// Unsigned fixed-width (u32) element type — direct ext-eq must verify.
#[test]
fn seq_new_u32_ext_eq_direct_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn seq_new_u32_ext_eq_direct_verifies() {
    let s = Seq::<u32>::new(4usize, |i: usize| (i as u32) * 7u32);
    trust_vc::assert!(s =~= Seq::<u32>::new(4usize, |i: usize| (i as u32) * 7u32));
}
"#,
        "seq_new_u32_ext_eq_direct_verifies",
    );
}

/// Control: the `int` (Sort::Int) element form must keep verifying (no #22
/// regression).
#[test]
fn seq_new_int_ext_eq_direct_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn seq_new_int_ext_eq_direct_verifies() {
    let s = Seq::<int>::new(5usize, |i: usize| (i as int) * 10);
    trust_vc::assert!(s =~= Seq::<int>::new(5usize, |i: usize| (i as int) * 10));
}
"#,
        "seq_new_int_ext_eq_direct_verifies",
    );
}

/// Control: a push-chain offset-subrange ext-eq (the #37 class) must keep
/// verifying — the BV seeding extension must not regress it.
#[test]
fn push_chain_offset_subrange_ext_eq_still_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn push_chain_offset_subrange_ext_eq_still_verifies() {
    trust_vc::assert!(
        Seq::<i32>::empty().push(10i32).push(20i32).push(30i32).push(40i32).push(50i32)
            .subrange(1usize, 4usize)
            =~= Seq::<i32>::empty().push(20i32).push(30i32).push(40i32)
    );
}
"#,
        "push_chain_offset_subrange_ext_eq_still_verifies",
    );
}

// ---------------------------------------------------------------------------
// Direction (ii): genuinely-different / false claims must still REFUTE.
// ---------------------------------------------------------------------------

/// Different generator value (`*10` vs `*11`) — direct. Must REFUTE.
#[test]
fn seq_new_i32_different_generator_direct_refuted() {
    assert_refuted(
        r#"
#[trust_vc::ensures(true)]
fn seq_new_i32_different_generator_direct_refuted() {
    let s = Seq::<i32>::new(5usize, |i: usize| (i as i32) * 10i32);
    trust_vc::assert!(s =~= Seq::<i32>::new(5usize, |i: usize| (i as i32) * 11i32));
}
"#,
        "seq_new_i32_different_generator_direct_refuted",
    );
}

/// Different generator value (`*10` vs `*11`) — through a subrange. Must REFUTE.
#[test]
fn seq_new_i32_different_generator_subrange_refuted() {
    assert_refuted(
        r#"
#[trust_vc::ensures(true)]
fn seq_new_i32_different_generator_subrange_refuted() {
    let s = Seq::<i32>::new(5usize, |i: usize| (i as i32) * 10i32);
    trust_vc::assert!(
        s.subrange(1usize, 4usize)
            =~= Seq::<i32>::new(3usize, |i: usize| ((i + 1) as i32) * 11i32)
    );
}
"#,
        "seq_new_i32_different_generator_subrange_refuted",
    );
}

/// A wrong concrete-element claim (`s.index(2) == 21`, true value 20) must NOT
/// verify.
#[test]
fn seq_new_i32_wrong_concrete_element_refuted() {
    assert_refuted(
        r#"
#[trust_vc::ensures(true)]
fn seq_new_i32_wrong_concrete_element_refuted() {
    let s = Seq::<i32>::new(5usize, |i: usize| (i as i32) * 10i32);
    trust_vc::assert!(s.index(2usize) == 21i32);
}
"#,
        "seq_new_i32_wrong_concrete_element_refuted",
    );
}

/// A wrong concrete-element claim THROUGH a subrange (`subrange(s,1,4).index(1)
/// == 21`, true value 20) must NOT verify.
#[test]
fn seq_new_i32_subrange_wrong_concrete_element_refuted() {
    assert_refuted(
        r#"
#[trust_vc::ensures(true)]
fn seq_new_i32_subrange_wrong_concrete_element_refuted() {
    let s = Seq::<i32>::new(5usize, |i: usize| (i as i32) * 10i32);
    trust_vc::assert!(s.subrange(1usize, 4usize).index(1usize) == 21i32);
}
"#,
        "seq_new_i32_subrange_wrong_concrete_element_refuted",
    );
}

/// A different length must REFUTE (the `len_eq` conjunct is false).
#[test]
fn seq_new_i32_different_length_refuted() {
    assert_refuted(
        r#"
#[trust_vc::ensures(true)]
fn seq_new_i32_different_length_refuted() {
    let s = Seq::<i32>::new(5usize, |i: usize| (i as i32) * 10i32);
    trust_vc::assert!(
        s.subrange(1usize, 4usize)
            =~= Seq::<i32>::new(2usize, |i: usize| ((i + 1) as i32) * 10i32)
    );
}
"#,
        "seq_new_i32_different_length_refuted",
    );
}
