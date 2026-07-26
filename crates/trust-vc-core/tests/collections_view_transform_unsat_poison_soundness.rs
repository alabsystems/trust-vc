// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Soundness guards for the collections precondition UNSAT-poisoning class
//! (cluster D residual): a length-DECREASING Seq view feeding a downstream
//! TRANSFORM whose result length is read.
//!
//! `collections_precond_unsat_poison_soundness.rs` closed the `==`/`!=`/`.add()`
//! operand bridges. This file closes the residual cross-surface holes where the
//! same NEGATIVE view length (`skip(n>len)` -> `len-n`, `subrange(i>j)` ->
//! `j-i`, `drop_first`/`drop_last` on empty -> `-1`) is re-bridged by a CONSUMER
//! transform:
//!   * `skip(n).map_values(f).len()`              (encode_seq_map_values)
//!   * `skip(n).filter(f).len()`                  (encode_seq_filter)
//!   * `skip(n).reverse().len()`                  (encode_seq_reverse)
//!   * `skip(n).fold_left(init, f)`               (encode_seq_fold_left)
//!   * `subrange(i,j).map_values(f).len()` / `.reverse().len()`
//!   * `drop_first()/drop_last().map_values(f).len()` on EMPTY
//!
//! Each consumer used the UNCONDITIONAL `len_index_companion` on the source
//! length; for a negative length that asserts `bv2int(companion) == -k`, which is
//! UNSAT (`bv2int >= 0`) and POISONED the whole solver context into a vacuous
//! proof — discharging BOTH the violated source precondition AND a false
//! downstream `.len() == 99` goal. The fix routes those source-length bridges
//! through the precondition-guarded `len_index_companion_maybe_negative` (and, in
//! `filter`, also guards the `result_len <= source_len` bound by
//! `source_len >= 0`), so a violated precondition leaves the bridge inert.
//!
//! Hallmark of the poison: BOTH `.len() == 99` AND `.len() == 0` reported
//! `Verified` (an assertion and a contradictory one cannot both hold). After the
//! fix neither may be `Verified`. Valid (non-negative) views still verify.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tag: &str, src: &str) -> VerifyResult {
    let path = std::env::temp_dir().join(format!("trust_vc_view_xform_poison_{tag}.rs"));
    let mut f = std::fs::File::create(&path).expect("create temp source");
    f.write_all(src.as_bytes()).expect("write temp source");
    verify_function_from_file(path.to_str().unwrap(), "test1")
        .unwrap_or_else(|e| panic!("{tag}: extract/verify failed: {e}"))
}

/// A precondition-violating / genuinely-false goal must NEVER be `Verified`.
/// Counterexample / Unknown / Error are all acceptable fail-closed verdicts.
fn assert_not_verified(tag: &str, src: &str) {
    let r = verify(tag, src);
    assert!(
        !matches!(r, VerifyResult::Verified),
        "{tag}: a precondition-violating length-decreasing view feeding a \
         transform must NOT be Verified (vacuous UNSAT-poisoned proof), got {r:?}"
    );
}

/// A VALID goal must keep verifying (no over-rejection from the guarded
/// source-length companion).
fn assert_verified(tag: &str, src: &str) {
    let r = verify(tag, src);
    assert!(
        matches!(r, VerifyResult::Verified),
        "{tag}: a VALID view+transform length goal must still VERIFY (no \
         over-rejection from the guarded companion), got {r:?}"
    );
}

/// A positive-length FALSE goal must REFUTE with a counterexample (proves the
/// transform's length reasoning is still real, not blunted by the guard).
fn assert_counterexample(tag: &str, src: &str) {
    let r = verify(tag, src);
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "{tag}: a positive-length FALSE view+transform goal must REFUTE with a \
         counterexample, got {r:?}"
    );
}

// ---------------------------------------------------------------------------
// Direction (i): precondition-VIOLATING view + transform must NOT be Verified.
// Each false-`== 99` is paired with the contradictory `== 0` (poison hallmark:
// both verified before the fix); neither may be Verified now.
// ---------------------------------------------------------------------------

#[test]
fn skip_over_len_map_values_len_not_verified() {
    assert_not_verified(
        "skip_map_99",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32].skip(5usize)
            .map_values(SpecFn::new(|x: i32| x)).len() == 99usize
    );
}
"#,
    );
}

#[test]
fn skip_over_len_map_values_len_zero_not_verified() {
    // Contradictory companion goal: with the same poisoned prefix this ALSO
    // verified before the fix. The skip precondition (5 <= 3) must refute.
    assert_not_verified(
        "skip_map_0",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32].skip(5usize)
            .map_values(SpecFn::new(|x: i32| x)).len() == 0usize
    );
}
"#,
    );
}

#[test]
fn skip_over_len_filter_len_not_verified() {
    assert_not_verified(
        "skip_filter_99",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        trust_vc_types::seq![1u8, 2u8, 3u8].skip(5usize)
            .filter(SpecFn::new(|x: u8| x > 0u8)).len() == 99usize
    );
}
"#,
    );
}

#[test]
fn skip_over_len_filter_len_zero_not_verified() {
    assert_not_verified(
        "skip_filter_0",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        trust_vc_types::seq![1u8, 2u8, 3u8].skip(5usize)
            .filter(SpecFn::new(|x: u8| x > 0u8)).len() == 0usize
    );
}
"#,
    );
}

#[test]
fn skip_over_len_reverse_len_not_verified() {
    assert_not_verified(
        "skip_reverse_99",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        trust_vc_types::seq![1u8, 2u8, 3u8].skip(5usize).reverse().len() == 99usize
    );
}
"#,
    );
}

#[test]
fn skip_over_len_reverse_len_zero_not_verified() {
    assert_not_verified(
        "skip_reverse_0",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        trust_vc_types::seq![1u8, 2u8, 3u8].skip(5usize).reverse().len() == 0usize
    );
}
"#,
    );
}

#[test]
fn skip_over_len_fold_left_not_verified() {
    assert_not_verified(
        "skip_fold_99",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32].skip(5usize)
            .fold_left(0i32, SpecFn::new(|acc: i32, x: i32| acc)) == 99i32
    );
}
"#,
    );
}

#[test]
fn skip_over_len_fold_left_zero_not_verified() {
    // Closure returns `acc` unchanged so the TRUE value is the init (0); even the
    // "matching" 0 must not verify because the skip precondition is violated.
    assert_not_verified(
        "skip_fold_0",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32].skip(5usize)
            .fold_left(0i32, SpecFn::new(|acc: i32, x: i32| acc)) == 0i32
    );
}
"#,
    );
}

#[test]
fn inverted_subrange_map_values_len_not_verified() {
    assert_not_verified(
        "subrange_map_99",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        trust_vc_types::seq![10u8, 20u8, 30u8, 40u8, 50u8].subrange(4usize, 2usize)
            .map_values(SpecFn::new(|x: u8| x)).len() == 99usize
    );
}
"#,
    );
}

#[test]
fn inverted_subrange_reverse_len_not_verified() {
    assert_not_verified(
        "subrange_reverse_99",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        trust_vc_types::seq![10u8, 20u8, 30u8, 40u8, 50u8].subrange(4usize, 2usize)
            .reverse().len() == 99usize
    );
}
"#,
    );
}

#[test]
fn empty_drop_first_map_values_len_not_verified() {
    assert_not_verified(
        "drop_first_map_99",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        Seq::<u8>::empty().drop_first()
            .map_values(SpecFn::new(|x: u8| x)).len() == 99usize
    );
}
"#,
    );
}

#[test]
fn empty_drop_first_map_values_len_zero_not_verified() {
    assert_not_verified(
        "drop_first_map_0",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        Seq::<u8>::empty().drop_first()
            .map_values(SpecFn::new(|x: u8| x)).len() == 0usize
    );
}
"#,
    );
}

#[test]
fn empty_drop_last_map_values_len_not_verified() {
    assert_not_verified(
        "drop_last_map_99",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        Seq::<u8>::empty().drop_last()
            .map_values(SpecFn::new(|x: u8| x)).len() == 99usize
    );
}
"#,
    );
}

// ---------------------------------------------------------------------------
// Direction (ii): VALID views still VERIFY (NO over-rejection), and a
// positive-length FALSE claim still REFUTES.
// ---------------------------------------------------------------------------

#[test]
fn valid_skip_map_values_len_still_verifies() {
    assert_verified(
        "valid_skip_map_len",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32].skip(1usize)
            .map_values(SpecFn::new(|x: i32| x)).len() == 2usize
    );
}
"#,
    );
}

#[test]
fn valid_subrange_map_values_len_still_verifies() {
    assert_verified(
        "valid_subrange_map_len",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        trust_vc_types::seq![10u8, 20u8, 30u8].subrange(1usize, 3usize)
            .map_values(SpecFn::new(|x: u8| x)).len() == 2usize
    );
}
"#,
    );
}

#[test]
fn valid_skip_reverse_len_still_verifies() {
    assert_verified(
        "valid_skip_reverse_len",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        trust_vc_types::seq![1u8, 2u8, 3u8].skip(1usize).reverse().len() == 2usize
    );
}
"#,
    );
}

#[test]
fn valid_map_values_len_no_view_still_verifies() {
    assert_verified(
        "valid_map_len",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32]
            .map_values(SpecFn::new(|x: i32| x)).len() == 3usize
    );
}
"#,
    );
}

#[test]
fn positive_length_false_map_values_len_refutes() {
    // map_values length reasoning is real on a well-formed (non-negative) source:
    // the false claim must REFUTE, not vacuously pass.
    assert_counterexample(
        "false_map_len_refutes",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32]
            .map_values(SpecFn::new(|x: i32| x)).len() == 99usize
    );
}
"#,
    );
}

#[test]
fn positive_length_false_skip_map_values_len_refutes() {
    // Valid in-bounds skip(1) -> len 2; the false `== 99` must REFUTE.
    assert_counterexample(
        "false_skip_map_len_refutes",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32].skip(1usize)
            .map_values(SpecFn::new(|x: i32| x)).len() == 99usize
    );
}
"#,
    );
}
