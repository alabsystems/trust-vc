// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Soundness guards for the collections precondition UNSAT-poisoning class
//! (cluster P1-C).
//!
//! A length-DECREASING Seq view — `subrange(start, end)` with `start > end`,
//! `skip(n)` with `n > len`, or `drop_first()`/`drop_last()` on an empty/too-
//! short Seq — has a modeled length that goes NEGATIVE exactly when the op's
//! Verus precondition is violated. When such a view was used as an operand of
//! an extensional Seq equality (`compare_seq.rs`) or of `Seq::add`/`concat`
//! (`seq_transforms.rs`), the operand-length BV companion bridge
//! `bv2int(companion) == negative_len` is UNSAT (because `bv2int >= 0`), which
//! POISONED the whole solver context into a vacuous proof: the violated
//! precondition AND the (false) main goal were both discharged. The hallmark is
//! that BOTH `X == [99]` and `X != [99]` reported `Verified` — an assertion and
//! its negation cannot both hold.
//!
//! The fix routes those operand-length bridges through the
//! precondition-guarded `len_index_companion_maybe_negative` (the same guarded
//! companion already used for the shifted-view RESULT length), so a violated
//! precondition leaves the bridge inert and the precondition guard refutes,
//! while every non-negative (valid) view length delivers the bridge unchanged.
//!
//! These tests pin BOTH soundness directions:
//!   * a precondition-VIOLATING view in an `==`/`!=`/`.add()` operand is NOT
//!     `Verified` (Counterexample / Unknown — never a vacuous pass), and
//!   * a VALID (non-negative-length) Seq op in the same surface still VERIFIES
//!     (no over-rejection), and a positive-length FALSE claim still REFUTES.

use std::fs;
use std::path::Path;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(code: &str, name: &str) -> VerifyResult {
    let dir = Path::new("target/collections_precond_unsat_poison_soundness");
    fs::create_dir_all(dir).unwrap();
    let f = dir.join(format!("{name}.rs"));
    fs::write(&f, code).unwrap();
    verify_function_from_file(f.to_str().unwrap(), name)
        .unwrap_or_else(|e| panic!("{name} should extract+verify: {e}"))
}

/// A genuinely-FALSE goal (or a precondition-violating one) must NEVER be
/// `Verified`. Counterexample / Unknown / Error are all acceptable
/// fail-closed verdicts; only `Verified` is the catastrophic false-positive.
fn assert_not_verified(code: &str, name: &str) {
    let r = verify(code, name);
    assert!(
        !matches!(r, VerifyResult::Verified),
        "{name}: a precondition-violating / false collection goal must NOT be \
         Verified (vacuous UNSAT-poisoned proof), got {r:?}"
    );
}

/// A VALID goal must keep verifying (no over-rejection).
fn assert_verified(code: &str, name: &str) {
    let r = verify(code, name);
    assert!(
        matches!(r, VerifyResult::Verified),
        "{name}: a VALID Seq op must still VERIFY (no over-rejection from the \
         guarded operand-length companion), got {r:?}"
    );
}

// ---------------------------------------------------------------------------
// Direction (i): precondition-VIOLATING views must NOT be Verified.
//
// The smoking gun for each is that BOTH `== [99]` and `!= [99]` were Verified
// before the fix (poisoned context); now neither may be Verified.
// ---------------------------------------------------------------------------

#[test]
fn reversed_subrange_ext_eq_not_verified() {
    assert_not_verified(
        r#"
#[trust_vc::ensures(true)]
fn reversed_subrange_ext_eq_not_verified() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32].subrange(2usize, 1usize)
            == trust_vc_types::seq![99i32]
    );
}
"#,
        "reversed_subrange_ext_eq_not_verified",
    );
}

#[test]
fn reversed_subrange_ext_ne_not_verified() {
    assert_not_verified(
        r#"
#[trust_vc::ensures(true)]
fn reversed_subrange_ext_ne_not_verified() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32].subrange(2usize, 1usize)
            != trust_vc_types::seq![99i32]
    );
}
"#,
        "reversed_subrange_ext_ne_not_verified",
    );
}

#[test]
fn out_of_range_skip_ext_eq_not_verified() {
    assert_not_verified(
        r#"
#[trust_vc::ensures(true)]
fn out_of_range_skip_ext_eq_not_verified() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32].skip(5usize)
            == trust_vc_types::seq![99i32]
    );
}
"#,
        "out_of_range_skip_ext_eq_not_verified",
    );
}

#[test]
fn out_of_range_skip_ext_eq_contradictory_rhs_not_verified() {
    // Same receiver, a DIFFERENT RHS: skip(5) cannot equal both [99] and [42].
    assert_not_verified(
        r#"
#[trust_vc::ensures(true)]
fn out_of_range_skip_ext_eq_contradictory_rhs_not_verified() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32].skip(5usize)
            == trust_vc_types::seq![42i32]
    );
}
"#,
        "out_of_range_skip_ext_eq_contradictory_rhs_not_verified",
    );
}

#[test]
fn empty_drop_first_ext_eq_not_verified() {
    assert_not_verified(
        r#"
#[trust_vc::ensures(true)]
fn empty_drop_first_ext_eq_not_verified() {
    trust_vc::assert!(
        Seq::<i32>::empty().drop_first() == trust_vc_types::seq![99i32]
    );
}
"#,
        "empty_drop_first_ext_eq_not_verified",
    );
}

#[test]
fn empty_drop_first_ext_ne_not_verified() {
    assert_not_verified(
        r#"
#[trust_vc::ensures(true)]
fn empty_drop_first_ext_ne_not_verified() {
    trust_vc::assert!(
        Seq::<i32>::empty().drop_first() != trust_vc_types::seq![99i32]
    );
}
"#,
        "empty_drop_first_ext_ne_not_verified",
    );
}

#[test]
fn empty_drop_last_ext_eq_not_verified() {
    assert_not_verified(
        r#"
#[trust_vc::ensures(true)]
fn empty_drop_last_ext_eq_not_verified() {
    trust_vc::assert!(
        Seq::<i32>::empty().drop_last() == trust_vc_types::seq![99i32]
    );
}
"#,
        "empty_drop_last_ext_eq_not_verified",
    );
}

#[test]
fn reversed_subrange_concat_len_not_verified() {
    // `subrange(2,1).add([5,6]).len() == 999` — the negative operand length
    // re-bridged into concat must not poison the context (any of 999/1/… would
    // "verify" under the old poison).
    assert_not_verified(
        r#"
#[trust_vc::ensures(true)]
fn reversed_subrange_concat_len_not_verified() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32].subrange(2usize, 1usize)
            .add(trust_vc_types::seq![5i32, 6i32]).len() == 999usize
    );
}
"#,
        "reversed_subrange_concat_len_not_verified",
    );
}

#[test]
fn out_of_range_skip_concat_len_not_verified() {
    assert_not_verified(
        r#"
#[trust_vc::ensures(true)]
fn out_of_range_skip_concat_len_not_verified() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32].skip(5usize)
            .add(trust_vc_types::seq![5i32, 6i32]).len() == 999usize
    );
}
"#,
        "out_of_range_skip_concat_len_not_verified",
    );
}

#[test]
fn reversed_subrange_concat_len_one_not_verified() {
    // The modeled concat length here is `-1 + 2 = 1`. Even the "matching"
    // length must NOT verify: the subrange precondition `start <= end` is still
    // violated, so the only sound verdict is a refutation/incompleteness.
    assert_not_verified(
        r#"
#[trust_vc::ensures(true)]
fn reversed_subrange_concat_len_one_not_verified() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32].subrange(2usize, 1usize)
            .add(trust_vc_types::seq![5i32, 6i32]).len() == 1usize
    );
}
"#,
        "reversed_subrange_concat_len_one_not_verified",
    );
}

#[test]
fn reversed_subrange_as_rhs_concat_not_verified() {
    // The negative-length view as the RHS operand of `.add()` must also fail
    // closed (both concat operand bridges are guarded).
    assert_not_verified(
        r#"
#[trust_vc::ensures(true)]
fn reversed_subrange_as_rhs_concat_not_verified() {
    trust_vc::assert!(
        trust_vc_types::seq![5i32, 6i32]
            .add(trust_vc_types::seq![10i32, 20i32, 30i32].subrange(2usize, 1usize))
            .len() == 999usize
    );
}
"#,
        "reversed_subrange_as_rhs_concat_not_verified",
    );
}

// ---------------------------------------------------------------------------
// Direction (ii): VALID ops must still VERIFY (NO over-rejection), and a
// positive-length FALSE claim must still REFUTE (the guard did not blunt the
// non-negative path).
// ---------------------------------------------------------------------------

#[test]
fn valid_subrange_ext_eq_still_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn valid_subrange_ext_eq_still_verifies() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32].subrange(1usize, 3usize)
            == trust_vc_types::seq![20i32, 30i32]
    );
}
"#,
        "valid_subrange_ext_eq_still_verifies",
    );
}

#[test]
fn positive_length_false_subrange_ext_eq_refutes() {
    let r = verify(
        r#"
#[trust_vc::ensures(true)]
fn positive_length_false_subrange_ext_eq_refutes() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32].subrange(1usize, 3usize)
            == trust_vc_types::seq![99i32, 98i32]
    );
}
"#,
        "positive_length_false_subrange_ext_eq_refutes",
    );
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "a positive-length FALSE ext-eq must REFUTE with a counterexample, got {r:?}"
    );
}

#[test]
fn valid_subrange_concat_len_still_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn valid_subrange_concat_len_still_verifies() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32].subrange(0usize, 2usize)
            .add(trust_vc_types::seq![5i32, 6i32]).len() == 4usize
    );
}
"#,
        "valid_subrange_concat_len_still_verifies",
    );
}

#[test]
fn plain_concat_len_still_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn plain_concat_len_still_verifies() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32]
            .add(trust_vc_types::seq![5i32, 6i32]).len() == 5usize
    );
}
"#,
        "plain_concat_len_still_verifies",
    );
}

#[test]
fn positive_length_false_concat_len_refutes() {
    let r = verify(
        r#"
#[trust_vc::ensures(true)]
fn positive_length_false_concat_len_refutes() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32].subrange(0usize, 2usize)
            .add(trust_vc_types::seq![5i32, 6i32]).len() == 999usize
    );
}
"#,
        "positive_length_false_concat_len_refutes",
    );
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "a positive-operand FALSE concat .len() must REFUTE, got {r:?}"
    );
}

// ---------------------------------------------------------------------------
// Push/push_back consumer site. A constructor-backed push result must not add
// an unconditional non-negative-length assertion when its source view has a
// negative modeled length because a source precondition was violated.
// ---------------------------------------------------------------------------

#[test]
fn out_of_range_skip_push_len_not_verified() {
    assert_not_verified(
        r#"
#[trust_vc::ensures(true)]
fn out_of_range_skip_push_len_not_verified() {
    trust_vc::assert!(
        trust_vc_types::seq![1i32, 2i32, 3i32].skip(100usize).push(5i32).len() == 777usize
    );
}
"#,
        "out_of_range_skip_push_len_not_verified",
    );
}

#[test]
fn out_of_range_skip_push_len_zero_not_verified() {
    assert_not_verified(
        r#"
#[trust_vc::ensures(true)]
fn out_of_range_skip_push_len_zero_not_verified() {
    trust_vc::assert!(
        trust_vc_types::seq![1i32, 2i32, 3i32].skip(100usize).push(5i32).len() == 0usize
    );
}
"#,
        "out_of_range_skip_push_len_zero_not_verified",
    );
}

#[test]
fn out_of_range_skip_push_back_len_not_verified() {
    assert_not_verified(
        r#"
#[trust_vc::ensures(true)]
fn out_of_range_skip_push_back_len_not_verified() {
    trust_vc::assert!(
        trust_vc_types::seq![1i32, 2i32, 3i32].skip(100usize).push_back(5i32).len() == 777usize
    );
}
"#,
        "out_of_range_skip_push_back_len_not_verified",
    );
}

#[test]
fn reversed_subrange_push_len_not_verified() {
    assert_not_verified(
        r#"
#[trust_vc::ensures(true)]
fn reversed_subrange_push_len_not_verified() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32].subrange(2usize, 1usize).push(5i32).len() == 777usize
    );
}
"#,
        "reversed_subrange_push_len_not_verified",
    );
}

#[test]
fn empty_drop_first_push_len_not_verified() {
    assert_not_verified(
        r#"
#[trust_vc::ensures(true)]
fn empty_drop_first_push_len_not_verified() {
    trust_vc::assert!(Seq::<i32>::empty().drop_first().push(5i32).len() == 777usize);
}
"#,
        "empty_drop_first_push_len_not_verified",
    );
}

#[test]
fn out_of_range_skip_push_index_not_verified() {
    assert_not_verified(
        r#"
#[trust_vc::ensures(true)]
fn out_of_range_skip_push_index_not_verified() {
    trust_vc::assert!(
        trust_vc_types::seq![1i32, 2i32, 3i32].skip(100usize).push(5i32).index(0usize) == 424242i32
    );
}
"#,
        "out_of_range_skip_push_index_not_verified",
    );
}

#[test]
fn valid_skip_push_len_still_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn valid_skip_push_len_still_verifies() {
    trust_vc::assert!(
        trust_vc_types::seq![1i32, 2i32, 3i32].skip(2usize).push(5i32).len() == 2usize
    );
}
"#,
        "valid_skip_push_len_still_verifies",
    );
}

#[test]
fn valid_skip_to_empty_push_len_still_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn valid_skip_to_empty_push_len_still_verifies() {
    trust_vc::assert!(
        trust_vc_types::seq![1i32, 2i32, 3i32].skip(3usize).push(5i32).len() == 1usize
    );
}
"#,
        "valid_skip_to_empty_push_len_still_verifies",
    );
}

#[test]
fn valid_skip_zero_push_len_still_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn valid_skip_zero_push_len_still_verifies() {
    trust_vc::assert!(
        trust_vc_types::seq![1i32, 2i32, 3i32].skip(0usize).push(5i32).len() == 4usize
    );
}
"#,
        "valid_skip_zero_push_len_still_verifies",
    );
}

#[test]
fn positive_length_false_skip_push_len_refutes() {
    let result = verify(
        r#"
#[trust_vc::ensures(true)]
fn positive_length_false_skip_push_len_refutes() {
    trust_vc::assert!(
        trust_vc_types::seq![1i32, 2i32, 3i32].skip(2usize).push(5i32).len() == 999usize
    );
}
"#,
        "positive_length_false_skip_push_len_refutes",
    );
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "a valid-precondition false skip-then-push length must refute, got {result:?}"
    );
}

#[test]
fn plain_push_len_still_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn plain_push_len_still_verifies() {
    trust_vc::assert!(
        trust_vc_types::seq![1i32, 2i32, 3i32].push(5i32).len() == 4usize
    );
}
"#,
        "plain_push_len_still_verifies",
    );
}
