// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Soundness + completeness regression (BOTH directions) for CONCRETE-index
//! reads of a `Seq::map`-ped sequence: `s.map(f).index(k) == f(k, s.index(k))`.
//!
//! # The gap
//!
//! `encode_seq_map` asserts the pointwise axiom
//!   forall i. i < len ==> result[i] == f(i, source[i])
//! which is a TRUE fact, but ay's quantifier instantiation does not reliably
//! e-match it at a CONCRETE-index goal such as `s.map(f).index(2) == 34` — the
//! closure body crosses the BV->Int boundary (`i as int`, `bv2int(source[i])`),
//! so the in-range element was left unconstrained and a valid goal was wrongly
//! refuted (spurious counterexample, model: empty/under-constrained source).
//!
//! # The fix
//!
//! For each concrete index `k` in `0..n`, seed a ground instance of the SAME
//! equation by SUBSTITUTING the quantifier's bound index with the concrete index
//! constant in the already-built body equation (`solver.substitute`), guarded by
//! `k < len` in the Int length domain. Substitution rebuilds + eagerly folds, so
//! `(k as i32)` becomes a literal and `select(store_chain, k)` resolves to the
//! stored element — without re-encoding the closure body (which would otherwise
//! hit a BV-constant interning collision between the `usize` index constant and
//! an equal-valued signed element literal on the 32-bit-pointer arch leg).
//!
//! # Soundness in BOTH directions
//!
//! (i)  a TRUE concrete-index map read VERIFIES (no false counterexample);
//! (ii) a WRONG value claim is a Counterexample (no false Verified);
//! (iii) an out-of-range read is fail-closed (the `Seq::index` `i < len`
//!       precondition refutes — the seed adds nothing past `len`);
//! (iv) no internal encoder Error (the interning collision is avoided).

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tag: &str, src: &str) -> VerifyResult {
    let path = std::env::temp_dir().join(format!("trust_vc_seq_map_idx_{tag}.rs"));
    let mut f = std::fs::File::create(&path).expect("create temp source");
    f.write_all(src.as_bytes()).expect("write temp source");
    verify_function_from_file(path.to_str().unwrap(), "test1")
        .unwrap_or_else(|e| panic!("{tag}: extract/verify failed: {e}"))
}

fn assert_verified(tag: &str, src: &str) {
    match verify(tag, src) {
        VerifyResult::Verified => {}
        other => panic!(
            "{tag}: a TRUE concrete-index map read must VERIFY (never a false \
             counterexample / Unknown / Error), got: {other:?}"
        ),
    }
}

fn assert_counterexample(tag: &str, src: &str) {
    match verify(tag, src) {
        VerifyResult::Counterexample { .. } => {}
        other => panic!(
            "{tag}: a WRONG concrete-index map claim MUST stay a Counterexample \
             (never a false Verified), got: {other:?}"
        ),
    }
}

fn assert_not_verified(tag: &str, src: &str) {
    if verify(tag, src) == VerifyResult::Verified {
        panic!(
            "{tag}: an out-of-range map index read must NOT verify (the \
         Seq::index precondition is unmet) — false Verified is a soundness hole"
        )
    }
}

// =====================================================================
// (i) TRUE concrete-index reads VERIFY — element types, indices, bodies
// =====================================================================

#[test]
fn i32_index0_doubling_verifies() {
    assert_verified(
        "i32_idx0_dbl",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        Seq::<i32>::empty().push(10i32).push(20i32).push(30i32)
            .map(SpecFn::new(|(i, a): (usize, i32)| 2i32 * a)).index(0usize) == 20i32
    );
}
"#,
    );
}

#[test]
fn i32_index2_scout_index_plus_elem_verifies() {
    // The upstream seqs scout body `2*i + a` at index 2: 2*2 + 30 == 34.
    assert_verified(
        "i32_idx2_scout",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        Seq::<i32>::empty().push(10i32).push(20i32).push(30i32)
            .map(SpecFn::new(|(i, a): (usize, i32)| 2i32 * (i as i32) + a)).index(2usize) == 34i32
    );
}
"#,
    );
}

#[test]
fn i32_scout_index1_verifies() {
    // 2*1 + 20 == 22.
    assert_verified(
        "i32_idx1_scout",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        Seq::<i32>::empty().push(10i32).push(20i32).push(30i32)
            .map(SpecFn::new(|(i, a): (usize, i32)| 2i32 * (i as i32) + a)).index(1usize) == 22i32
    );
}
"#,
    );
}

#[test]
fn usize_index1_elem_plus_index_verifies() {
    // usize element: a + i at index 1: 6 + 1 == 7.
    assert_verified(
        "usize_idx1",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        Seq::<usize>::empty().push(5usize).push(6usize).push(7usize)
            .map(SpecFn::new(|(i, a): (usize, usize)| a + i)).index(1usize) == 7usize
    );
}
"#,
    );
}

#[test]
fn int_element_map_of_from_fn_source_verifies() {
    // `int` element source built by Seq::new, then mapped and read at index 1.
    assert_verified(
        "int_from_fn_idx1",
        r#"
use trust_vc_types::{Seq, SpecFn, int};
#[trust_vc::ensures(true)]
fn test1() {
    let s = Seq::<int>::new(3usize, SpecFn::new(|i: usize| i as int));
    trust_vc::assert!(s.map(SpecFn::new(|(i, a): (usize, int)| 2 * a)).index(1usize) == 2);
}
"#,
    );
}

#[test]
fn nontrivial_body_2x_plus_1_verifies() {
    // 2*30 + 1 == 61 at index 2.
    assert_verified(
        "nontrivial_2x_plus_1",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        Seq::<i32>::empty().push(10i32).push(20i32).push(30i32)
            .map(SpecFn::new(|(i, a): (usize, i32)| 2i32 * a + 1i32)).index(2usize) == 61i32
    );
}
"#,
    );
}

#[test]
fn map_length_preserved_symbolic_seq_still_verifies() {
    // Control: the pre-existing length fact must not regress.
    assert_verified(
        "len_preserved",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1(s: Seq<i32>) {
    trust_vc::assert!(s.map(SpecFn::new(|(i, a): (usize, i32)| 2i32 * a)).len() == s.len());
}
"#,
    );
}

// =====================================================================
// (ii) WRONG value claims stay Counterexamples — no false Verified
// =====================================================================

#[test]
fn wrong_value_doubling_is_counterexample() {
    // True value is 60; claiming 99 must refute.
    assert_counterexample(
        "WRONG_i32_idx2",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        Seq::<i32>::empty().push(10i32).push(20i32).push(30i32)
            .map(SpecFn::new(|(i, a): (usize, i32)| 2i32 * a)).index(2usize) == 99i32
    );
}
"#,
    );
}

#[test]
fn wrong_value_scout_off_by_one_is_counterexample() {
    // True value is 34; claiming 35 must refute.
    assert_counterexample(
        "WRONG_scout_idx2",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        Seq::<i32>::empty().push(10i32).push(20i32).push(30i32)
            .map(SpecFn::new(|(i, a): (usize, i32)| 2i32 * (i as i32) + a)).index(2usize) == 35i32
    );
}
"#,
    );
}

#[test]
fn wrong_value_int_from_fn_is_counterexample() {
    // True value is 2; claiming 3 must refute.
    assert_counterexample(
        "WRONG_from_fn_idx1",
        r#"
use trust_vc_types::{Seq, SpecFn, int};
#[trust_vc::ensures(true)]
fn test1() {
    let s = Seq::<int>::new(3usize, SpecFn::new(|i: usize| i as int));
    trust_vc::assert!(s.map(SpecFn::new(|(i, a): (usize, int)| 2 * a)).index(1usize) == 3);
}
"#,
    );
}

// =====================================================================
// (iii) Out-of-range read is fail-closed (precondition refutes)
// =====================================================================

#[test]
fn out_of_range_index_does_not_falsely_verify() {
    // index(5) of a length-3 mapped seq: the `Seq::index` `i < len` precondition
    // is unmet, so the seed adds nothing and the obligation must NOT verify.
    assert_not_verified(
        "OOR_idx5",
        r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        Seq::<i32>::empty().push(10i32).push(20i32).push(30i32)
            .map(SpecFn::new(|(i, a): (usize, i32)| 2i32 * a)).index(5usize) == 0i32
    );
}
"#,
    );
}
