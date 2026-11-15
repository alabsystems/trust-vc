// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN (mut_refs_libs `test_vec_index_assign::test_fields`,
//! 2026-09-12): `v[i].k = x` on a `let mut v = vec![(..), (..)];` local. The
//! handler already rewrote the assignment to a `Seq` update of the element
//! with field `k` replaced, but it took the element's tuple shape only from a
//! DECLARED variable type — a `vec![..]` literal local has none and failed
//! closed. The shape is now read from the scoped literal itself when every
//! element is a tuple of one arity. The liars pin that the other fields and
//! the other elements keep their values and that a false tail is refuted.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_vltf_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
    let _ = std::fs::remove_file(&p);
    result
}

const SRC: &str = r#"
// CONTROL: the written field changes, the sibling field and the other
// elements do not.
#[trust_vc::ensures(true)]
fn tuple_field_write_verifies() {
    let mut v = vec![(1u64, 11u64), (2u64, 12u64), (3u64, 13u64)];
    v[1].0 = 5u64;
    trust_vc::assert!(v[1].0 == 5u64);
    trust_vc::assert!(v[1].1 == 12u64);
    trust_vc::assert!(v[0].0 == 1u64);
    trust_vc::assert!(v[2].1 == 13u64);
}

// LIAR: the sibling field is NOT the written value.
#[trust_vc::ensures(true)]
fn sibling_field_is_not_written_liar() {
    let mut v = vec![(1u64, 11u64), (2u64, 12u64), (3u64, 13u64)];
    v[1].0 = 5u64;
    trust_vc::assert!(v[1].1 == 5u64);
}

// LIAR: the other element is NOT written.
#[trust_vc::ensures(true)]
fn other_element_is_not_written_liar() {
    let mut v = vec![(1u64, 11u64), (2u64, 12u64), (3u64, 13u64)];
    v[1].0 = 5u64;
    trust_vc::assert!(v[2].0 == 5u64);
}

// LIAR (the corpus shape): a reachable false tail after the write.
#[trust_vc::ensures(true)]
fn false_tail_after_write_liar() {
    let mut v = vec![(1u64, 11u64), (2u64, 12u64), (3u64, 13u64)];
    v[1].0 = 5u64;
    trust_vc::assert!(v[1].0 == 5u64);
    trust_vc::assert!(v[2].1 == 13u64);
    trust_vc::assert!(false);
}

// CONTROL: the second field of a 3-tuple, two writes in a row.
#[trust_vc::ensures(true)]
fn three_tuple_two_writes_verify() {
    let mut v = vec![(1u64, 2u64, 3u64), (4u64, 5u64, 6u64)];
    v[0].1 = 20u64;
    v[1].2 = 60u64;
    trust_vc::assert!(v[0].0 == 1u64);
    trust_vc::assert!(v[0].1 == 20u64);
    trust_vc::assert!(v[0].2 == 3u64);
    trust_vc::assert!(v[1].2 == 60u64);
    trust_vc::assert!(v[1].1 == 5u64);
}

// LIAR (BOUNDS): writing a field of an out-of-range element of a 3-element
// literal must not verify.
#[trust_vc::ensures(true)]
fn out_of_bounds_literal_write_liar() {
    let mut v = vec![(1u64, 11u64), (2u64, 12u64), (3u64, 13u64)];
    v[3].0 = 5u64;
    trust_vc::assert!(v[0].0 == 1u64);
}

// LIAR (BOUNDS): a symbolic index with no bound is an unproven bounds
// obligation — never Verified.
#[trust_vc::ensures(true)]
fn symbolic_index_without_bound_liar(i: usize) {
    let mut v = vec![(1u64, 11u64), (2u64, 12u64), (3u64, 13u64)];
    v[i].0 = 5u64;
    trust_vc::assert!(v[i].0 == 5u64);
}

// CONTROL: … and with the bound in the precondition it verifies.
#[trust_vc::requires(i < 3usize)]
#[trust_vc::ensures(true)]
fn symbolic_index_with_bound_verifies(i: usize) {
    let mut v = vec![(1u64, 11u64), (2u64, 12u64), (3u64, 13u64)];
    v[i].0 = 5u64;
    trust_vc::assert!(v[i].0 == 5u64);
}

// CONTROL (tuple STRUCT elements, declared type, push-built): the element is
// rebuilt through its own constructor.
struct Pair(u64, u64);

#[trust_vc::ensures(true)]
fn tuple_struct_push_built_write_verifies() {
    let mut v: Vec<Pair> = Vec::new();
    v.push(Pair(1u64, 11u64));
    v.push(Pair(2u64, 12u64));
    v[1usize].0 = 5u64;
    trust_vc::assert!(v[1usize].0 == 5u64);
    trust_vc::assert!(v[1usize].1 == 12u64);
    trust_vc::assert!(v[0usize].0 == 1u64);
}

// LIAR (the corpus shape): a false tail after a tuple-struct field write.
#[trust_vc::ensures(true)]
fn tuple_struct_push_built_false_tail_liar() {
    let mut v: Vec<Pair> = Vec::new();
    v.push(Pair(1u64, 11u64));
    v.push(Pair(2u64, 12u64));
    v[1usize].0 = 5u64;
    trust_vc::assert!(false);
}

// CONTROL (plain tuples, push-built): the shape comes from the pushed values.
// (An UNTYPED `Vec::new()` root cannot even be read — its element type is not
// inferred by the lowering — so the root carries the element type.)
#[trust_vc::ensures(true)]
fn plain_tuple_push_built_write_verifies() {
    let mut v: Vec<(u64, u64)> = Vec::new();
    v.push((1u64, 11u64));
    v.push((2u64, 12u64));
    v[1usize].1 = 7u64;
    trust_vc::assert!(v[1usize].1 == 7u64);
    trust_vc::assert!(v[1usize].0 == 2u64);
}

// CONTROL: a DECLARED element type still takes the declared-type path.
#[trust_vc::ensures(true)]
fn declared_type_path_still_verifies() {
    let mut v: Vec<(u64, u64)> = vec![(1u64, 11u64), (2u64, 12u64)];
    v[0].1 = 7u64;
    trust_vc::assert!(v[0].1 == 7u64);
    trust_vc::assert!(v[0].0 == 1u64);
}
"#;

fn expect_verified(id: &str, func: &str) {
    match verify(id, func, SRC) {
        VerifyResult::Verified => {}
        other => panic!("{func}: expected Verified, got {other:?}"),
    }
}

fn expect_counterexample(id: &str, func: &str) {
    match verify(id, func, SRC) {
        VerifyResult::Counterexample { .. } => {}
        other => panic!("{func}: expected Counterexample, got {other:?}"),
    }
}

#[test]
fn control_tuple_field_write_verifies() {
    expect_verified("c1", "tuple_field_write_verifies");
}

#[test]
fn liar_sibling_field_is_not_written() {
    expect_counterexample("l1", "sibling_field_is_not_written_liar");
}

#[test]
fn liar_other_element_is_not_written() {
    expect_counterexample("l2", "other_element_is_not_written_liar");
}

#[test]
fn liar_false_tail_after_write_is_refuted() {
    expect_counterexample("l3", "false_tail_after_write_liar");
}

#[test]
fn control_three_tuple_two_writes_verify() {
    expect_verified("c2", "three_tuple_two_writes_verify");
}

fn expect_not_verified(id: &str, func: &str) {
    match verify(id, func, SRC) {
        VerifyResult::Verified => panic!("{func}: must NOT verify"),
        VerifyResult::Unknown { reason, .. } => {
            panic!("{func}: solver Unknown is not stable evidence: {reason}")
        }
        _ => {}
    }
}

#[test]
fn liar_out_of_bounds_literal_write_is_rejected() {
    expect_not_verified("b1", "out_of_bounds_literal_write_liar");
}

#[test]
fn liar_symbolic_index_without_bound_is_rejected() {
    expect_not_verified("b2", "symbolic_index_without_bound_liar");
}

#[test]
fn control_symbolic_index_with_bound_verifies() {
    expect_verified("b3", "symbolic_index_with_bound_verifies");
}

#[test]
fn control_tuple_struct_push_built_write_verifies() {
    expect_verified("s1", "tuple_struct_push_built_write_verifies");
}

#[test]
fn liar_tuple_struct_push_built_false_tail_is_refuted() {
    expect_counterexample("s2", "tuple_struct_push_built_false_tail_liar");
}

#[test]
fn control_plain_tuple_push_built_write_verifies() {
    expect_verified("s3", "plain_tuple_push_built_write_verifies");
}

#[test]
fn control_declared_type_path_still_verifies() {
    expect_verified("c3", "declared_type_path_still_verifies");
}
