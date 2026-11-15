// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS GUARD — a length PIN must be keyed on the collection whose
//! `len()` the assumption actually reads.
//!
//! An assumption `coll.len() == N` (a `requires`, an `assume!`, a verified
//! loop invariant replayed into a later query) lets the encoder REPLACE the
//! named collection's length term with `N` for every later encoding in the
//! same query (`record_concrete_collection_len_assumption`, and the F3
//! declaration-time pin). The name came from the `len()` node's
//! `receiver_name`, which lowering threads through a whole method chain — the
//! ROOT of `s.push(x).len()` is `s`, and every `vec![..]` / `seq![..]` literal
//! carries its EMPTY constructor's name. Before the fix:
//!
//!   * a loop invariant `v.view().len() == 3` over `let v = vec![3, 4, 6]`
//!     pinned the EMPTY sequence's length to 3, so the invariant's second
//!     encoding in the body query folded to `false` and EVERY obligation of
//!     the loop body verified — `assert!(false)` included. The same held for
//!     `v.len() == 3`, `3 == v.view().len()`, a `u64` element type, a Vec built
//!     by `push`, and a `seq![..]` literal with `s.len() == 3`. Six liars below
//!     were `Verified`;
//!   * a straight-line `assume!(v.view().len() == 3)` stated twice read as
//!     contradictory (`Unknown (VacuousTruth)`) instead of refuting the
//!     following `assert!(false)`.
//!
//! The pin is now taken only when the `len()` receiver IS the named variable
//! (or its identity `view()` for a `Seq`-modelled variable); any other receiver
//! keeps the equality as an asserted term and skips the pin. The controls pin
//! the other direction: the literal-length facts still verify, and a
//! parameter's `requires` pin — the case the pin exists for — still decides
//! both a true and a false claim.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_clpr_{}_{}.rs", std::process::id(), tmp_id));
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
use trust_vc_types::{Seq, View};

// LIAR (was Verified): the invariant is true, the body is reachable.
#[trust_vc::ensures(true)]
fn vec_literal_view_len_invariant_body_false_liar() {
    let v = vec![3u32, 4u32, 6u32];
    let mut pos: usize = 0usize;
    while pos < 3usize {
        trust_vc::invariant!(v.view().len() == 3usize);
        trust_vc::assert!(false);
        pos = pos + 1usize;
    }
}

// LIAR (was Verified): the exec `len()` spelling.
#[trust_vc::ensures(true)]
fn vec_literal_exec_len_invariant_body_false_liar() {
    let v = vec![3u32, 4u32, 6u32];
    let mut pos: usize = 0usize;
    while pos < 3usize {
        trust_vc::invariant!(v.len() == 3usize);
        trust_vc::assert!(false);
        pos = pos + 1usize;
    }
}

// LIAR (was Verified): the literal on the left.
#[trust_vc::ensures(true)]
fn vec_literal_reversed_len_invariant_body_false_liar() {
    let v = vec![3u32, 4u32, 6u32];
    let mut k: u64 = 0u64;
    while k < 3u64 {
        trust_vc::invariant!(3usize == v.view().len());
        trust_vc::assert!(false);
        k = k + 1u64;
    }
}

// LIAR (was Verified): a Vec built by `push`.
#[trust_vc::ensures(true)]
fn pushed_vec_len_invariant_body_false_liar() {
    let mut v: Vec<u32> = Vec::new();
    v.push(3u32);
    let mut pos: usize = 0usize;
    while pos < 3usize {
        trust_vc::invariant!(v.view().len() == 1usize);
        trust_vc::assert!(false);
        pos = pos + 1usize;
    }
}

// LIAR (was Verified): a `seq!` literal.
#[trust_vc::ensures(true)]
fn seq_literal_len_invariant_body_false_liar() {
    let s = trust_vc_types::seq![3u32, 4u32, 6u32];
    let mut pos: usize = 0usize;
    while pos < 3usize {
        trust_vc::invariant!(s.len() == 3nat);
        trust_vc::assert!(false);
        pos = pos + 1usize;
    }
}

// LIAR (was Verified): a claim false at `pos == 2`, not just `false`.
#[trust_vc::ensures(true)]
fn vec_literal_len_invariant_body_position_liar() {
    let v = vec![3u32, 4u32, 6u32];
    let mut pos: usize = 0usize;
    while pos < 3usize {
        trust_vc::invariant!(v.view().len() == 3usize);
        trust_vc::assert!(pos < 2usize);
        pos = pos + 1usize;
    }
}

// LIAR (was Unknown VacuousTruth): consistent assumptions, a false claim.
#[trust_vc::ensures(true)]
fn assume_literal_len_twice_then_false_liar() {
    let v = vec![3u32, 4u32, 6u32];
    trust_vc::assume!(v.view().len() == 3usize);
    trust_vc::assume!(v.view().len() == 3usize);
    trust_vc::assert!(false);
}

// CONTROL: the length fact itself, inside the loop body.
#[trust_vc::ensures(true)]
fn vec_literal_len_invariant_body_true_claim() {
    let v = vec![3u32, 4u32, 6u32];
    let mut pos: usize = 0usize;
    while pos < 3usize {
        trust_vc::invariant!(v.view().len() == 3usize);
        trust_vc::assert!(pos < v.view().len());
        pos = pos + 1usize;
    }
}

// CONTROL: the same assumption twice, the true claim.
#[trust_vc::ensures(true)]
fn assume_literal_len_twice_then_true_claim() {
    let v = vec![3u32, 4u32, 6u32];
    trust_vc::assume!(v.view().len() == 3usize);
    trust_vc::assume!(v.view().len() == 3usize);
    trust_vc::assert!(v.view().len() == 3usize);
}

// CONTROL: a `Seq` parameter's `requires` pin still decides both directions.
#[trust_vc::requires(s.len() == 3usize)]
#[trust_vc::ensures(true)]
fn seq_param_len_pin_true_claim(s: Seq<i32>) {
    trust_vc::assert!(s.len() == 3usize);
}

#[trust_vc::requires(s.len() == 3usize)]
#[trust_vc::ensures(true)]
fn seq_param_len_pin_liar(s: Seq<i32>) {
    trust_vc::assert!(s.len() == 4usize);
}

// CONTROL: the identity `view()` of a `Vec` parameter keeps its pin.
#[trust_vc::requires(v.view().len() == 3usize)]
#[trust_vc::ensures(true)]
fn vec_param_view_len_pin_true_claim(v: Vec<u32>) {
    trust_vc::assert!(v.view().len() == 3usize);
}

#[trust_vc::requires(v.view().len() == 3usize)]
#[trust_vc::ensures(true)]
fn vec_param_view_len_pin_liar(v: Vec<u32>) {
    trust_vc::assert!(v.view().len() == 2usize);
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
fn literal_length_invariant_does_not_make_the_loop_body_vacuous() {
    expect_counterexample("l1", "vec_literal_view_len_invariant_body_false_liar");
    expect_counterexample("l2", "vec_literal_exec_len_invariant_body_false_liar");
    expect_counterexample("l3", "vec_literal_reversed_len_invariant_body_false_liar");
    expect_counterexample("l4", "pushed_vec_len_invariant_body_false_liar");
    expect_counterexample("l5", "seq_literal_len_invariant_body_false_liar");
    expect_counterexample("l6", "vec_literal_len_invariant_body_position_liar");
}

#[test]
fn repeated_literal_length_assumption_is_not_contradictory() {
    expect_counterexample("l7", "assume_literal_len_twice_then_false_liar");
    expect_verified("c1", "assume_literal_len_twice_then_true_claim");
}

#[test]
fn literal_length_invariant_still_proves_its_consequences() {
    expect_verified("c2", "vec_literal_len_invariant_body_true_claim");
}

#[test]
fn a_variable_length_pin_still_decides_both_directions() {
    expect_verified("c3", "seq_param_len_pin_true_claim");
    expect_counterexample("l8", "seq_param_len_pin_liar");
    expect_verified("c4", "vec_param_view_len_pin_true_claim");
    expect_counterexample("l9", "vec_param_view_len_pin_liar");
}
