// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS PIN (no-invariant loop body head): a loop WITHOUT an
//! invariant is `invariant!(true)` — every variable it modifies is arbitrary
//! at every loop head. The loop-body havoc symbols (`__loopbody_N`) model
//! loop-modelable SCALARS only, and a no-invariant body has no encoder
//! inductive step, so a modified DECLARED variable of any other type — an
//! owned or `&mut` struct / tuple parameter, a `Vec`, a `char` — was read at
//! the body head through its bare ENTRY symbol, still pinned by the
//! `requires`. Before the fix eleven of the stale-head reads
//! below were `Verified` (false from the second iteration on), including a
//! loop-body `p.f + 1` overflow check evaluated at the entry value.
//! `havoc_unmodeled_declared_vars_at_loop_body_head` rebinds each such
//! variable to a fresh symbol of its declared type at the head of a
//! no-invariant `loop` / `while` / `while let` / `for` body — the same model
//! the post-loop frame already applies after the loop.
//!
//! Every stale-head liar is a Counterexample; the in-iteration controls (a
//! write then a read, a guard-bounded increment with the post-loop exit fact)
//! still verify; the invariant lane and the range-`for` lane are unchanged.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(func: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_nilbh_{}_{}.rs", std::process::id(), func));
    std::fs::write(&p, SRC).expect("write fixture");
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
struct Pair {
    f: u64,
    g: u64,
}

#[trust_vc::requires(p.f == 1u64)]
fn mut_ref_struct_param_field_body_stale(p: &mut Pair, c: bool) {
    loop {
        trust_vc::assert!(p.f == 1u64);
        p.f = 20u64;
        if c {
            break;
        }
    }
}

#[trust_vc::requires(p.f == 1u64)]
fn mut_ref_struct_param_field_body_write_then_read(p: &mut Pair, c: bool) {
    loop {
        p.f = 20u64;
        trust_vc::assert!(p.f == 20u64);
        if c {
            break;
        }
    }
}

#[trust_vc::requires(p.f == 1u64)]
fn mut_ref_struct_param_field_body_write_then_read_liar(p: &mut Pair, c: bool) {
    loop {
        p.f = 20u64;
        trust_vc::assert!(p.f == 21u64);
        if c {
            break;
        }
    }
}

#[trust_vc::requires(p.f == 1u64)]
fn owned_struct_param_field_body_stale(mut p: Pair, c: bool) {
    loop {
        trust_vc::assert!(p.f == 1u64);
        p.f = 20u64;
        if c {
            break;
        }
    }
}

#[trust_vc::requires(p.f == 1u64)]
fn mut_ref_struct_param_while_body_stale(p: &mut Pair, n: u64) {
    let mut i = 0u64;
    while i < n {
        trust_vc::assert!(p.f == 1u64);
        p.f = 20u64;
        i = i + 1u64;
    }
}

#[trust_vc::requires(v.len() == 0)]
fn mut_vec_param_push_body_stale(v: &mut Vec<u64>, c: bool) {
    loop {
        trust_vc::assert!(v.len() == 0);
        v.push(1u64);
        if c {
            break;
        }
    }
}

#[trust_vc::requires(p.0 == 1u64)]
fn tuple_param_field_body_stale(mut p: (u64, u64), c: bool) {
    loop {
        trust_vc::assert!(p.0 == 1u64);
        p.0 = 20u64;
        if c {
            break;
        }
    }
}

#[trust_vc::requires(p.f == 1u64)]
fn whole_struct_assign_body_stale(mut p: Pair, c: bool) {
    loop {
        trust_vc::assert!(p.f == 1u64);
        p = Pair { f: 20u64, g: 0u64 };
        if c {
            break;
        }
    }
}

#[trust_vc::requires(p.g == 2u64)]
fn unwritten_field_read_is_head_state_liar(p: &mut Pair, c: bool) {
    loop {
        p.f = 20u64;
        trust_vc::assert!(p.g == 2u64);
        p.g = 3u64;
        if c {
            break;
        }
    }
}

#[trust_vc::requires(p.f < 100u64)]
fn body_arith_on_head_field(p: &mut Pair, c: bool) {
    loop {
        let y = p.f + 1u64;
        p.f = 18446744073709551615u64;
        if c {
            break;
        }
    }
}

#[trust_vc::requires(v.len() == 0)]
fn vec_while_let_stale(v: &mut Vec<u64>, o: Option<u64>) {
    while let Some(_k) = o {
        trust_vc::assert!(v.len() == 0);
        v.push(1u64);
    }
}

#[trust_vc::requires(c == 'a')]
fn char_param_body_stale(mut c: char, k: bool) {
    loop {
        trust_vc::assert!(c == 'a');
        c = 'b';
        if k {
            break;
        }
    }
}

#[trust_vc::requires(p.f < 10u64)]
fn while_guard_struct_field_bounded_true(p: &mut Pair) {
    while p.f < 10u64 {
        p.f = p.f + 1u64;
    }
    trust_vc::assert!(p.f >= 10u64);
}

#[trust_vc::requires(p.f < 10u64)]
fn while_guard_struct_field_liar(p: &mut Pair) {
    while p.f < 10u64 {
        p.f = p.f + 1u64;
    }
    trust_vc::assert!(p.f == 3u64);
}

#[trust_vc::requires(p.f == 1u64)]
fn nested_inner_struct_stale(p: &mut Pair, k: bool) {
    loop {
        loop {
            trust_vc::assert!(p.f == 1u64);
            p.f = 20u64;
            if k {
            break;
        }
        }
        break;
    }
}

#[trust_vc::requires(p.f == 1u64)]
fn for_range_struct_stale(p: &mut Pair, n: u64) {
    for _k in 0u64..n {
        trust_vc::assert!(p.f == 1u64);
        p.f = 20u64;
    }
}
"#;

fn assert_verified(func: &str) {
    let r = verify(func);
    assert!(r.is_verified(), "{func} must verify, got: {r:?}");
}

fn assert_counterexample(func: &str) {
    let r = verify(func);
    assert!(
        r.is_counterexample(),
        "{func} must be a Counterexample (never Verified), got: {r:?}"
    );
}

#[test]
fn struct_parameter_head_reads_are_arbitrary() {
    assert_counterexample("mut_ref_struct_param_field_body_stale");
    assert_counterexample("owned_struct_param_field_body_stale");
    assert_counterexample("mut_ref_struct_param_while_body_stale");
    assert_counterexample("whole_struct_assign_body_stale");
    assert_counterexample("unwritten_field_read_is_head_state_liar");
    assert_counterexample("nested_inner_struct_stale");
}

#[test]
fn tuple_collection_and_char_head_reads_are_arbitrary() {
    assert_counterexample("mut_vec_param_push_body_stale");
    assert_counterexample("tuple_param_field_body_stale");
    assert_counterexample("vec_while_let_stale");
    assert_counterexample("char_param_body_stale");
}

#[test]
fn body_arithmetic_is_checked_at_the_arbitrary_head() {
    let r = verify("body_arith_on_head_field");
    let VerifyResult::Counterexample {
        obligation_name, ..
    } = &r
    else {
        panic!("a head-state `p.f + 1` must be refuted as a possible overflow, got: {r:?}");
    };
    assert!(
        obligation_name.contains("overflow"),
        "the refutation must be the overflow check, got: {obligation_name}"
    );
}

#[test]
fn in_iteration_facts_still_verify_both_directions() {
    assert_verified("mut_ref_struct_param_field_body_write_then_read");
    assert_counterexample("mut_ref_struct_param_field_body_write_then_read_liar");
    assert_verified("while_guard_struct_field_bounded_true");
    assert_counterexample("while_guard_struct_field_liar");
}

#[test]
fn range_for_lane_unchanged() {
    assert_counterexample("for_range_struct_stale");
}
