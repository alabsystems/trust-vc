// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! An array / slice / `Vec` index inside a loop body carries its bounds
//! obligation (every out-of-bounds shape below used to be VERIFIED).
//!
//! The index-bounds pin was DEFERRED — i.e. dropped — for every access inside
//! any loop body, a leftover from before the loop encoding routed the guard
//! and invariant into body-site obligations. The arithmetic path has since
//! been routed; the index path now renders the access over the loop-body havoc
//! symbols and weakens the goal by the guard + invariant the same way, so a
//! bound the guard establishes still verifies.
//!
//! Every positive has a liar refuted in the same file context.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_lbib_{}_{}.rs", std::process::id(), id));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}

const SRC: &str = r#"
#[trust_vc::ensures(true)]
fn while_write_literal_oob(mut a: [u8; 2]) { let mut i = 0usize; while i < 5usize { trust_vc::invariant!(i <= 5usize); a[5] = 0u8; i = i + 1usize; } }
#[trust_vc::ensures(true)]
fn while_read_literal_oob(a: [u8; 2]) { let mut i = 0usize; let mut x = 0u8; while i < 5usize { trust_vc::invariant!(i <= 5usize); x = a[5]; i = i + 1usize; } }
#[trust_vc::requires(v.len() == 0)]
fn while_read_empty_vec(v: Vec<u8>) { let mut i = 0usize; let mut x = 0u8; while i < 3usize { trust_vc::invariant!(i <= 3usize); x = v[0]; i = i + 1usize; } }
#[trust_vc::ensures(true)]
fn for_write_literal_oob(mut a: [u8; 2]) { for i in 0usize..5usize { a[7] = 0u8; } }
#[trust_vc::ensures(true)]
fn while_let_read_const_index_oob(a: [u8; 2]) { let mut i = 0usize; let k = 2usize; while i < 3usize { trust_vc::invariant!(i <= 3usize); let y = a[k]; i = i + 1usize; } }

#[trust_vc::ensures(true)]
fn while_read_counter_oob(a: [u8; 2]) { let mut i = 0usize; let mut x = 0u8; while i < 5usize { trust_vc::invariant!(i <= 5usize); x = a[i]; i = i + 1usize; } }
#[trust_vc::ensures(true)]
fn while_read_unconstrained_vec(v: Vec<u8>) { let mut i = 0usize; let mut x = 0u8; while i < 10usize { trust_vc::invariant!(i <= 10usize); x = v[i]; i = i + 1usize; } }
#[trust_vc::ensures(true)]
fn for_write_counter_oob(mut a: [u8; 2]) { for i in 0usize..5usize { a[i] = 0u8; } }
#[trust_vc::ensures(true)]
fn while_write_off_by_one(mut a: [u8; 4]) { let mut i = 0usize; while i <= 4usize { trust_vc::invariant!(i <= 5usize); a[i] = 1u8; i = i + 1usize; } }
#[trust_vc::ensures(true)]
fn nested_inner_read_oob(a: [u8; 2]) { let mut i = 0usize; while i < 2usize { trust_vc::invariant!(i <= 2usize); let mut j = 0usize; while j < 3usize { trust_vc::invariant!(j <= 3usize && i < 2usize); let y = a[j]; j = j + 1usize; } i = i + 1usize; } }

#[trust_vc::ensures(true)]
fn while_read_in_bounds(a: [u8; 2]) { let mut i = 0usize; let mut x = 0u8; while i < 2usize { trust_vc::invariant!(i <= 2usize); x = a[i]; i = i + 1usize; } }
#[trust_vc::ensures(true)]
fn while_read_in_bounds_liar(a: [u8; 2]) { let mut i = 0usize; let mut x = 0u8; while i < 2usize { trust_vc::invariant!(i <= 2usize); x = a[i]; i = i + 1usize; } trust_vc::assert!(i == 1usize); }
#[trust_vc::ensures(true)]
fn for_read_in_bounds(a: [u8; 2]) { let mut x = 0u8; for i in 0usize..2usize { x = a[i]; } }
#[trust_vc::ensures(true)]
fn for_read_in_bounds_liar(a: [u8; 2]) { let mut x = 0u8; for i in 0usize..2usize { x = a[i]; trust_vc::assert!(i == 0usize); } }
#[trust_vc::ensures(true)]
fn while_write_in_bounds(mut a: [u8; 4]) { let mut i = 0usize; while i < 4usize { trust_vc::invariant!(i <= 4usize); a[i] = 1u8; i = i + 1usize; } }
#[trust_vc::ensures(true)]
fn while_write_in_bounds_liar(mut a: [u8; 4]) { let mut i = 0usize; while i < 4usize { trust_vc::invariant!(i <= 4usize); a[i] = 1u8; i = i + 1usize; } trust_vc::assert!(i == 3usize); }
"#;

#[test]
fn an_out_of_bounds_index_inside_a_loop_body_is_refuted() {
    let mut failures = Vec::new();
    for (index, func) in [
        "while_write_literal_oob",
        "while_read_literal_oob",
        "while_read_empty_vec",
        "for_write_literal_oob",
        "while_let_read_const_index_oob",
    ]
    .into_iter()
    .enumerate()
    {
        let r = verify(&format!("o{index}"), func, SRC);
        let refuted = matches!(&r, VerifyResult::Counterexample { obligation_name, .. } if obligation_name.starts_with("index_bounds_check_"));
        if !refuted {
            failures.push(format!("{func}: {r:?}"));
        }
    }
    assert!(
        failures.is_empty(),
        "CARDINAL: each of these indexes out of bounds inside a loop body and must be refuted at its bounds obligation:\n{}",
        failures.join("\n")
    );
}

#[test]
fn a_counter_indexed_out_of_bounds_access_inside_a_loop_body_does_not_verify() {
    // These panic on a later iteration; the loop-body bound over the havoc'd
    // counter is not refuted by the solver (it returns `NotProved`), but it must
    // never verify.
    let mut failures = Vec::new();
    for (index, func) in [
        "while_read_counter_oob",
        "while_read_unconstrained_vec",
        "for_write_counter_oob",
        "while_write_off_by_one",
        "nested_inner_read_oob",
    ]
    .into_iter()
    .enumerate()
    {
        let r = verify(&format!("c{index}"), func, SRC);
        if matches!(r, VerifyResult::Verified) {
            failures.push(format!("{func}: {r:?}"));
        }
    }
    assert!(
        failures.is_empty(),
        "CARDINAL: a guaranteed out-of-bounds panic on a later loop iteration must not verify:\n{}",
        failures.join("\n")
    );
}

#[test]
fn a_bound_established_by_the_guard_verifies_and_its_liar_is_refuted() {
    let mut failures = Vec::new();
    for (index, func) in [
        "while_read_in_bounds",
        "for_read_in_bounds",
        "while_write_in_bounds",
    ]
    .into_iter()
    .enumerate()
    {
        let r = verify(&format!("t{index}"), func, SRC);
        if !matches!(r, VerifyResult::Verified) {
            failures.push(format!("{func} should verify: {r:?}"));
        }
        let liar = format!("{func}_liar");
        let r = verify(&format!("l{index}"), &liar, SRC);
        if !matches!(r, VerifyResult::Counterexample { .. }) {
            failures.push(format!("{liar} must be refuted: {r:?}"));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
