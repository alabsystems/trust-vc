// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Well-founded structural-ordering spec surface (Verus `decreases_to!` predicate
//! & height intrinsic): `height(x)` and `is_smaller_than(a, b)` / `decreases_to`
//! over recursive datatypes, backed by the trusted `dt_size` measure UF.
//!
//! A genuine substructure relation verifies (`is_smaller_than(t, Cons(h, t))`,
//! `height(child) < height(parent)`); every cardinal liar (self, parent-smaller,
//! unrelated pair, wrong height) fail-closes. Only recursive datatypes carry a
//! `dt_size` — a bogus `height(int)` fail-closes at encode.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
        let mut p = std::env::temp_dir();
        p.push(format!("tvc_dos_{}_{}.rs", std::process::id(), id));
        std::fs::write(&p, src).expect("write fixture");
        let r = verify_function_from_file(p.to_str().unwrap(), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
        let _ = std::fs::remove_file(&p);
        r
    })
}
fn verified(r: &VerifyResult) -> bool {
    matches!(r, VerifyResult::Verified)
}

const SRC: &str = r#"
enum List { Nil, Cons(u64, Box<List>) }

// A recursive child is strictly smaller than its parent constructor.
#[trust_vc::ensures(true)]
fn child_smaller_than_parent(h: u64, t: List) {
    trust_vc::assert!(is_smaller_than(t, Cons(h, Box::new(t))));
}
// height(child) < height(parent).
#[trust_vc::ensures(true)]
fn height_child_lt_parent(h: u64, t: List) {
    trust_vc::assert!(height(t) < height(Cons(h, Box::new(t))));
}
// height is non-negative.
#[trust_vc::ensures(true)]
fn height_nonneg(t: List) {
    trust_vc::assert!(height(t) >= 0);
}
// A Cons has strictly positive height.
#[trust_vc::ensures(true)]
fn cons_height_positive(h: u64, t: List) {
    trust_vc::assert!(height(Cons(h, Box::new(t))) > 0);
}

// CARDINAL LIARS ----------------------------------------------------------
// Nothing is smaller than itself.
#[trust_vc::ensures(true)]
fn self_smaller_liar(t: List) {
    trust_vc::assert!(is_smaller_than(t, t));
}
// The parent is NOT smaller than its child.
#[trust_vc::ensures(true)]
fn parent_smaller_liar(h: u64, t: List) {
    trust_vc::assert!(is_smaller_than(Cons(h, Box::new(t)), t));
}
// Two unrelated values have no provable ordering.
#[trust_vc::ensures(true)]
fn unrelated_liar(a: List, b: List) {
    trust_vc::assert!(is_smaller_than(a, b));
}
// A Cons never has height 0.
#[trust_vc::ensures(true)]
fn cons_height_zero_liar(h: u64, t: List) {
    trust_vc::assert!(height(Cons(h, Box::new(t))) == 0);
}

// INTEGER well-order: is_smaller_than(a, b) == (0 <= a < b).
#[trust_vc::ensures(true)]
fn int_smaller_pos() {
    trust_vc::assert!(is_smaller_than(3u64, 5u64));
}
#[trust_vc::ensures(true)]
fn int_smaller_ge_liar() {
    trust_vc::assert!(is_smaller_than(5u64, 3u64));
}
#[trust_vc::ensures(true)]
fn int_self_liar(n: u64) {
    trust_vc::assert!(is_smaller_than(n, n));
}
// A general decreasing step: for n > 0, n-1 is smaller than n (the termination shape).
#[trust_vc::ensures(true)]
fn int_pred_step(n: u64) {
    trust_vc::assert!(n == 0u64 || is_smaller_than(n - 1u64, n));
}
// Negative measure is NOT below zero's successor (bounded-below semantics).
#[trust_vc::ensures(true)]
fn int_negative_liar(n: int) {
    trust_vc::assert!(is_smaller_than(n, 5int));
}

// LEXICOGRAPHIC (multidecrease): is_smaller_than((a1,a2), (b1,b2)).
// First component decreases → smaller regardless of the second.
#[trust_vc::ensures(true)]
fn lex_first_decreases() {
    trust_vc::assert!(is_smaller_than((3u64, 0u64), (5u64, 9u64)));
}
// First component ties, second decreases → smaller.
#[trust_vc::ensures(true)]
fn lex_tie_second_decreases() {
    trust_vc::assert!(is_smaller_than((5u64, 2u64), (5u64, 9u64)));
}
// First ties, second INCREASES → NOT smaller.
#[trust_vc::ensures(true)]
fn lex_second_larger_liar() {
    trust_vc::assert!(is_smaller_than((5u64, 9u64), (5u64, 3u64)));
}
// First component LARGER → not smaller even though the second is smaller.
#[trust_vc::ensures(true)]
fn lex_first_larger_liar() {
    trust_vc::assert!(is_smaller_than((5u64, 0u64), (3u64, 9u64)));
}
// Equal tuples are NOT strictly smaller.
#[trust_vc::ensures(true)]
fn lex_equal_liar() {
    trust_vc::assert!(is_smaller_than((4u64, 7u64), (4u64, 7u64)));
}

// `decreases_to!(from => to)` MACRO in spec position: holds iff `to` is smaller
// than `from` (scalar + lexicographic), matching the runtime marker's direction.
#[trust_vc::ensures(true)]
fn dt_scalar_pos() {
    trust_vc::assert!(decreases_to!(5u64 => 3u64));
}
#[trust_vc::ensures(true)]
fn dt_scalar_liar() {
    trust_vc::assert!(decreases_to!(3u64 => 5u64));
}
#[trust_vc::ensures(true)]
fn dt_lex_first_pos() {
    trust_vc::assert!(decreases_to!(10u64, 1u64 => 5u64, 100u64));
}
#[trust_vc::ensures(true)]
fn dt_lex_tie_pos() {
    trust_vc::assert!(decreases_to!(5u64, 9u64 => 5u64, 2u64));
}
#[trust_vc::ensures(true)]
fn dt_lex_liar() {
    trust_vc::assert!(decreases_to!(5u64, 2u64 => 5u64, 9u64));
}

// The surface is position-agnostic: it works directly in ensures/requires and
// inside an implication, not only under `assert!`.
#[trust_vc::ensures(decreases_to!(5u64 => 3u64))]
fn dt_in_ensures() -> u64 {
    0u64
}
#[trust_vc::ensures(decreases_to!(3u64 => 5u64))]
fn dt_in_ensures_liar() -> u64 {
    0u64
}
#[trust_vc::requires(decreases_to!(5u64 => 3u64))]
#[trust_vc::ensures(true)]
fn dt_in_requires() {}
#[trust_vc::ensures(is_smaller_than(3u64, 5u64) ==> result == 0u64)]
fn dt_smaller_in_implication() -> u64 {
    0u64
}
"#;

#[test]
fn structural_ordering_positives() {
    for f in [
        "child_smaller_than_parent",
        "height_child_lt_parent",
        "height_nonneg",
        "cons_height_positive",
        "int_smaller_pos",
        "int_pred_step",
        "lex_first_decreases",
        "lex_tie_second_decreases",
        "dt_scalar_pos",
        "dt_lex_first_pos",
        "dt_lex_tie_pos",
        "dt_in_ensures",
        "dt_in_requires",
        "dt_smaller_in_implication",
    ] {
        assert!(
            verified(&verify(f, f, SRC)),
            "`{f}` should verify (sound structural-ordering fact); got {:?}",
            verify(f, f, SRC)
        );
    }
}

#[test]
fn structural_ordering_cardinal_liars() {
    for f in [
        "self_smaller_liar",
        "parent_smaller_liar",
        "unrelated_liar",
        "cons_height_zero_liar",
        "int_smaller_ge_liar",
        "int_self_liar",
        "int_negative_liar",
        "lex_second_larger_liar",
        "lex_first_larger_liar",
        "lex_equal_liar",
        "dt_scalar_liar",
        "dt_lex_liar",
        "dt_in_ensures_liar",
    ] {
        assert!(
            !verified(&verify(f, f, SRC)),
            "CARDINAL: `{f}` must NOT verify (false ordering claim)"
        );
    }
}
