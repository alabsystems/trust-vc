// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN (soundness, 2026-09-14): a mutable borrow of an indexed
//! place, `&mut P[idx]`, carries the same index-bounds obligation as the
//! shared borrow `&P[idx]` and the plain read `P[idx]`.
//!
//! Rust semantics: evaluating `&mut P[idx]` calls `IndexMut::index_mut`, which
//! for arrays, slices and `Vec` panics out of bounds exactly as `Index::index`
//! does for `&P[idx]` — unconditionally, AT THE BORROW, and it fixes the
//! borrowed slot to the value `idx` has at that moment.
//!
//! The hole (measured at main `ee37bb64`, file lane, cache off): every
//! value-position `&mut P[idx]` returned `Verified` with no bound — let
//! borrows on array / slice / Vec receivers, a write through the reference,
//! call arguments, match scrutinees, bare statements, aggregates — and each of
//! those programs panics at runtime. Three defects in
//! `vc_extraction/body_extract.rs`:
//!
//! * R1 — the value-position index and arithmetic collectors only looked
//!   inside a SHARED reference, so `&mut P[idx]` (and `&mut (a + b)`) pinned
//!   no bounds / overflow obligation anywhere.
//! * R2 — the `&mut P[idx]` alias target recorded the index as RAW TOKENS, so
//!   a later `*r = v` resolved the index at the WRITE (a shadowed or
//!   reassigned `i` retargeted the write to another slot), or failed to
//!   resolve a let-local index at all.
//! * R3 — the direct form `*(&mut P[idx]) = v` is instrumented by no
//!   collector; it now fails closed with the existing unsupported-deref
//!   rejection.
//!
//! Call arguments need one more rule. A call that writes through a `&mut`
//! argument rebinds that argument's root, and the value-position collectors
//! run after the visit — over the rebound root. So an argument access that
//! reads a rebound root (`noop(&mut s[0usize])`, `setz(x[j], &mut j)`) is
//! pinned AT THE CALL, and only where that pin point is the access's own
//! evaluation point: a free call is modelled before its arguments are visited
//! (faithful when no argument up to the access has a side effect), a method
//! call after (faithful when no later argument has one). Anything else fails
//! closed. `setz(x[j], &mut j)` with a contracted `*r == 0` callee was a false
//! `Verified` for the SHARED read too — the bound was checked over the
//! post-call `j`.
//!
//! Review round 1 found two more shapes, both `Verified` on main as well:
//!
//! * R2 across an invariant loop — the index string recorded at the borrow
//!   reads a BARE name (a parameter, or a `let mut i = i;` shadow of one), and
//!   an invariant loop that modifies that name rebinds it to its POST-loop
//!   value, so a later `*r = v` (or `*r` read) used the post-loop slot. The
//!   loop now snapshots each such name exactly as it snapshots a scalar `let`
//!   that reads it, and renames the alias strings to the snapshot — also on the
//!   strings a block / branch restore brings back after a nested loop (a
//!   desugared `for` range loop is such a block).
//! * A free-call argument access nested in a branch, arm, guard, block or
//!   `unsafe` block (`setz(if c { &mut x[j] } else { &mut y }, &mut j)`) is
//!   bounded by the visit of that argument, which runs after the call's `&mut`
//!   havoc — over the post-call `j`. When it reads a root the call rebinds, the
//!   function now fails closed.
//!
//! Every liar below is a program that panics (or whose assertion is false) at
//! runtime and is pinned REFUTED (Counterexample) or fail-closed (Error); every
//! control is a true program pinned `Verified`. The twin table pins that each
//! `&mut` shape lands in the same verdict class as its `&` twin.

use std::sync::OnceLock;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, unused_assignments, unused_must_use)]

#[trust_vc::ensures(true)]
fn noop(_r: &mut u8) {}

fn noop_nc(_r: &mut u8) {}

struct H;

impl H {
    #[trust_vc::ensures(true)]
    fn m(&self, _r: &mut u8) {}
}

struct S3 {
    arr: [u8; 3],
}

#[trust_vc::ensures(*k == 5usize)]
fn g5(k: &mut usize) -> usize {
    *k = 5usize;
    0usize
}

#[trust_vc::ensures(*k == 0usize)]
fn g0(k: &mut usize) -> usize {
    *k = 0usize;
    0usize
}

#[trust_vc::ensures(*r == 0usize)]
fn setz(_v: u8, r: &mut usize) {
    *r = 0usize;
}

#[trust_vc::ensures(true)]
fn noop2(_u: usize, _r: &mut u8) {}

#[trust_vc::ensures(true)]
fn noop2r(_r: &mut u8, _u: usize) {}

#[trust_vc::ensures(*k == 0usize)]
fn setz_r(_r: &mut u8, k: &mut usize) {
    *k = 0usize;
}

#[trust_vc::ensures(*k == 0usize)]
fn setz_s(_r: &u8, k: &mut usize) {
    *k = 0usize;
}

struct Hs;

impl Hs {
    #[trust_vc::ensures(*k == 0usize)]
    fn setz(_r: &mut u8, k: &mut usize) {
        *k = 0usize;
    }
}

struct KIdx {
    k: usize,
}

impl H {
    #[trust_vc::ensures(*k == 0usize)]
    fn setz_mr(&self, _r: &mut u8, k: &mut usize) {
        *k = 0usize;
    }

    #[trust_vc::ensures(true)]
    fn m2(&self, _r: &mut u8, _u: usize) {}

    #[trust_vc::ensures(true)]
    fn m2l(&self, _u: usize, _r: &mut u8) {}
}

// ----------------------------------------------------------------------------
// R1 liars: the bound at the borrow.
// ----------------------------------------------------------------------------

#[trust_vc::ensures(true)]
fn liar01_let_borrow_param_index(i: usize) {
    let mut x = [1u8, 2u8, 3u8];
    let _r = &mut x[i];
}

#[trust_vc::ensures(true)]
fn liar02_write_through_borrow(i: usize) {
    let mut x = [1u8, 2u8, 3u8];
    let r = &mut x[i];
    *r = 0u8;
}

#[trust_vc::requires(i == 3usize)]
#[trust_vc::ensures(true)]
fn liar03_requires_forces_oob(i: usize) {
    let mut x = [1u8, 2u8, 3u8];
    let _r = &mut x[i];
}

// Non-vacuity twin of liar03: the `i == 3usize` context is satisfiable.
#[trust_vc::requires(i == 3usize)]
#[trust_vc::ensures(true)]
fn liar03b_requires_forces_oob_nonvacuous(i: usize) {
    let mut x = [1u8, 2u8, 3u8];
    let _r = &mut x[i];
    trust_vc::assert!(false);
}

// The bound is CHECKED, never ASSUMED.
#[trust_vc::ensures(true)]
fn liar04_bound_not_assumed(i: usize) {
    let mut x = [1u8, 2u8, 3u8];
    let _r = &mut x[i];
    trust_vc::assert!(i < 3usize);
}

#[trust_vc::ensures(true)]
fn liar05_slice_param(s: &mut [u8]) {
    let _r = &mut s[0usize];
}

#[trust_vc::ensures(true)]
fn liar06_vec_param_write(v: &mut Vec<u8>) {
    let r = &mut v[0usize];
    *r = 7u8;
}

#[trust_vc::ensures(true)]
fn liar07_vec_param_index_write(v: &mut Vec<u8>, i: usize) {
    let r = &mut v[i];
    *r = 0u8;
}

// The solver answers `Unknown(incomplete)` on a Vec-parameter bound whose
// length is only symbolically related to the index (`i` unconstrained, or
// `i == v.len()`) — for the `&v[i]` read and the `&mut v[i]` borrow alike (see
// the twin table). A ground length pins the refuted verdict for the same shape.
#[trust_vc::requires(v.len() == 2usize)]
#[trust_vc::requires(i == 2usize)]
#[trust_vc::ensures(true)]
fn liar07b_vec_param_index_write_at_len(v: &mut Vec<u8>, i: usize) {
    let r = &mut v[i];
    *r = 0u8;
}

#[trust_vc::ensures(true)]
fn liar08_vec_local_write(i: usize) {
    let mut v = vec![1u8, 2u8];
    let r = &mut v[i];
    *r = 4u8;
}

#[trust_vc::ensures(true)]
fn liar09_nested_vec_literal() {
    let mut v = vec![vec![1u64, 2u64, 3u64], vec![4u64, 5u64], vec![6u64]];
    let _r = &mut v[2][1];
}

#[trust_vc::ensures(true)]
fn liar10_nested_array(i: usize) {
    let mut x = [[1u8, 2u8], [3u8, 4u8]];
    let _r = &mut x[0usize][i];
}

#[trust_vc::ensures(true)]
fn liar11_guarded(i: usize, c: bool) {
    let mut x = [1u8, 2u8, 3u8];
    if c {
        let r = &mut x[i];
        *r = 4u8;
    }
}

#[trust_vc::ensures(true)]
fn liar12_reassign_rhs(i: usize) {
    let mut x = [1u8, 2u8, 3u8];
    let mut y = 0u8;
    let mut r = &mut y;
    r = &mut x[i];
    *r = 5u8;
}

#[trust_vc::ensures(true)]
fn liar13a_typed_let(i: usize) {
    let mut x = [1u8, 2u8, 3u8];
    let r: &mut u8 = &mut x[i];
    *r = 4u8;
}

#[trust_vc::ensures(true)]
fn liar13b_paren_place(i: usize) {
    let mut x = [1u8, 2u8, 3u8];
    let r = &mut (x[i]);
    *r = 4u8;
}

#[trust_vc::ensures(true)]
fn liar14_method_receiver(i: usize) {
    let mut x = [1u8, 2u8, 3u8];
    let _b = (&mut x[i]).clone();
}

#[trust_vc::ensures(true)]
fn liar15_call_argument(i: usize) {
    let mut x = [1u8, 2u8, 3u8];
    noop(&mut x[i]);
}

// Call arguments whose root the `&mut`-argument havoc rebinds: the bound is
// checked in the PRE-call state (a declared slice / Vec parameter becomes a
// fresh symbol after the call; an array local is invalidated).
#[trust_vc::ensures(true)]
fn liar15b_call_argument_slice_param(s: &mut [u8]) {
    noop(&mut s[0usize]);
}

#[trust_vc::ensures(true)]
fn liar15c_call_argument_vec_param(v: &mut Vec<u8>) {
    noop(&mut v[0usize]);
}

#[trust_vc::ensures(true)]
fn liar15d_uncontracted_call_argument(s: &mut [u8]) {
    noop_nc(&mut s[0usize]);
}

#[trust_vc::ensures(true)]
fn liar15e_method_call_argument(h: &H, s: &mut [u8]) {
    h.m(&mut s[0usize]);
}

#[trust_vc::ensures(true)]
fn liar15f_let_bound_call_argument(s: &mut [u8]) {
    let _u = noop(&mut s[0usize]);
}

#[trust_vc::ensures(true)]
fn liar15g_struct_field_array_call_argument(o: &mut S3, i: usize) {
    noop(&mut o.arr[i]);
}

#[trust_vc::ensures(true)]
fn liar15h_struct_local_field_array(i: usize) {
    let mut o = S3 { arr: [1u8, 2u8, 3u8] };
    let _r = &mut o.arr[i];
}

#[trust_vc::ensures(true)]
fn liar16_match_scrutinee(i: usize) {
    let mut x = [1u8, 2u8, 3u8];
    match &mut x[i] {
        _ => {}
    }
}

#[trust_vc::ensures(true)]
fn liar17_bare_statement(i: usize) {
    let mut x = [1u8, 2u8, 3u8];
    &mut x[i];
}

#[trust_vc::ensures(true)]
fn liar18_aggregate(i: usize) {
    let mut x = [1u8, 2u8, 3u8];
    let mut y = 0u8;
    let _t = (&mut x[i], &mut y);
}

#[trust_vc::ensures(true)]
fn liar19_arith_inside_index(a: usize, b: usize) {
    let mut x = [1u8, 2u8, 3u8];
    let _r = &mut x[(a + b) % 3usize];
}

#[trust_vc::ensures(true)]
fn liar20_arith_under_mut_borrow(a: u8, b: u8) {
    let _r = &mut (a + b);
}

#[trust_vc::ensures(true)]
fn liar_const_index_past_array_len() {
    let mut x = [1u8, 2u8, 3u8];
    let _r = &mut x[3usize];
}

#[trust_vc::ensures(true)]
fn liar_vec_literal_const_index_past_len() {
    let mut v = vec![1u8, 2u8];
    let _r = &mut v[2usize];
}

// ----------------------------------------------------------------------------
// Call-argument evaluation order. Each liar panics at runtime (checked with
// trustc -Ztrust-verify=off).
// ----------------------------------------------------------------------------

// `g5` runs first (i = 5), then `&mut x[i]` panics. A free call is modelled
// before its arguments are visited, so the borrow cannot be pinned faithfully:
// fail closed.
#[trust_vc::requires(i < 3usize)]
#[trust_vc::ensures(true)]
fn liar28_free_call_earlier_arg_effect(i: usize) {
    let mut i = i;
    let mut x = [1u8, 2u8, 3u8];
    noop2(g5(&mut i), &mut x[i]);
}

// `&mut x[i]` with i = 3 panics before `g0` runs. A method call is modelled
// after its arguments are visited: fail closed.
#[trust_vc::requires(i == 3usize)]
#[trust_vc::ensures(true)]
fn liar29_method_call_later_arg_effect(h: &H, i: usize) {
    let mut i = i;
    let mut x = [1u8, 2u8, 3u8];
    h.m2(&mut x[i], g0(&mut i));
}

// Faithful order for a free call: pinned before `g0` runs.
#[trust_vc::requires(i == 3usize)]
#[trust_vc::ensures(true)]
fn liar30_free_call_later_arg_effect(i: usize) {
    let mut i = i;
    let mut x = [1u8, 2u8, 3u8];
    noop2r(&mut x[i], g0(&mut i));
}

// Faithful order for a method call: pinned after `g5` ran (i = 5).
#[trust_vc::requires(i < 3usize)]
#[trust_vc::ensures(true)]
fn liar31_method_call_earlier_arg_effect(h: &H, i: usize) {
    let mut i = i;
    let mut x = [1u8, 2u8, 3u8];
    h.m2l(g5(&mut i), &mut x[i]);
}

// A SHARED read whose index the call rebinds: `x[j]` is read with j = 3,
// before `setz` sets j = 0.
#[trust_vc::requires(j == 3usize)]
#[trust_vc::ensures(true)]
fn liar32_shared_read_of_rebound_index(j: usize) {
    let mut j = j;
    let x = [1u8, 2u8, 3u8];
    setz(x[j], &mut j);
}

// `&mut s[s.len() - 1usize]` evaluates the index before the borrow (built-in
// slice indexing; the `Vec` spelling is a borrowck error), so its `len()` read
// is not an ordering hazard and the bound is still pinned at the call.
#[trust_vc::ensures(true)]
fn liar33_slice_last_index_call_argument(s: &mut [u8]) {
    noop2(0usize, &mut s[s.len() - 1usize]);
}

// ----------------------------------------------------------------------------
// R3 liar: the direct deref-of-borrow write fails closed.
// ----------------------------------------------------------------------------

#[trust_vc::ensures(true)]
fn liar21_direct_deref_of_borrow_write(i: usize) {
    let mut x = [1u8, 2u8, 3u8];
    *(&mut x[i]) = 0u8;
}

// ----------------------------------------------------------------------------
// R1 range and loop shapes (twinned with the shared borrow).
// ----------------------------------------------------------------------------

#[trust_vc::ensures(true)]
fn liar22_range_mut(s: &mut [u8], i: usize) {
    let _r = &mut s[0usize..i];
}

#[trust_vc::ensures(true)]
fn liar22_range_shared(s: &[u8], i: usize) {
    let _r = &s[0usize..i];
}

#[trust_vc::ensures(true)]
fn gap23_loop_body_mut(i: usize) {
    let mut x = [1u8, 2u8, 3u8];
    let mut k = 0usize;
    while k < 1usize {
        trust_vc::invariant!(k <= 1usize);
        let _r = &mut x[i];
        k = k + 1usize;
    }
}

#[trust_vc::ensures(true)]
fn gap23_loop_body_shared_read(i: usize) {
    let mut x = [1u8, 2u8, 3u8];
    let mut k = 0usize;
    while k < 1usize {
        trust_vc::invariant!(k <= 1usize);
        let _r = &x[i];
        k = k + 1usize;
    }
}

// ----------------------------------------------------------------------------
// R2 liars: the borrowed slot is fixed by the index value AT THE BORROW.
// ----------------------------------------------------------------------------

#[trust_vc::requires(i == 0usize)]
#[trust_vc::ensures(true)]
fn liar24_shadowed_index_retargets_write(i: usize) {
    let mut x = [0u8, 0u8, 0u8];
    let i = 2usize;
    let r = &mut x[i];
    *r = 7u8;
    trust_vc::assert!(x[0usize] == 7u8);
}

#[trust_vc::requires(i == 0usize)]
#[trust_vc::ensures(true)]
fn liar25_reassigned_param_index_retargets_write(mut i: usize) {
    let mut x = [0u8, 0u8, 0u8];
    i = 2usize;
    let r = &mut x[i];
    *r = 7u8;
    trust_vc::assert!(x[0usize] == 7u8);
}

#[trust_vc::requires(i == 0usize)]
#[trust_vc::ensures(true)]
fn liar26_shadowed_index_arith_retargets_write(i: usize) {
    let mut x = [0u8, 0u8, 0u8];
    let i = 1usize;
    let r = &mut x[i + 1usize];
    *r = 7u8;
    trust_vc::assert!(x[1usize] == 7u8);
}

#[trust_vc::ensures(true)]
fn liar27_index_reassigned_after_borrow(u: u8) {
    let mut x = [0u8, 0u8, 0u8];
    let mut j = 0usize;
    let r = &mut x[j];
    j = 2usize;
    *r = 7u8;
    trust_vc::assert!(x[2usize] == 7u8);
}

// ----------------------------------------------------------------------------
// R2 across an invariant loop (review round 1). Each liar borrows slot 0 with
// `i == 0`, then a loop takes `i` to 2 before the write or read; the program
// asserts slot 2 and panics. Each true twin asserts slot 0.
// ----------------------------------------------------------------------------

#[trust_vc::requires(i == 0usize)]
#[trust_vc::ensures(true)]
fn liar34_loop_moves_param_index(mut i: usize) {
    let mut x = [0u8, 0u8, 0u8];
    let r = &mut x[i];
    let mut k = 0usize;
    while k < 2usize {
        trust_vc::invariant!(k <= 2usize && i == k);
        i = i + 1usize;
        k = k + 1usize;
    }
    *r = 7u8;
    trust_vc::assert!(x[2usize] == 7u8);
}

#[trust_vc::requires(i == 0usize)]
#[trust_vc::ensures(true)]
fn control23_loop_moves_param_index_true_slot(mut i: usize) {
    let mut x = [0u8, 0u8, 0u8];
    let r = &mut x[i];
    let mut k = 0usize;
    while k < 2usize {
        trust_vc::invariant!(k <= 2usize && i == k);
        i = i + 1usize;
        k = k + 1usize;
    }
    *r = 7u8;
    trust_vc::assert!(x[0usize] == 7u8);
}

#[trust_vc::requires(i == 0usize)]
#[trust_vc::ensures(true)]
fn liar35_loop_moves_shadowed_index(i: usize) {
    let mut i = i;
    let mut x = [0u8, 0u8, 0u8];
    let r = &mut x[i];
    let mut k = 0usize;
    while k < 2usize {
        trust_vc::invariant!(k <= 2usize && i == k);
        i = i + 1usize;
        k = k + 1usize;
    }
    *r = 7u8;
    trust_vc::assert!(x[2usize] == 7u8);
}

#[trust_vc::requires(i == 0usize)]
#[trust_vc::ensures(true)]
fn liar36_loop_moves_index_arith(mut i: usize) {
    let mut x = [0u8, 0u8, 0u8, 0u8];
    let r = &mut x[i + 1usize];
    let mut k = 0usize;
    while k < 2usize {
        trust_vc::invariant!(k <= 2usize && i == k);
        i = i + 1usize;
        k = k + 1usize;
    }
    *r = 7u8;
    trust_vc::assert!(x[3usize] == 7u8);
}

#[trust_vc::requires(i == 0usize)]
#[trust_vc::ensures(true)]
fn control24_loop_moves_index_arith_true_slot(mut i: usize) {
    let mut x = [0u8, 0u8, 0u8, 0u8];
    let r = &mut x[i + 1usize];
    let mut k = 0usize;
    while k < 2usize {
        trust_vc::invariant!(k <= 2usize && i == k);
        i = i + 1usize;
        k = k + 1usize;
    }
    *r = 7u8;
    trust_vc::assert!(x[1usize] == 7u8);
}

#[trust_vc::requires(i == 0usize)]
#[trust_vc::ensures(true)]
fn liar37_loop_moves_reassign_rhs_index(mut i: usize) {
    let mut x = [0u8, 0u8, 0u8];
    let mut y = 0u8;
    let mut r = &mut y;
    r = &mut x[i];
    let mut k = 0usize;
    while k < 2usize {
        trust_vc::invariant!(k <= 2usize && i == k);
        i = i + 1usize;
        k = k + 1usize;
    }
    *r = 7u8;
    trust_vc::assert!(x[2usize] == 7u8);
}

// The READ through the alias names the borrowed slot too: `*r` is 0, slot 2 is 5.
#[trust_vc::requires(i == 0usize)]
#[trust_vc::ensures(true)]
fn liar38_loop_moves_index_read_through_alias(mut i: usize) {
    let mut x = [0u8, 0u8, 5u8];
    let r = &mut x[i];
    let mut k = 0usize;
    while k < 2usize {
        trust_vc::invariant!(k <= 2usize && i == k);
        i = i + 1usize;
        k = k + 1usize;
    }
    let v = *r;
    trust_vc::assert!(v == 5u8);
}

#[trust_vc::requires(i == 0usize)]
#[trust_vc::ensures(true)]
fn liar39_bare_loop_moves_index(mut i: usize) {
    let mut x = [0u8, 0u8, 0u8];
    let r = &mut x[i];
    let mut k = 0usize;
    loop {
        trust_vc::invariant!(k <= 2usize && i == k);
        if k >= 2usize {
            break;
        }
        i = i + 1usize;
        k = k + 1usize;
    }
    *r = 7u8;
    trust_vc::assert!(x[i] == 7u8);
}

// A flat `for` range loop is desugared into `{ let mut q = 0; while .. }` — a
// BLOCK, whose scope restore used to bring the pre-loop alias strings back.
#[trust_vc::requires(i == 0usize)]
#[trust_vc::ensures(true)]
fn liar40_for_range_loop_moves_index(mut i: usize) {
    let mut x = [0u8, 0u8, 0u8];
    let r = &mut x[i];
    for q in 0usize..2usize {
        trust_vc::invariant!(i == q);
        i = i + 1usize;
    }
    *r = 7u8;
    trust_vc::assert!(x[2usize] == 7u8);
}

#[trust_vc::requires(i == 0usize)]
#[trust_vc::ensures(true)]
fn control25_for_range_loop_true_slot(mut i: usize) {
    let mut x = [0u8, 0u8, 0u8];
    let r = &mut x[i];
    for q in 0usize..2usize {
        trust_vc::invariant!(i == q);
        i = i + 1usize;
    }
    *r = 7u8;
    trust_vc::assert!(x[0usize] == 7u8);
}

#[trust_vc::requires(i == 0usize && c)]
#[trust_vc::ensures(true)]
fn liar41_branch_loop_moves_index(mut i: usize, c: bool) {
    let mut x = [0u8, 0u8, 0u8];
    let r = &mut x[i];
    let mut k = 0usize;
    if c {
        while k < 2usize {
            trust_vc::invariant!(k <= 2usize && i == k);
            i = i + 1usize;
            k = k + 1usize;
        }
    }
    *r = 7u8;
    trust_vc::assert!(x[2usize] == 7u8);
}

#[trust_vc::requires(b == 0u8)]
#[trust_vc::ensures(true)]
fn liar42_loop_moves_cast_index(mut b: u8) {
    let mut x = [0u8, 0u8, 0u8];
    let r = &mut x[b as usize];
    let mut k = 0usize;
    while k < 2usize {
        trust_vc::invariant!(k <= 2usize && b as usize == k);
        b = b + 1u8;
        k = k + 1usize;
    }
    *r = 7u8;
    trust_vc::assert!(x[2usize] == 7u8);
}

// The index reads a struct the loop modifies: no scalar snapshot exists, so
// the function fails closed.
#[trust_vc::requires(o.k == 0usize)]
#[trust_vc::ensures(true)]
fn liar43_loop_moves_struct_field_index(mut o: KIdx) {
    let mut x = [0u8, 0u8, 0u8];
    let r = &mut x[o.k];
    let mut q = 0usize;
    while q < 2usize {
        trust_vc::invariant!(q <= 2usize && o.k == q);
        o.k = o.k + 1usize;
        q = q + 1usize;
    }
    *r = 7u8;
    trust_vc::assert!(x[2usize] == 7u8);
}

// A borrow taken AFTER the loop fixes the post-loop slot (i == 2).
#[trust_vc::requires(i == 0usize)]
#[trust_vc::ensures(true)]
fn control26_borrow_after_loop_post_loop_slot(mut i: usize) {
    let mut x = [0u8, 0u8, 0u8];
    let mut r = &mut x[i];
    let mut k = 0usize;
    while k < 2usize {
        trust_vc::invariant!(k <= 2usize && i == k);
        i = i + 1usize;
        k = k + 1usize;
    }
    r = &mut x[i];
    *r = 7u8;
    trust_vc::assert!(x[2usize] == 7u8);
}

// ----------------------------------------------------------------------------
// A free-call argument access nested in a branch / arm / guard / block reads a
// root the call rebinds (review round 1). `j == 3` when the argument is
// evaluated; `setz_*` sets it to 0 only afterwards. Every liar panics.
// ----------------------------------------------------------------------------

#[trust_vc::requires(j == 3usize && c)]
#[trust_vc::ensures(true)]
fn liar44_free_call_if_arg_mut(j: usize, c: bool) {
    let mut j = j;
    let mut x = [1u8, 2u8, 3u8];
    let mut y = 0u8;
    setz_r(if c { &mut x[j] } else { &mut y }, &mut j);
}

#[trust_vc::requires(j == 3usize && c)]
#[trust_vc::ensures(true)]
fn liar45_free_call_if_arg_shared(j: usize, c: bool) {
    let mut j = j;
    let x = [1u8, 2u8, 3u8];
    let y = 0u8;
    setz_s(if c { &x[j] } else { &y }, &mut j);
}

#[trust_vc::requires(j == 3usize && c)]
#[trust_vc::ensures(true)]
fn liar46_free_call_match_arg(j: usize, c: bool) {
    let mut j = j;
    let mut x = [1u8, 2u8, 3u8];
    let mut y = 0u8;
    setz_r(
        match c {
            true => &mut x[j],
            false => &mut y,
        },
        &mut j,
    );
}

#[trust_vc::requires(j == 3usize)]
#[trust_vc::ensures(true)]
fn liar47_free_call_block_arg_shared(j: usize) {
    let mut j = j;
    let x = [1u8, 2u8, 3u8];
    setz_s({ &x[j] }, &mut j);
}

#[trust_vc::requires(j == 3usize)]
#[trust_vc::ensures(true)]
fn liar48_free_call_block_arg_mut(j: usize) {
    let mut j = j;
    let mut x = [1u8, 2u8, 3u8];
    setz_r({ &mut x[j] }, &mut j);
}

#[trust_vc::requires(j == 3usize)]
#[trust_vc::ensures(true)]
fn liar49_free_call_unsafe_block_arg(j: usize) {
    let mut j = j;
    let mut x = [1u8, 2u8, 3u8];
    setz_r(unsafe { &mut x[j] }, &mut j);
}

#[trust_vc::requires(j == 3usize)]
#[trust_vc::ensures(true)]
fn liar50_free_call_if_condition_arg(j: usize) {
    let mut j = j;
    let x = [1u8, 2u8, 3u8];
    let y = 0u8;
    setz_s(if x[j] == 1u8 { &y } else { &y }, &mut j);
}

#[trust_vc::requires(j == 3usize && c)]
#[trust_vc::ensures(true)]
fn liar51_free_call_match_guard_arg(j: usize, c: bool) {
    let mut j = j;
    let x = [1u8, 2u8, 3u8];
    let y = 0u8;
    setz_s(
        match c {
            true if x[j] == 1u8 => &y,
            _ => &y,
        },
        &mut j,
    );
}

#[trust_vc::requires(j == 3usize && c)]
#[trust_vc::ensures(true)]
fn liar52_assoc_fn_if_arg(j: usize, c: bool) {
    let mut j = j;
    let mut x = [1u8, 2u8, 3u8];
    let mut y = 0u8;
    Hs::setz(if c { &mut x[j] } else { &mut y }, &mut j);
}

#[trust_vc::requires(j == 3usize && c)]
#[trust_vc::ensures(true)]
fn liar53_free_call_nested_block_in_if_arg(j: usize, c: bool) {
    let mut j = j;
    let mut x = [1u8, 2u8, 3u8];
    let mut y = 0u8;
    setz_r(if c { { &mut x[j] } } else { &mut y }, &mut j);
}

// A method call visits its arguments before the havoc: already refuted.
#[trust_vc::requires(j == 3usize && c)]
#[trust_vc::ensures(true)]
fn liar54_method_call_if_arg(h: &H, j: usize, c: bool) {
    let mut j = j;
    let mut x = [1u8, 2u8, 3u8];
    let mut y = 0u8;
    h.setz_mr(if c { &mut x[j] } else { &mut y }, &mut j);
}

// The nested access reads no rebound root: no rejection.
#[trust_vc::requires(c)]
#[trust_vc::ensures(true)]
fn control27_free_call_if_arg_unrelated_root(j: usize, c: bool) {
    let mut j = j;
    let mut x = [1u8, 2u8, 3u8];
    let mut y = 0u8;
    setz_r(if c { &mut x[0usize] } else { &mut y }, &mut j);
    trust_vc::assert!(j == 0usize);
}

// ----------------------------------------------------------------------------
// Controls: true programs that must stay Verified.
// ----------------------------------------------------------------------------

#[trust_vc::ensures(true)]
fn control01_in_bounds_literal_write() {
    let mut x = [1u8, 2u8, 3u8];
    let r = &mut x[2usize];
    *r = 9u8;
    trust_vc::assert!(x[2usize] == 9u8);
}

#[trust_vc::requires(i < 3usize)]
#[trust_vc::ensures(true)]
fn control02_requires_in_bounds_write(i: usize) {
    let mut x = [1u8, 2u8, 3u8];
    let r = &mut x[i];
    *r = 9u8;
    trust_vc::assert!(x[i] == 9u8);
}

#[trust_vc::requires(s.len() > 0usize)]
#[trust_vc::ensures(true)]
fn control03_slice_requires_nonempty(s: &mut [u8]) {
    let r = &mut s[0usize];
    *r = 1u8;
}

#[trust_vc::requires(v.len() > i)]
#[trust_vc::ensures(true)]
fn control04_vec_requires_in_bounds(v: &mut Vec<u8>, i: usize) {
    let r = &mut v[i];
    *r = 0u8;
}

#[trust_vc::ensures(true)]
fn control05_guarded_by_bound(i: usize) {
    let mut x = [1u8, 2u8, 3u8];
    if i < 3usize {
        let r = &mut x[i];
        *r = 1u8;
    }
}

#[trust_vc::requires(i < 3usize)]
#[trust_vc::ensures(true)]
fn control06_call_argument_in_bounds(i: usize) {
    let mut x = [1u8, 2u8, 3u8];
    noop(&mut x[i]);
}

#[trust_vc::requires(s.len() > 0usize)]
#[trust_vc::ensures(true)]
fn control06b_call_argument_slice_param(s: &mut [u8]) {
    noop(&mut s[0usize]);
}

#[trust_vc::requires(v.len() > i)]
#[trust_vc::ensures(true)]
fn control06c_call_argument_vec_param(v: &mut Vec<u8>, i: usize) {
    noop(&mut v[i]);
}

#[trust_vc::requires(s.len() > 0usize)]
#[trust_vc::ensures(true)]
fn control06d_uncontracted_call_argument(s: &mut [u8]) {
    noop_nc(&mut s[0usize]);
}

#[trust_vc::requires(s.len() > 0usize)]
#[trust_vc::ensures(true)]
fn control06e_method_call_argument(h: &H, s: &mut [u8]) {
    h.m(&mut s[0usize]);
}

#[trust_vc::requires(s.len() > 0usize)]
#[trust_vc::ensures(true)]
fn control06f_let_bound_call_argument(s: &mut [u8]) {
    let _u = noop(&mut s[0usize]);
}

#[trust_vc::requires(i < 3usize)]
#[trust_vc::ensures(true)]
fn control06g_struct_field_array_call_argument(o: &mut S3, i: usize) {
    noop(&mut o.arr[i]);
}

#[trust_vc::requires(i < 3usize)]
#[trust_vc::ensures(true)]
fn control06h_struct_local_field_array(i: usize) {
    let mut o = S3 { arr: [1u8, 2u8, 3u8] };
    let _r = &mut o.arr[i];
}

#[trust_vc::requires(i < 3usize)]
#[trust_vc::ensures(true)]
fn control07_match_scrutinee_in_bounds(i: usize) {
    let mut x = [1u8, 2u8, 3u8];
    match &mut x[i] {
        _ => {}
    }
}

#[trust_vc::requires(i < 3usize)]
#[trust_vc::ensures(true)]
fn control08_reassign_rhs_in_bounds(i: usize) {
    let mut x = [1u8, 2u8, 3u8];
    let mut y = 0u8;
    let mut r = &mut y;
    r = &mut x[i];
    *r = 5u8;
    trust_vc::assert!(x[i] == 5u8);
}

// Corpus mut_refs_slices_arrays_mut_ref_of_array_index.
#[trust_vc::ensures(true)]
fn control09_corpus_array_index() {
    let mut x: [u64; 3] = [5u64, 7u64, 8u64];
    let x_ref = &mut x[1usize];
    *x_ref = 20u64;
    trust_vc::assert!(x[1usize] == 20u64);
}

// Corpus mut_refs_slices_arrays_mut_ref_of_slice_index.
#[trust_vc::requires(x.len() == 3usize)]
#[trust_vc::requires(x[0usize] == 5u64)]
#[trust_vc::requires(x[1usize] == 7u64)]
#[trust_vc::requires(x[2usize] == 8u64)]
#[trust_vc::ensures(true)]
fn control10_corpus_slice_index(x: &mut [u64]) {
    let x_ref = &mut x[1usize];
    *x_ref = 20u64;
    trust_vc::assert!(x[1usize] == 20u64);
}

// Corpus mut_refs_libs_vec_index_mut_ref.
#[trust_vc::ensures(true)]
fn control11_corpus_vec_index() {
    let mut v = vec![1u64, 2u64, 3u64];
    let r = &mut v[1];
    *r = 5u64;
    trust_vc::assert!(v[1] == 5u64);
}

#[trust_vc::ensures(true)]
fn liar11b_corpus_vec_index_false_tail() {
    let mut v = vec![1u64, 2u64, 3u64];
    let r = &mut v[1];
    *r = 5u64;
    trust_vc::assert!(v[1] == 5u64);
    trust_vc::assert!(false);
}

// Corpus mut_refs_libs_vec_push_index_mut_ref.
#[trust_vc::ensures(true)]
fn control12_corpus_vec_push_index() {
    let mut v: Vec<u64> = Vec::new();
    v.push(1u64);
    v.push(2u64);
    v.push(3u64);
    let r = &mut v[1usize];
    *r = 5u64;
    trust_vc::assert!(v[1usize] == 5u64);
}

// Blocked corpus rows keep their fail-closed messages.
#[trust_vc::ensures(true)]
fn control13a_blocked_vec_index_tuple_field() {
    let mut v = vec![(1u64, 11u64), (2u64, 12u64), (3u64, 13u64)];
    let r = &mut v[1].0;
    *r = 5u64;
}

#[trust_vc::ensures(true)]
fn control13b_blocked_vec_nested_index() {
    let mut v = vec![vec![1u64, 2u64, 3u64], vec![4u64, 5u64], vec![6u64]];
    let r = &mut v[1][1];
    *r = 15u64;
}

#[trust_vc::ensures(true)]
fn control13c_blocked_vec_nested_index_oob() {
    let mut v = vec![vec![1u64, 2u64, 3u64], vec![4u64, 5u64], vec![6u64]];
    let r = &mut v[2][1];
    *r = 5u64;
}

#[trust_vc::ensures(true)]
fn control13d_blocked_vec_literal_index_oob() {
    let mut v = vec![1u64, 2u64, 3u64];
    let r = &mut v[3];
    *r = 5u64;
}

// R2 completeness twin of liar24: the write lands in slot 2.
#[trust_vc::requires(i == 0usize)]
#[trust_vc::ensures(true)]
fn control14_shadowed_index_true_slot(i: usize) {
    let mut x = [0u8, 0u8, 0u8];
    let i = 2usize;
    let r = &mut x[i];
    *r = 7u8;
    trust_vc::assert!(x[2usize] == 7u8);
}

#[trust_vc::ensures(true)]
fn control15_let_local_index(u: u8) {
    let mut x = [0u8, 0u8, 0u8];
    let j = 1usize;
    let r = &mut x[j];
    *r = 7u8;
    trust_vc::assert!(x[1usize] == 7u8);
}

#[trust_vc::ensures(true)]
fn control16_index_reassigned_after_borrow_true_slot(u: u8) {
    let mut x = [0u8, 0u8, 0u8];
    let mut j = 0usize;
    let r = &mut x[j];
    j = 2usize;
    *r = 7u8;
    trust_vc::assert!(x[0usize] == 7u8);
}

#[trust_vc::requires(i == 0usize)]
#[trust_vc::ensures(true)]
fn control17_param_reassigned_after_borrow(mut i: usize) {
    let mut x = [0u8, 0u8, 0u8];
    let r = &mut x[i];
    i = 2usize;
    *r = 7u8;
    trust_vc::assert!(x[0usize] == 7u8);
}

#[trust_vc::ensures(true)]
fn control18_literal_arith_index(u: u8) {
    let mut x = [1u8, 2u8, 3u8];
    let r = &mut x[0usize + 1usize];
    *r = 9u8;
    trust_vc::assert!(x[1usize] == 9u8);
}

#[trust_vc::requires(s.len() > 0usize)]
#[trust_vc::ensures(true)]
fn control19_slice_last_index_call_argument(s: &mut [u8]) {
    noop2(0usize, &mut s[s.len() - 1usize]);
}

#[trust_vc::requires(j < 3usize)]
#[trust_vc::ensures(true)]
fn control20_shared_read_of_rebound_index(j: usize) {
    let mut j = j;
    let x = [1u8, 2u8, 3u8];
    setz(x[j], &mut j);
}

#[trust_vc::requires(i < 3usize)]
#[trust_vc::ensures(true)]
fn control21_method_call_earlier_pure_arg(h: &H, i: usize) {
    let mut x = [1u8, 2u8, 3u8];
    h.m2l(0usize, &mut x[i]);
}

#[trust_vc::requires(i < 3usize)]
#[trust_vc::ensures(true)]
fn control22_free_call_later_pure_arg(i: usize) {
    let mut x = [1u8, 2u8, 3u8];
    noop2r(&mut x[i], 7usize);
}
"#;

// ----------------------------------------------------------------------------
// Harness.
// ----------------------------------------------------------------------------

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn verify_in(src: &str, func: &str) -> VerifyResult {
    // The on-disk VC-result cache replays `Verified` verdicts without
    // re-encoding, so it must be off for a true verdict. Serialized behind the
    // workspace env lock; the guards drop before the lock releases.
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_mut_borrow_index_bounds_{}_{seq}_{func}.rs",
        std::process::id()
    ));
    std::fs::write(&path, src).expect("write fixture");
    let result =
        verify_function_from_file(path.to_str().expect("utf8 path"), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
    let _ = std::fs::remove_file(&path);
    println!("VERDICT {func}: {result:?}");
    result
}

fn verify(func: &str) -> VerifyResult {
    verify_in(SRC, func)
}

fn expect_verified(func: &str) {
    let r = verify(func);
    assert!(
        matches!(r, VerifyResult::Verified),
        "{func}: a true program must verify (no over-rejection), got {r:?}"
    );
}

fn expect_counterexample(func: &str) {
    let r = verify(func);
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "{func}: a panicking / false program must be refuted, got {r:?}"
    );
}

/// Refuted on an obligation whose name carries `fragment` — pins that the
/// counterexample is the SAFETY obligation, not an incidental assertion.
fn expect_counterexample_named(func: &str, fragment: &str) {
    let r = verify(func);
    match &r {
        VerifyResult::Counterexample {
            obligation_name, ..
        } => assert!(
            obligation_name.contains(fragment),
            "{func}: refuted, but on `{obligation_name}` rather than a `{fragment}` obligation"
        ),
        other => panic!("{func}: expected a `{fragment}` counterexample, got {other:?}"),
    }
}

fn expect_not_verified(func: &str) {
    let r = verify(func);
    assert!(
        !matches!(r, VerifyResult::Verified),
        "{func}: a panicking / false program must never verify, got {r:?}"
    );
}

fn expect_error_containing(func: &str, fragment: &str) {
    let r = verify(func);
    match &r {
        VerifyResult::Error { message } => assert!(
            message.contains(fragment),
            "{func}: fail-closed Error must name `{fragment}`, got `{message}`"
        ),
        other => panic!("{func}: expected a fail-closed Error naming `{fragment}`, got {other:?}"),
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum Class {
    Verified,
    Counterexample,
    Error,
    Other,
}

fn class(r: &VerifyResult) -> Class {
    match r {
        VerifyResult::Verified => Class::Verified,
        VerifyResult::Counterexample { .. } => Class::Counterexample,
        VerifyResult::Error { .. } => Class::Error,
        _ => Class::Other,
    }
}

macro_rules! pin {
    ($test:ident, verified, $func:literal) => {
        #[test]
        fn $test() {
            expect_verified($func);
        }
    };
    ($test:ident, counterexample, $func:literal) => {
        #[test]
        fn $test() {
            expect_counterexample($func);
        }
    };
    ($test:ident, index_bounds, $func:literal) => {
        #[test]
        fn $test() {
            expect_counterexample_named($func, "index_bounds_check_");
        }
    };
    ($test:ident, not_verified, $func:literal) => {
        #[test]
        fn $test() {
            expect_not_verified($func);
        }
    };
}

// ---- R1 liars ----
pin!(
    liar01_let_borrow_param_index,
    index_bounds,
    "liar01_let_borrow_param_index"
);
pin!(
    liar02_write_through_borrow,
    index_bounds,
    "liar02_write_through_borrow"
);
pin!(
    liar03_requires_forces_oob,
    index_bounds,
    "liar03_requires_forces_oob"
);
pin!(
    liar03b_requires_forces_oob_nonvacuous,
    counterexample,
    "liar03b_requires_forces_oob_nonvacuous"
);
pin!(
    liar04_bound_not_assumed,
    not_verified,
    "liar04_bound_not_assumed"
);
pin!(liar05_slice_param, index_bounds, "liar05_slice_param");
pin!(
    liar06_vec_param_write,
    index_bounds,
    "liar06_vec_param_write"
);
// Never Verified; the solver answers `Unknown(incomplete)` on the unconstrained
// symbolic `v[i]` bound for a Vec parameter, exactly as it does for the `&v[i]`
// twin (twin table row `vec_param`). liar07b pins the refuted form.
pin!(
    liar07_vec_param_index_write,
    not_verified,
    "liar07_vec_param_index_write"
);
pin!(
    liar07b_vec_param_index_write_at_len,
    index_bounds,
    "liar07b_vec_param_index_write_at_len"
);
pin!(
    liar08_vec_local_write,
    index_bounds,
    "liar08_vec_local_write"
);
pin!(
    liar09_nested_vec_literal,
    index_bounds,
    "liar09_nested_vec_literal"
);
pin!(liar10_nested_array, index_bounds, "liar10_nested_array");
pin!(liar11_guarded, index_bounds, "liar11_guarded");
pin!(liar12_reassign_rhs, index_bounds, "liar12_reassign_rhs");
pin!(liar13a_typed_let, index_bounds, "liar13a_typed_let");
pin!(liar13b_paren_place, index_bounds, "liar13b_paren_place");
pin!(
    liar14_method_receiver,
    index_bounds,
    "liar14_method_receiver"
);
pin!(liar15_call_argument, index_bounds, "liar15_call_argument");
pin!(
    liar15b_call_argument_slice_param,
    index_bounds,
    "liar15b_call_argument_slice_param"
);
pin!(
    liar15c_call_argument_vec_param,
    index_bounds,
    "liar15c_call_argument_vec_param"
);
pin!(
    liar15d_uncontracted_call_argument,
    index_bounds,
    "liar15d_uncontracted_call_argument"
);
pin!(
    liar15e_method_call_argument,
    index_bounds,
    "liar15e_method_call_argument"
);
pin!(
    liar15f_let_bound_call_argument,
    index_bounds,
    "liar15f_let_bound_call_argument"
);
pin!(
    liar15g_struct_field_array_call_argument,
    index_bounds,
    "liar15g_struct_field_array_call_argument"
);
pin!(
    liar15h_struct_local_field_array,
    index_bounds,
    "liar15h_struct_local_field_array"
);
pin!(
    liar16_match_scrutinee,
    index_bounds,
    "liar16_match_scrutinee"
);
pin!(liar17_bare_statement, index_bounds, "liar17_bare_statement");
pin!(liar18_aggregate, index_bounds, "liar18_aggregate");
pin!(
    liar19_arith_inside_index,
    counterexample,
    "liar19_arith_inside_index"
);
pin!(
    liar_const_index_past_array_len,
    index_bounds,
    "liar_const_index_past_array_len"
);
pin!(
    liar_vec_literal_const_index_past_len,
    not_verified,
    "liar_vec_literal_const_index_past_len"
);

#[test]
fn liar20_arith_under_mut_borrow() {
    expect_counterexample_named("liar20_arith_under_mut_borrow", "overflow_check_");
}

// ---- call-argument evaluation order ----
const EVALUATION_ORDER_REJECTION: &str = "cannot be checked at the access's evaluation point";

#[test]
fn liar28_free_call_earlier_arg_effect() {
    expect_error_containing(
        "liar28_free_call_earlier_arg_effect",
        EVALUATION_ORDER_REJECTION,
    );
}

#[test]
fn liar29_method_call_later_arg_effect() {
    expect_error_containing(
        "liar29_method_call_later_arg_effect",
        EVALUATION_ORDER_REJECTION,
    );
}

pin!(
    liar30_free_call_later_arg_effect,
    index_bounds,
    "liar30_free_call_later_arg_effect"
);
pin!(
    liar31_method_call_earlier_arg_effect,
    index_bounds,
    "liar31_method_call_earlier_arg_effect"
);
pin!(
    liar32_shared_read_of_rebound_index,
    index_bounds,
    "liar32_shared_read_of_rebound_index"
);
pin!(
    liar33_slice_last_index_call_argument,
    counterexample,
    "liar33_slice_last_index_call_argument"
);
pin!(
    control19_slice_last_index_call_argument,
    verified,
    "control19_slice_last_index_call_argument"
);
pin!(
    control20_shared_read_of_rebound_index,
    verified,
    "control20_shared_read_of_rebound_index"
);
pin!(
    control21_method_call_earlier_pure_arg,
    verified,
    "control21_method_call_earlier_pure_arg"
);
pin!(
    control22_free_call_later_pure_arg,
    verified,
    "control22_free_call_later_pure_arg"
);

// ---- R2 across an invariant loop (review round 1) ----
pin!(
    liar34_loop_moves_param_index,
    counterexample,
    "liar34_loop_moves_param_index"
);
pin!(
    liar35_loop_moves_shadowed_index,
    counterexample,
    "liar35_loop_moves_shadowed_index"
);
pin!(
    liar36_loop_moves_index_arith,
    counterexample,
    "liar36_loop_moves_index_arith"
);
pin!(
    liar37_loop_moves_reassign_rhs_index,
    counterexample,
    "liar37_loop_moves_reassign_rhs_index"
);
pin!(
    liar38_loop_moves_index_read_through_alias,
    counterexample,
    "liar38_loop_moves_index_read_through_alias"
);
pin!(
    liar39_bare_loop_moves_index,
    counterexample,
    "liar39_bare_loop_moves_index"
);
pin!(
    liar40_for_range_loop_moves_index,
    counterexample,
    "liar40_for_range_loop_moves_index"
);
pin!(
    liar41_branch_loop_moves_index,
    counterexample,
    "liar41_branch_loop_moves_index"
);
pin!(
    liar42_loop_moves_cast_index,
    counterexample,
    "liar42_loop_moves_cast_index"
);

#[test]
fn liar43_loop_moves_struct_field_index() {
    expect_error_containing(
        "liar43_loop_moves_struct_field_index",
        "has no modelable scalar type to snapshot",
    );
}

pin!(
    control23_loop_moves_param_index_true_slot,
    verified,
    "control23_loop_moves_param_index_true_slot"
);
pin!(
    control24_loop_moves_index_arith_true_slot,
    verified,
    "control24_loop_moves_index_arith_true_slot"
);
pin!(
    control25_for_range_loop_true_slot,
    verified,
    "control25_for_range_loop_true_slot"
);
pin!(
    control26_borrow_after_loop_post_loop_slot,
    verified,
    "control26_borrow_after_loop_post_loop_slot"
);

// ---- free-call argument access nested in a branch / block (review round 1) ----
const CONDITIONAL_ARGUMENT_REJECTION: &str =
    "is evaluated conditionally (inside a branch, arm, block or closure of the argument)";

#[test]
fn liar44_to_53_nested_argument_access_fails_closed() {
    for func in [
        "liar44_free_call_if_arg_mut",
        "liar45_free_call_if_arg_shared",
        "liar46_free_call_match_arg",
        "liar47_free_call_block_arg_shared",
        "liar48_free_call_block_arg_mut",
        "liar49_free_call_unsafe_block_arg",
        "liar50_free_call_if_condition_arg",
        "liar51_free_call_match_guard_arg",
        "liar52_assoc_fn_if_arg",
        "liar53_free_call_nested_block_in_if_arg",
    ] {
        expect_error_containing(func, CONDITIONAL_ARGUMENT_REJECTION);
    }
}

pin!(
    liar54_method_call_if_arg,
    index_bounds,
    "liar54_method_call_if_arg"
);
pin!(
    control27_free_call_if_arg_unrelated_root,
    verified,
    "control27_free_call_if_arg_unrelated_root"
);

// ---- R3 liar ----
#[test]
fn liar21_direct_deref_of_borrow_write() {
    expect_error_containing(
        "liar21_direct_deref_of_borrow_write",
        "assignment through a dereferenced reference is unsupported",
    );
}

// ---- R1 range: fails closed exactly as the shared twin does ----
#[test]
fn liar22_range_borrow_matches_shared_twin() {
    let mut_result = verify("liar22_range_mut");
    let shared_result = verify("liar22_range_shared");
    assert!(
        !matches!(mut_result, VerifyResult::Verified),
        "`&mut s[0usize..i]` must never verify, got {mut_result:?}"
    );
    assert_eq!(
        class(&mut_result),
        class(&shared_result),
        "`&mut s[0..i]` ({mut_result:?}) and `&s[0..i]` ({shared_result:?}) must land in one class"
    );
}

// ---- loop-body index sites: the shared read is refuted, `&mut` fails closed ----
//
// An in-loop index access carries its bounds obligation, so the shared
// `&x[i]` read is refuted. The `&mut x[i]` borrow is an argument the call's
// `&mut` havoc rebinds, and the call-argument pin that renders it at its
// evaluation point is deferred inside a loop, so the post-visit rendering
// reads an unresolved receiver and fails closed. Neither may ever verify.
#[test]
fn gap23_loop_body_borrow_never_verifies() {
    let mut_result = verify("gap23_loop_body_mut");
    let shared_result = verify("gap23_loop_body_shared_read");
    assert!(
        !matches!(mut_result, VerifyResult::Verified),
        "in-loop `&mut x[i]` must never verify, got {mut_result:?}"
    );
    assert!(
        !matches!(shared_result, VerifyResult::Verified),
        "in-loop `&x[i]` must never verify, got {shared_result:?}"
    );
}

// ---- R2 liars ----
pin!(
    liar24_shadowed_index_retargets_write,
    counterexample,
    "liar24_shadowed_index_retargets_write"
);
pin!(
    liar25_reassigned_param_index_retargets_write,
    counterexample,
    "liar25_reassigned_param_index_retargets_write"
);
pin!(
    liar26_shadowed_index_arith_retargets_write,
    counterexample,
    "liar26_shadowed_index_arith_retargets_write"
);
pin!(
    liar27_index_reassigned_after_borrow,
    counterexample,
    "liar27_index_reassigned_after_borrow"
);

// ---- controls ----
pin!(
    control01_in_bounds_literal_write,
    verified,
    "control01_in_bounds_literal_write"
);
pin!(
    control02_requires_in_bounds_write,
    verified,
    "control02_requires_in_bounds_write"
);
pin!(
    control03_slice_requires_nonempty,
    verified,
    "control03_slice_requires_nonempty"
);
pin!(
    control04_vec_requires_in_bounds,
    verified,
    "control04_vec_requires_in_bounds"
);
pin!(
    control05_guarded_by_bound,
    verified,
    "control05_guarded_by_bound"
);
pin!(
    control06_call_argument_in_bounds,
    verified,
    "control06_call_argument_in_bounds"
);
pin!(
    control06b_call_argument_slice_param,
    verified,
    "control06b_call_argument_slice_param"
);
pin!(
    control06c_call_argument_vec_param,
    verified,
    "control06c_call_argument_vec_param"
);
pin!(
    control06d_uncontracted_call_argument,
    verified,
    "control06d_uncontracted_call_argument"
);
pin!(
    control06e_method_call_argument,
    verified,
    "control06e_method_call_argument"
);
pin!(
    control06f_let_bound_call_argument,
    verified,
    "control06f_let_bound_call_argument"
);
pin!(
    control06g_struct_field_array_call_argument,
    verified,
    "control06g_struct_field_array_call_argument"
);
pin!(
    control06h_struct_local_field_array,
    verified,
    "control06h_struct_local_field_array"
);
pin!(
    control07_match_scrutinee_in_bounds,
    verified,
    "control07_match_scrutinee_in_bounds"
);
pin!(
    control08_reassign_rhs_in_bounds,
    verified,
    "control08_reassign_rhs_in_bounds"
);
pin!(
    control09_corpus_array_index,
    verified,
    "control09_corpus_array_index"
);
pin!(
    control10_corpus_slice_index,
    verified,
    "control10_corpus_slice_index"
);
pin!(
    control11_corpus_vec_index,
    verified,
    "control11_corpus_vec_index"
);
pin!(
    liar11b_corpus_vec_index_false_tail,
    counterexample,
    "liar11b_corpus_vec_index_false_tail"
);
pin!(
    control12_corpus_vec_push_index,
    verified,
    "control12_corpus_vec_push_index"
);
pin!(
    control14_shadowed_index_true_slot,
    verified,
    "control14_shadowed_index_true_slot"
);
pin!(
    control15_let_local_index,
    verified,
    "control15_let_local_index"
);
pin!(
    control16_index_reassigned_after_borrow_true_slot,
    verified,
    "control16_index_reassigned_after_borrow_true_slot"
);
pin!(
    control17_param_reassigned_after_borrow,
    verified,
    "control17_param_reassigned_after_borrow"
);
pin!(
    control18_literal_arith_index,
    verified,
    "control18_literal_arith_index"
);

#[test]
fn control13_blocked_rows_keep_their_messages() {
    for func in [
        "control13a_blocked_vec_index_tuple_field",
        "control13b_blocked_vec_nested_index",
        "control13c_blocked_vec_nested_index_oob",
    ] {
        expect_error_containing(
            func,
            "assignment through a dereferenced reference is unsupported",
        );
    }
    expect_error_containing(
        "control13d_blocked_vec_literal_index_oob",
        "Vec literal index is out of bounds",
    );
}

// ----------------------------------------------------------------------------
// Twin table: each `&mut` shape lands in the SAME verdict class as its `&`
// twin. `@` is the borrow operator (`&mut ` / `&`) and `NOOP` the matching
// sink; `expected` is the class both must reach.
// ----------------------------------------------------------------------------

#[derive(Debug, Clone, Copy)]
enum Expect {
    Exactly(Class),
    /// Any non-`Verified` class, the same on both twins.
    NotVerified,
}

struct Twin {
    name: &'static str,
    attrs: &'static str,
    params: &'static str,
    body: &'static str,
    expected: Expect,
}

const TWINS: &[Twin] = &[
    Twin {
        name: "let_borrow",
        attrs: "",
        params: "i: usize",
        body: "let mut x = [1u8, 2u8, 3u8]; let _r = @x[i];",
        expected: Expect::Exactly(Class::Counterexample),
    },
    Twin {
        name: "typed_let",
        attrs: "",
        params: "i: usize",
        body: "let mut x = [1u8, 2u8, 3u8]; let _r: @u8 = @x[i];",
        expected: Expect::Exactly(Class::Counterexample),
    },
    Twin {
        name: "paren_place",
        attrs: "",
        params: "i: usize",
        body: "let mut x = [1u8, 2u8, 3u8]; let _r = @(x[i]);",
        expected: Expect::Exactly(Class::Counterexample),
    },
    Twin {
        name: "method_receiver",
        attrs: "",
        params: "i: usize",
        body: "let mut x = [1u8, 2u8, 3u8]; let _b = (@x[i]).clone();",
        expected: Expect::Exactly(Class::Counterexample),
    },
    Twin {
        name: "call_argument",
        attrs: "",
        params: "i: usize",
        body: "let mut x = [1u8, 2u8, 3u8]; NOOP(@x[i]);",
        expected: Expect::Exactly(Class::Counterexample),
    },
    Twin {
        name: "match_scrutinee",
        attrs: "",
        params: "i: usize",
        body: "let mut x = [1u8, 2u8, 3u8]; match @x[i] { _ => {} }",
        expected: Expect::Exactly(Class::Counterexample),
    },
    Twin {
        name: "bare_statement",
        attrs: "",
        params: "i: usize",
        body: "let mut x = [1u8, 2u8, 3u8]; @x[i];",
        expected: Expect::Exactly(Class::Counterexample),
    },
    Twin {
        name: "aggregate",
        attrs: "",
        params: "i: usize",
        body: "let mut x = [1u8, 2u8, 3u8]; let mut y = 0u8; let _t = (@x[i], @y);",
        expected: Expect::Exactly(Class::Counterexample),
    },
    Twin {
        name: "arith_inside_index",
        attrs: "",
        params: "a: usize, b: usize",
        body: "let mut x = [1u8, 2u8, 3u8]; let _r = @x[(a + b) % 3usize];",
        expected: Expect::Exactly(Class::Counterexample),
    },
    Twin {
        name: "arith_under_borrow",
        attrs: "",
        params: "a: u8, b: u8",
        body: "let _r = @(a + b);",
        expected: Expect::Exactly(Class::Counterexample),
    },
    Twin {
        name: "slice_param",
        attrs: "",
        params: "s: @[u8]",
        body: "let _r = @s[0usize];",
        expected: Expect::Exactly(Class::Counterexample),
    },
    Twin {
        name: "vec_param",
        attrs: "",
        params: "v: @Vec<u8>, i: usize",
        body: "let _r = @v[i];",
        // The solver answers Unknown(incomplete) on this bound for both kinds.
        expected: Expect::NotVerified,
    },
    Twin {
        name: "vec_param_literal_index",
        attrs: "",
        params: "v: @Vec<u8>",
        body: "let _r = @v[0usize];",
        expected: Expect::Exactly(Class::Counterexample),
    },
    Twin {
        name: "slice_param_call_argument",
        attrs: "",
        params: "s: @[u8]",
        body: "NOOP(@s[0usize]);",
        expected: Expect::Exactly(Class::Counterexample),
    },
    Twin {
        name: "slice_param_method_argument",
        attrs: "",
        params: "h: &H, s: @[u8]",
        body: "h.METH(@s[0usize]);",
        expected: Expect::Exactly(Class::Counterexample),
    },
    Twin {
        name: "slice_param_let_bound_call",
        attrs: "",
        params: "s: @[u8]",
        body: "let _u = NOOP(@s[0usize]);",
        expected: Expect::Exactly(Class::Counterexample),
    },
    Twin {
        name: "struct_local_field_array",
        attrs: "",
        params: "i: usize",
        body: "let mut o = S3 { arr: [1u8, 2u8, 3u8] }; let _r = @o.arr[i];",
        expected: Expect::Exactly(Class::Counterexample),
    },
    Twin {
        name: "struct_param_field_array",
        attrs: "",
        params: "o: @S3, i: usize",
        body: "let _r = @o.arr[i];",
        expected: Expect::Exactly(Class::Counterexample),
    },
    Twin {
        name: "vec_local",
        attrs: "",
        params: "i: usize",
        body: "let mut v = vec![1u8, 2u8]; let _r = @v[i];",
        expected: Expect::Exactly(Class::Counterexample),
    },
    Twin {
        name: "nested_vec_literal",
        attrs: "",
        params: "",
        body: "let mut v = vec![vec![1u64, 2u64, 3u64], vec![4u64, 5u64], vec![6u64]]; let _r = @v[2][1];",
        expected: Expect::Exactly(Class::Counterexample),
    },
    Twin {
        name: "nested_array",
        attrs: "",
        params: "i: usize",
        body: "let mut x = [[1u8, 2u8], [3u8, 4u8]]; let _r = @x[0usize][i];",
        expected: Expect::Exactly(Class::Counterexample),
    },
    Twin {
        name: "guarded",
        attrs: "",
        params: "i: usize, c: bool",
        body: "let mut x = [1u8, 2u8, 3u8]; if c { let _r = @x[i]; }",
        expected: Expect::Exactly(Class::Counterexample),
    },
    Twin {
        name: "reassign_rhs",
        attrs: "",
        params: "i: usize",
        body: "let mut x = [1u8, 2u8, 3u8]; let mut y = 0u8; let mut r = @y; r = @x[i];",
        expected: Expect::Exactly(Class::Counterexample),
    },
    Twin {
        name: "control_let_borrow",
        attrs: "#[trust_vc::requires(i < 3usize)]",
        params: "i: usize",
        body: "let mut x = [1u8, 2u8, 3u8]; let _r = @x[i];",
        expected: Expect::Exactly(Class::Verified),
    },
    Twin {
        name: "control_call_argument",
        attrs: "#[trust_vc::requires(i < 3usize)]",
        params: "i: usize",
        body: "let mut x = [1u8, 2u8, 3u8]; NOOP(@x[i]);",
        expected: Expect::Exactly(Class::Verified),
    },
    Twin {
        name: "control_match_scrutinee",
        attrs: "#[trust_vc::requires(i < 3usize)]",
        params: "i: usize",
        body: "let mut x = [1u8, 2u8, 3u8]; match @x[i] { _ => {} }",
        expected: Expect::Exactly(Class::Verified),
    },
    Twin {
        name: "control_slice_param_call_argument",
        attrs: "#[trust_vc::requires(s.len() > 0usize)]",
        params: "s: @[u8]",
        body: "NOOP(@s[0usize]);",
        expected: Expect::Exactly(Class::Verified),
    },
    Twin {
        name: "control_slice_param_method_argument",
        attrs: "#[trust_vc::requires(s.len() > 0usize)]",
        params: "h: &H, s: @[u8]",
        body: "h.METH(@s[0usize]);",
        expected: Expect::Exactly(Class::Verified),
    },
    Twin {
        name: "control_struct_param_field_array",
        attrs: "#[trust_vc::requires(i < 3usize)]",
        params: "o: @S3, i: usize",
        body: "let _r = @o.arr[i];",
        expected: Expect::Exactly(Class::Verified),
    },
    Twin {
        name: "control_guarded",
        attrs: "",
        params: "i: usize",
        body: "let mut x = [1u8, 2u8, 3u8]; if i < 3usize { let _r = @x[i]; }",
        expected: Expect::Exactly(Class::Verified),
    },
    Twin {
        name: "control_arith_under_borrow",
        attrs: "#[trust_vc::requires(a < 100u8 && b < 100u8)]",
        params: "a: u8, b: u8",
        body: "let _r = @(a + b);",
        expected: Expect::Exactly(Class::Verified),
    },
];

fn render_twin(twin: &Twin, borrow: &str, kind: &str) -> String {
    format!(
        "{attrs}\n#[trust_vc::ensures(true)]\nfn twin_{name}_{kind}({params}) {{\n    {body}\n}}\n",
        attrs = twin.attrs,
        name = twin.name,
        params = twin.params.replace('@', borrow),
        body = twin
            .body
            .replace('@', borrow)
            .replace("NOOP", &format!("noop_{kind}"))
            .replace("METH", &format!("m_{kind}")),
    )
}

fn twin_src() -> &'static str {
    static SRC: OnceLock<String> = OnceLock::new();
    SRC.get_or_init(|| {
        let mut src = String::from(
            "#![allow(dead_code, unused_mut, unused_variables, unused_assignments, unused_must_use)]\n\n\
             #[trust_vc::ensures(true)]\nfn noop_mut(_r: &mut u8) {}\n\n\
             #[trust_vc::ensures(true)]\nfn noop_shared(_r: &u8) {}\n\n\
             struct H;\n\n\
             impl H {\n\
             \x20   #[trust_vc::ensures(true)]\n    fn m_mut(&self, _r: &mut u8) {}\n\n\
             \x20   #[trust_vc::ensures(true)]\n    fn m_shared(&self, _r: &u8) {}\n}\n\n\
             struct S3 {\n    arr: [u8; 3],\n}\n\n",
        );
        for twin in TWINS {
            src.push_str(&render_twin(twin, "&mut ", "mut"));
            src.push_str(&render_twin(twin, "&", "shared"));
        }
        src
    })
}

#[test]
fn twin_table_mut_borrow_matches_shared_borrow() {
    let mut failures = Vec::new();
    for twin in TWINS {
        let mut_fn = format!("twin_{}_mut", twin.name);
        let shared_fn = format!("twin_{}_shared", twin.name);
        let mut_result = verify_in(twin_src(), &mut_fn);
        let shared_result = verify_in(twin_src(), &shared_fn);
        let (m, s) = (class(&mut_result), class(&shared_result));
        let expected_holds = match twin.expected {
            Expect::Exactly(class) => m == class,
            Expect::NotVerified => m != Class::Verified,
        };
        if m != s || !expected_holds {
            failures.push(format!(
                "{}: expected {:?}; &mut -> {mut_result:?}; & -> {shared_result:?}",
                twin.name, twin.expected
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "twin table mismatches:\n{}",
        failures.join("\n")
    );
}
