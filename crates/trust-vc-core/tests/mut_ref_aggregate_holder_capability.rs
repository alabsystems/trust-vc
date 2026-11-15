// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY + SOUNDNESS PIN (mut_refs `test_mut_ref_in_pair` /
//! `control_flow_conditional_with_pair` / `test_moves_via_let_decl`,
//! 2026-09-14): a tuple / struct-literal local HOLDING `&mut` borrows of
//! scalar `let` locals (`let h = (&mut x, &mut y);`, `let h = S { x: &mut u,
//! y: 70u64 };`) is a tracked HOLDER when a whole-body syntactic scan admits
//! every use of it. This is the HOLDER-ONLY increment: it carries no
//! value-lane / block-exit change for holder-free programs, and every case
//! below either declares or uses a holder, or (l14, g4) pins a holder
//! boundary on a holder-free twin.
//!
//! Five model changes, for scan-admitted names only: (1) the borrow-time
//! invalidation of the holder's roots is suppressed; (2) `*h.m = v` is modeled
//! as `root = v` through the existing scalar `&mut` Local arm; (3) `*h.m` /
//! `h.m` reads resolve (the root's CURRENT binding / the construction-time
//! constant snapshot); (4) `let h2 = h;` copies the holder and poisons `h`;
//! (5) a holder root's exact `if` join merge survives the deref-write region
//! exit (not for a root with a live bare `&mut` alias — l14).
//!
//! Admission (`mut_ref_holder_candidates`) is STRUCTURAL: a holder write
//! `*h.m = v` is admitted only as a semicolon statement whose enclosing chain
//! up to the body is made of statement-position blocks (the body; the then /
//! else blocks of a statement `if`, else-if chains included; the block /
//! bare-assignment arms of a statement `match`; a plain / `unsafe` block
//! statement). A write in any expression position (an `if` condition, a
//! `match` scrutinee / guard, a `let` initializer, an assignment RHS, a macro
//! argument, a closure, a value-position / labelled block, a non-unit tail, a
//! loop body, an operand, a parenthesized assignment) refuses the holder and
//! the body keeps HEAD's verbatim `assignment through a dereferenced reference
//! is unsupported` refusal (`SRC_R3` holder probes, `SRC_R4` r4g1-r4g16).
//! Every other holder disqualifier accumulated over five adversarial review
//! rounds is pinned: holder escapes (call / method arguments, reborrows,
//! closures, destructuring, `old()`), component rebinds, nested aggregates,
//! use after move, shadowed / reassigned / doubly-held roots, a method
//! receiver rooted at a holder root (g27 / g28), a function-local
//! `macro_rules!` (l26-l28, g24), `ref` / `ref mut` bindings and raw borrows
//! (l31-l35, g25 / g26), a raw or non-ASCII identifier (l62-l68, g57-g59), a
//! struct holder outside the body's own block (a `Drop` impl may write the
//! root when a nested scope ends: l54-l61, g55 / g56, c18, now gated), a nested
//! `const` / `static` / `fn` / `struct` / `use` item named like a
//! pattern-bound name or a `#[cfg]` / `#[cfg_attr]` attribute (`SRC_R3`
//! r3c / r3n), and a plain member that is not a `bool` or SUFFIXED integer
//! literal (l29 / l30; `SRC_R4F` g1-g4, l1), and an UNSUFFIXED integer
//! literal anywhere in the body (`SRC_R4F` split-l1 / split-g1: an untyped
//! literal reaches the encoder without a width).
//!
//! Review of the holder-only split (`SRC_R6`, `SRC_R6_CFG`): HEAD refuses
//! every body that writes through a holder, so its modelling gaps on UNRELATED
//! locals were unreachable there; lifting that refusal made them new false
//! `Verified`s. A body admits no holder when any effect sits outside the
//! statement walk — an assignment / compound assignment outside a statement of
//! a statement-position block (an `if` condition / `match` scrutinee block, a
//! `let` initializer, a non-unit tail block, an assignment RHS, a macro
//! argument, a loop body), a method call (autoref writes), a closure / `async`
//! block, a labelled block or any `break` / `continue`, a `&mut` borrow other
//! than a `let` initializer or `let` literal component, a macro other than a
//! parseable body-lane spec macro statement (a spec assertion nested in an
//! assertion argument) — and when the SOURCE FILE carries a `cfg` /
//! `cfg_attr` attribute outside function bodies (a compiled-out const was the
//! definition the model resolved). r6-l1..l24 are those probes, all refused;
//! r6-c1 / r6-l23 pin that a plain statement write beside a holder write
//! keeps the lane.
//!
//! Every verdict below was MEASURED on the holder-only build (stock lane);
//! the gated needles are the HEAD refusal texts. Holder-free cases that pinned
//! the value-lane / block-exit hardening of the dev increment are not here —
//! they belong to that later, separate increment.
//!
//! Review round 2 of the split (`SRC_R7`, `SRC_R7_MOD`,
//! `SRC_R7_CONST_GENERIC`, `SRC_R7_DROP`, 2026-09-15): HEAD modelling gaps
//! still reachable in a body that passed every rule above, closed by
//! NARROWING admission only. A body admits no holder when it contains ANY
//! nested item (a block `const` / `static` read before its declaration
//! resolved to the file-level item: r7-l1..l5), any `let` expression (an
//! `if let` scrutinee had no safety obligation, and a write to a `mut` pattern
//! binding hit the outer local: r7-l12 / l13), any call expression (a
//! contract-less callee's overflow never reached the call site: r7-l14), or an
//! assignment whose left-hand side is not a bare identifier or a dereference
//! (a field / tuple-field / `_` assignment had no RHS safety obligation:
//! r7-l9..l11). A function admits no holder when its tokens, joined with the
//! file items it names, mix integer types or mention `self` / `Self` (a
//! literal-derived `i32` product was encoded at an `i8` / aliased `u8`
//! variable's width: r7-l6..l8). A file admits no holder when it carries a
//! `mod` item (bare-name const registry: r7-l15), a `const` generic parameter
//! (r7-l16), a `Drop` token (drop glue is never run: r7-l17; the round-2 `Drop`
//! probes moved to `SRC_DROP`, and control c18 is now gated), or an
//! item-position macro outside function bodies. Control r3n-n5 (a nested
//! `const` declared before its use) is now gated too; r7-c1 / r7-l18 pin that
//! the `SRC_R7` fixture is not refused wholesale.
//!
//! 209 cases: 16 controls, 104 liars, 89 gated.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_mrah_{}_{}.rs", std::process::id(), tmp_id));
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
use std::ops::AddAssign;

struct RefPair<'a> {
    x: &'a mut u64,
    y: u64,
}

struct Pair<'a>(&'a mut u64, u64);

fn consume(_t: (&mut u64, u64)) {}

fn bump(v: &mut u64) {
    *v = 0u64;
}

fn f(v: u64) -> u64 {
    v
}

fn consume_set(t: (&mut u64, u64)) {
    *t.0 = 9u64;
}

fn set9(v: &mut u64) {
    *v = 9u64;
}

// CONTROL c1: corpus case 1 (struct holder) plus a deref read-back.
#[trust_vc::ensures(true)]
fn struct_holder_write_and_plain_member_read_verifies() {
    let mut u: u64 = 20u64;
    let u_ref = RefPair {
        x: &mut u,
        y: 70u64,
    };

    *u_ref.x = 30u64;

    trust_vc::assert!(u == 30u64);
    trust_vc::assert!(u_ref.y == 70u64);
    trust_vc::assert!(*u_ref.x == 30u64);
}

// CONTROL c2: corpus case 2 (tuple holder written on both branches).
#[trust_vc::ensures(true)]
fn tuple_holder_branch_writes_join_verifies(b: bool) {
    let mut x: u64 = 0u64;
    let mut y: u64 = 0u64;
    let x_ref = (&mut x, &mut y);

    if b {
        *x_ref.0 = 20u64;
    } else {
        *x_ref.1 = 30u64;
    }

    trust_vc::assert!(x == 20u64 || y == 30u64);
}

// CONTROL c3: corpus case 3 (tuple holder moved, one root written, sibling untouched).
#[trust_vc::ensures(true)]
fn tuple_holder_move_write_sibling_unchanged_verifies() {
    let mut x: u64 = 0u64;
    let mut y: u64 = 0u64;
    let refs = (&mut x, &mut y);
    let refs2 = refs;

    *refs2.0 = 30u64;

    trust_vc::assert!(x == 30u64);
    trust_vc::assert!(y == 0u64);
}

// CONTROL c4: sequential writes, an RHS read through another component.
#[trust_vc::ensures(true)]
fn tuple_holder_sequential_writes_and_cross_read_verify() {
    let mut x: u64 = 0u64;
    let mut y: u64 = 0u64;
    let t = (&mut x, &mut y);
    *t.0 = 1u64;
    *t.1 = 2u64;
    *t.0 = *t.1 + 1u64;
    trust_vc::assert!(x == 3u64);
    trust_vc::assert!(y == 2u64);
    trust_vc::assert!(*t.0 == 3u64);
}

// CONTROL c5: else-less branch write joins against the pre-`if` value.
#[trust_vc::ensures(true)]
fn tuple_holder_then_only_branch_join_verifies(b: bool) {
    let mut x: u64 = 0u64;
    let mut y: u64 = 0u64;
    let t = (&mut x, &mut y);
    if b {
        *t.0 = 20u64;
    }
    trust_vc::assert!(x == 20u64 || x == 0u64);
    trust_vc::assert!(y == 0u64);
}

// CONTROL c6: a straight-line write, then a branch write (pins the self-mark strip).
#[trust_vc::ensures(true)]
fn holder_straight_write_then_branch_write_join_verifies(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    *t.0 = 1u64;
    if b {
        *t.0 = 2u64;
    }
    trust_vc::assert!(x == 1u64 || x == 2u64);
}

// CONTROL c7: holder declared INSIDE the branch (root recorded by `&mut x`).
#[trust_vc::ensures(true)]
fn holder_declared_inside_branch_verifies(b: bool) {
    let mut x: u64 = 0u64;
    if b {
        let t = (&mut x, 1u64);
        *t.0 = 5u64;
    }
    trust_vc::assert!(x == 5u64 || x == 0u64);
}

// CONTROL c8: struct holder moved, then written through the move target.
#[trust_vc::ensures(true)]
fn struct_holder_moved_then_written_verifies() {
    let mut u: u64 = 20u64;
    let u_ref = RefPair {
        x: &mut u,
        y: 70u64,
    };
    let u2 = u_ref;
    *u2.x = 5u64;
    trust_vc::assert!(u == 5u64);
    trust_vc::assert!(u2.y == 70u64);
}

// CONTROL c9: reads through the holder after a join see the merged root.
#[trust_vc::ensures(true)]
fn holder_read_through_after_join_verifies(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        *t.0 = 20u64;
    } else {
        *t.0 = 30u64;
    }
    trust_vc::assert!(*t.0 == 20u64 || *t.0 == 30u64);
}

// CONTROL c10: a holder function with a RETURN value (the return lane runs the scan).
#[trust_vc::ensures(result == 4u64)]
fn holder_function_with_return_value_verifies(b: bool) -> u64 {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    *t.0 = 4u64;
    x
}

// LIAR l1: the wrong written value.
#[trust_vc::ensures(true)]
fn struct_holder_wrong_written_value() {
    let mut u: u64 = 20u64;
    let u_ref = RefPair {
        x: &mut u,
        y: 70u64,
    };
    *u_ref.x = 30u64;
    trust_vc::assert!(u == 31u64);
}

// LIAR l2: the stale pre-borrow value.
#[trust_vc::ensures(true)]
fn struct_holder_stale_preborrow_value() {
    let mut u: u64 = 20u64;
    let u_ref = RefPair {
        x: &mut u,
        y: 70u64,
    };
    *u_ref.x = 30u64;
    trust_vc::assert!(u == 20u64);
}

// LIAR l3: the plain member's wrong value.
#[trust_vc::ensures(true)]
fn struct_holder_plain_member_wrong() {
    let mut u: u64 = 20u64;
    let u_ref = RefPair {
        x: &mut u,
        y: 70u64,
    };
    *u_ref.x = 30u64;
    trust_vc::assert!(u_ref.y == 71u64);
}

// LIAR l4: only one disjunct of the branch join.
#[trust_vc::ensures(true)]
fn tuple_holder_branch_then_disjunct_only(b: bool) {
    let mut x: u64 = 0u64;
    let mut y: u64 = 0u64;
    let x_ref = (&mut x, &mut y);
    if b {
        *x_ref.0 = 20u64;
    } else {
        *x_ref.1 = 30u64;
    }
    trust_vc::assert!(x == 20u64);
}

// LIAR l5: both branch writes assumed at once.
#[trust_vc::ensures(true)]
fn tuple_holder_branch_both_written(b: bool) {
    let mut x: u64 = 0u64;
    let mut y: u64 = 0u64;
    let x_ref = (&mut x, &mut y);
    if b {
        *x_ref.0 = 20u64;
    } else {
        *x_ref.1 = 30u64;
    }
    trust_vc::assert!(x == 20u64 && y == 30u64);
}

// LIAR l6: the untouched sibling root assumed changed.
#[trust_vc::ensures(true)]
fn tuple_holder_move_sibling_root_changed() {
    let mut x: u64 = 0u64;
    let mut y: u64 = 0u64;
    let refs = (&mut x, &mut y);
    let refs2 = refs;
    *refs2.0 = 30u64;
    trust_vc::assert!(y == 30u64);
}

// LIAR l7: the written root's stale value after a move.
#[trust_vc::ensures(true)]
fn tuple_holder_move_stale_root() {
    let mut x: u64 = 0u64;
    let mut y: u64 = 0u64;
    let refs = (&mut x, &mut y);
    let refs2 = refs;
    *refs2.0 = 30u64;
    trust_vc::assert!(x == 0u64);
}

// LIAR l8: a stale deref read after a write.
#[trust_vc::ensures(true)]
fn stale_deref_read_after_write() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    *t.0 = 5u64;
    trust_vc::assert!(*t.0 == 0u64);
}

// LIAR l9: the first of two sequential writes.
#[trust_vc::ensures(true)]
fn sequential_writes_first_value() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    *t.0 = 1u64;
    *t.0 = 2u64;
    trust_vc::assert!(x == 1u64);
}

// LIAR l10: a branch-local holder write assumed never to happen.
#[trust_vc::ensures(true)]
fn branch_local_holder_unconditional_pre_value(b: bool) {
    let mut x: u64 = 0u64;
    if b {
        let t = (&mut x, 1u64);
        *t.0 = 5u64;
    }
    trust_vc::assert!(x == 0u64);
}

// LIAR l11: a plain-block write, then a root read (region havoc must run).
#[trust_vc::ensures(true)]
fn plain_block_write_then_root_read_never_verifies() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    {
        *t.0 = 1u64;
    }
    trust_vc::assert!(x == 1u64);
}

// LIAR l12: a match-arm write, then a stale root read.
#[trust_vc::ensures(true)]
fn match_arm_write_then_stale_read_never_verifies(k: u64) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    match k {
        0u64 => {
            *t.0 = 1u64;
        }
        _ => {}
    }
    trust_vc::assert!(x == 0u64);
}

// LIAR l13: a read through the poisoned move source.
#[trust_vc::ensures(true)]
fn moved_from_holder_read_never_verifies() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    let t2 = t;
    *t2.0 = 30u64;
    trust_vc::assert!(*t.0 == 30u64);
}

// LIAR l14: a bare alias mixed with a direct write across a join (no holder):
// the keep-exact join must never apply to a root with a bare `&mut` alias.
#[trust_vc::ensures(true)]
fn alias_mix_branch_join_never_verifies(c: bool) {
    let mut x: u64 = 0u64;
    let r = &mut x;
    if c {
        *r = 2u64;
    } else {
        x = 1u64;
    }
    trust_vc::assert!(x == 1u64 || x == 0u64);
}

// LIAR l15: a value-position block whose `if` writes through the holder.
#[trust_vc::ensures(true)]
fn value_block_if_write_never_verifies(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    let v: u64 = {
        if b {
            *t.0 = 20u64;
        }
        x
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR l16: the holder escapes into a call (not admitted; the borrow havoc stays).
#[trust_vc::ensures(true)]
fn holder_escaping_into_call_never_verifies() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    consume(t);
    trust_vc::assert!(x == 0u64);
}

// GATED g1: compound write through a holder.
#[trust_vc::ensures(true)]
fn compound_write_through_holder() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    *t.0 += 1u64;
    trust_vc::assert!(x == 1u64);
}

// GATED g2: loop-body write through a local holder.
#[trust_vc::ensures(true)]
fn loop_body_write_through_local_holder() {
    let mut x: u64 = 0u64;
    let mut y: u64 = 0u64;
    let t = (&mut x, &mut y);
    loop {
        *t.0 = 5u64;
        return;
    }
}

// GATED g3: by-value tuple-of-`&mut` PARAM (mut_refs_loops pin).
#[trust_vc::ensures(true)]
fn param_tuple_holder(pair: (&mut u64, &mut u64)) {
    loop {
        *pair.0 = 5u64;
        return;
    }
}

// GATED g4: field borrow of a plain tuple (mut_refs_closures pin).
#[trust_vc::ensures(true)]
fn field_borrow_of_plain_tuple() {
    let mut x = (0u64, 1u64);
    let fst: &mut u64 = &mut x.0;
    *fst = 10u64;
    trust_vc::assert!(x.0 == 10u64);
}

// GATED g5: tuple literal deref without a `let` (mut_refs_temporaries pin).
#[trust_vc::ensures(true)]
fn tuple_literal_deref_without_let() {
    let mut a = 0u64;
    let mut b = 0u64;
    *(&mut a, &mut b).0 = 5u64;
    trust_vc::assert!(a == 5u64);
}

// GATED g6: `old()` over a held reference (mut_refs_old pin).
#[trust_vc::ensures(true)]
fn old_over_held_reference() {
    let mut left = 0u64;
    let mut right = 10u64;
    let pair = (&mut left, &mut right);
    *pair.0 = 5u64;
    trust_vc::assert!(*old(pair.0) == 0u64);
}

// GATED g7: nested aggregate projection.
#[trust_vc::ensures(true)]
fn nested_aggregate_projection() {
    let mut x: u64 = 0u64;
    let t = ((&mut x, 1u64), 2u64);
    *t.0.0 = 5u64;
    trust_vc::assert!(x == 5u64);
}

// GATED g8: a component retarget, then a write.
#[trust_vc::ensures(true)]
fn component_retarget_then_write() {
    let mut x: u64 = 0u64;
    let mut y: u64 = 0u64;
    let mut z: u64 = 0u64;
    let mut t = (&mut x, &mut y);
    t.0 = &mut z;
    *t.0 = 9u64;
    trust_vc::assert!(z == 9u64);
}

// GATED g9: a plain member rebind, then a write.
#[trust_vc::ensures(true)]
fn plain_member_rebind_then_write() {
    let mut u: u64 = 20u64;
    let mut u_ref = RefPair {
        x: &mut u,
        y: 70u64,
    };
    u_ref.y = 71u64;
    *u_ref.x = 1u64;
    trust_vc::assert!(u == 1u64);
}

// GATED g10: the holder passed to a call, then written.
#[trust_vc::ensures(true)]
fn holder_passed_to_call_then_write() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    consume(t);
    *t.0 = 1u64;
    trust_vc::assert!(x == 1u64);
}

// GATED g11: a held reference passed to a call, then written.
#[trust_vc::ensures(true)]
fn held_ref_passed_to_call_then_write() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    bump(t.0);
    *t.0 = 1u64;
    trust_vc::assert!(x == 1u64);
}

// GATED g12: a reborrow of a held reference.
#[trust_vc::ensures(true)]
fn reborrow_of_held_ref() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    let r = &mut *t.0;
    *r = 5u64;
    trust_vc::assert!(x == 5u64);
}

// GATED g13: the holder captured by a closure.
#[trust_vc::ensures(true)]
fn holder_in_closure() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    let c = || {
        *t.0 = 1u64;
    };
    c();
    trust_vc::assert!(x == 1u64);
}

// GATED g14: a shadowed root (bound twice in the body).
#[trust_vc::ensures(true)]
fn shadowed_root() {
    let mut x: u64 = 0u64;
    let t = (&mut x,);
    {
        let x: u64 = 5u64;
        *t.0 = 9u64;
        trust_vc::assert!(x == 5u64);
    }
}

// GATED g15: destructured components.
#[trust_vc::ensures(true)]
fn destructured_components() {
    let mut x: u64 = 0u64;
    let mut y: u64 = 0u64;
    let (a, b) = (&mut x, &mut y);
    *a = 5u64;
    *b = 6u64;
    trust_vc::assert!(x == 5u64);
}

// GATED g16: the root assigned by name while the holder is live.
#[trust_vc::ensures(true)]
fn direct_root_write_while_live() {
    let mut x: u64 = 0u64;
    let t = (&mut x,);
    x = 5u64;
    *t.0 = 6u64;
    trust_vc::assert!(x == 6u64);
}

// GATED g17: two holders sharing a root.
#[trust_vc::ensures(true)]
fn two_holders_share_a_root() {
    let mut x: u64 = 0u64;
    let c = (&mut x,);
    let d = (&mut x,);
    *d.0 = 1u64;
    trust_vc::assert!(x == 1u64);
}

// GATED g18: a tuple-struct constructor is a call, not a literal.
#[trust_vc::ensures(true)]
fn tuple_struct_ctor_holder() {
    let mut x: u64 = 0u64;
    let c = Pair(&mut x, 1u64);
    *c.0 = 1u64;
    trust_vc::assert!(x == 1u64);
}

// GATED g19: a non-value-like plain component.
#[trust_vc::ensures(true)]
fn non_value_like_plain_component() {
    let mut x: u64 = 0u64;
    let t = (&mut x, f(1u64));
    *t.0 = 5u64;
    trust_vc::assert!(x == 5u64);
}

// GATED g20: a deref of a plain member is not a whitelisted shape.
#[trust_vc::ensures(true)]
fn deref_of_plain_member() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    *t.0 = 2u64;
    trust_vc::assert!(*t.1 == 1u64);
}

// GATED g21: a move inside a branch is not admitted (a move must be a direct
// statement of the declaring block), so the write through the move target `q`
// refuses (the fixture observes `* q . 0`; `t` itself is never written).
#[trust_vc::ensures(true)]
fn move_inside_branch(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        let q = t;
        *q.0 = 5u64;
    }
    trust_vc::assert!(x == 5u64 || x == 0u64);
}

// GATED g22: a write through the poisoned move source.
#[trust_vc::ensures(true)]
fn use_after_move_write() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    let t2 = t;
    *t.0 = 1u64;
    trust_vc::assert!(x == 1u64);
}

// GATED g23: a bare use of the holder as a call argument AFTER an otherwise
// admitted write and plain-member read refuses admission of the whole name, so
// the first write `*t.0 = 2u64` already refuses.
#[trust_vc::ensures(true)]
fn holder_call_argument_after_writes() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    *t.0 = 2u64;
    trust_vc::assert!(t.1 == 1u64 && x == 2u64);
    consume(t);
}

// LIAR l18 (c5): the then-only branch assumed always taken.
#[trust_vc::ensures(true)]
fn then_only_branch_assumed_taken(b: bool) {
    let mut x: u64 = 0u64;
    let mut y: u64 = 0u64;
    let t = (&mut x, &mut y);
    if b {
        *t.0 = 20u64;
    }
    trust_vc::assert!(x == 20u64);
}

// LIAR l19 (c5): the then-only branch assumed never taken.
#[trust_vc::ensures(true)]
fn then_only_branch_assumed_skipped(b: bool) {
    let mut x: u64 = 0u64;
    let mut y: u64 = 0u64;
    let t = (&mut x, &mut y);
    if b {
        *t.0 = 20u64;
    }
    trust_vc::assert!(x == 0u64);
}

// LIAR l20 (c6): the branch overwrite assumed unconditional.
#[trust_vc::ensures(true)]
fn straight_then_branch_assumed_overwrite(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    *t.0 = 1u64;
    if b {
        *t.0 = 2u64;
    }
    trust_vc::assert!(x == 2u64);
}

// LIAR l21 (c6): the pre-borrow value assumed to survive the straight write.
#[trust_vc::ensures(true)]
fn straight_then_branch_stale(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    *t.0 = 1u64;
    if b {
        *t.0 = 2u64;
    }
    trust_vc::assert!(x == 1u64 || x == 0u64);
}

// LIAR l22 (c8): the stale root after a struct-holder move and write.
#[trust_vc::ensures(true)]
fn struct_move_stale_root() {
    let mut u: u64 = 20u64;
    let u_ref = RefPair {
        x: &mut u,
        y: 70u64,
    };
    let u2 = u_ref;
    *u2.x = 5u64;
    trust_vc::assert!(u == 20u64);
}

// LIAR l23 (c8): the plain member of the move target assumed to be the written value.
#[trust_vc::ensures(true)]
fn struct_move_plain_member_wrong() {
    let mut u: u64 = 20u64;
    let u_ref = RefPair {
        x: &mut u,
        y: 70u64,
    };
    let u2 = u_ref;
    *u2.x = 5u64;
    trust_vc::assert!(u2.y == 5u64);
}

// LIAR l24 (c9): a read-through after the join claims one disjunct.
#[trust_vc::ensures(true)]
fn read_through_join_one_disjunct(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        *t.0 = 20u64;
    } else {
        *t.0 = 30u64;
    }
    trust_vc::assert!(*t.0 == 20u64);
}

// LIAR l25 (c10): the RETURN lane claims the pre-write root.
#[trust_vc::ensures(result == 0u64)]
fn return_value_stale(b: bool) -> u64 {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    *t.0 = 4u64;
    x
}

// LIAR l26 (review p5): the whole holder escapes inside a function-local macro.
#[trust_vc::ensures(true)]
fn local_macro_hides_holder_escape() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    macro_rules! esc {
        () => {
            consume_set(t);
        };
    }
    esc!();
    trust_vc::assert!(x == 0u64);
}

// LIAR l27 (review p5b): a held reference escapes into a call inside a local macro.
#[trust_vc::ensures(true)]
fn local_macro_hides_held_ref_call() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    macro_rules! esc {
        () => {
            set9(t.0);
        };
    }
    esc!();
    trust_vc::assert!(x == 0u64);
}

// LIAR l28 (review q10): a held reference is swapped inside a local macro.
#[trust_vc::ensures(true)]
fn local_macro_hides_held_ref_swap() {
    let mut x: u64 = 0u64;
    let mut y: u64 = 9u64;
    let t = (&mut x, 1u64);
    macro_rules! esc {
        () => {
            std::mem::swap(t.0, &mut y);
        };
    }
    esc!();
    trust_vc::assert!(x == 0u64);
}

// GATED g24 (review q9): a local-macro escape in the else arm of a holder join.
#[trust_vc::ensures(true)]
fn local_macro_escape_in_else_arm(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    macro_rules! esc {
        () => {
            set9(t.0);
        };
    }
    if b {
        *t.0 = 1u64;
    } else {
        esc!();
    }
    trust_vc::assert!(x == 1u64 || x == 0u64);
}

// LIAR l29 (review q2): a plain member naming a binding an invariant loop re-frames.
#[trust_vc::requires(p < 100u64)]
#[trust_vc::ensures(true)]
fn value_member_named_binding_across_invariant_loop(mut p: u64) {
    let k: u64 = p;
    let mut x: u64 = 0u64;
    let t = (&mut x, k);
    while p < 100u64 {
        trust_vc::invariant!(p <= 100u64);
        p = p + 1u64;
    }
    trust_vc::assert!(t.1 == p);
}

// LIAR l30 (review q2c): the same member read inside the invariant loop body.
#[trust_vc::requires(p < 100u64)]
#[trust_vc::ensures(true)]
fn value_member_named_binding_in_invariant_loop_body(mut p: u64) {
    let k: u64 = p;
    let mut x: u64 = 0u64;
    let t = (&mut x, k);
    while p < 100u64 {
        trust_vc::invariant!(p <= 100u64);
        trust_vc::assert!(t.1 == p);
        p = p + 1u64;
    }
}

// LIAR l31 (review p1): `let ref mut` borrows the held deref place, then a call writes it.
#[trust_vc::ensures(true)]
fn ref_mut_let_of_held_deref_then_call() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    let ref mut r = *t.0;
    set9(r);
    trust_vc::assert!(x == 0u64);
}

// LIAR l32 (review p1c): the same place borrow, written by a method autoref.
#[trust_vc::ensures(true)]
fn ref_mut_let_of_held_deref_add_assign() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    let ref mut r = *t.0;
    r.add_assign(9u64);
    trust_vc::assert!(x == 0u64);
}

// LIAR l33 (review p2): a raw borrow of the held deref place.
#[trust_vc::ensures(true)]
fn raw_borrow_of_held_deref() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    let p: *mut u64 = &raw mut *t.0;
    unsafe {
        p.write(9u64);
    }
    trust_vc::assert!(x == 0u64);
}

// LIAR l34 (review q5): `let ref mut` borrows a plain member.
#[trust_vc::ensures(true)]
fn ref_mut_let_of_value_member_then_call() {
    let mut x: u64 = 0u64;
    let mut t = (&mut x, 1u64);
    let ref mut r = t.1;
    set9(r);
    trust_vc::assert!(t.1 == 1u64);
}

// LIAR l35 (review q5b): a raw borrow of a plain member.
#[trust_vc::ensures(true)]
fn raw_borrow_of_value_member() {
    let mut x: u64 = 0u64;
    let mut t = (&mut x, 1u64);
    let p: *mut u64 = &raw mut t.1;
    unsafe {
        p.write(9u64);
    }
    trust_vc::assert!(t.1 == 1u64);
}

// GATED g25 (review p4): `let ref mut` of the ROOT in the else arm of a holder join.
#[trust_vc::ensures(true)]
fn keep_exact_ref_mut_root_in_else(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        *t.0 = 1u64;
    } else {
        let ref mut r = x;
        set9(r);
    }
    trust_vc::assert!(x == 1u64 || x == 0u64);
}

// GATED g26 (review p4d): a raw borrow write of the ROOT in the else arm.
#[trust_vc::ensures(true)]
fn keep_exact_raw_root_in_else(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        *t.0 = 1u64;
    } else {
        let p: *mut u64 = &raw mut x;
        unsafe {
            p.write(9u64);
        }
    }
    trust_vc::assert!(x == 1u64 || x == 0u64);
}

// GATED g27 (review p4b): a method autoref mutates the ROOT in the else arm.
#[trust_vc::ensures(true)]
fn keep_exact_add_assign_root_in_else(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        *t.0 = 1u64;
    } else {
        x.add_assign(9u64);
    }
    trust_vc::assert!(x == 1u64 || x == 0u64);
}

// GATED g28 (review q8): the same autoref in the last arm of an else-if chain.
#[trust_vc::ensures(true)]
fn keep_exact_add_assign_root_in_else_if_chain(a: bool, b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if a {
        *t.0 = 1u64;
    } else if b {
        *t.0 = 2u64;
    } else {
        x.add_assign(9u64);
    }
    trust_vc::assert!(x == 1u64 || x == 2u64 || x == 0u64);
}

// LIAR l45 (value lane): a holder write, then a stale read through the holder.
#[trust_vc::ensures(true)]
fn value_block_if_holder_write_deref_read_stale(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    let v: u64 = {
        if b {
            *t.0 = 2u64;
        }
        *t.0
    };
    trust_vc::assert!(v == 0u64);
}

// ---- Review round 2 (2026-09-14). Every probe below was measured on the
// round-1 build; the comment names its round-2 id and that verdict.

// LIAR l62 (a01, was Verified): a raw-identifier holder use escapes the scans.
#[trust_vc::ensures(true)]
fn raw_ident_holder_call_escape() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    consume_set(r#t);
    trust_vc::assert!(x == 0u64);
}

// LIAR l63 (a03, was Verified): `std::mem::swap` through a raw spelling.
#[trust_vc::ensures(true)]
fn raw_ident_held_ref_swap() {
    let mut x: u64 = 0u64;
    let mut y: u64 = 4u64;
    let t = (&mut x, 1u64);
    std::mem::swap(r#t.0, &mut y);
    trust_vc::assert!(x == 0u64);
}

// LIAR l64 (a08, was Verified): a struct holder's member.
#[trust_vc::ensures(true)]
fn raw_ident_struct_holder_member_call() {
    let mut a: u64 = 0u64;
    let s = RefPair {
        x: &mut a,
        y: 1u64,
    };
    set9(r#s.x);
    trust_vc::assert!(a == 0u64);
}

// GATED g57 (a10, was Verified): the escape in the else arm of a join.
#[trust_vc::ensures(true)]
fn raw_ident_holder_escape_in_else_arm(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        *t.0 = 5u64;
    } else {
        consume_set(r#t);
    }
    trust_vc::assert!(x == 5u64 || x == 0u64);
}

// LIAR l65 (a11, was Verified): a raw-spelled move.
#[trust_vc::ensures(true)]
fn raw_ident_holder_move_then_call() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    let u = r#t;
    consume_set(u);
    trust_vc::assert!(x == 0u64);
}

// GATED g58 (a13, was Verified): a raw-spelled reborrow after a holder write.
#[trust_vc::ensures(true)]
fn raw_ident_held_ref_reborrow_after_write() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    *t.0 = 5u64;
    set9(&mut *r#t.0);
    trust_vc::assert!(x == 5u64);
}

// GATED g59 (m01, was Verified): a raw-spelled shadow redirects later writes.
#[trust_vc::ensures(true)]
fn raw_ident_holder_shadow_redirects_write() {
    let mut x: u64 = 0u64;
    let mut y: u64 = 0u64;
    let t = (&mut x, 1u64);
    *t.0 = 1u64;
    let r#t = (&mut y, 2u64);
    *t.0 = 7u64;
    trust_vc::assert!(x == 7u64);
}

// LIAR l66 (m02, was Verified): a raw-spelled `let`, plain-spelled escape.
#[trust_vc::ensures(true)]
fn raw_ident_holder_let_plain_escape() {
    let mut x: u64 = 0u64;
    let r#t = (&mut x, 1u64);
    consume_set(t);
    trust_vc::assert!(x == 0u64);
}

// LIAR l67 (m03, was Verified): a precomposed `let`, decomposed escape (NFC).
// The two placeholders are substituted with `t\u{e9}` / `te\u{301}` by the
// test, keeping this file ASCII.
#[trust_vc::ensures(true)]
fn nfc_ident_holder_escape() {
    let mut x: u64 = 0u64;
    let NFC_PRECOMPOSED = (&mut x, 1u64);
    consume_set(NFC_DECOMPOSED);
    trust_vc::assert!(x == 0u64);
}

// LIAR l68 (m04, was Verified): a raw spelling captured by a `move` closure.
#[trust_vc::ensures(true)]
fn raw_ident_holder_closure_escape() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    let c = move || consume_set(r#t);
    c();
    trust_vc::assert!(x == 0u64);
}
"#;

const DEREF_REFUSAL: &str = "assignment through a dereferenced reference is unsupported";
/// The LHS token spelling of `*t.0` inside the deref refusal (the statement a
/// non-admitted holder's first write is refused at). `expect_gated_containing`
/// with this fragment pins WHICH write was refused, not just the family.
const HOLDER_WRITE: &str = "`* t . 0`";
/// The pre-existing refusal a component rebind `t.0 = &mut z` hits BEFORE the
/// deref write is reached (the raw tuple value has no struct type).
const FIELD_ASSIGN_REFUSAL: &str =
    "direct field assignment to an owned/parameter struct is unsupported";
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

fn expect_never_verified(id: &str, func: &str) {
    match verify(id, func, SRC) {
        VerifyResult::Verified => panic!("{func}: must NOT verify"),
        VerifyResult::Unknown { reason, .. } => {
            panic!("{func}: solver Unknown is not stable evidence: {reason}")
        }
        _ => {}
    }
}

fn expect_gated_containing(id: &str, func: &str, needle: &str, fragment: &str) {
    match verify(id, func, SRC) {
        VerifyResult::Error { message } if message.contains(needle) && message.contains(fragment) => {
        }
        other => panic!(
            "{func}: expected the fail-closed error containing {needle:?} and {fragment:?}, got {other:?}"
        ),
    }
}

// ---------------------------------------------------------------------------
// The round-2 `Drop` probes (l54-l61, g55 / g56, g-c18), in their own fixture:
// a file that mentions `Drop` admits no holder at all (review round 2 of the
// holder-only split, 2026-09-15), which would otherwise refuse every holder in
// `SRC`.
// ---------------------------------------------------------------------------
const SRC_DROP: &str = r#"
struct DropPair<'a> {
    x: &'a mut u64,
    y: u64,
}

impl<'a> Drop for DropPair<'a> {
    fn drop(&mut self) {
        *self.x = 99u64;
    }
}

// LIAR l54 (b02, was Verified): a struct holder whose type has a `Drop` impl,
// declared in a branch — the destructor writes the root when the branch ends.
#[trust_vc::ensures(true)]
fn drop_holder_in_if_branch(b: bool) {
    let mut a: u64 = 0u64;
    if b {
        let d = DropPair {
            x: &mut a,
            y: 1u64,
        };
    }
    trust_vc::assert!(a == 0u64);
}

// LIAR l55 (b08, was Verified): with a read through the holder.
#[trust_vc::ensures(true)]
fn drop_holder_in_if_branch_with_read(b: bool) {
    let mut a: u64 = 0u64;
    if b {
        let d = DropPair {
            x: &mut a,
            y: 1u64,
        };
        trust_vc::assert!(*d.x == 0u64);
    }
    trust_vc::assert!(a == 0u64);
}

// GATED g55 (b10, was Verified): a write through the holder, keep-exact merge.
#[trust_vc::ensures(true)]
fn drop_holder_write_in_if_branch(b: bool) {
    let mut a: u64 = 0u64;
    if b {
        let d = DropPair {
            x: &mut a,
            y: 1u64,
        };
        *d.x = 5u64;
    }
    trust_vc::assert!(!b || a == 5u64);
}

// LIAR l56 (b11, was Verified): the else branch.
#[trust_vc::ensures(true)]
fn drop_holder_in_else_branch(b: bool) {
    let mut a: u64 = 0u64;
    if b {
    } else {
        let d = DropPair {
            x: &mut a,
            y: 1u64,
        };
    }
    trust_vc::assert!(a == 0u64);
}

// LIAR l57 (b12, was Verified): the return lane.
#[trust_vc::ensures(result == 0u64)]
fn drop_holder_in_if_branch_return(b: bool) -> u64 {
    let mut a: u64 = 0u64;
    if b {
        let d = DropPair {
            x: &mut a,
            y: 1u64,
        };
    }
    a
}

// LIAR l58 (b13, was Verified): a value-position `if` arm.
#[trust_vc::ensures(true)]
fn drop_holder_in_value_if_arm(b: bool) {
    let mut a: u64 = 0u64;
    let v: u64 = if b {
        let d = DropPair {
            x: &mut a,
            y: 1u64,
        };
        1u64
    } else {
        2u64
    };
    trust_vc::assert!(a == 0u64);
}

// LIAR l59 (b15, was Verified): an else-if.
#[trust_vc::ensures(true)]
fn drop_holder_in_else_if_branch(b: bool, c: bool) {
    let mut a: u64 = 0u64;
    if b {
    } else if c {
        let d = DropPair {
            x: &mut a,
            y: 1u64,
        };
    }
    trust_vc::assert!(a == 0u64);
}

// LIAR l60 (b17, was Verified): moved inside the branch.
#[trust_vc::ensures(true)]
fn drop_holder_moved_in_if_branch(b: bool) {
    let mut a: u64 = 0u64;
    if b {
        let d = DropPair {
            x: &mut a,
            y: 1u64,
        };
        let e = d;
    }
    trust_vc::assert!(a == 0u64);
}

// LIAR l61 (b21, was Verified): a nested if.
#[trust_vc::ensures(true)]
fn drop_holder_in_nested_if_branch(b: bool, c: bool) {
    let mut a: u64 = 0u64;
    if b {
        if c {
            let d = DropPair {
                x: &mut a,
                y: 1u64,
            };
        }
    }
    trust_vc::assert!(a == 0u64);
}

// GATED g56 (b22, was Verified): write + read-back, disjunctive post claim.
#[trust_vc::ensures(true)]
fn drop_holder_write_read_in_if_branch(b: bool) {
    let mut a: u64 = 0u64;
    if b {
        let d = DropPair {
            x: &mut a,
            y: 1u64,
        };
        *d.x = 5u64;
        trust_vc::assert!(*d.x == 5u64);
    }
    trust_vc::assert!(a == 0u64 || a == 5u64);
}

// GATED g-c18 (was CONTROL c18, a TRUE program): a `Drop` struct holder in the
// FUNCTION BODY block. Review round 2 of the split (2026-09-15): a file that
// mentions `Drop` admits no holder — the model never runs drop glue, and a
// panicking destructor run at the body end or an early `return` was unseen
// (`SRC_R7_DROP`).
#[trust_vc::ensures(true)]
fn drop_struct_holder_in_body_block_verifies() {
    let mut u: u64 = 20u64;
    let u_ref = DropPair {
        x: &mut u,
        y: 70u64,
    };
    *u_ref.x = 30u64;
    trust_vc::assert!(*u_ref.x == 30u64);
}
"#;

fn expect_never_verified_in(id: &str, func: &str, src: &str) {
    match verify(id, func, src) {
        VerifyResult::Verified => panic!("{func}: must NOT verify"),
        VerifyResult::Unknown { reason, .. } => {
            panic!("{func}: solver Unknown is not stable evidence: {reason}")
        }
        _ => {}
    }
}

fn expect_refused_in(id: &str, func: &str, src: &str, fragment: &str) {
    match verify(id, func, src) {
        VerifyResult::Error { message }
            if message.contains(DEREF_REFUSAL) && message.contains(fragment) => {}
        other => panic!(
            "{func}: expected the fail-closed error containing {DEREF_REFUSAL:?} and {fragment:?}, got {other:?}"
        ),
    }
}

#[test]
fn control_struct_holder_write_and_plain_member_read_verifies() {
    expect_verified("c1", "struct_holder_write_and_plain_member_read_verifies");
}

#[test]
fn control_tuple_holder_branch_writes_join_verifies() {
    expect_verified("c2", "tuple_holder_branch_writes_join_verifies");
}

#[test]
fn control_tuple_holder_move_write_sibling_unchanged_verifies() {
    expect_verified("c3", "tuple_holder_move_write_sibling_unchanged_verifies");
}

#[test]
fn control_tuple_holder_sequential_writes_and_cross_read_verify() {
    expect_verified("c4", "tuple_holder_sequential_writes_and_cross_read_verify");
}

#[test]
fn control_tuple_holder_then_only_branch_join_verifies() {
    expect_verified("c5", "tuple_holder_then_only_branch_join_verifies");
}

#[test]
fn control_holder_straight_write_then_branch_write_join_verifies() {
    expect_verified(
        "c6",
        "holder_straight_write_then_branch_write_join_verifies",
    );
}

#[test]
fn control_holder_declared_inside_branch_verifies() {
    expect_verified("c7", "holder_declared_inside_branch_verifies");
}

#[test]
fn control_struct_holder_moved_then_written_verifies() {
    expect_verified("c8", "struct_holder_moved_then_written_verifies");
}

#[test]
fn control_holder_read_through_after_join_verifies() {
    expect_verified("c9", "holder_read_through_after_join_verifies");
}

#[test]
fn control_holder_function_with_return_value_verifies() {
    expect_verified("c10", "holder_function_with_return_value_verifies");
}

#[test]
fn liar_struct_holder_wrong_written_value_is_refuted() {
    expect_counterexample("l1", "struct_holder_wrong_written_value");
}

#[test]
fn liar_struct_holder_stale_preborrow_value_is_refuted() {
    expect_counterexample("l2", "struct_holder_stale_preborrow_value");
}

#[test]
fn liar_struct_holder_plain_member_wrong_is_refuted() {
    expect_counterexample("l3", "struct_holder_plain_member_wrong");
}

#[test]
fn liar_tuple_holder_branch_then_disjunct_only_is_refuted() {
    expect_counterexample("l4", "tuple_holder_branch_then_disjunct_only");
}

#[test]
fn liar_tuple_holder_branch_both_written_is_refuted() {
    expect_counterexample("l5", "tuple_holder_branch_both_written");
}

#[test]
fn liar_tuple_holder_move_sibling_root_changed_is_refuted() {
    expect_counterexample("l6", "tuple_holder_move_sibling_root_changed");
}

#[test]
fn liar_tuple_holder_move_stale_root_is_refuted() {
    expect_counterexample("l7", "tuple_holder_move_stale_root");
}

#[test]
fn liar_stale_deref_read_after_write_is_refuted() {
    expect_counterexample("l8", "stale_deref_read_after_write");
}

#[test]
fn liar_sequential_writes_first_value_is_refuted() {
    expect_counterexample("l9", "sequential_writes_first_value");
}

#[test]
fn liar_branch_local_holder_unconditional_pre_value_is_refuted() {
    expect_counterexample("l10", "branch_local_holder_unconditional_pre_value");
}

#[test]
fn liar_plain_block_write_then_root_read_never_verifies() {
    expect_never_verified("l11", "plain_block_write_then_root_read_never_verifies");
}

#[test]
fn liar_match_arm_write_then_stale_read_never_verifies() {
    expect_never_verified("l12", "match_arm_write_then_stale_read_never_verifies");
}

#[test]
fn liar_moved_from_holder_read_never_verifies() {
    expect_never_verified("l13", "moved_from_holder_read_never_verifies");
}

#[test]
fn liar_alias_mix_branch_join_never_verifies() {
    expect_never_verified("l14", "alias_mix_branch_join_never_verifies");
}

#[test]
fn liar_value_block_if_write_never_verifies() {
    expect_never_verified("l15", "value_block_if_write_never_verifies");
}

#[test]
fn liar_holder_escaping_into_call_never_verifies() {
    expect_never_verified("l16", "holder_escaping_into_call_never_verifies");
}

#[test]
fn gated_compound_write_through_holder() {
    expect_gated_containing(
        "g1",
        "compound_write_through_holder",
        DEREF_REFUSAL,
        "* t . 0",
    );
}

#[test]
fn gated_loop_body_write_through_local_holder() {
    expect_gated_containing(
        "g2",
        "loop_body_write_through_local_holder",
        DEREF_REFUSAL,
        "* t . 0",
    );
}

#[test]
fn gated_param_tuple_holder() {
    expect_gated_containing("g3", "param_tuple_holder", DEREF_REFUSAL, "* pair . 0");
}

/// Refused at the `let` (design-trust-proof-backend.md §5b rule 12): the
/// element type of an un-ascribed tuple local is not determined here, so a
/// `&mut u64` alias of it is not shown to point at a `u64`. It was refused at
/// the write through it (`DEREF_REFUSAL`, "tuple/index/nested projections").
#[test]
fn gated_field_borrow_of_plain_tuple() {
    expect_gated_containing(
        "g4",
        "field_borrow_of_plain_tuple",
        "a reference does not convert its referent",
        "& mut x . 0",
    );
}

#[test]
fn gated_tuple_literal_deref_without_let() {
    expect_gated_containing(
        "g5",
        "tuple_literal_deref_without_let",
        DEREF_REFUSAL,
        "* (& mut a , & mut b) . 0",
    );
}

#[test]
fn gated_old_over_held_reference() {
    expect_gated_containing("g6", "old_over_held_reference", DEREF_REFUSAL, "* pair . 0");
}

#[test]
fn gated_nested_aggregate_projection() {
    expect_gated_containing(
        "g7",
        "nested_aggregate_projection",
        DEREF_REFUSAL,
        "* t . 0 . 0",
    );
}

#[test]
fn gated_component_retarget_then_write() {
    expect_gated_containing(
        "g8",
        "component_retarget_then_write",
        FIELD_ASSIGN_REFUSAL,
        "t . 0",
    );
}

#[test]
fn gated_plain_member_rebind_then_write() {
    expect_gated_containing(
        "g9",
        "plain_member_rebind_then_write",
        DEREF_REFUSAL,
        "* u_ref . x",
    );
}

#[test]
fn gated_holder_passed_to_call_then_write() {
    expect_gated_containing(
        "g10",
        "holder_passed_to_call_then_write",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn gated_held_ref_passed_to_call_then_write() {
    expect_gated_containing(
        "g11",
        "held_ref_passed_to_call_then_write",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn gated_reborrow_of_held_ref() {
    expect_gated_containing("g12", "reborrow_of_held_ref", DEREF_REFUSAL, "* r");
}

#[test]
fn gated_holder_in_closure() {
    expect_gated_containing("g13", "holder_in_closure", DEREF_REFUSAL, HOLDER_WRITE);
}

#[test]
fn gated_shadowed_root() {
    expect_gated_containing("g14", "shadowed_root", DEREF_REFUSAL, HOLDER_WRITE);
}

#[test]
fn gated_destructured_components() {
    expect_gated_containing("g15", "destructured_components", DEREF_REFUSAL, "* a");
}

#[test]
fn gated_direct_root_write_while_live() {
    expect_gated_containing(
        "g16",
        "direct_root_write_while_live",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn gated_two_holders_share_a_root() {
    expect_gated_containing("g17", "two_holders_share_a_root", DEREF_REFUSAL, "* d . 0");
}

#[test]
fn gated_tuple_struct_ctor_holder() {
    expect_gated_containing("g18", "tuple_struct_ctor_holder", DEREF_REFUSAL, "* c . 0");
}

#[test]
fn gated_non_value_like_plain_component() {
    expect_gated_containing(
        "g19",
        "non_value_like_plain_component",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn gated_deref_of_plain_member() {
    expect_gated_containing("g20", "deref_of_plain_member", DEREF_REFUSAL, HOLDER_WRITE);
}

#[test]
fn gated_move_inside_branch() {
    expect_gated_containing("g21", "move_inside_branch", DEREF_REFUSAL, "* q . 0");
}

#[test]
fn gated_use_after_move_write() {
    expect_gated_containing("g22", "use_after_move_write", DEREF_REFUSAL, HOLDER_WRITE);
}

#[test]
fn gated_holder_call_argument_after_writes() {
    expect_gated_containing(
        "g23",
        "holder_call_argument_after_writes",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn liar_then_only_branch_assumed_taken_is_refuted() {
    expect_counterexample("l18", "then_only_branch_assumed_taken");
}

#[test]
fn liar_then_only_branch_assumed_skipped_is_refuted() {
    expect_counterexample("l19", "then_only_branch_assumed_skipped");
}

#[test]
fn liar_straight_then_branch_assumed_overwrite_is_refuted() {
    expect_counterexample("l20", "straight_then_branch_assumed_overwrite");
}

#[test]
fn liar_straight_then_branch_stale_is_refuted() {
    expect_counterexample("l21", "straight_then_branch_stale");
}

#[test]
fn liar_struct_move_stale_root_is_refuted() {
    expect_counterexample("l22", "struct_move_stale_root");
}

#[test]
fn liar_struct_move_plain_member_wrong_is_refuted() {
    expect_counterexample("l23", "struct_move_plain_member_wrong");
}

#[test]
fn liar_read_through_join_one_disjunct_is_refuted() {
    expect_counterexample("l24", "read_through_join_one_disjunct");
}

#[test]
fn liar_return_value_stale_is_refuted() {
    expect_counterexample("l25", "return_value_stale");
}

#[test]
fn liar_local_macro_hides_holder_escape_never_verifies() {
    expect_never_verified("l26", "local_macro_hides_holder_escape");
}

#[test]
fn liar_local_macro_hides_held_ref_call_never_verifies() {
    expect_never_verified("l27", "local_macro_hides_held_ref_call");
}

#[test]
fn liar_local_macro_hides_held_ref_swap_never_verifies() {
    expect_never_verified("l28", "local_macro_hides_held_ref_swap");
}

#[test]
fn gated_local_macro_escape_in_else_arm() {
    expect_gated_containing(
        "g24",
        "local_macro_escape_in_else_arm",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn liar_value_member_named_binding_across_invariant_loop_never_verifies() {
    expect_never_verified("l29", "value_member_named_binding_across_invariant_loop");
}

#[test]
fn liar_value_member_named_binding_in_invariant_loop_body_never_verifies() {
    expect_never_verified("l30", "value_member_named_binding_in_invariant_loop_body");
}

#[test]
fn liar_ref_mut_let_of_held_deref_then_call_never_verifies() {
    expect_never_verified("l31", "ref_mut_let_of_held_deref_then_call");
}

#[test]
fn liar_ref_mut_let_of_held_deref_add_assign_never_verifies() {
    expect_never_verified("l32", "ref_mut_let_of_held_deref_add_assign");
}

#[test]
fn liar_raw_borrow_of_held_deref_never_verifies() {
    expect_never_verified("l33", "raw_borrow_of_held_deref");
}

#[test]
fn liar_ref_mut_let_of_value_member_then_call_never_verifies() {
    expect_never_verified("l34", "ref_mut_let_of_value_member_then_call");
}

#[test]
fn liar_raw_borrow_of_value_member_never_verifies() {
    expect_never_verified("l35", "raw_borrow_of_value_member");
}

#[test]
fn gated_keep_exact_ref_mut_root_in_else() {
    expect_gated_containing(
        "g25",
        "keep_exact_ref_mut_root_in_else",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn gated_keep_exact_raw_root_in_else() {
    expect_gated_containing(
        "g26",
        "keep_exact_raw_root_in_else",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn gated_keep_exact_add_assign_root_in_else() {
    expect_gated_containing(
        "g27",
        "keep_exact_add_assign_root_in_else",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn gated_keep_exact_add_assign_root_in_else_if_chain() {
    expect_gated_containing(
        "g28",
        "keep_exact_add_assign_root_in_else_if_chain",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn liar_value_block_if_holder_write_deref_read_stale_never_verifies() {
    expect_never_verified("l45", "value_block_if_holder_write_deref_read_stale");
}

#[test]
fn liar_drop_holder_in_if_branch_never_verifies() {
    expect_never_verified_in("l54", "drop_holder_in_if_branch", SRC_DROP);
}

#[test]
fn liar_drop_holder_in_if_branch_with_read_never_verifies() {
    expect_never_verified_in("l55", "drop_holder_in_if_branch_with_read", SRC_DROP);
}

#[test]
fn gated_drop_holder_write_in_if_branch() {
    expect_refused_in(
        "g55",
        "drop_holder_write_in_if_branch",
        SRC_DROP,
        "`* d . x`",
    );
}

#[test]
fn liar_drop_holder_in_else_branch_never_verifies() {
    expect_never_verified_in("l56", "drop_holder_in_else_branch", SRC_DROP);
}

#[test]
fn liar_drop_holder_in_if_branch_return_never_verifies() {
    expect_never_verified_in("l57", "drop_holder_in_if_branch_return", SRC_DROP);
}

#[test]
fn liar_drop_holder_in_value_if_arm_never_verifies() {
    expect_never_verified_in("l58", "drop_holder_in_value_if_arm", SRC_DROP);
}

#[test]
fn liar_drop_holder_in_else_if_branch_never_verifies() {
    expect_never_verified_in("l59", "drop_holder_in_else_if_branch", SRC_DROP);
}

#[test]
fn liar_drop_holder_moved_in_if_branch_never_verifies() {
    expect_never_verified_in("l60", "drop_holder_moved_in_if_branch", SRC_DROP);
}

#[test]
fn liar_drop_holder_in_nested_if_branch_never_verifies() {
    expect_never_verified_in("l61", "drop_holder_in_nested_if_branch", SRC_DROP);
}

#[test]
fn gated_drop_holder_write_read_in_if_branch() {
    expect_refused_in(
        "g56",
        "drop_holder_write_read_in_if_branch",
        SRC_DROP,
        "`* d . x`",
    );
}

#[test]
fn gated_drop_struct_holder_in_body_block() {
    expect_refused_in(
        "c18",
        "drop_struct_holder_in_body_block_verifies",
        SRC_DROP,
        "`* u_ref . x`",
    );
}

#[test]
fn liar_raw_ident_holder_call_escape_never_verifies() {
    expect_never_verified("l62", "raw_ident_holder_call_escape");
}

#[test]
fn liar_raw_ident_held_ref_swap_never_verifies() {
    expect_never_verified("l63", "raw_ident_held_ref_swap");
}

#[test]
fn liar_raw_ident_struct_holder_member_call_never_verifies() {
    expect_never_verified("l64", "raw_ident_struct_holder_member_call");
}

#[test]
fn gated_raw_ident_holder_escape_in_else_arm() {
    expect_gated_containing(
        "g57",
        "raw_ident_holder_escape_in_else_arm",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn liar_raw_ident_holder_move_then_call_never_verifies() {
    expect_never_verified("l65", "raw_ident_holder_move_then_call");
}

#[test]
fn gated_raw_ident_held_ref_reborrow_after_write() {
    expect_gated_containing(
        "g58",
        "raw_ident_held_ref_reborrow_after_write",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn gated_raw_ident_holder_shadow_redirects_write() {
    expect_gated_containing(
        "g59",
        "raw_ident_holder_shadow_redirects_write",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn liar_raw_ident_holder_let_plain_escape_never_verifies() {
    expect_never_verified("l66", "raw_ident_holder_let_plain_escape");
}

#[test]
fn liar_nfc_ident_holder_escape_never_verifies() {
    let src = SRC
        .replace("NFC_PRECOMPOSED", "t\u{e9}")
        .replace("NFC_DECOMPOSED", "te\u{301}");
    match verify("l67", "nfc_ident_holder_escape", &src) {
        VerifyResult::Verified => panic!("nfc_ident_holder_escape: must NOT verify"),
        VerifyResult::Unknown { reason, .. } => {
            panic!("nfc_ident_holder_escape: solver Unknown is not stable evidence: {reason}")
        }
        _ => {}
    }
}

#[test]
fn liar_raw_ident_holder_closure_escape_never_verifies() {
    expect_never_verified("l68", "raw_ident_holder_closure_escape");
}

// ---------------------------------------------------------------------------
// Review round 3 (2026-09-14): the reproduced HOLDER probes of the third
// adversarial review, in their own fixture file. The `round 3, finding N:`
// comments record the pre-fix dev verdict each probe was filed with; every
// gated case now carries HEAD's deref refusal (the round-4 position gate).
// ---------------------------------------------------------------------------

const SRC_R3: &str = r#"
struct RefPair<'a> {
    x: &'a mut u64,
    y: u64,
}

// round 3, finding 1: TopErr(extract body assertions: operand `({ * h . 0 = 1u64 ;
#[trust_vc::ensures(true)]
fn r3_m5_holder_ifcond_simple() {
    let mut x: u64 = 0u64;
    let h = (&mut x, 0u64);
    let v: u64 = if ({ *h.0 = 1u64; true }) { *h.0 } else { 0u64 };
    trust_vc::assert!(v == 0u64);
}

// round 3, finding 1: TopErr(extract body assertions: operand `({ if b { * h . 0 =
#[trust_vc::ensures(true)]
fn r3_h1_holder_ifcond_block(b: bool) {
    let mut x: u64 = 0u64;
    let h = (&mut x, 0u64);
    let v: u64 = if ({ if b { *h.0 = 1u64; } true }) { *h.0 } else { 7u64 };
    trust_vc::assert!(v == 0u64);
}

// round 3, finding 1: TopErr(extract body assertions: operand `({ * h . 0 = 1u64 ;
#[trust_vc::ensures(true)]
fn r3_h2_holder_ifcond_uncond() {
    let mut x: u64 = 0u64;
    let h = (&mut x, 0u64);
    let v: u64 = if ({ *h.0 = 1u64; true }) { *h.0 } else { 7u64 };
    trust_vc::assert!(v == 0u64);
}

// round 3, finding 1: TopErr(extract verification conditions: Function 'p_h4_holde
#[trust_vc::ensures(result == 0u64)]
fn r3_h4_holder_return_ifcond() -> u64 {
    let mut x: u64 = 0u64;
    let h = (&mut x, 0u64);
    if ({ *h.0 = 1u64; true }) { *h.0 } else { 7u64 }
}

// round 3, finding 1: TopErr(extract body assertions: operand `({ * h . 0 = 1u64 ;
#[trust_vc::ensures(true)]
fn r3_i5_holder_else_if_cond(c: bool) {
    let mut x: u64 = 0u64;
    let h = (&mut x, 0u64);
    let v: u64 = if c { 0u64 } else if ({ *h.0 = 1u64; true }) { *h.0 } else { 7u64 };
    trust_vc::assert!(v == 0u64);
}

// round 3, finding 1: TopErr(extract verification conditions: Function 'p_i6_holde
#[trust_vc::ensures(result == 0u64)]
fn r3_i6_holder_return_else_reads(b: bool) -> u64 {
    let mut x: u64 = 0u64;
    let h = (&mut x, 0u64);
    if ({ if b { *h.0 = 1u64; } false }) { 7u64 } else { *h.0 }
}

// round 3, finding 1: TopErr(extract body assertions: operand `({ if b { * h . 0 =
#[trust_vc::ensures(true)]
fn r3_i7_holder_ifcond_both_branches(b: bool) {
    let mut x: u64 = 0u64;
    let h = (&mut x, 0u64);
    let v: u64 = if ({ if b { *h.0 = 1u64; } b }) { *h.0 } else { *h.0 };
    trust_vc::assert!(v == 0u64);
}

// round 3, finding 1: TopErr(extract body assertions: operand `({ * h . x = 1u64 ;
#[trust_vc::ensures(true)]
fn r3_i9_holder_ifcond_struct_holder() {
    let mut x: u64 = 0u64;
    let h = RefPair { x: &mut x, y: 0u64 };
    let v: u64 = if ({ *h.x = 1u64; true }) { *h.x } else { 7u64 };
    trust_vc::assert!(v == 0u64);
}

// round 3, finding 1: TopErr(extract body assertions: operand `({ * h . 0 = 1u64 ;
#[trust_vc::ensures(result == 0u64)]
fn r3_i12_holder_return_tail_if_in_block() -> u64 {
    let mut x: u64 = 0u64;
    let h = (&mut x, 0u64);
    let r: u64 = if ({ *h.0 = 1u64; true }) { *h.0 } else { 7u64 };
    r
}

// round 3, finding 1: TopErr(extract body assertions: operand `({ * h . 0 = 1u64 ;
#[trust_vc::ensures(true)]
fn r3_i13_holder_ifcond_nested_value_block_in_assert() {
    let mut x: u64 = 0u64;
    let h = (&mut x, 0u64);
    trust_vc::assert!(if ({ *h.0 = 1u64; true }) { *h.0 == 0u64 } else { false });
}

// round 3, finding 2: TopErr(extract body assertions: statement `(* h . 0 = 1u64)`
#[trust_vc::ensures(true)]
fn r3_j4_holder_let_init_paren_assign() {
    let mut x: u64 = 0u64;
    let h = (&mut x, 0u64);
    let v: u64 = { let _w = (*h.0 = 1u64); *h.0 };
    trust_vc::assert!(v == 0u64);
}

// round 3, finding 2: TopErr(extract verification conditions: Function 'p_j9_holde
#[trust_vc::ensures(result == 0u64)]
fn r3_j9_holder_return_block_let_init(b: bool) -> u64 {
    let mut x: u64 = 0u64;
    let h = (&mut x, 0u64);
    { let _w = (*h.0 = 1u64); *h.0 }
}

// round 3, finding 2: TopErr(extract body assertions: statement `match n { 0u64 =>
#[trust_vc::ensures(true)]
fn r3_j10_let_init_blockless_match_arm_assign_holder(n: u64) {
    let mut x: u64 = 0u64;
    let h = (&mut x, 0u64);
    let v: u64 = { let _w = match n { 0u64 => *h.0 = 1u64, _ => () }; *h.0 };
    trust_vc::assert!(v == 0u64);
}

// round 3, finding 3: TopErr(extract body assertions: statement `{ * h . 0 = 1u64 
#[trust_vc::ensures(true)]
fn r3_i1_holder_assert_arg_mutation_value() {
    let mut x: u64 = 0u64;
    let h = (&mut x, 0u64);
    let v: u64 = { assert!({ *h.0 = 1u64; true }); *h.0 };
    trust_vc::assert!(v == 0u64);
}

// round 3, finding 3: TopErr(extract verification conditions: Function 'p_k3_holde
#[trust_vc::ensures(result == 0u64)]
fn r3_k3_holder_return_assert_arg_mutation() -> u64 {
    let mut x: u64 = 0u64;
    let h = (&mut x, 0u64);
    { assert!({ *h.0 = 1u64; true }); *h.0 }
}

// round 3, finding 3: TopErr(extract body assertions: statement `{ * h . 0 = 1u64 
#[trust_vc::ensures(true)]
fn r3_k4_holder_if_value_assert_arg_mutation(c: bool) {
    let mut x: u64 = 0u64;
    let h = (&mut x, 0u64);
    let v: u64 = if c { assert!({ *h.0 = 1u64; true }); *h.0 } else { 0u64 };
    trust_vc::assert!(v == 0u64);
}

// round 3, finding 11: TopErr(extract body assertions: assignment through a derefer
#[trust_vc::ensures(true)]
fn r3c_a1_const_shadow_root_in_branch_join(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        const x: u64 = 9u64;
        *t.0 = 5u64;
    }
    trust_vc::assert!(x == 0u64);
}

// round 3, finding 11: TopErr(extract body assertions: assignment through a derefer
#[trust_vc::ensures(true)]
fn r3c_a3_static_shadow_root_in_else_join(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
    } else {
        static x: u64 = 9u64;
        *t.0 = 5u64;
    }
    trust_vc::assert!(x == 0u64);
}

// round 3, finding 11: TopErr(extract body assertions: assignment through a derefer
#[trust_vc::ensures(true)]
fn r3c_a4_const_shadow_struct_holder(b: bool) {
    let mut a: u64 = 0u64;
    let s = RefPair { x: &mut a, y: 1u64 };
    if b {
        const a: u64 = 3u64;
        *s.x = 5u64;
    }
    trust_vc::assert!(a == 0u64);
}

// round 3, finding 11: TopErr(extract body assertions: assignment through a derefer
#[trust_vc::ensures(true)]
fn r3c_a12_const_shadow_join_then_holder_read(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        const x: u64 = 9u64;
        *t.0 = 5u64;
    }
    trust_vc::assert!(*t.0 == 0u64);
}

// round 3, finding 11: TopErr(extract body assertions: assignment through a derefer
#[trust_vc::ensures(result == 0u64)]
fn r3c_a13_const_shadow_join_return(b: bool) -> u64 {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        const x: u64 = 9u64;
        *t.0 = 5u64;
    }
    x
}

// round 3, finding 11: TopErr(extract body assertions: assignment through a derefer
#[trust_vc::ensures(true)]
fn r3c_a15_const_shadow_write_in_else_if(b: bool, c: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        *t.0 = 1u64;
    } else if c {
        const x: u64 = 9u64;
        *t.0 = 2u64;
    }
    trust_vc::assert!(x == 0u64 || x == 1u64);
}

// round 3, finding 11: TopErr(extract body assertions: assignment through a derefer
#[trust_vc::ensures(true)]
fn r3c_a17_const_shadow_write_then_straight_read(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        const x: u64 = 9u64;
        *t.0 = 5u64;
        trust_vc::assert!(*t.0 == 5u64);
    }
    trust_vc::assert!(x == 0u64);
}

// round 3, finding 11: TopErr(extract body assertions: assignment through a derefer
#[trust_vc::ensures(result == 0u64)]
fn r3c_a28_return_after_branch_write_const_shadow(b: bool) -> u64 {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        static x: u64 = 1u64;
        *t.0 = 5u64;
    }
    *t.0
}

// round 3, finding 12: Error(prepare obligation: Failed to lower obligation 'assert
#[trust_vc::ensures(true)]
fn r3c_a8_const_shadow_holder_read_plain_block() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    {
        const x: u64 = 9u64;
        trust_vc::assert!(*t.0 == 9u64);
    }
}

// round 3, finding 12: Error(prepare obligation: Failed to lower obligation 'assert
#[trust_vc::ensures(true)]
fn r3c_a9_const_shadow_holder_read_if_no_write(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        const x: u64 = 9u64;
        trust_vc::assert!(*t.0 == 9u64);
    }
}

// round 3, finding 12: Error(prepare obligation: Failed to lower obligation 'assert
#[trust_vc::ensures(true)]
fn r3c_a14_struct_holder_const_shadow_read_block() {
    let mut a: u64 = 4u64;
    let s = RefPair { x: &mut a, y: 1u64 };
    {
        static a: u64 = 3u64;
        trust_vc::assert!(*s.x == 3u64);
    }
}

// round 3, finding 12: Error(prepare obligation: Failed to lower obligation 'assert
#[trust_vc::ensures(true)]
fn r3c_a16_const_shadow_read_in_loop(n: u64) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    let mut i: u64 = 0u64;
    while i < 1u64 {
        const x: u64 = 9u64;
        trust_vc::assert!(*t.0 == 9u64);
        i = i + 1u64;
    }
}

// round 3, finding 12: TopErr(extract body assertions: assignment through a derefer
#[trust_vc::ensures(true)]
fn r3c_a24_const_shadow_between_writes(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    *t.0 = 2u64;
    if b {
        const x: u64 = 9u64;
        trust_vc::assert!(*t.0 == 9u64);
    }
    trust_vc::assert!(x == 2u64);
}

// round 3, finding 12: Error(prepare obligation: Failed to lower obligation 'assert
#[trust_vc::ensures(true)]
fn r3c_a26_value_block_const_shadow_holder_read() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    let v: u64 = {
        const x: u64 = 9u64;
        *t.0
    };
    trust_vc::assert!(v == 9u64);
}

// round 3, finding 12: Error(prepare obligation: Failed to lower obligation 'return
#[trust_vc::ensures(result == 9u64)]
fn r3c_a27_return_block_const_shadow_holder_read() -> u64 {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    {
        const x: u64 = 9u64;
        *t.0
    }
}

// round 3, finding 13: TopErr(extract body assertions: assignment through a derefer
#[trust_vc::ensures(true)]
fn r3c_a19_holder_borrows_const_temporary() {
    let mut x: u64 = 0u64;
    {
        const x: u64 = 9u64;
        let t = (&mut x, 1u64);
        *t.0 = 5u64;
        trust_vc::assert!(x == 5u64);
    }
}

// round 3, finding 13: TopErr(extract body assertions: assignment through a derefer
#[trust_vc::ensures(true)]
fn r3c_a22_branch_holder_borrows_const(b: bool) {
    let mut x: u64 = 0u64;
    if b {
        const x: u64 = 9u64;
        let t = (&mut x, 1u64);
        *t.0 = 5u64;
        trust_vc::assert!(*t.0 == 5u64);
        trust_vc::assert!(x == 5u64);
    }
}

// round 3, finding 13: TopErr(extract body assertions: assignment through a derefer
#[trust_vc::ensures(true)]
fn r3c_a2_const_shadow_root_in_branch_inner_read(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        const x: u64 = 9u64;
        *t.0 = 5u64;
        trust_vc::assert!(x == 5u64);
    }
}

// round 3, finding 14: TopErr(extract body assertions: assignment through a derefer
#[trust_vc::ensures(true)]
fn r3c_c3b_cfg_if_holder_write(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    #[cfg(any())]
    if b {
        *t.0 = 5u64;
    }
    trust_vc::assert!(!b || x == 5u64);
}

// round 3, finding 0: Verified
#[trust_vc::ensures(true)]
fn r3n_n5_holder_with_unrelated_const_verifies() {
    const N: u64 = 5u64;
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    *t.0 = N;
    trust_vc::assert!(x == 5u64);
}

// round 3, finding 0: TopErr(extract body assertions: assignment through a derefer
#[trust_vc::ensures(true)]
fn r3n_n10_holder_const_shadow_non_root_let(b: bool) {
    let mut x: u64 = 0u64;
    let y: u64 = 1u64;
    let t = (&mut x, 1u64);
    if b { const y: u64 = 9u64; *t.0 = y; }
    trust_vc::assert!(!b || x == 9u64);
}

// round 3, finding 0: TopErr(extract body assertions: assignment through a derefer
#[trust_vc::ensures(true)]
fn r3n_n11_cfg_attr_holder(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    #[cfg_attr(any(), allow(unused))]
    if b { *t.0 = 5u64; }
    trust_vc::assert!(!b || x == 5u64);
}

// round 3, finding 0: TopErr(extract body assertions: assignment through a derefer
#[trust_vc::ensures(true)]
fn r3n_n12_index_holder_base(b: bool) {
    let mut x: u64 = 0u64;
    let h = (&mut x, 0u64);
    let arr: [u64; 2] = [10u64, 20u64];
    let v: u64 = ({ if b { *h.0 = 1u64; } arr })[*h.0 as usize];
    trust_vc::assert!(v == 10u64);
}

// round 3, finding 0: TopErr(extract body assertions: operand `{ if b { * h . 0 = 
#[trust_vc::ensures(true)]
fn r3n_n13_binary_holder_right(b: bool) {
    let mut x: u64 = 0u64;
    let h = (&mut x, 0u64);
    let v: u64 = { if b { *h.0 = 1u64; } 5u64 } + *h.0;
    trust_vc::assert!(v == 5u64);
}
"#;

fn expect_never_verified_r3(id: &str, func: &str) {
    match verify(id, func, SRC_R3) {
        VerifyResult::Verified => panic!("{func}: must NOT verify"),
        VerifyResult::Unknown { reason, .. } => {
            panic!("{func}: solver Unknown is not stable evidence: {reason}")
        }
        _ => {}
    }
}

fn expect_gated_containing_r3(id: &str, func: &str, needle: &str, fragment: &str) {
    match verify(id, func, SRC_R3) {
        VerifyResult::Error { message } if message.contains(needle) && message.contains(fragment) => {
        }
        other => panic!(
            "{func}: expected the fail-closed error containing {needle:?} and {fragment:?}, got {other:?}"
        ),
    }
}

#[test]
fn gated_r3_m5_holder_ifcond_simple() {
    expect_gated_containing_r3(
        "r3m5",
        "r3_m5_holder_ifcond_simple",
        DEREF_REFUSAL,
        "`* h . 0`",
    );
}

#[test]
fn gated_r3_h1_holder_ifcond_block() {
    expect_gated_containing_r3(
        "r3h1",
        "r3_h1_holder_ifcond_block",
        DEREF_REFUSAL,
        "`* h . 0`",
    );
}

#[test]
fn gated_r3_h2_holder_ifcond_uncond() {
    expect_gated_containing_r3(
        "r3h2",
        "r3_h2_holder_ifcond_uncond",
        DEREF_REFUSAL,
        "`* h . 0`",
    );
}

#[test]
fn gated_r3_h4_holder_return_ifcond() {
    expect_gated_containing_r3(
        "r3h4",
        "r3_h4_holder_return_ifcond",
        DEREF_REFUSAL,
        "`* h . 0`",
    );
}

#[test]
fn gated_r3_i5_holder_else_if_cond() {
    expect_gated_containing_r3(
        "r3i5",
        "r3_i5_holder_else_if_cond",
        DEREF_REFUSAL,
        "`* h . 0`",
    );
}

#[test]
fn gated_r3_i6_holder_return_else_reads() {
    expect_gated_containing_r3(
        "r3i6",
        "r3_i6_holder_return_else_reads",
        DEREF_REFUSAL,
        "`* h . 0`",
    );
}

#[test]
fn gated_r3_i7_holder_ifcond_both_branches() {
    expect_gated_containing_r3(
        "r3i7",
        "r3_i7_holder_ifcond_both_branches",
        DEREF_REFUSAL,
        "`* h . 0`",
    );
}

#[test]
fn gated_r3_i9_holder_ifcond_struct_holder() {
    expect_gated_containing_r3(
        "r3i9",
        "r3_i9_holder_ifcond_struct_holder",
        DEREF_REFUSAL,
        "`* h . x`",
    );
}

#[test]
fn gated_r3_i12_holder_return_tail_if_in_block() {
    expect_gated_containing_r3(
        "r3i12",
        "r3_i12_holder_return_tail_if_in_block",
        DEREF_REFUSAL,
        "`* h . 0`",
    );
}

#[test]
fn gated_r3_i13_holder_ifcond_nested_value_block_in_assert() {
    expect_gated_containing_r3(
        "r3i13",
        "r3_i13_holder_ifcond_nested_value_block_in_assert",
        DEREF_REFUSAL,
        "`* h . 0`",
    );
}

#[test]
fn gated_r3_j4_holder_let_init_paren_assign() {
    expect_gated_containing_r3(
        "r3j4",
        "r3_j4_holder_let_init_paren_assign",
        DEREF_REFUSAL,
        "`* h . 0`",
    );
}

#[test]
fn gated_r3_j9_holder_return_block_let_init() {
    expect_gated_containing_r3(
        "r3j9",
        "r3_j9_holder_return_block_let_init",
        DEREF_REFUSAL,
        "`* h . 0`",
    );
}

#[test]
fn gated_r3_j10_let_init_blockless_match_arm_assign_holder() {
    expect_gated_containing_r3(
        "r3j10",
        "r3_j10_let_init_blockless_match_arm_assign_holder",
        DEREF_REFUSAL,
        "`* h . 0`",
    );
}

#[test]
fn gated_r3_i1_holder_assert_arg_mutation_value() {
    expect_gated_containing_r3(
        "r3i1",
        "r3_i1_holder_assert_arg_mutation_value",
        DEREF_REFUSAL,
        "`* h . 0`",
    );
}

#[test]
fn gated_r3_k3_holder_return_assert_arg_mutation() {
    expect_gated_containing_r3(
        "r3k3",
        "r3_k3_holder_return_assert_arg_mutation",
        DEREF_REFUSAL,
        "`* h . 0`",
    );
}

#[test]
fn gated_r3_k4_holder_if_value_assert_arg_mutation() {
    expect_gated_containing_r3(
        "r3k4",
        "r3_k4_holder_if_value_assert_arg_mutation",
        DEREF_REFUSAL,
        "`* h . 0`",
    );
}

#[test]
fn gated_r3c_a1_const_shadow_root_in_branch_join() {
    expect_gated_containing_r3(
        "r3ca1",
        "r3c_a1_const_shadow_root_in_branch_join",
        DEREF_REFUSAL,
        "`* t . 0`",
    );
}

#[test]
fn gated_r3c_a3_static_shadow_root_in_else_join() {
    expect_gated_containing_r3(
        "r3ca3",
        "r3c_a3_static_shadow_root_in_else_join",
        DEREF_REFUSAL,
        "`* t . 0`",
    );
}

#[test]
fn gated_r3c_a4_const_shadow_struct_holder() {
    expect_gated_containing_r3(
        "r3ca4",
        "r3c_a4_const_shadow_struct_holder",
        DEREF_REFUSAL,
        "`* s . x`",
    );
}

#[test]
fn gated_r3c_a12_const_shadow_join_then_holder_read() {
    expect_gated_containing_r3(
        "r3ca12",
        "r3c_a12_const_shadow_join_then_holder_read",
        DEREF_REFUSAL,
        "`* t . 0`",
    );
}

#[test]
fn gated_r3c_a13_const_shadow_join_return() {
    expect_gated_containing_r3(
        "r3ca13",
        "r3c_a13_const_shadow_join_return",
        DEREF_REFUSAL,
        "`* t . 0`",
    );
}

#[test]
fn gated_r3c_a15_const_shadow_write_in_else_if() {
    expect_gated_containing_r3(
        "r3ca15",
        "r3c_a15_const_shadow_write_in_else_if",
        DEREF_REFUSAL,
        "`* t . 0`",
    );
}

#[test]
fn gated_r3c_a17_const_shadow_write_then_straight_read() {
    expect_gated_containing_r3(
        "r3ca17",
        "r3c_a17_const_shadow_write_then_straight_read",
        DEREF_REFUSAL,
        "`* t . 0`",
    );
}

#[test]
fn gated_r3c_a28_return_after_branch_write_const_shadow() {
    expect_gated_containing_r3(
        "r3ca28",
        "r3c_a28_return_after_branch_write_const_shadow",
        DEREF_REFUSAL,
        "`* t . 0`",
    );
}

#[test]
fn liar_r3c_a8_const_shadow_holder_read_plain_block_never_verifies() {
    expect_never_verified_r3("r3ca8", "r3c_a8_const_shadow_holder_read_plain_block");
}

#[test]
fn liar_r3c_a9_const_shadow_holder_read_if_no_write_never_verifies() {
    expect_never_verified_r3("r3ca9", "r3c_a9_const_shadow_holder_read_if_no_write");
}

#[test]
fn liar_r3c_a14_struct_holder_const_shadow_read_block_never_verifies() {
    expect_never_verified_r3("r3ca14", "r3c_a14_struct_holder_const_shadow_read_block");
}

#[test]
fn liar_r3c_a16_const_shadow_read_in_loop_never_verifies() {
    expect_never_verified_r3("r3ca16", "r3c_a16_const_shadow_read_in_loop");
}

#[test]
fn gated_r3c_a24_const_shadow_between_writes() {
    expect_gated_containing_r3(
        "r3ca24",
        "r3c_a24_const_shadow_between_writes",
        DEREF_REFUSAL,
        "`* t . 0`",
    );
}

#[test]
fn liar_r3c_a26_value_block_const_shadow_holder_read_never_verifies() {
    expect_never_verified_r3("r3ca26", "r3c_a26_value_block_const_shadow_holder_read");
}

#[test]
fn liar_r3c_a27_return_block_const_shadow_holder_read_never_verifies() {
    expect_never_verified_r3("r3ca27", "r3c_a27_return_block_const_shadow_holder_read");
}

#[test]
fn gated_r3c_a19_holder_borrows_const_temporary() {
    expect_gated_containing_r3(
        "r3ca19",
        "r3c_a19_holder_borrows_const_temporary",
        DEREF_REFUSAL,
        "`* t . 0`",
    );
}

#[test]
fn gated_r3c_a22_branch_holder_borrows_const() {
    expect_gated_containing_r3(
        "r3ca22",
        "r3c_a22_branch_holder_borrows_const",
        DEREF_REFUSAL,
        "`* t . 0`",
    );
}

#[test]
fn gated_r3c_a2_const_shadow_root_in_branch_inner_read() {
    expect_gated_containing_r3(
        "r3ca2",
        "r3c_a2_const_shadow_root_in_branch_inner_read",
        DEREF_REFUSAL,
        "`* t . 0`",
    );
}

#[test]
fn gated_r3c_c3b_cfg_if_holder_write() {
    expect_gated_containing_r3(
        "r3cc3b",
        "r3c_c3b_cfg_if_holder_write",
        DEREF_REFUSAL,
        "`* t . 0`",
    );
}

#[test]
fn gated_r3n_n5_holder_with_unrelated_const() {
    // Was a CONTROL (a TRUE program): review round 2 of the split (2026-09-15)
    // refuses EVERY nested item in a holder body (a block `const` read before
    // its declaration resolved to the file-level item: `SRC_R7` r7-l1 / r7-l2).
    expect_gated_containing_r3(
        "r3nn5",
        "r3n_n5_holder_with_unrelated_const_verifies",
        DEREF_REFUSAL,
        "`* t . 0`",
    );
}

#[test]
fn gated_r3n_n10_holder_const_shadow_non_root_let() {
    expect_gated_containing_r3(
        "r3nn10",
        "r3n_n10_holder_const_shadow_non_root_let",
        DEREF_REFUSAL,
        "`* t . 0`",
    );
}

#[test]
fn gated_r3n_n11_cfg_attr_holder() {
    expect_gated_containing_r3(
        "r3nn11",
        "r3n_n11_cfg_attr_holder",
        DEREF_REFUSAL,
        "`* t . 0`",
    );
}

#[test]
fn gated_r3n_n12_index_holder_base() {
    expect_gated_containing_r3(
        "r3nn12",
        "r3n_n12_index_holder_base",
        DEREF_REFUSAL,
        "`* h . 0`",
    );
}

#[test]
fn gated_r3n_n13_binary_holder_right() {
    expect_gated_containing_r3(
        "r3nn13",
        "r3n_n13_binary_holder_right",
        DEREF_REFUSAL,
        "`* h . 0`",
    );
}

// ---------------------------------------------------------------------------
// Review round 4 (2026-09-14): the STRUCTURAL position gate. A holder write
// `*h.m = v` is admitted only as a semicolon statement of a statement-position
// block (the body block; the then / else blocks of a statement `if`, else-if
// chains included; the block / bare-assignment arm bodies of a statement
// `match`; a plain / `unsafe` block statement; a semicolon-less statement
// counts when it is not its block's tail or when that tail is syntactically
// unit-valued). A write anywhere else refuses admission of the holder, so the
// body takes HEAD's fail-closed path: every gated case below was measured to
// carry the verbatim HEAD refusal (`lensR/bin_base`, 2026-09-14). Before the
// gate, ten of them reached the solver with the root unbound (`unresolved
// variable `x``) and three (r4g9 / r4g10 / r4g14) `Verified` a runtime-true
// claim through a write position the value lane does not model; r4g2 / r4g6 /
// r4g11 were already refused.
// ---------------------------------------------------------------------------

const SRC_R4: &str = r#"
// GATED r4g1: a holder write inside an `if` CONDITION block.
#[trust_vc::ensures(true)]
fn r4_ifcond_block_write() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if ({ *t.0 = 5u64; true }) {
        trust_vc::assert!(true);
    }
    trust_vc::assert!(x == 5u64);
}

// GATED r4g2: a holder write inside a `match` SCRUTINEE block.
#[trust_vc::ensures(true)]
fn r4_match_scrutinee_block_write() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    match ({ *t.0 = 5u64; 1u64 }) {
        _ => {}
    }
    trust_vc::assert!(x == 5u64);
}

// GATED r4g3: a holder write inside a unit `let` INITIALIZER block.
#[trust_vc::ensures(true)]
fn r4_let_init_unit_block_write() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    let _u: () = {
        *t.0 = 5u64;
    };
    trust_vc::assert!(x == 5u64);
}

// GATED r4g4: a holder write inside an assignment RHS block.
#[trust_vc::ensures(true)]
fn r4_assign_rhs_block_write() {
    let mut x: u64 = 0u64;
    let mut y: u64 = 0u64;
    let t = (&mut x, 1u64);
    y = {
        *t.0 = 5u64;
        1u64
    };
    trust_vc::assert!(x == 5u64);
    trust_vc::assert!(y == 1u64);
}

// GATED r4g5: a holder write inside a spec MACRO ARGUMENT block.
#[trust_vc::ensures(true)]
fn r4_macro_arg_block_write() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    trust_vc::assert!({ *t.0 = 5u64; true });
    trust_vc::assert!(x == 5u64);
}

// GATED r4g6: a holder write inside an immediately-invoked CLOSURE.
#[trust_vc::ensures(true)]
fn r4_closure_body_write() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    (|| {
        *t.0 = 5u64;
    })();
    trust_vc::assert!(x == 5u64);
}

// GATED r4g7: a holder write inside a VALUE-POSITION block.
#[trust_vc::ensures(true)]
fn r4_value_block_write() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    let v: u64 = {
        *t.0 = 5u64;
        3u64
    };
    trust_vc::assert!(x == 5u64);
    trust_vc::assert!(v == 3u64);
}

// GATED r4g8: a holder write inside a LABELLED block statement.
#[trust_vc::ensures(true)]
fn r4_labelled_block_statement_write() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    'a: {
        *t.0 = 5u64;
    }
    trust_vc::assert!(x == 5u64);
}

// GATED r4g9: a semicolon-less TAIL assignment of a statement `if` block.
#[trust_vc::ensures(true)]
fn r4_semicolonless_tail_assign_write(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        *t.0 = 5u64
    }
    trust_vc::assert!(x == 5u64 || x == 0u64);
}

// GATED r4g10: a holder write in a branch of the body's VALUE tail.
#[trust_vc::ensures(result == 5u64 || result == 0u64)]
fn r4_return_value_tail_if_write(b: bool) -> u64 {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        *t.0 = 5u64;
        x
    } else {
        0u64
    }
}

// GATED r4g11: a holder write inside a LOOP body left by `break`.
#[trust_vc::ensures(true)]
fn r4_loop_body_write() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    loop {
        *t.0 = 5u64;
        break;
    }
    trust_vc::assert!(x == 5u64);
}

// GATED r4g12: a holder write inside a binary EXPRESSION OPERAND block.
#[trust_vc::ensures(true)]
fn r4_binary_operand_block_write() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    let v: u64 = 1u64 + {
        *t.0 = 5u64;
        2u64
    };
    trust_vc::assert!(x == 5u64);
    trust_vc::assert!(v == 3u64);
}

// GATED r4g13: a statement `match` whose arm body is an `if` EXPRESSION (not a
// block or a bare assignment).
#[trust_vc::ensures(true)]
fn r4_match_arm_if_expression_write(k: u64, b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    match k {
        0u64 => if b {
            *t.0 = 5u64;
        },
        _ => {}
    }
    trust_vc::assert!(x == 5u64 || x == 0u64);
}

// GATED r4g14: a PARENTHESIZED assignment statement.
#[trust_vc::ensures(true)]
fn r4_paren_assign_statement_write() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    (*t.0 = 5u64);
    trust_vc::assert!(x == 5u64);
}

// GATED r4g15: a holder write inside a VALUE-POSITION `unsafe` block.
#[trust_vc::ensures(true)]
fn r4_value_unsafe_block_write() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    let v: u64 = unsafe {
        *t.0 = 5u64;
        1u64
    };
    trust_vc::assert!(x == 5u64);
    trust_vc::assert!(v == 1u64);
}

// GATED r4g16: a holder write inside a `match` GUARD block.
#[trust_vc::ensures(true)]
fn r4_match_guard_block_write(k: u64) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    match k {
        _ if ({ *t.0 = 5u64; true }) => {}
        _ => {}
    }
    trust_vc::assert!(x == 5u64);
}

// CONTROL r4c1: a statement `if` nested as the unit TAIL of a statement `if`
// then-block still admits the holder and joins exactly.
#[trust_vc::ensures(true)]
fn r4_nested_statement_if_tail_write_verifies(b: bool, c: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        if c {
            *t.0 = 1u64;
        }
    }
    trust_vc::assert!(x == 0u64 || x == 1u64);
}

// LIAR r4l1: the same nesting cannot verify a value the join excludes.
#[trust_vc::ensures(true)]
fn r4_nested_statement_if_tail_write_stale(b: bool, c: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        if c {
            *t.0 = 1u64;
        }
    }
    trust_vc::assert!(x == 0u64);
}

// CONTROL r4c2: writes in every arm of a statement else-if chain, inside a
// non-tail statement `if`.
#[trust_vc::ensures(true)]
fn r4_else_if_chain_writes_verify(a: bool, b: bool, c: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if a {
        if b {
            *t.0 = 1u64;
        } else if c {
            *t.0 = 2u64;
        } else {
            *t.0 = 3u64;
        }
    }
    trust_vc::assert!(t.1 == 1u64);
    trust_vc::assert!(x == 0u64 || x == 1u64 || x == 2u64 || x == 3u64);
}

// LIAR r4l2: the chain's join cannot drop the `else` arm's value.
#[trust_vc::ensures(true)]
fn r4_else_if_chain_writes_missing_arm(a: bool, b: bool, c: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if a {
        if b {
            *t.0 = 1u64;
        } else if c {
            *t.0 = 2u64;
        } else {
            *t.0 = 3u64;
        }
    }
    trust_vc::assert!(x == 0u64 || x == 1u64 || x == 2u64);
}

// CONTROL r4c3: a statement `match` (a block arm and a bare-assignment arm)
// inside a statement `if`; the in-arm read-back sees the write.
#[trust_vc::ensures(true)]
fn r4_statement_match_arms_write_verifies(k: u64, b: bool) {
    let mut x: u64 = 0u64;
    let mut y: u64 = 0u64;
    let t = (&mut x, &mut y);
    if b {
        match k {
            0u64 => {
                *t.0 = 1u64;
                trust_vc::assert!(*t.0 == 1u64);
            }
            _ => *t.1 = 2u64,
        }
    }
    trust_vc::assert!(true);
}
"#;

fn expect_verified_r4(id: &str, func: &str) {
    match verify(id, func, SRC_R4) {
        VerifyResult::Verified => {}
        other => panic!("{func}: expected Verified, got {other:?}"),
    }
}

fn expect_counterexample_r4(id: &str, func: &str) {
    match verify(id, func, SRC_R4) {
        VerifyResult::Counterexample { .. } => {}
        other => panic!("{func}: expected Counterexample, got {other:?}"),
    }
}

fn expect_gated_containing_r4(id: &str, func: &str, needle: &str, fragment: &str) {
    match verify(id, func, SRC_R4) {
        VerifyResult::Error { message } if message.contains(needle) && message.contains(fragment) => {
        }
        other => panic!(
            "{func}: expected the fail-closed error containing {needle:?} and {fragment:?}, got {other:?}"
        ),
    }
}

#[test]
fn gated_r4_ifcond_block_write() {
    expect_gated_containing_r4("r4g1", "r4_ifcond_block_write", DEREF_REFUSAL, HOLDER_WRITE);
}

#[test]
fn gated_r4_match_scrutinee_block_write() {
    expect_gated_containing_r4(
        "r4g2",
        "r4_match_scrutinee_block_write",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn gated_r4_let_init_unit_block_write() {
    expect_gated_containing_r4(
        "r4g3",
        "r4_let_init_unit_block_write",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn gated_r4_assign_rhs_block_write() {
    expect_gated_containing_r4(
        "r4g4",
        "r4_assign_rhs_block_write",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn gated_r4_macro_arg_block_write() {
    expect_gated_containing_r4(
        "r4g5",
        "r4_macro_arg_block_write",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn gated_r4_closure_body_write() {
    expect_gated_containing_r4("r4g6", "r4_closure_body_write", DEREF_REFUSAL, HOLDER_WRITE);
}

#[test]
fn gated_r4_value_block_write() {
    expect_gated_containing_r4("r4g7", "r4_value_block_write", DEREF_REFUSAL, HOLDER_WRITE);
}

#[test]
fn gated_r4_labelled_block_statement_write() {
    expect_gated_containing_r4(
        "r4g8",
        "r4_labelled_block_statement_write",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn gated_r4_semicolonless_tail_assign_write() {
    expect_gated_containing_r4(
        "r4g9",
        "r4_semicolonless_tail_assign_write",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn gated_r4_return_value_tail_if_write() {
    expect_gated_containing_r4(
        "r4g10",
        "r4_return_value_tail_if_write",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn gated_r4_loop_body_write() {
    expect_gated_containing_r4("r4g11", "r4_loop_body_write", DEREF_REFUSAL, HOLDER_WRITE);
}

#[test]
fn gated_r4_binary_operand_block_write() {
    expect_gated_containing_r4(
        "r4g12",
        "r4_binary_operand_block_write",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn gated_r4_match_arm_if_expression_write() {
    expect_gated_containing_r4(
        "r4g13",
        "r4_match_arm_if_expression_write",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn gated_r4_paren_assign_statement_write() {
    expect_gated_containing_r4(
        "r4g14",
        "r4_paren_assign_statement_write",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn gated_r4_value_unsafe_block_write() {
    expect_gated_containing_r4(
        "r4g15",
        "r4_value_unsafe_block_write",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn gated_r4_match_guard_block_write() {
    expect_gated_containing_r4(
        "r4g16",
        "r4_match_guard_block_write",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn control_r4_nested_statement_if_tail_write_verifies() {
    expect_verified_r4("r4c1", "r4_nested_statement_if_tail_write_verifies");
}

#[test]
fn liar_r4_nested_statement_if_tail_write_stale_is_refuted() {
    expect_counterexample_r4("r4l1", "r4_nested_statement_if_tail_write_stale");
}

#[test]
fn control_r4_else_if_chain_writes_verify() {
    expect_verified_r4("r4c2", "r4_else_if_chain_writes_verify");
}

#[test]
fn liar_r4_else_if_chain_writes_missing_arm_is_refuted() {
    expect_counterexample_r4("r4l2", "r4_else_if_chain_writes_missing_arm");
}

#[test]
fn control_r4_statement_match_arms_write_verifies() {
    expect_verified_r4("r4c3", "r4_statement_match_arms_write_verifies");
}

// Review round 4 FINDINGS (2026-09-14): finding 1, a holder VALUE member must
// carry its own type (a `bool` or a SUFFIXED integer literal); and, from the
// holder-only split, a body with an untyped integer literal admits no holder.
const SRC_R4F: &str = r#"
struct Pair8<'a> {
    x: &'a mut u8,
    y: u8,
}

// GATED r4f-g1 (fin1): an UNSUFFIXED struct-holder member typed `u8` only by
// the field; `128u8 << 1 == 0`, so the claim is false on every `b = true` run.
#[trust_vc::ensures(true)]
fn r4f_unsuffixed_struct_member_shl(b: bool) {
    let mut u: u8 = 0u8;
    let h = Pair8 { x: &mut u, y: 128 };
    if b {
        *h.x = h.y << 1;
    } else {
        *h.x = h.y;
    }
    trust_vc::assert!(u >= 128u8);
}

// GATED r4f-g2 (v2): `0u8 - 1` underflows (debug panic, release wraps).
#[trust_vc::ensures(true)]
fn r4f_unsuffixed_struct_member_sub(b: bool) {
    let mut u: u8 = 0u8;
    let h = Pair8 { x: &mut u, y: 0 };
    *h.x = h.y - if b { 1 } else { 0 };
    trust_vc::assert!(u < 1u8);
}

// GATED r4f-g3: an unsuffixed TUPLE member (a true claim; lost completeness).
#[trust_vc::ensures(true)]
fn r4f_unsuffixed_tuple_member() {
    let mut u: u8 = 0u8;
    let t = (&mut u, 200);
    *t.0 = 1u8;
    trust_vc::assert!(u == 1u8);
}

// LIAR r4f-l1 (w5): a read-only holder with an unsuffixed member.
#[trust_vc::ensures(true)]
fn r4f_unsuffixed_member_read_only(b: bool) {
    let mut u: u8 = 0u8;
    let h = Pair8 { x: &mut u, y: 128 };
    let v: u8 = h.y << if b { 1 } else { 0 };
    trust_vc::assert!(v >= 128u8);
}

// LIAR r4f-l2 (w8): `!0` typed by the field is 255.
#[trust_vc::ensures(true)]
fn r4f_unsuffixed_member_not() {
    let mut u: u8 = 0u8;
    let h = Pair8 { x: &mut u, y: 0 };
    let v: u8 = !h.y;
    *h.x = v;
    trust_vc::assert!(v != 255u8);
}

// CONTROL r4f-c1: a SUFFIXED member still rides the holder lane.
#[trust_vc::ensures(true)]
fn r4f_suffixed_member_true_claim_verifies(b: bool) {
    let mut u: u8 = 0u8;
    let h = Pair8 { x: &mut u, y: 100u8 };
    if b {
        *h.x = h.y;
    }
    trust_vc::assert!(u == 0u8 || u == 100u8);
}

// LIAR r4f-l3 (fin1s): the suffixed twin of g1 keeps the `u8` wrap.
#[trust_vc::ensures(true)]
fn r4f_suffixed_member_shl(b: bool) {
    let mut u: u8 = 0u8;
    let h = Pair8 { x: &mut u, y: 128u8 };
    if b {
        *h.x = h.y << 1u8;
    } else {
        *h.x = h.y;
    }
    trust_vc::assert!(u >= 128u8);
}

// LIAR r4f-l4: a suffixed `!0u8` member is 255.
#[trust_vc::ensures(true)]
fn r4f_suffixed_member_not() {
    let mut u: u8 = 0u8;
    let h = Pair8 { x: &mut u, y: !0u8 };
    *h.x = h.y;
    trust_vc::assert!(u != 255u8);
}

// ---- holder-only split (2026-09-14): an untyped literal anywhere in the body ----

// LIAR split-l1 (reviewer probe r5h `p_a9`): an UNSUFFIXED write value over a
// `u8` root. `250 + 10` overflows (debug panic, release wrap to 4), so the
// claim is false on every run; without the body-wide untyped-literal
// disqualifier the holder lane rendered `(250) + 10` with no overflow
// obligation and VERIFIED it (the direct / bare-alias twins verify at HEAD).
#[trust_vc::ensures(true)]
fn split_untyped_write_compare_gt_255() {
    let mut x: u8 = 0u8;
    let t = (&mut x, 1u64);
    *t.0 = 250;
    *t.0 = *t.0 + 10;
    trust_vc::assert!(x > 255u8);
}

// GATED split-g1: a true claim whose only untyped literal sits in a spec
// assertion (lost completeness: the whole body keeps HEAD's refusal).
#[trust_vc::ensures(true)]
fn split_untyped_literal_in_assert_true_claim() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    *t.0 = 5u64;
    trust_vc::assert!(x == 5);
}
"#;

/// The struct-holder member write LHS in the deref refusal.
const HOLDER_MEMBER_WRITE: &str = "`* h . x`";

fn expect_verified_r4f(id: &str, func: &str) {
    match verify(id, func, SRC_R4F) {
        VerifyResult::Verified => {}
        other => panic!("{func}: expected Verified, got {other:?}"),
    }
}

fn expect_counterexample_r4f(id: &str, func: &str) {
    match verify(id, func, SRC_R4F) {
        VerifyResult::Counterexample { .. } => {}
        other => panic!("{func}: expected Counterexample, got {other:?}"),
    }
}

fn expect_gated_containing_r4f(id: &str, func: &str, needle: &str, fragment: &str) {
    match verify(id, func, SRC_R4F) {
        VerifyResult::Error { message } if message.contains(needle) && message.contains(fragment) => {
        }
        other => panic!(
            "{func}: expected the fail-closed error containing {needle:?} and {fragment:?}, got {other:?}"
        ),
    }
}

#[test]
fn gated_r4f_unsuffixed_struct_member_shl() {
    expect_gated_containing_r4f(
        "r4fg1",
        "r4f_unsuffixed_struct_member_shl",
        DEREF_REFUSAL,
        HOLDER_MEMBER_WRITE,
    );
}

#[test]
fn gated_r4f_unsuffixed_struct_member_sub() {
    expect_gated_containing_r4f(
        "r4fg2",
        "r4f_unsuffixed_struct_member_sub",
        DEREF_REFUSAL,
        HOLDER_MEMBER_WRITE,
    );
}

#[test]
fn gated_r4f_unsuffixed_member_not() {
    expect_gated_containing_r4f(
        "r4fg4",
        "r4f_unsuffixed_member_not",
        DEREF_REFUSAL,
        HOLDER_MEMBER_WRITE,
    );
}

#[test]
fn gated_r4f_unsuffixed_tuple_member() {
    expect_gated_containing_r4f(
        "r4fg3",
        "r4f_unsuffixed_tuple_member",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn liar_r4f_unsuffixed_member_read_only() {
    expect_gated_containing_r4f(
        "r4fl1",
        "r4f_unsuffixed_member_read_only",
        "overflow_check_0",
        "`&mut not supported`",
    );
}

#[test]
fn control_r4f_suffixed_member_true_claim_verifies() {
    expect_verified_r4f("r4fc1", "r4f_suffixed_member_true_claim_verifies");
}

#[test]
fn liar_r4f_suffixed_member_shl_is_refuted() {
    expect_counterexample_r4f("r4fl3", "r4f_suffixed_member_shl");
}

#[test]
fn liar_r4f_suffixed_member_not_is_refuted() {
    expect_counterexample_r4f("r4fl4", "r4f_suffixed_member_not");
}

#[test]
fn liar_split_untyped_write_compare_gt_255_is_refused() {
    expect_gated_containing_r4f(
        "splitl1",
        "split_untyped_write_compare_gt_255",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

#[test]
fn gated_split_untyped_literal_in_assert_true_claim() {
    expect_gated_containing_r4f(
        "splitg1",
        "split_untyped_literal_in_assert_true_claim",
        DEREF_REFUSAL,
        HOLDER_WRITE,
    );
}

// ---- review of the holder-only split (2026-09-14): HEAD gaps on UNRELATED locals ----
//
// HEAD refuses every body that writes through a holder, so a HEAD modelling gap
// elsewhere in such a body was unreachable. Admitting the holder write lifted
// that refusal and each program below VERIFIED on the holder-only build (all
// FALSE on stock rustc; every holder-free twin is `Verified` at HEAD, an open
// class outside this lane). The body-wide effect-position disqualifier
// (`holder_admission_body_shape_disqualified`) and the file-level `cfg` gate
// (`CollectorLaneSeed::holder_file_admissible`) keep HEAD's deref refusal.
const SRC_R6: &str = r#"
use std::ops::AddAssign;

struct R6Pair<'a> {
    x: &'a mut u64,
    y: u64,
}

// LIAR r6-l1: a labelled block with `break 'l 7u64` was modelled as falling through to its
// tail `5u64` (the holder write is incidental). `b = true` gives `v == 7`.
#[trust_vc::ensures(true)]
fn r6_lbl_let_holder_incidental(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    *t.0 = 5u64;
    let v: u64 = 'l: {
        if b {
            break 'l 7u64;
        }
        5u64
    };
    trust_vc::assert!(v == 5u64);
}

// LIAR r6-l2: the same labelled-block gap in the RETURN lane. `b = true` returns 5.
#[trust_vc::ensures(result == 6u64)]
fn r6_lbl_ret_holder_read(b: bool) -> u64 {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    *t.0 = 5u64;
    'l: {
        if b {
            break 'l *t.0;
        }
        *t.0 + 1u64
    }
}

// LIAR r6-l3: a labelled block as the holder write RHS. `b = true` writes 7.
#[trust_vc::ensures(true)]
fn r6_rhs_labelled(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    *t.0 = 'l: {
        if b {
            break 'l 7u64;
        }
        5u64
    };
    trust_vc::assert!(x == 5u64);
}

// LIAR r6-l4 (generated, gen5 `p_g5_60128`): a labelled-block return tail
// reading a struct holder. `b = false` returns 1, `b = true` returns 0.
#[trust_vc::ensures(result == 1u64)]
fn r6_gen5_labelled_return_struct_holder(a: bool, b: bool, k: u64) -> u64 {
    let mut x: u64 = 0u64;
    let mut y: u64 = 0u64;
    let mut v0: u64 = 0u64;
    let mut v1: u64 = 0u64;
    let h = R6Pair { x: &mut x, y: 70u64 };
    let u = (&mut y, 3u64);
    *h.x = *h.x;
    *h.x = *u.0;
    *h.x = *h.x;
    'l: {
        if b {
            break 'l *h.x;
        }
        *h.x + 1u64
    }
}

// LIAR r6-l5: an autoref method on a PLAIN local (`v.add_assign(3u64)`) inside a branch
// that also writes the holder: the join never saw `v` change. `b = true` gives `v == 3`.
#[trust_vc::ensures(true)]
fn r6_j_aa_holder(b: bool) {
    let mut x: u64 = 0u64;
    let mut v: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        *t.0 = 2u64;
        v.add_assign(3u64);
    }
    trust_vc::assert!(v == 0u64);
}

// LIAR r6-l6: the autoref write inside the holder write's RHS value block. `x == 3`.
#[trust_vc::ensures(true)]
fn r6_aa_holder_rhs_block() {
    let mut x: u64 = 0u64;
    let mut v: u64 = 0u64;
    let t = (&mut x, 1u64);
    *t.0 = {
        v.add_assign(3u64);
        v
    };
    trust_vc::assert!(x == 0u64);
}

// LIAR r6-l7: an immediately-invoked closure writing a plain local in a holder branch. `v == 3`.
#[trust_vc::ensures(true)]
fn r6_j_cl_holder(b: bool) {
    let mut x: u64 = 0u64;
    let mut v: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        *t.0 = 2u64;
        (|| {
            v = 3u64;
        })();
    }
    trust_vc::assert!(v == 0u64);
}

// LIAR r6-l8: the closure write inside the holder write's RHS value block. `x == 3`.
#[trust_vc::ensures(true)]
fn r6_cl_holder_rhs_block() {
    let mut x: u64 = 0u64;
    let mut v: u64 = 0u64;
    let t = (&mut x, 1u64);
    *t.0 = {
        (|| {
            v = 3u64;
        })();
        v
    };
    trust_vc::assert!(x == 0u64);
}

// LIAR r6-l9: a plain write inside an `if` condition block (round-3 g1 with a holder). `v == 1`.
#[trust_vc::ensures(true)]
fn r6_g1_ifcond_uncond_assign_h(b: bool) {
    let mut hx: u64 = 0u64;
    let ht = (&mut hx, 1u64);
    *ht.0 = 5u64;
    let mut x: u64 = 0u64;
    let v: u64 = if ({ x = 1u64; b || !b }) { x } else { 7u64 };
    trust_vc::assert!(v == 0u64);
}

// LIAR r6-l10: a plain write inside a `match` scrutinee block (g2). `v == 1`.
#[trust_vc::ensures(true)]
fn r6_g2_match_scrutinee_uncond_assign_h() {
    let mut hx: u64 = 0u64;
    let ht = (&mut hx, 1u64);
    *ht.0 = 5u64;
    let mut x: u64 = 0u64;
    let v: u64 = match ({ x = 1u64; 0u64 }) { 0u64 => x, _ => 9u64 };
    trust_vc::assert!(v == 0u64);
}

// LIAR r6-l11: g3: the `if`-condition write in the return tail. `result == 1`.
#[trust_vc::ensures(result == 0u64)]
fn r6_g3_return_ifcond_uncond_assign_h(b: bool) -> u64 {
    let mut hx: u64 = 0u64;
    let ht = (&mut hx, 1u64);
    *ht.0 = 5u64;
    let mut x: u64 = 0u64;
    if ({ x = 1u64; b || !b }) { x } else { 7u64 }
}

// LIAR r6-l12: g4: the scrutinee write in the return tail. `result == 1`.
#[trust_vc::ensures(result == 0u64)]
fn r6_g4_return_match_scrutinee_h() -> u64 {
    let mut hx: u64 = 0u64;
    let ht = (&mut hx, 1u64);
    *ht.0 = 5u64;
    let mut x: u64 = 0u64;
    match ({ x = 1u64; 0u64 }) { 0u64 => x, _ => 9u64 }
}

// LIAR r6-l13: g5: a conditional write in an `if` condition, read by the else branch. `b = true` gives `v == 1`.
#[trust_vc::ensures(true)]
fn r6_g5_ifcond_else_reads_h(b: bool) {
    let mut hx: u64 = 0u64;
    let ht = (&mut hx, 1u64);
    *ht.0 = 5u64;
    let mut x: u64 = 0u64;
    let v: u64 = if ({ if b { x = 1u64; } false }) { 7u64 } else { x };
    trust_vc::assert!(v == 0u64);
}

// LIAR r6-l14: b5: a conditional write in an `if` condition, read by the then branch.
#[trust_vc::ensures(true)]
fn r6_b5_if_cond_block_then_reads_h(b: bool) {
    let mut hx: u64 = 0u64;
    let ht = (&mut hx, 1u64);
    *ht.0 = 5u64;
    let mut x: u64 = 0u64;
    let v: u64 = if ({ if b { x = 1u64; } true }) { x } else { 7u64 };
    trust_vc::assert!(v == 0u64);
}

// LIAR r6-l15: b6: a conditional write in a `match` scrutinee, read by the arm.
#[trust_vc::ensures(true)]
fn r6_b6_match_scrutinee_block_arm_reads_h(b: bool) {
    let mut hx: u64 = 0u64;
    let ht = (&mut hx, 1u64);
    *ht.0 = 5u64;
    let mut x: u64 = 0u64;
    let v: u64 = match ({ if b { x = 1u64; } 0u64 }) { 0u64 => x, _ => 9u64 };
    trust_vc::assert!(v == 0u64);
}

// LIAR r6-l16: i14: an `if`-condition write inside a spec assertion argument. The assertion is false.
#[trust_vc::ensures(true)]
fn r6_i14_local_ifcond_in_assert_h() {
    let mut hx: u64 = 0u64;
    let ht = (&mut hx, 1u64);
    *ht.0 = 5u64;
    let mut x: u64 = 0u64;
    trust_vc::assert!(if ({ x = 1u64; true }) { x == 0u64 } else { false });
}

// LIAR r6-l17: a6: a spec assertion nested inside another assertion's argument block was
// never emitted. `b = true` panics on the inner assertion.
#[trust_vc::ensures(true)]
fn r6_a6_spec_in_assert_arg_block_h(b: bool) {
    let mut hx: u64 = 0u64;
    let ht = (&mut hx, 1u64);
    *ht.0 = 5u64;
    let mut x: u64 = 0u64;
    trust_vc::assert!({ if b { x = 1u64; } trust_vc::assert!(x == 0u64); true });
}

// LIAR r6-l18: k5: `assert!({ assert!(false); true })` always panics.
#[trust_vc::ensures(true)]
fn r6_k5_spec_assert_arg_nested_false_h() {
    let mut hx: u64 = 0u64;
    let ht = (&mut hx, 1u64);
    *ht.0 = 5u64;
    trust_vc::assert!({ trust_vc::assert!(false); true });
}

// LIAR r6-l19: g44: statement writes inside a NON-UNIT tail block (value position). `result` is 1 or 2.
#[trust_vc::ensures(result == 0u64)]
fn r6_g44_return_block_if_else_write_tail_read_local_h(b: bool) -> u64 {
    let mut hx: u64 = 0u64;
    let ht = (&mut hx, 1u64);
    *ht.0 = 5u64;
    let mut x: u64 = 0u64;
    {
        if b {
            x = 1u64;
        } else {
            x = 2u64;
        }
        x
    }
}

// LIAR r6-l20: g40: a write inside a `let` initializer nested in a value block. `b = true` gives `v == 1`.
#[trust_vc::ensures(true)]
fn r6_g40_let_init_if_write_h(b: bool) {
    let mut hx: u64 = 0u64;
    let ht = (&mut hx, 1u64);
    *ht.0 = 5u64;
    let mut x: u64 = 0u64;
    let v: u64 = {
        let w: u64 = if b {
            x = 1u64;
            3u64
        } else {
            3u64
        };
        x
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR r6-l21: g43: writes in a `let` initializer inside the tail block. `result` is 1 or 2.
#[trust_vc::ensures(result == 0u64)]
fn r6_g43_return_block_let_init_if_else_write_local_h(b: bool) -> u64 {
    let mut hx: u64 = 0u64;
    let ht = (&mut hx, 1u64);
    *ht.0 = 5u64;
    let mut x: u64 = 0u64;
    {
        let v: u64 = {
            if b {
                x = 1u64;
            } else {
                x = 2u64;
            }
            5u64
        };
        x
    }
}

// LIAR r6-l22: an `async` block writing a plain local was modelled as run; it is never
// polled, so `x == 0`.
#[trust_vc::ensures(true)]
fn r6_async_block_write_h(c: bool) {
    let mut hx: u64 = 0u64;
    let ht = (&mut hx, 1u64);
    *ht.0 = 5u64;
    let mut x: u64 = 0u64;
    let _f = async {
        x = 5u64;
    };
    trust_vc::assert!(x == 5u64);
}

// CONTROL r6-c1 (narrowness): a PLAIN statement write beside a holder write in
// the same statement branch keeps the holder lane.
#[trust_vc::ensures(true)]
fn r6_plain_statement_write_beside_holder_write_verifies(b: bool) {
    let mut x: u64 = 0u64;
    let mut v: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        *t.0 = 2u64;
        v = 3u64;
    }
    trust_vc::assert!(v == 0u64 || v == 3u64);
    trust_vc::assert!(x == 0u64 || x == 2u64);
}

// LIAR r6-l23: the same body claiming the branch never ran.
#[trust_vc::ensures(true)]
fn r6_plain_statement_write_beside_holder_write_refuted(b: bool) {
    let mut x: u64 = 0u64;
    let mut v: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        *t.0 = 2u64;
        v = 3u64;
    }
    trust_vc::assert!(v == 0u64);
}
"#;

// LIAR r6-l24 (file-level `cfg`): the registries resolve `K` to the compiled-OUT
// definition (1); the compiled `K` is 2, so `x == 1u64` is false. Its own
// fixture, because a file-level `cfg` refuses every holder in the file.
const SRC_R6_CFG: &str = r#"
#[cfg(any())]
const K: u64 = 1u64;
#[cfg(not(any()))]
const K: u64 = 2u64;

#[trust_vc::ensures(true)]
fn r6_cfg_selected_const_holder_write() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    *t.0 = K;
    trust_vc::assert!(x == 1u64);
}
"#;

/// The `ht` holder write LHS in the deref refusal.
const HOLDER_WRITE_HT: &str = "`* ht . 0`";

/// The `h.x` struct-holder write LHS in the deref refusal.
const HOLDER_MEMBER_WRITE_R6: &str = "`* h . x`";

fn expect_refused_r6(id: &str, func: &str, src: &str, fragment: &str) {
    match verify(id, func, src) {
        VerifyResult::Error { message }
            if message.contains(DEREF_REFUSAL) && message.contains(fragment) => {}
        other => panic!(
            "{func}: expected the fail-closed error containing {DEREF_REFUSAL:?} and {fragment:?}, got {other:?}"
        ),
    }
}

#[test]
fn liar_r6_lbl_let_holder_incidental_is_refused() {
    expect_refused_r6("r6l1", "r6_lbl_let_holder_incidental", SRC_R6, HOLDER_WRITE);
}

#[test]
fn liar_r6_lbl_ret_holder_read_is_refused() {
    expect_refused_r6("r6l2", "r6_lbl_ret_holder_read", SRC_R6, HOLDER_WRITE);
}

#[test]
fn liar_r6_rhs_labelled_is_refused() {
    expect_refused_r6("r6l3", "r6_rhs_labelled", SRC_R6, HOLDER_WRITE);
}

#[test]
fn liar_r6_gen5_labelled_return_struct_holder_is_refused() {
    expect_refused_r6(
        "r6l4",
        "r6_gen5_labelled_return_struct_holder",
        SRC_R6,
        HOLDER_MEMBER_WRITE_R6,
    );
}

#[test]
fn liar_r6_j_aa_holder_is_refused() {
    expect_refused_r6("r6l5", "r6_j_aa_holder", SRC_R6, HOLDER_WRITE);
}

#[test]
fn liar_r6_aa_holder_rhs_block_is_refused() {
    expect_refused_r6("r6l6", "r6_aa_holder_rhs_block", SRC_R6, HOLDER_WRITE);
}

#[test]
fn liar_r6_j_cl_holder_is_refused() {
    expect_refused_r6("r6l7", "r6_j_cl_holder", SRC_R6, HOLDER_WRITE);
}

#[test]
fn liar_r6_cl_holder_rhs_block_is_refused() {
    expect_refused_r6("r6l8", "r6_cl_holder_rhs_block", SRC_R6, HOLDER_WRITE);
}

#[test]
fn liar_r6_g1_ifcond_uncond_assign_h_is_refused() {
    expect_refused_r6(
        "r6l9",
        "r6_g1_ifcond_uncond_assign_h",
        SRC_R6,
        HOLDER_WRITE_HT,
    );
}

#[test]
fn liar_r6_g2_match_scrutinee_uncond_assign_h_is_refused() {
    expect_refused_r6(
        "r6l10",
        "r6_g2_match_scrutinee_uncond_assign_h",
        SRC_R6,
        HOLDER_WRITE_HT,
    );
}

#[test]
fn liar_r6_g3_return_ifcond_uncond_assign_h_is_refused() {
    expect_refused_r6(
        "r6l11",
        "r6_g3_return_ifcond_uncond_assign_h",
        SRC_R6,
        HOLDER_WRITE_HT,
    );
}

#[test]
fn liar_r6_g4_return_match_scrutinee_h_is_refused() {
    expect_refused_r6(
        "r6l12",
        "r6_g4_return_match_scrutinee_h",
        SRC_R6,
        HOLDER_WRITE_HT,
    );
}

#[test]
fn liar_r6_g5_ifcond_else_reads_h_is_refused() {
    expect_refused_r6(
        "r6l13",
        "r6_g5_ifcond_else_reads_h",
        SRC_R6,
        HOLDER_WRITE_HT,
    );
}

#[test]
fn liar_r6_b5_if_cond_block_then_reads_h_is_refused() {
    expect_refused_r6(
        "r6l14",
        "r6_b5_if_cond_block_then_reads_h",
        SRC_R6,
        HOLDER_WRITE_HT,
    );
}

#[test]
fn liar_r6_b6_match_scrutinee_block_arm_reads_h_is_refused() {
    expect_refused_r6(
        "r6l15",
        "r6_b6_match_scrutinee_block_arm_reads_h",
        SRC_R6,
        HOLDER_WRITE_HT,
    );
}

#[test]
fn liar_r6_i14_local_ifcond_in_assert_h_is_refused() {
    expect_refused_r6(
        "r6l16",
        "r6_i14_local_ifcond_in_assert_h",
        SRC_R6,
        HOLDER_WRITE_HT,
    );
}

#[test]
fn liar_r6_a6_spec_in_assert_arg_block_h_is_refused() {
    expect_refused_r6(
        "r6l17",
        "r6_a6_spec_in_assert_arg_block_h",
        SRC_R6,
        HOLDER_WRITE_HT,
    );
}

#[test]
fn liar_r6_k5_spec_assert_arg_nested_false_h_is_refused() {
    expect_refused_r6(
        "r6l18",
        "r6_k5_spec_assert_arg_nested_false_h",
        SRC_R6,
        HOLDER_WRITE_HT,
    );
}

#[test]
fn liar_r6_g44_return_block_if_else_write_tail_read_local_h_is_refused() {
    expect_refused_r6(
        "r6l19",
        "r6_g44_return_block_if_else_write_tail_read_local_h",
        SRC_R6,
        HOLDER_WRITE_HT,
    );
}

#[test]
fn liar_r6_g40_let_init_if_write_h_is_refused() {
    expect_refused_r6(
        "r6l20",
        "r6_g40_let_init_if_write_h",
        SRC_R6,
        HOLDER_WRITE_HT,
    );
}

#[test]
fn liar_r6_g43_return_block_let_init_if_else_write_local_h_is_refused() {
    expect_refused_r6(
        "r6l21",
        "r6_g43_return_block_let_init_if_else_write_local_h",
        SRC_R6,
        HOLDER_WRITE_HT,
    );
}

#[test]
fn liar_r6_async_block_write_h_is_refused() {
    expect_refused_r6("r6l22", "r6_async_block_write_h", SRC_R6, HOLDER_WRITE_HT);
}

#[test]
fn liar_r6_cfg_selected_const_holder_write_is_refused() {
    expect_refused_r6(
        "r6l24",
        "r6_cfg_selected_const_holder_write",
        SRC_R6_CFG,
        HOLDER_WRITE,
    );
}

#[test]
fn control_r6_plain_statement_write_beside_holder_write_verifies() {
    match verify(
        "r6c1",
        "r6_plain_statement_write_beside_holder_write_verifies",
        SRC_R6,
    ) {
        VerifyResult::Verified => {}
        other => panic!("expected Verified, got {other:?}"),
    }
}

#[test]
fn liar_r6_plain_statement_write_beside_holder_write_refuted() {
    match verify(
        "r6l23",
        "r6_plain_statement_write_beside_holder_write_refuted",
        SRC_R6,
    ) {
        VerifyResult::Counterexample { .. } => {}
        other => panic!("expected Counterexample, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Review round 2 of the holder-only split (2026-09-15): HEAD false-Verified
// holes still reachable in a body that passed every round-1 disqualifier, each
// reproduced on the pre-fix split build (Verified; HEAD refuses the body with
// the deref refusal; every claim is FALSE at runtime under stock rustc debug)
// and closed by NARROWING admission only. Body-level rules: any nested item,
// any `let` expression (`if let` / let chains), any call expression, and an
// assignment whose left-hand side is not a bare identifier or a dereference
// (`body_extract::holder_admission_body_disqualified`); function-level: a
// function whose tokens (and the file items it names) mix integer types or
// mention `self` / `Self`; file-level: a `mod` item, a `const` generic
// parameter, a `Drop` token, or an item-position macro outside function bodies
// (`vc_extraction::holder_lane_file_admissible`). The file-level probes sit in
// their own fixtures because each refuses every holder in its file.
// ---------------------------------------------------------------------------
const SRC_R7: &str = r#"
const K: u64 = 2u64;
const KW: u32 = 0u32;
type Byte = u8;

struct Pl8 {
    f: u8,
    g: u8,
}

fn inc_nc(v: u8) -> u8 {
    v + 1u8
}

// LIAR r7-l1 (confirm/final f1 p_item_after_use): a block `const` declared
// AFTER its use; rustc resolves `KW` to the block item (7), the model read the
// file-level `KW` (0). `c = false` panics on the assertion.
#[trust_vc::ensures(true)]
fn r7_item_after_use(c: bool) {
    let mut x: u8 = 0u8;
    let h = (&mut x, 1u8);
    *h.0 = 2u8;
    let v: u32 = KW;
    const KW: u32 = 7u32;
    trust_vc::assert!(v != 7u32);
}

// LIAR r7-l2 (f1 p_item_after_return): the item after an early `return`.
// `c = true` returns 7.
#[trust_vc::ensures(result != 7u32)]
fn r7_item_after_return(c: bool) -> u32 {
    let mut x: u8 = 0u8;
    let h = (&mut x, 1u8);
    if c {
        *h.0 = 1u8;
        return KW;
        const KW: u32 = 7u32;
    }
    KW
}

// LIAR r7-l3: r7-l1 with ONE integer type (the nested-item rule alone).
#[trust_vc::ensures(true)]
fn r7_item_after_use_one_width(c: bool) {
    let mut x: u32 = 0u32;
    let h = (&mut x, 1u32);
    *h.0 = 2u32;
    let v: u32 = KW;
    const KW: u32 = 7u32;
    trust_vc::assert!(v != 7u32);
}

// LIAR r7-l4 (hand2 zfinal p_fa_late_block_const): returns 1, not 2.
#[trust_vc::ensures(result == 2u64)]
fn r7_late_block_const() -> u64 {
    let mut x: u64 = 0u64;
    let t = (&mut x, 0u64);
    *t.0 = K;
    const K: u64 = 1u64;
    x
}

// LIAR r7-l5: the same with a block `static`; `x == 1`.
#[trust_vc::ensures(true)]
fn r7_late_block_static() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 0u64);
    *t.0 = K;
    static K: u64 = 1u64;
    trust_vc::assert!(x == 2u64);
}

// LIAR r7-l6 (confirm/final f2 p_mul_width): `21i32 * 21i32` was encoded at the
// `i8` parameter's width and wrapped; `a = 2` panics (`r0 == 441`).
#[trust_vc::requires(a == 2i8)]
#[trust_vc::ensures(true)]
fn r7_mul_width(a: i8) {
    let mut r0: i32 = 0i32;
    let h = (&mut r0, 1u8);
    *h.0 = 21i32 * 21i32;
    trust_vc::assert!(r0 != 441i32);
}

// LIAR r7-l7 (f2 p_mul_width_disj, reduced from generator hit p_403608).
#[trust_vc::ensures(true)]
fn r7_mul_width_disj(a: i8) {
    let mut r0: i32 = (-3i32);
    let mut f3: i32 = (31i32 - 10i32);
    let u0 = (1u8, &mut r0);
    *(u0.1) = (f3 * f3);
    assert!((a != 2i8) || (r0 != 441i32));
}

// LIAR r7-l8: the narrow width hidden behind a `type` alias (no `u8` token in
// the function). `a = 2` panics.
#[trust_vc::requires(a == a)]
#[trust_vc::ensures(true)]
fn r7_mul_width_type_alias(a: Byte) {
    let mut r0: i32 = 0i32;
    let h = (&mut r0, 1i32);
    *h.0 = 21i32 * 21i32;
    trust_vc::assert!(a != a || r0 != 441i32);
}

// LIAR r7-l9 (hand2 p_fe_field_assign_ovf, one width): a struct-field
// assignment got no overflow obligation; `n = 255` panics.
#[trust_vc::ensures(true)]
fn r7_field_assign_ovf(n: u8) {
    let mut x: u8 = 0u8;
    let t = (&mut x, 0u8);
    let mut s = Pl8 { f: 0u8, g: 0u8 };
    s.f = n + 1u8;
    *t.0 = 1u8;
}

// LIAR r7-l10 (p_fe_underscore_assign_div): `_ = 100u8 / n`; `n = 0` panics.
#[trust_vc::ensures(true)]
fn r7_underscore_assign_div(n: u8) {
    let mut x: u8 = 0u8;
    let t = (&mut x, 0u8);
    _ = 100u8 / n;
    *t.0 = 1u8;
}

// LIAR r7-l11 (hand2 u18): a tuple-field compound assignment; `n = 1` panics.
#[trust_vc::ensures(true)]
fn r7_tuple_field_compound_sub(n: u8) {
    let mut x: u8 = 0u8;
    let t = (&mut x, 0u8);
    let mut p = (0u8, 0u8);
    p.1 -= n;
    *t.0 = 1u8;
}

// LIAR r7-l12 (p_fg_iflet_scrutinee_ovf): an `if let` scrutinee got no
// overflow obligation; `n = 255` panics.
#[trust_vc::ensures(true)]
fn r7_iflet_scrutinee_ovf(n: u8) {
    let mut x: u8 = 0u8;
    let t = (&mut x, 0u8);
    if let 0u8 = n + 1u8 {
        *t.0 = 1u8;
    }
}

// LIAR r7-l13 (p_fh_iflet_mut_binding): `y = 5u8` writes the pattern binding,
// not the outer `y`; `o = Some(_)` panics.
#[trust_vc::ensures(true)]
fn r7_iflet_mut_binding(o: Option<u8>) {
    let mut x: u8 = 0u8;
    let t = (&mut x, 0u8);
    *t.0 = 1u8;
    let mut y: u8 = 0u8;
    if let Some(mut y) = o {
        y = 5u8;
    } else {
        y = 5u8;
    }
    trust_vc::assert!(y == 5u8);
}

// LIAR r7-l14 (p_fd_callee_nocontract_ovf): the contract-less callee
// overflows for `n = 255`; its safety obligation never reached the call site.
#[trust_vc::ensures(true)]
fn r7_callee_nocontract_ovf(n: u8) {
    let mut x: u8 = 0u8;
    let t = (&mut x, 0u8);
    *t.0 = inc_nc(n);
}

// CONTROL r7-c1 (narrowness): in the same fixture, a one-width holder body
// that reads the file-level `K` and uses none of the refused shapes still
// verifies (the fixture is not refused wholesale).
#[trust_vc::ensures(true)]
fn r7_one_width_holder_reads_file_const_verifies(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        *t.0 = K;
    }
    trust_vc::assert!(x == 0u64 || x == 2u64);
}

// LIAR r7-l18 (narrowness twin of r7-c1): the same body claiming the branch
// never ran is refuted, not refused.
#[trust_vc::ensures(true)]
fn r7_one_width_holder_reads_file_const_refuted(b: bool) {
    let mut x: u64 = 0u64;
    let t = (&mut x, 1u64);
    if b {
        *t.0 = K;
    }
    trust_vc::assert!(x == 0u64);
}
"#;

const SRC_R7_MOD: &str = r#"
const K: u64 = 2u64;

mod ma {
    const K: u64 = 7u64;

    // LIAR r7-l15 (hand2 p_fb_module_local_const): `K` is `ma::K` (7); the
    // bare-name registry read the crate-root `K`.
    #[trust_vc::ensures(result == 2u64)]
    pub fn r7_module_local_const() -> u64 {
        let mut x: u64 = 0u64;
        let t = (&mut x, 0u64);
        *t.0 = K;
        x
    }
}
"#;

const SRC_R7_CONST_GENERIC: &str = r#"
const K: u64 = 2u64;

// LIAR r7-l16 (hand2 p_fc_const_generic): the const generic `K` shadows the
// file const; `r7_const_generic::<1>()` returns 1.
#[trust_vc::ensures(result == 2u64)]
fn r7_const_generic<const K: u64>() -> u64 {
    let mut x: u64 = 0u64;
    let t = (&mut x, 0u64);
    *t.0 = K;
    x
}
"#;

const SRC_R7_DROP: &str = r#"
struct Guard {
    v: u64,
}

impl Drop for Guard {
    fn drop(&mut self) {
        if self.v == 5u64 {
            panic!();
        }
    }
}

// LIAR r7-l17 (hand2 p_fd_guard_drop_panics): the guard's destructor panics
// when the inner block ends; the model never runs drop glue.
#[trust_vc::ensures(true)]
fn r7_guard_drop_panics() {
    let mut x: u64 = 0u64;
    let t = (&mut x, 0u64);
    {
        let g = Guard { v: 5u64 };
    }
    *t.0 = 1u64;
}
"#;

/// The `h` tuple-holder write LHS in the deref refusal.
const HOLDER_WRITE_H: &str = "`* h . 0`";

#[test]
fn liar_r7_item_after_use_is_refused() {
    expect_refused_in("r7l1", "r7_item_after_use", SRC_R7, HOLDER_WRITE_H);
}

#[test]
fn liar_r7_item_after_return_is_refused() {
    expect_refused_in("r7l2", "r7_item_after_return", SRC_R7, HOLDER_WRITE_H);
}

#[test]
fn liar_r7_item_after_use_one_width_is_refused() {
    expect_refused_in(
        "r7l3",
        "r7_item_after_use_one_width",
        SRC_R7,
        HOLDER_WRITE_H,
    );
}

#[test]
fn liar_r7_late_block_const_is_refused() {
    expect_refused_in("r7l4", "r7_late_block_const", SRC_R7, HOLDER_WRITE);
}

#[test]
fn liar_r7_late_block_static_is_refused() {
    expect_refused_in("r7l5", "r7_late_block_static", SRC_R7, HOLDER_WRITE);
}

#[test]
fn liar_r7_mul_width_is_refused() {
    expect_refused_in("r7l6", "r7_mul_width", SRC_R7, HOLDER_WRITE_H);
}

#[test]
fn liar_r7_mul_width_disj_is_refused() {
    expect_refused_in("r7l7", "r7_mul_width_disj", SRC_R7, "`* (u0 . 1)`");
}

#[test]
fn liar_r7_mul_width_type_alias_is_refused() {
    expect_refused_in("r7l8", "r7_mul_width_type_alias", SRC_R7, HOLDER_WRITE_H);
}

#[test]
fn liar_r7_field_assign_ovf_is_refused() {
    expect_refused_in("r7l9", "r7_field_assign_ovf", SRC_R7, HOLDER_WRITE);
}

#[test]
fn liar_r7_underscore_assign_div_is_refused() {
    expect_refused_in("r7l10", "r7_underscore_assign_div", SRC_R7, HOLDER_WRITE);
}

#[test]
fn liar_r7_tuple_field_compound_sub_is_refused() {
    expect_refused_in("r7l11", "r7_tuple_field_compound_sub", SRC_R7, HOLDER_WRITE);
}

#[test]
fn liar_r7_iflet_scrutinee_ovf_is_refused() {
    expect_refused_in("r7l12", "r7_iflet_scrutinee_ovf", SRC_R7, HOLDER_WRITE);
}

#[test]
fn liar_r7_iflet_mut_binding_is_refused() {
    expect_refused_in("r7l13", "r7_iflet_mut_binding", SRC_R7, HOLDER_WRITE);
}

#[test]
fn liar_r7_callee_nocontract_ovf_is_refused() {
    expect_refused_in("r7l14", "r7_callee_nocontract_ovf", SRC_R7, HOLDER_WRITE);
}

#[test]
fn liar_r7_module_local_const_is_refused() {
    expect_refused_in("r7l15", "r7_module_local_const", SRC_R7_MOD, HOLDER_WRITE);
}

#[test]
fn liar_r7_const_generic_is_refused() {
    expect_refused_in(
        "r7l16",
        "r7_const_generic",
        SRC_R7_CONST_GENERIC,
        HOLDER_WRITE,
    );
}

#[test]
fn liar_r7_guard_drop_panics_is_refused() {
    expect_refused_in("r7l17", "r7_guard_drop_panics", SRC_R7_DROP, HOLDER_WRITE);
}

#[test]
fn control_r7_one_width_holder_reads_file_const_verifies() {
    match verify(
        "r7c1",
        "r7_one_width_holder_reads_file_const_verifies",
        SRC_R7,
    ) {
        VerifyResult::Verified => {}
        other => panic!("expected Verified, got {other:?}"),
    }
}

#[test]
fn liar_r7_one_width_holder_reads_file_const_refuted() {
    match verify(
        "r7l18",
        "r7_one_width_holder_reads_file_const_refuted",
        SRC_R7,
    ) {
        VerifyResult::Counterexample { .. } => {}
        other => panic!("expected Counterexample, got {other:?}"),
    }
}
