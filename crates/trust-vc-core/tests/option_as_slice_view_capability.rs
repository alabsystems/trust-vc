// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY + SOUNDNESS PIN (mut_refs_libs `test_options_as_mut_slice::
//! test_as_slice_none` / `test_as_slice_some` / `fail_as_slice_none` /
//! `fail_as_slice_some`, 2026-09-16): `Option::<T>::as_slice()` on a receiver
//! whose state is KNOWN at the call is a pure `Seq<T>` VIEW in spec lowering.
//! `None.as_slice()` lowers to the empty `Seq<T>` constructor that `seq![]` /
//! `vec![]` root their push chains at, and `Some(v).as_slice()` lowers to the
//! one-element push chain `Push(empty, v)` — the term `vec![v]` builds — so
//! `.len()`, `[i]` (with the existing Seq index bounds obligation) and `==`
//! take the push-chain length axioms the encoder already tracks. The view is
//! a value SNAPSHOT of the receiver at the call: the extractor substitutes the
//! receiver's scoped constructor string into the bound local BEFORE it poisons
//! the receiver, and that poison is deliberately kept (g4, g10).
//!
//! Admission is exactly one shape, in `lower_option_method_call` only: a
//! zero-argument `as_slice` call whose receiver type is `Option<T>` with `T`
//! `bool` or a primitive integer, and whose `known_option_binding` answers a
//! known `None` or a known `Some` with a lowered payload. Everything adjacent
//! fails closed with a pinned text: an unknown or partially known state (a
//! parameter even under `requires(x.is_some())`, an `if`-joined local, a
//! field projection: g1 / g7 / g9 / g11 — no `ite` form is admitted), a
//! payload that is not `bool` / integer (nested `Option`, tuple, `Seq`,
//! `char`: g2 / g6 / g13 / g14), `as_mut_slice` (kept OUT of the Option method
//! set, so it keeps the generic "not available in specification context"
//! refusal: g3 / g12), a `Vec` literal receiver (g5, unchanged from HEAD), a
//! receiver written in a loop before the call (g8 — the extractor's loop
//! havoc poisons `x` BEFORE the view is lowered, so this pins a pre-existing
//! refusal the view sits behind, not new code), and any read of the receiver
//! after the call (g4 / g10, the pre-existing receiver poison).
//! An out-of-range literal index on the view is a COUNTEREXAMPLE on the Seq
//! index bounds obligation, never `Verified` (b1 / b2), and element
//! arithmetic on the view is checked at the payload's width (c20 / l20).
//!
//! REVIEW NARROWING (2026-09-16, finding "declared `Option<u8>` receiver with
//! an unsuffixed payload is viewed as `Seq<i32>`"): the extractor records
//! `let x: Option<u8> = Some(200);` as `Option<i32>` — a `let` annotation is
//! carried only for a bare primitive-integer binding — so the first cut of
//! this capability discharged `s[0usize] + 100u8` at 32 bits and VERIFIED a
//! program that panics on u8 overflow (g15). A defaulted literal, a computed
//! payload over defaulted literals (g18) and a genuine `i32` (g21 / g22) are
//! indistinguishable in lowering, so every `Option<i32>` receiver now fails
//! closed with one pinned text (g15-g22); `c4` / `l4` (declared `Option<u8>`,
//! unsuffixed `Some(7)`) and `c6` / `l6` (`Some(-3i32)`) were re-keyed from
//! control/liar to gated as g15 / g21. A declared `Option<u8> = None` keeps
//! the annotation and still takes the view (c21 / l21).
//!
//! RE-KEYED 2026-09-18 by the `let` ANNOTATION WIDTH CARRY
//! (`vc_extraction::declared_width`). The premise of that narrowing — "a
//! declared `Option<uN>` is recorded as `Option<i32>`" — is no longer true: the
//! ascription now carries `uN` into the payload, so such a receiver arrives as
//! `Option<uN>` and TAKES the view. FIVE gated cases became controls / liars —
//! g15 -> c25 (`Verified`), g16 -> l25 (`Counterexample`), g17 -> c26 (a
//! genuine `overflow_check_0` counterexample, which is the soundness pin: the
//! shape that VERIFIED before the narrowing is now REFUTED rather than merely
//! refused), g20 -> c27 (`Verified`, the `Seq<u8>` sorts match), g23 -> c28.
//! g18 stays refused on a DIFFERENT arm (the carry's WALL: a computed payload
//! is not a literal the ascription fixes), and g19 / g21 / g22 / g24 stay
//! refused on the ORIGINAL text — they are the H1b backward-inference class,
//! which the carry does not touch. The `Option<i32>` refusal itself is
//! UNCHANGED, deliberately: `200i32` and `200` are the same
//! `IntLit { ty: Int { width: 32 } }` after lowering, so telling a decided
//! `i32` from an undecided one needs a type channel this increment did not
//! build.
//!
//! Every control has a runtime-false liar; `runtime_twins_execute_std_behavior`
//! executes std twins of every control and liar under stock rustc so the
//! pinned truth values are the program's, not the model's. c12 / l12 (the
//! view passed to a contract-less callee whose body is inlined) and c19 / l19
//! (a shared-reference payload erased to its scalar) exercise PRE-EXISTING
//! mechanisms the view merely flows through; they are pinned as regression
//! guards, not as new claims.
//!
//! 69 cases: 25 controls, 23 liars, 2 bounds liars, 19 gated (re-counted
//! 2026-09-18 after the width-carry re-key above; six gated cases were
//! re-keyed — five to controls/liars and g18 to the constant-arithmetic
//! control c29 — and g29 was added for the wall's real domain, so controls
//! went 20 -> 25 and gated 24 -> 19). 70 tests: the 69 plus
//! `runtime_twins_execute_std_behavior`.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_oasv_{}_{}.rs", std::process::id(), tmp_id));
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

fn assert_verified(func: &str) {
    let result = verify(func, func, SRC);
    assert!(
        matches!(result, VerifyResult::Verified),
        "{func} should verify, got: {result:?}"
    );
}

fn assert_counterexample(func: &str, obligation_needle: &str) {
    let result = verify(func, func, SRC);
    match &result {
        VerifyResult::Counterexample { obligation_name, .. } => assert!(
            obligation_name.contains(obligation_needle),
            "{func} should fail on an obligation containing {obligation_needle:?}, got: {obligation_name}"
        ),
        other => panic!("{func} should be a Counterexample, got: {other:?}"),
    }
}

fn assert_gated(func: &str, needles: &[&str]) {
    let result = verify(func, func, SRC);
    let VerifyResult::Error { message } = &result else {
        panic!("{func} should fail closed with Error, got: {result:?}");
    };
    for needle in needles {
        assert!(
            message.contains(needle),
            "{func} refusal should contain {needle:?}, got: {message}"
        );
    }
}

const SRC: &str = r#"
struct Holder {
    o: Option<u64>,
}

// CONTROL c1: known None view has length 0.
#[trust_vc::ensures(true)]
fn c1_none_len_verifies() {
    let x = Option::<u64>::None;
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 0usize);
}

// CONTROL c2: known Some view has length 1 and the payload at index 0.
#[trust_vc::ensures(true)]
fn c2_some_len_index_verifies() {
    let x = Some(20u64);
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 1usize);
    trust_vc::assert!(s[0usize] == 20u64);
}

// CONTROL c3: bool payload.
#[trust_vc::ensures(true)]
fn c3_bool_payload_verifies() {
    let x = Some(true);
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 1usize);
    trust_vc::assert!(s[0usize] == true);
}

// GATED g15 (was CONTROL c4): unsuffixed payload literal under a declared
// Option<u8> — the extractor drops the annotation, the receiver is recorded as
// Option<i32>, and the view is refused wholesale.
#[trust_vc::ensures(true)]
fn c25_unsuffixed_payload_declared_u8_verifies() {
    let x: Option<u8> = Some(7);
    let s = x.as_slice();
    trust_vc::assert!(s[0usize] == 7u8);
}

// CONTROL c5: `None::<u64>` spelling (the runtime witness spelling).
#[trust_vc::ensures(true)]
fn c5_none_turbofish_verifies() {
    let x = None::<u64>;
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 0usize);
}

// GATED g21 (was CONTROL c6): a genuine, suffixed i32 payload is refused with
// the same text — the over-refusal is deliberate (see the module doc).
#[trust_vc::ensures(true)]
fn g21_suffixed_i32_payload_gated() {
    let x = Some(-3i32);
    let s = x.as_slice();
    trust_vc::assert!(s[0usize] == -3i32);
}

// CONTROL c6: signed payload of a non-i32 width.
#[trust_vc::ensures(true)]
fn c6_signed_payload_verifies() {
    let x = Some(-3i64);
    let s = x.as_slice();
    trust_vc::assert!(s[0usize] == -3i64);
}

// CONTROL c7: parameter payload (a lowered value, not a literal).
#[trust_vc::ensures(true)]
fn c7_param_payload_verifies(v: u64) {
    let x = Some(v);
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 1usize);
    trust_vc::assert!(s[0usize] == v);
}

// CONTROL c8: rebinding the receiver before the call is honoured.
#[trust_vc::ensures(true)]
fn c8_rebound_receiver_verifies() {
    let mut x = Some(1u64);
    x = None;
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 0usize);
}

// CONTROL c9: shadowed receiver uses the innermost binding.
#[trust_vc::ensures(true)]
fn c9_shadowed_receiver_verifies() {
    let x = Some(1u64);
    let x = Option::<u64>::None;
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 0usize);
}

// CONTROL c10: the view taken inline in the assertion.
#[trust_vc::ensures(true)]
fn c10_inline_view_verifies() {
    let x = Some(20u64);
    trust_vc::assert!(x.as_slice().len() == 1usize);
}

// CONTROL c11: declared None of bool.
#[trust_vc::ensures(true)]
fn c11_declared_none_bool_verifies() {
    let x: Option<bool> = None;
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 0usize);
}

// LIAR l1: None view claimed length 1.
#[trust_vc::ensures(true)]
fn l1_none_len_one_refuted() {
    let x = Option::<u64>::None;
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 1usize);
}

// LIAR l2a: wrong payload.
#[trust_vc::ensures(true)]
fn l2a_some_wrong_payload_refuted() {
    let x = Some(20u64);
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 1usize);
    trust_vc::assert!(s[0usize] == 21u64);
}

// LIAR l2b: Some view claimed empty.
#[trust_vc::ensures(true)]
fn l2b_some_len_zero_refuted() {
    let x = Some(20u64);
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 0usize);
}

// LIAR l3: bool payload negated.
#[trust_vc::ensures(true)]
fn l3_bool_payload_refuted() {
    let x = Some(true);
    let s = x.as_slice();
    trust_vc::assert!(s[0usize] == false);
}

// GATED g16 (was LIAR l4): the unsuffixed-payload shape is refused whatever
// the claim — a false claim is never reached as a verdict.
#[trust_vc::ensures(true)]
fn l25_unsuffixed_payload_declared_u8_false_claim_refuted() {
    let x: Option<u8> = Some(7);
    let s = x.as_slice();
    trust_vc::assert!(s[0usize] == 8u8);
}

// LIAR l5: turbofish None claimed non-empty.
#[trust_vc::ensures(true)]
fn l5_none_turbofish_refuted() {
    let x = None::<u64>;
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 1usize);
}

// LIAR l6: signed payload sign flipped.
#[trust_vc::ensures(true)]
fn l6_signed_payload_refuted() {
    let x = Some(-3i64);
    let s = x.as_slice();
    trust_vc::assert!(s[0usize] == 3i64);
}

// LIAR l7: parameter payload claimed empty.
#[trust_vc::ensures(true)]
fn l7_param_payload_refuted(v: u64) {
    let x = Some(v);
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 0usize);
}

// LIAR l8: rebound receiver claimed to still be Some.
#[trust_vc::ensures(true)]
fn l8_rebound_receiver_refuted() {
    let mut x = Some(1u64);
    x = None;
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 1usize);
}

// LIAR l9: shadowed receiver claimed to be the outer Some.
#[trust_vc::ensures(true)]
fn l9_shadowed_receiver_refuted() {
    let x = Some(1u64);
    let x = Option::<u64>::None;
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 1usize);
}

// LIAR l10: inline view claimed empty.
#[trust_vc::ensures(true)]
fn l10_inline_view_refuted() {
    let x = Some(20u64);
    trust_vc::assert!(x.as_slice().len() == 0usize);
}

// LIAR l11: declared None of bool claimed non-empty.
#[trust_vc::ensures(true)]
fn l11_declared_none_bool_refuted() {
    let x: Option<bool> = None;
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 1usize);
}

// BOUNDS LIAR b1: index into the empty view.
#[trust_vc::ensures(true)]
fn b1_none_index_out_of_bounds() {
    let x = Option::<u64>::None;
    let s = x.as_slice();
    trust_vc::assert!(s[0usize] == 0u64);
}

// BOUNDS LIAR b2: index 1 into the one-element view.
#[trust_vc::ensures(true)]
fn b2_some_index_out_of_bounds() {
    let x = Some(20u64);
    let s = x.as_slice();
    trust_vc::assert!(s[1usize] == 20u64);
}

// GATED g1: unknown state (parameter).
#[trust_vc::ensures(true)]
fn g1_unknown_state_param_gated(x: Option<u64>) {
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 0usize);
}

// GATED g2: nested Option payload.
#[trust_vc::ensures(true)]
fn g2_nested_option_payload_gated() {
    let x = Some(Some(1u64));
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 1usize);
}

// GATED g3: as_mut_slice keeps the generic refusal.
#[trust_vc::ensures(true)]
fn g3_as_mut_slice_gated() {
    let mut x = Some(20u64);
    let s = x.as_mut_slice();
    trust_vc::assert!(s.len() == 1usize);
}

// GATED g4: the receiver stays poisoned after the call.
#[trust_vc::ensures(true)]
fn g4_receiver_read_after_call_gated() {
    let x = Some(20u64);
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 1usize);
    trust_vc::assert!(x.is_some());
}

// GATED g5: non-Option receiver.
#[trust_vc::ensures(true)]
fn g5_vec_as_slice_gated() {
    let v = vec![1u64];
    let s = v.as_slice();
    trust_vc::assert!(s.len() == 1usize);
}

// GATED g6: tuple payload.
#[trust_vc::ensures(true)]
fn g6_tuple_payload_gated() {
    let x = Some((1u64, 2u64));
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 1usize);
}

// GATED g7: conditional receiver state.
#[trust_vc::ensures(true)]
fn g7_conditional_state_gated(b: bool) {
    let x = if b { Some(1u64) } else { None };
    let s = x.as_slice();
    trust_vc::assert!(s.len() <= 1usize);
}

// GATED g8: receiver written in a loop body before the call. The extractor's
// loop havoc poisons `x` before the view is lowered (HEAD refuses identically),
// so this is a regression guard on the refusal the view sits behind.
#[trust_vc::ensures(true)]
fn g8_loop_havoced_receiver_gated() {
    let mut x = Some(1u64);
    let mut i = 0u64;
    while i < 2u64 {
        x = None;
        i += 1u64;
    }
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 0usize);
}

// GATED g9: field-projected receiver.
#[trust_vc::ensures(true)]
fn g9_field_receiver_gated() {
    let h = Holder { o: Some(1u64) };
    let s = h.o.as_slice();
    trust_vc::assert!(s.len() == 1usize);
}

// GATED g10: two views of the same receiver (second read after poison).
#[trust_vc::ensures(true)]
fn g10_second_view_gated() {
    let x = Some(20u64);
    let s = x.as_slice();
    let t = x.as_slice();
    trust_vc::assert!(s.len() == t.len());
}

// GATED g11: known Some with a requires-constrained parameter receiver.
#[trust_vc::ensures(true)]
#[trust_vc::requires(x.is_some())]
fn g11_requires_some_param_gated(x: Option<u64>) {
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 1usize);
}

// GATED g12: write through the view.
#[trust_vc::ensures(true)]
fn g12_write_through_view_gated() {
    let mut x = Some(20u64);
    let s = x.as_mut_slice();
    s[0] = 30u64;
    trust_vc::assert!(s[0usize] == 30u64);
}

// GATED g13: Some holding a Seq payload.
#[trust_vc::ensures(true)]
fn g13_vec_payload_gated() {
    let x = Some(vec![1u64]);
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 1usize);
}

fn takes_len(s: &[u64]) -> usize {
    s.len()
}

fn takes_len_plus_one(s: &[u64]) -> usize {
    s.len() + 1usize
}

// GATED g14: char payload.
#[trust_vc::ensures(true)]
fn g14_char_payload_gated() {
    let x = Some('a');
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 1usize);
}

// CONTROL c12: the view flows into a contract-less callee (body inlined, as a
// slice literal does at HEAD).
#[trust_vc::ensures(true)]
fn c12_view_call_argument_verifies() {
    let x = Some(20u64);
    let s = x.as_slice();
    let n = takes_len(s);
    trust_vc::assert!(n == 1usize);
}

// LIAR l12a: callee result claimed 0.
#[trust_vc::ensures(true)]
fn l12a_view_call_argument_refuted() {
    let x = Some(20u64);
    let s = x.as_slice();
    let n = takes_len(s);
    trust_vc::assert!(n == 0usize);
}

// LIAR l12b: a callee that adds one, claimed unchanged.
#[trust_vc::ensures(true)]
fn l12b_view_call_argument_plus_one_refuted() {
    let x = Some(20u64);
    let s = x.as_slice();
    let n = takes_len_plus_one(s);
    trust_vc::assert!(n == 1usize);
}

// CONTROL c13: the view compared element-wise with a vec! literal.
#[trust_vc::ensures(true)]
fn c13_view_against_vec_literal_verifies() {
    let x = Some(20u64);
    let s = x.as_slice();
    let t = vec![20u64];
    trust_vc::assert!(s.len() == t.len());
    trust_vc::assert!(s[0usize] == t[0usize]);
}

// LIAR l13: different element.
#[trust_vc::ensures(true)]
fn l13_view_against_vec_literal_refuted() {
    let x = Some(20u64);
    let s = x.as_slice();
    let t = vec![21u64];
    trust_vc::assert!(s[0usize] == t[0usize]);
}

// CONTROL c14: usize payload.
#[trust_vc::ensures(true)]
fn c14_usize_payload_verifies() {
    let x = Some(3usize);
    let s = x.as_slice();
    trust_vc::assert!(s[0usize] == 3usize);
}

// LIAR l14: usize payload off by one.
#[trust_vc::ensures(true)]
fn l14_usize_payload_refuted() {
    let x = Some(3usize);
    let s = x.as_slice();
    trust_vc::assert!(s[0usize] == 4usize);
}

// CONTROL c15: a computed payload over a parameter.
#[trust_vc::ensures(true)]
fn c15_computed_payload_verifies(a: u64) {
    let x = Some(a % 4u64);
    let s = x.as_slice();
    trust_vc::assert!(s[0usize] < 4u64);
}

// LIAR l15: bound too tight.
#[trust_vc::ensures(true)]
fn l15_computed_payload_refuted(a: u64) {
    let x = Some(a % 4u64);
    let s = x.as_slice();
    trust_vc::assert!(s[0usize] < 3u64);
}

// CONTROL c16: the view rebound to another local.
#[trust_vc::ensures(true)]
fn c16_view_rebound_verifies() {
    let x = Some(20u64);
    let s = x.as_slice();
    let t = s;
    trust_vc::assert!(t.len() == 1usize);
}

// LIAR l16: rebound view claimed empty.
#[trust_vc::ensures(true)]
fn l16_view_rebound_refuted() {
    let x = Some(20u64);
    let s = x.as_slice();
    let t = s;
    trust_vc::assert!(t.len() == 0usize);
}

// CONTROL c17: the indexed view as the return value under an ensures.
#[trust_vc::ensures(result == 20u64)]
fn c17_view_index_return_verifies() -> u64 {
    let x = Some(20u64);
    let s = x.as_slice();
    s[0usize]
}

// LIAR l17: wrong postcondition.
#[trust_vc::ensures(result == 21u64)]
fn l17_view_index_return_refuted() -> u64 {
    let x = Some(20u64);
    let s = x.as_slice();
    s[0usize]
}

// CONTROL c18: the payload is a SNAPSHOT at the `Some(v)` binding, not a live
// read of `v`.
#[trust_vc::ensures(true)]
fn c18_payload_snapshot_verifies() {
    let mut v = 1u64;
    let x = Some(v);
    v = 2u64;
    let s = x.as_slice();
    trust_vc::assert!(s[0usize] == 1u64);
}

// LIAR l18: the later write to `v` claimed visible through the view.
#[trust_vc::ensures(true)]
fn l18_payload_snapshot_refuted() {
    let mut v = 1u64;
    let x = Some(v);
    v = 2u64;
    let s = x.as_slice();
    trust_vc::assert!(s[0usize] == 2u64);
}

// CONTROL c19: a shared-reference payload (erased to its scalar by the
// pre-existing reference erasure; the referent is immutable).
#[trust_vc::ensures(true)]
fn c19_shared_ref_payload_verifies() {
    let v = 1u64;
    let x = Some(&v);
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 1usize);
}

// LIAR l19: shared-reference payload view claimed empty.
#[trust_vc::ensures(true)]
fn l19_shared_ref_payload_refuted() {
    let v = 1u64;
    let x = Some(&v);
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 0usize);
}

// GATED g17 (review probe p4): the shape that VERIFIED before the narrowing —
// a declared Option<u8> with an unsuffixed 200 whose view element, added to
// 100u8, overflows at runtime. Must never be Verified.
#[trust_vc::ensures(true)]
fn c26_declared_u8_unsuffixed_overflow_refuted() {
    let x: Option<u8> = Some(200);
    let s = x.as_slice();
    let y = s[0usize] + 100u8;
    trust_vc::assert!(y > 0u8);
}

// RE-KEYED from GATED g18 (review probe q2): a CONSTANT-arithmetic payload is
// decided by the ascription, so the view reads a `u8` 200 and the `+ 100u8`
// that follows overflows — the program's own behaviour.
#[trust_vc::ensures(true)]
fn c29_declared_u8_constant_payload_overflow_refuted() {
    let x: Option<u8> = Some(100 + 100);
    let s = x.as_slice();
    let y = s[0usize] + 100u8;
    trust_vc::assert!(y > 0u8);
}

// GATED g29: the wall's real domain — a NON-constant operand beside a bare
// literal, whose type this file cannot decide.
#[trust_vc::ensures(true)]
fn g29_declared_u8_non_constant_payload_gated() {
    let z = 100u8;
    let x: Option<u8> = Some(z + 100);
    let s = x.as_slice();
    let y = s[0usize] + 100u8;
    trust_vc::assert!(y > 0u8);
}

// GATED g19 (review probe q3): the unsuffixed literal bound to a local first.
#[trust_vc::ensures(true)]
fn g19_declared_u8_let_unsuffixed_payload_gated() {
    let v = 200;
    let x: Option<u8> = Some(v);
    let s = x.as_slice();
    let y = s[0usize] + 100u8;
    trust_vc::assert!(y > 0u8);
}

// GATED g20 (review probe p28): the view compared against a vec! of the
// declared width (was an encoder sort-mismatch Unknown before the narrowing).
#[trust_vc::ensures(true)]
fn c27_declared_u8_view_eq_vec_verifies() {
    let x: Option<u8> = Some(7);
    let s = x.as_slice();
    trust_vc::assert!(s == vec![7u8]);
}

// GATED g22 (review probe q4): a genuine i32 parameter payload — refused by
// the same wholesale rule.
#[trust_vc::ensures(true)]
fn g22_i32_param_payload_gated(v: i32) {
    let x = Some(v);
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 1usize);
}

// GATED g23 (review probe p24): the u8 operand on the left of the view element.
#[trust_vc::ensures(true)]
fn c28_declared_u8_unsuffixed_left_operand_refuted() {
    let x: Option<u8> = Some(200);
    let s = x.as_slice();
    let y = 100u8 + s[0usize];
    trust_vc::assert!(y > 0u8);
}

// GATED g24 (review probe q9): an unannotated unsuffixed payload IS an i32 at
// runtime, but it is indistinguishable from g15 in lowering.
#[trust_vc::ensures(true)]
fn g24_unannotated_unsuffixed_payload_gated() {
    let x = Some(7);
    let s = x.as_slice();
    trust_vc::assert!(s[0usize] == 7i32);
}

// CONTROL c20 (review probe p4s, in-range): a SUFFIXED u8 payload types the
// receiver exactly; element arithmetic on the view is checked at 8 bits.
#[trust_vc::ensures(true)]
fn c20_suffixed_u8_view_arithmetic_verifies() {
    let x = Some(200u8);
    let s = x.as_slice();
    let y = s[0usize] + 50u8;
    trust_vc::assert!(y == 250u8);
}

// LIAR l20 (review probe p4s): the same view element plus 100u8 overflows —
// refuted on the overflow check, never Verified.
#[trust_vc::ensures(true)]
fn l20_suffixed_u8_view_arithmetic_overflow_refuted() {
    let x = Some(200u8);
    let s = x.as_slice();
    let y = s[0usize] + 100u8;
    trust_vc::assert!(y > 0u8);
}

// CONTROL c21 (review probe q7): a declared `Option<u8> = None` keeps its
// annotation (there is no literal to default) and takes the view.
#[trust_vc::ensures(true)]
fn c21_declared_u8_none_verifies() {
    let x: Option<u8> = None;
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 0usize);
}

// LIAR l21: declared `Option<u8> = None` claimed non-empty.
#[trust_vc::ensures(true)]
fn l21_declared_u8_none_refuted() {
    let x: Option<u8> = None;
    let s = x.as_slice();
    trust_vc::assert!(s.len() == 1usize);
}
"#;

/// The `let` annotation width carry's WALL arm
/// (`vc_extraction::declared_width::ERR_WALL`). g18's payload is an arithmetic
/// expression, not a literal the ascription fixes.
const LET_ANNOTATION_WALL_REFUSAL: &str = "`let` annotation width carry: an unsuffixed numeric literal sits inside an expression the declared-width walk does not model, at a position whose `let` annotation fixes a non-default integer width";

const I32_PAYLOAD_REFUSAL: &str = "Option::as_slice does not model an `i32` payload: a declared `let x: Option<uN> = Some(<unsuffixed literal>)` is recorded as `Option<i32>` (the annotation is not carried into the literal), so an i32-typed payload cannot be told apart from a defaulted literal under a dropped annotation and fails closed; suffix the payload (`Some(7u8)`) or use a non-i32 payload type";

#[test]
fn c1_none_len_verifies() {
    assert_verified("c1_none_len_verifies");
}

#[test]
fn c2_some_len_index_verifies() {
    assert_verified("c2_some_len_index_verifies");
}

#[test]
fn c3_bool_payload_verifies() {
    assert_verified("c3_bool_payload_verifies");
}

/// RE-KEYED 2026-09-18 (was GATED g15) by the `let` annotation width carry: a
/// declared `Option<u8>` receiver now arrives as `Option<u8>`, not as the `i32`
/// default, so it takes the view again and the claim is decided at 8 bits.
#[test]
fn c25_unsuffixed_payload_declared_u8_verifies() {
    assert_verified("c25_unsuffixed_payload_declared_u8_verifies");
}

/// RE-KEYED 2026-09-18 (was GATED g16): the liar of c25.
#[test]
fn l25_unsuffixed_payload_declared_u8_false_claim_refuted() {
    assert_counterexample(
        "l25_unsuffixed_payload_declared_u8_false_claim_refuted",
        "assertion_0",
    );
}

/// RE-KEYED 2026-09-18 (was GATED g17). THE SOUNDNESS PIN of this re-key: the
/// shape that VERIFIED before the wholesale `i32` narrowing is now a genuine
/// COUNTEREXAMPLE, because the declared `u8` reaches the view and `200u8 +
/// 100u8` overflows. The refusal is no longer needed to keep it out.
#[test]
fn c26_declared_u8_unsuffixed_overflow_refuted() {
    assert_counterexample(
        "c26_declared_u8_unsuffixed_overflow_refuted",
        "overflow_check_0",
    );
}

/// RE-KEYED 2026-09-18 (was GATED g18): a CONSTANT-arithmetic payload IS
/// decided by the ascription — every leaf of `100 + 100` is an integer
/// literal, so rustc's inference has one choice and the position's `u8`
/// propagates to both. The view therefore reads a `u8` payload of 200 and the
/// `+ 100u8` that follows is refuted, which is the program's truth (the twin
/// prints `payload=200 overflow=true`). An earlier cut walled this off along
/// with eight sibling spellings; that was a regression, and the wall now owns
/// only NON-constant operands (g29).
#[test]
fn c29_declared_u8_constant_payload_overflow_refuted() {
    assert_counterexample(
        "c29_declared_u8_constant_payload_overflow_refuted",
        "overflow_check_1",
    );
}

/// The wall's real domain, kept as the gated exemplar: a payload whose operand
/// is not a literal, so this file cannot show the `+` is the primitive impl.
#[test]
fn g29_declared_u8_non_constant_payload_gated() {
    assert_gated(
        "g29_declared_u8_non_constant_payload_gated",
        &[LET_ANNOTATION_WALL_REFUSAL],
    );
}

/// DECIDED now (design-trust-proof-backend.md §5b rule 12): `Some(v)` under
/// the `Option<u8>` ascription binds its payload at `u8`, and `v`'s value is
/// the unsuffixed literal 200, which `u8` holds — so `200u8 + 100u8`
/// overflows, as the program does. It was refused at the `let` (an
/// `Option<i32>` is not an `Option<u8>`) and, before that, by the `as_slice`
/// payload wall (`I32_PAYLOAD_REFUSAL`).
#[test]
fn g19_declared_u8_let_unsuffixed_payload_gated() {
    assert_counterexample(
        "g19_declared_u8_let_unsuffixed_payload_gated",
        "addition overflow",
    );
}

/// RE-KEYED 2026-09-18 (was GATED g20): the view compared against a `vec!` of
/// the declared width — both sides are `Seq<u8>` now, so the sort matches.
#[test]
fn c27_declared_u8_view_eq_vec_verifies() {
    assert_verified("c27_declared_u8_view_eq_vec_verifies");
}

#[test]
fn g21_suffixed_i32_payload_gated() {
    assert_gated("g21_suffixed_i32_payload_gated", &[I32_PAYLOAD_REFUSAL]);
}

#[test]
fn g22_i32_param_payload_gated() {
    assert_gated("g22_i32_param_payload_gated", &[I32_PAYLOAD_REFUSAL]);
}

/// RE-KEYED 2026-09-18 (was GATED g23): the `u8` operand on the LEFT.
#[test]
fn c28_declared_u8_unsuffixed_left_operand_refuted() {
    assert_counterexample(
        "c28_declared_u8_unsuffixed_left_operand_refuted",
        "overflow_check_0",
    );
}

#[test]
fn g24_unannotated_unsuffixed_payload_gated() {
    assert_gated(
        "g24_unannotated_unsuffixed_payload_gated",
        &[I32_PAYLOAD_REFUSAL],
    );
}

#[test]
fn c20_suffixed_u8_view_arithmetic_verifies() {
    assert_verified("c20_suffixed_u8_view_arithmetic_verifies");
}

#[test]
fn l20_suffixed_u8_view_arithmetic_overflow_refuted() {
    assert_counterexample(
        "l20_suffixed_u8_view_arithmetic_overflow_refuted",
        "overflow_check_",
    );
}

#[test]
fn c21_declared_u8_none_verifies() {
    assert_verified("c21_declared_u8_none_verifies");
}

#[test]
fn l21_declared_u8_none_refuted() {
    assert_counterexample("l21_declared_u8_none_refuted", "assertion_");
}

#[test]
fn c5_none_turbofish_verifies() {
    assert_verified("c5_none_turbofish_verifies");
}

#[test]
fn c6_signed_payload_verifies() {
    assert_verified("c6_signed_payload_verifies");
}

#[test]
fn c7_param_payload_verifies() {
    assert_verified("c7_param_payload_verifies");
}

#[test]
fn c8_rebound_receiver_verifies() {
    assert_verified("c8_rebound_receiver_verifies");
}

#[test]
fn c9_shadowed_receiver_verifies() {
    assert_verified("c9_shadowed_receiver_verifies");
}

#[test]
fn c10_inline_view_verifies() {
    assert_verified("c10_inline_view_verifies");
}

#[test]
fn c11_declared_none_bool_verifies() {
    assert_verified("c11_declared_none_bool_verifies");
}

#[test]
fn l1_none_len_one_refuted() {
    assert_counterexample("l1_none_len_one_refuted", "assertion_");
}

#[test]
fn l2a_some_wrong_payload_refuted() {
    assert_counterexample("l2a_some_wrong_payload_refuted", "assertion_");
}

#[test]
fn l2b_some_len_zero_refuted() {
    assert_counterexample("l2b_some_len_zero_refuted", "assertion_");
}

#[test]
fn l3_bool_payload_refuted() {
    assert_counterexample("l3_bool_payload_refuted", "assertion_");
}

#[test]
fn l5_none_turbofish_refuted() {
    assert_counterexample("l5_none_turbofish_refuted", "assertion_");
}

#[test]
fn l6_signed_payload_refuted() {
    assert_counterexample("l6_signed_payload_refuted", "assertion_");
}

#[test]
fn l7_param_payload_refuted() {
    assert_counterexample("l7_param_payload_refuted", "assertion_");
}

#[test]
fn l8_rebound_receiver_refuted() {
    assert_counterexample("l8_rebound_receiver_refuted", "assertion_");
}

#[test]
fn l9_shadowed_receiver_refuted() {
    assert_counterexample("l9_shadowed_receiver_refuted", "assertion_");
}

#[test]
fn l10_inline_view_refuted() {
    assert_counterexample("l10_inline_view_refuted", "assertion_");
}

#[test]
fn l11_declared_none_bool_refuted() {
    assert_counterexample("l11_declared_none_bool_refuted", "assertion_");
}

#[test]
fn b1_none_index_out_of_bounds() {
    assert_counterexample("b1_none_index_out_of_bounds", "requires i < len");
}

#[test]
fn b2_some_index_out_of_bounds() {
    assert_counterexample("b2_some_index_out_of_bounds", "requires i < len");
}

#[test]
fn g1_unknown_state_param_gated() {
    assert_gated("g1_unknown_state_param_gated", &["Option::as_slice requires a receiver with a known None or Some(<payload>) binding; unknown or partially known state fails closed"]);
}

#[test]
fn g2_nested_option_payload_gated() {
    assert_gated(
        "g2_nested_option_payload_gated",
        &["Option::as_slice is modeled only for bool/integer payloads; got `Option<u64>`"],
    );
}

#[test]
fn g3_as_mut_slice_gated() {
    assert_gated(
        "g3_as_mut_slice_gated",
        &[
            "as_mut_slice() on type `Option<u64>`",
            "method is not available in specification context",
        ],
    );
}

#[test]
fn g4_receiver_read_after_call_gated() {
    assert_gated(
        "g4_receiver_read_after_call_gated",
        &[
            "Failed to lower obligation 'assertion_1'",
            "unresolved variable `x`",
        ],
    );
}

#[test]
fn g5_vec_as_slice_gated() {
    assert_gated(
        "g5_vec_as_slice_gated",
        &[
            "as_slice() on type `Seq<u64>`",
            "method is not available in specification context",
        ],
    );
}

#[test]
fn g6_tuple_payload_gated() {
    assert_gated(
        "g6_tuple_payload_gated",
        &["Option::as_slice is modeled only for bool/integer payloads; got `(u64, u64)`"],
    );
}

#[test]
fn g7_conditional_state_gated() {
    assert_gated("g7_conditional_state_gated", &["Option::as_slice requires a receiver with a known None or Some(<payload>) binding; unknown or partially known state fails closed"]);
}

#[test]
fn g8_loop_havoced_receiver_gated() {
    assert_gated(
        "g8_loop_havoced_receiver_gated",
        &["unresolved variable `x`"],
    );
}

#[test]
fn g9_field_receiver_gated() {
    assert_gated("g9_field_receiver_gated", &["Option::as_slice requires a receiver with a known None or Some(<payload>) binding; unknown or partially known state fails closed"]);
}

#[test]
fn g10_second_view_gated() {
    assert_gated(
        "g10_second_view_gated",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unresolved variable `x`",
        ],
    );
}

#[test]
fn g11_requires_some_param_gated() {
    assert_gated("g11_requires_some_param_gated", &["Option::as_slice requires a receiver with a known None or Some(<payload>) binding; unknown or partially known state fails closed"]);
}

#[test]
fn g12_write_through_view_gated() {
    assert_gated(
        "g12_write_through_view_gated",
        &[
            "as_mut_slice() on type `Option<u64>`",
            "method is not available in specification context",
        ],
    );
}

#[test]
fn g13_vec_payload_gated() {
    assert_gated(
        "g13_vec_payload_gated",
        &["Option::as_slice is modeled only for bool/integer payloads; got `Seq<u64>`"],
    );
}

#[test]
fn g14_char_payload_gated() {
    assert_gated(
        "g14_char_payload_gated",
        &["Option::as_slice is modeled only for bool/integer payloads; got `char`"],
    );
}

#[test]
fn c12_view_call_argument_verifies() {
    assert_verified("c12_view_call_argument_verifies");
}

#[test]
fn l12a_view_call_argument_refuted() {
    assert_counterexample("l12a_view_call_argument_refuted", "assertion_");
}

#[test]
fn l12b_view_call_argument_plus_one_refuted() {
    assert_counterexample("l12b_view_call_argument_plus_one_refuted", "assertion_");
}

#[test]
fn c13_view_against_vec_literal_verifies() {
    assert_verified("c13_view_against_vec_literal_verifies");
}

#[test]
fn l13_view_against_vec_literal_refuted() {
    assert_counterexample("l13_view_against_vec_literal_refuted", "assertion_");
}

#[test]
fn c14_usize_payload_verifies() {
    assert_verified("c14_usize_payload_verifies");
}

#[test]
fn l14_usize_payload_refuted() {
    assert_counterexample("l14_usize_payload_refuted", "assertion_");
}

#[test]
fn c15_computed_payload_verifies() {
    assert_verified("c15_computed_payload_verifies");
}

#[test]
fn l15_computed_payload_refuted() {
    assert_counterexample("l15_computed_payload_refuted", "assertion_");
}

#[test]
fn c16_view_rebound_verifies() {
    assert_verified("c16_view_rebound_verifies");
}

#[test]
fn l16_view_rebound_refuted() {
    assert_counterexample("l16_view_rebound_refuted", "assertion_");
}

#[test]
fn c17_view_index_return_verifies() {
    assert_verified("c17_view_index_return_verifies");
}

#[test]
fn l17_view_index_return_refuted() {
    assert_counterexample("l17_view_index_return_refuted", "postcondition");
}

#[test]
fn c18_payload_snapshot_verifies() {
    assert_verified("c18_payload_snapshot_verifies");
}

#[test]
fn l18_payload_snapshot_refuted() {
    assert_counterexample("l18_payload_snapshot_refuted", "assertion_");
}

#[test]
fn c19_shared_ref_payload_verifies() {
    assert_verified("c19_shared_ref_payload_verifies");
}

#[test]
fn l19_shared_ref_payload_refuted() {
    assert_counterexample("l19_shared_ref_payload_refuted", "assertion_");
}

// Std twins of every control (runtime-true) and liar (runtime-false), executed
// under stock rustc: the harness pins the program's truth values, not the
// model's.
#[allow(
    clippy::bool_comparison,
    unused_mut,
    unused_assignments,
    unused_variables
)]
#[test]
#[expect(
    clippy::len_zero,
    reason = "The twin executes the same slice length claim as the verifier regression."
)]
#[expect(
    clippy::get_first,
    reason = "The twin preserves the indexed get operation tested by the verifier."
)]
#[expect(
    clippy::identity_op,
    reason = "The twin preserves the exact arithmetic expression tested by the verifier."
)]
#[expect(
    clippy::useless_vec,
    reason = "The twin tests Vec-backed slice behavior, so an array is a different input."
)]
fn runtime_twins_execute_std_behavior() {
    fn takes_len(s: &[u64]) -> usize {
        s.len()
    }
    fn takes_len_plus_one(s: &[u64]) -> usize {
        s.len() + 1usize
    }
    // c1 / l1 / c5 / l5 / b1
    {
        let x = Option::<u64>::None;
        let s = x.as_slice();
        assert!(s.len() == 0usize);
        assert!(!(s.len() == 1usize));
        assert!(s.get(0usize).is_none());
    }
    // c2 / l2a / l2b / c10 / l10 / c16 / l16 / b2
    {
        let x = Some(20u64);
        let s = x.as_slice();
        assert!(s.len() == 1usize);
        assert!(s[0usize] == 20u64);
        assert!(!(s[0usize] == 21u64));
        assert!(!(s.len() == 0usize));
        let t = s;
        assert!(t.len() == 1usize);
        assert!(s.get(1usize).is_none());
    }
    // c3 / l3
    {
        let x = Some(true);
        let s = x.as_slice();
        assert!(s.len() == 1usize);
        assert!(s[0usize] == true);
        assert!(!(s[0usize] == false));
    }
    // g15 / g16 (runtime truth of the refused shape: true / false)
    {
        let x: Option<u8> = Some(7);
        let s = x.as_slice();
        assert!(s[0usize] == 7u8);
        assert!(!(s[0usize] == 8u8));
    }
    // g17 / g18 / g19 / g23: the refused shapes PANIC at runtime on u8
    // overflow — `checked_add` pins that independently of the debug profile.
    {
        let x: Option<u8> = Some(200);
        let s = x.as_slice();
        assert!(s[0usize].checked_add(100u8).is_none());
        assert!(100u8.checked_add(s[0usize]).is_none());
        let y: Option<u8> = Some(100 + 100);
        assert!(y.as_slice()[0usize].checked_add(100u8).is_none());
        let v = 200;
        let z: Option<u8> = Some(v);
        assert!(z.as_slice()[0usize].checked_add(100u8).is_none());
    }
    // g20 / g21 / g22 / g24 (runtime-true shapes that are nonetheless refused)
    {
        let x: Option<u8> = Some(7);
        assert!(x.as_slice() == vec![7u8]);
        let y = Some(-3i32);
        assert!(y.as_slice()[0usize] == -3i32);
        let z = Some(7);
        assert!(z.as_slice()[0usize] == 7i32);
        for v in [i32::MIN, 0, i32::MAX] {
            assert!(Some(v).as_slice().len() == 1usize);
        }
    }
    // c6 / l6
    {
        let x = Some(-3i64);
        let s = x.as_slice();
        assert!(s[0usize] == -3i64);
        assert!(!(s[0usize] == 3i64));
    }
    // c20 / l20
    {
        let x = Some(200u8);
        let s = x.as_slice();
        assert!(s[0usize] + 50u8 == 250u8);
        assert!(s[0usize].checked_add(100u8).is_none());
    }
    // c21 / l21
    {
        let x: Option<u8> = None;
        let s = x.as_slice();
        assert!(s.len() == 0usize);
        assert!(!(s.len() == 1usize));
    }
    // c7 / l7 / c15 / l15
    for v in [0u64, 1u64, 3u64, 4u64, u64::MAX] {
        let x = Some(v);
        let s = x.as_slice();
        assert!(s.len() == 1usize);
        assert!(s[0usize] == v);
        assert!(!(s.len() == 0usize));
        let y = Some(v % 4u64);
        let t = y.as_slice();
        assert!(t[0usize] < 4u64);
    }
    {
        let y = Some(3u64 % 4u64);
        let t = y.as_slice();
        assert!(!(t[0usize] < 3u64));
    }
    // c8 / l8
    {
        let mut x = Some(1u64);
        x = None;
        let s = x.as_slice();
        assert!(s.len() == 0usize);
        assert!(!(s.len() == 1usize));
    }
    // c9 / l9
    {
        let x = Some(1u64);
        let x = Option::<u64>::None;
        let s = x.as_slice();
        assert!(s.len() == 0usize);
        assert!(!(s.len() == 1usize));
    }
    // c11 / l11
    {
        let x: Option<bool> = None;
        let s = x.as_slice();
        assert!(s.len() == 0usize);
        assert!(!(s.len() == 1usize));
    }
    // c12 / l12a / l12b
    {
        let x = Some(20u64);
        let s = x.as_slice();
        let n = takes_len(s);
        assert!(n == 1usize);
        assert!(!(n == 0usize));
        let m = takes_len_plus_one(s);
        assert!(!(m == 1usize));
    }
    // c13 / l13
    {
        let x = Some(20u64);
        let s = x.as_slice();
        let t = vec![20u64];
        assert!(s.len() == t.len());
        assert!(s[0usize] == t[0usize]);
        let u = vec![21u64];
        assert!(!(s[0usize] == u[0usize]));
    }
    // c14 / l14
    {
        let x = Some(3usize);
        let s = x.as_slice();
        assert!(s[0usize] == 3usize);
        assert!(!(s[0usize] == 4usize));
    }
    // c17 / l17
    {
        let x = Some(20u64);
        let s = x.as_slice();
        let r = s[0usize];
        assert!(r == 20u64);
        assert!(!(r == 21u64));
    }
    // c18 / l18
    {
        let mut v = 1u64;
        let x = Some(v);
        v = 2u64;
        let s = x.as_slice();
        assert!(s[0usize] == 1u64);
        assert!(!(s[0usize] == 2u64));
        let _ = v;
    }
    // c19 / l19
    {
        let v = 1u64;
        let x = Some(&v);
        let s = x.as_slice();
        assert!(s.len() == 1usize);
        assert!(!(s.len() == 0usize));
    }
}
