// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// ROUND-10 PROBES, part 4: the ghost VIEW method-name table, which answered
// `Ghost` for ANY receiver whose method merely happens to be called `view`,
// and the in-body `const`/`static` ITEM the `let` collector never visited.
// Every `_cx` body ALWAYS divides by zero.
struct Hv {
    d: Vec<u64>,
}

#[trust_vc::ensures(true)]
fn ry1_user_view_returns_exec_cx(h: Hv) {
    let _ = h.view().map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ry2_user_to_seq_returns_exec_cx(h: Hv) {
    let _ = h.to_seq().map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ry3_user_deep_view_returns_exec_cx(h: Hv) {
    let _ = h.deep_view().map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// RY4 THE CONTROL: the same carrier's EXEC field, reached directly. A
// non-verify before and after, so what `ry1`-`ry3` bought was the METHOD NAME.
#[trust_vc::ensures(true)]
fn ry4_control_plain_field_cx(h: Hv) {
    let _ = h.d.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// RY5 THE LIAR TWIN: a view of a receiver the seam HAS measured as a
// collection is a spec value, exactly as before, and must keep VERIFYING.
#[trust_vc::ensures(true)]
fn ry5_genuine_view_of_exec_vec_ok(v: Vec<u64>) {
    let _ = v.view().map(|i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ry5b_genuine_view_of_spec_seq_ok(s: Seq<u64>) {
    let _ = s.view().map(|i| i + 1);
    trust_vc::assert!(true);
}

// RY5C THE REFUTED HALF of `ry5`: the same body at the same element width with
// no view in the way is still CHECKED.
#[trust_vc::ensures(true)]
fn ry5c_exec_vec_direct_cx(v: Vec<u64>) {
    let _ = v.map(|i| i + 1);
    trust_vc::assert!(true);
}

// RY6/RY7 an in-body `const`/`static` ITEM binds its name, and `visit_local`
// never sees it (it is a `Stmt::Item`). The PARAMETER's ghost provenance kept
// answering for the name the item had taken. No WELL-TYPED false verify was
// constructed from this (a `u64` const has no `.map`), so it is recorded as a
// binder-visibility fix of round 8's class, not as a cardinal false verify.
#[trust_vc::ensures(true)]
fn ry6_const_item_shadows_spec_param_cx(s: Seq<u64>) {
    const s: u64 = 0u64;
    let _ = s.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ry7_static_item_shadows_spec_param_cx(s: Seq<u64>) {
    static s: u64 = 0u64;
    let _ = s.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// RY8 THE LIAR TWIN for the const half: an in-body `const` of SOME OTHER name
// leaves the spec receiver alone. Only the NAME may distinguish it from `ry6`.
#[trust_vc::ensures(true)]
fn ry8_const_item_other_name_ok(s: Seq<u64>) {
    const qqq: u64 = 0u64;
    let _ = qqq;
    let _ = s.map(|i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ry1_user_view_returns_exec_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ry2_user_to_seq_returns_exec_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ry3_user_deep_view_returns_exec_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ry6_const_item_shadows_spec_param_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ry7_static_item_shadows_spec_param_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}
