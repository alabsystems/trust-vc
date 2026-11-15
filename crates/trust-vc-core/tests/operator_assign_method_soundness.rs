// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! An operator assignment method (`add_assign`, `sub_assign`, `div_assign`,
//! `shl_assign`, ...) on a primitive integer panics exactly where the
//! compound operator does, whatever place it writes and however it is
//! spelled.
//!
//! `x.add_assign(e)` carried the overflow obligation of `x += e` only when
//! `x` was a binding the function binds once, to a written primitive integer
//! type. A rebound name, a `&mut` reference, a dereference, a field, a tuple
//! element, an explicit `(&mut x)` receiver, and every path spelling
//! (`AddAssign::add_assign(&mut x, e)`, `u64::add_assign(&mut x, e)`) went
//! unchecked. Each call now carries the obligation of the compound operator
//! over the place it writes, and the method named as a value
//! (`let f = u64::add_assign;`) fails closed.
//!
//! Every liar below is well typed and panics at run time (overflow checks
//! on). Every twin is true and must verify. A file type whose own impl
//! declares the method keeps the ordinary method path, and a binding of that
//! name shadowed by an integer is still checked.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_operator_assign_method_{}_{}_{seq}.rs",
        std::process::id(),
        func
    ));
    std::fs::write(&path, src).expect("write fixture");
    let result =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            verify_function_from_file(path.to_str().expect("utf8 path"), func)
        })
        .map_err(|e| e.to_string());
    let _ = std::fs::remove_file(&path);
    result
}

#[derive(Clone, Copy, Debug)]
enum Expect {
    /// A true program: must verify.
    Verified,
    /// A panicking program: refuted with a counterexample.
    Counterexample,
    /// Refused before any verdict.
    FailClosed,
    /// Any answer but `Verified`.
    NotVerified,
}

fn render(r: &Result<VerifyResult, String>) -> String {
    match r {
        Ok(VerifyResult::Verified) => "Verified".into(),
        Ok(VerifyResult::Counterexample {
            obligation_name, ..
        }) => format!("Counterexample({obligation_name})"),
        Ok(VerifyResult::Error { message }) => {
            format!("Error({})", message.chars().take(240).collect::<String>())
        }
        Ok(other) => format!("{:.240}", format!("{other:?}")),
        Err(e) => format!("Err({})", e.chars().take(240).collect::<String>()),
    }
}

fn check_table(src: &str, table: &[(&str, Expect)]) {
    let mut failures = Vec::new();
    for (func, expect) in table {
        let r = verify(src, func);
        let ok = match expect {
            Expect::Verified => matches!(r, Ok(VerifyResult::Verified)),
            Expect::Counterexample => matches!(r, Ok(VerifyResult::Counterexample { .. })),
            Expect::FailClosed => matches!(r, Ok(VerifyResult::Error { .. }) | Err(_)),
            Expect::NotVerified => !matches!(r, Ok(VerifyResult::Verified)),
        };
        println!(
            "{func}: expect={expect:?} got={} {}",
            render(&r),
            if ok { "ok" } else { "MISMATCH" }
        );
        if !ok {
            failures.push(format!("{func}: expected {expect:?}, got {}", render(&r)));
        }
    }
    assert!(
        failures.is_empty(),
        "{} mismatch(es):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

use Expect::{Counterexample, FailClosed, NotVerified, Verified};

const SRC: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_must_use)]

use std::ops::{AddAssign, DivAssign, ShlAssign, SubAssign};

struct S {
    c: u64,
}

#[derive(Clone, Copy)]
struct V {
    a: u64,
}

impl AddAssign for V {
    fn add_assign(&mut self, o: V) {}
}

#[trust_vc::ensures(true)]
fn b1_rebound_liar(x: u64) {
    let mut x = x;
    x.add_assign(1u64);
}

#[trust_vc::ensures(true)]
fn b2_reference_liar(r: &mut u64) {
    r.add_assign(1u64);
}

#[trust_vc::ensures(true)]
fn b9_field_liar(mut s: S) {
    s.c.add_assign(1u64);
}

#[trust_vc::requires(x == 5u64)]
#[trust_vc::ensures(true)]
fn u1_ufcs_liar(mut x: u64) {
    std::ops::AddAssign::add_assign(&mut x, u64::MAX);
}

#[trust_vc::requires(x == 5u64)]
#[trust_vc::ensures(true)]
fn u2_explicit_borrow_liar(mut x: u64) {
    (&mut x).add_assign(u64::MAX);
}

#[trust_vc::ensures(true)]
fn l1_untyped_let_liar(x: u64) {
    let mut y = x;
    y.add_assign(1u64);
}

#[trust_vc::ensures(true)]
fn l2_deref_liar(r: &mut u64) {
    (*r).add_assign(1u64);
}

#[trust_vc::ensures(true)]
fn l3_deref_of_borrow_liar(mut x: u64) {
    (*(&mut x)).add_assign(1u64);
}

#[trust_vc::ensures(true)]
fn l4_tuple_element_liar(mut t: (u64, u64)) {
    t.0.add_assign(1u64);
}

#[trust_vc::ensures(true)]
fn l5_local_reference_liar(mut x: u64) {
    let r = &mut x;
    r.add_assign(1u64);
}

#[trust_vc::ensures(true)]
fn l6_type_path_liar(mut x: u64) {
    u64::add_assign(&mut x, 1u64);
}

#[trust_vc::ensures(true)]
fn l7_qualified_path_liar(mut x: u64) {
    <u64 as AddAssign>::add_assign(&mut x, 1u64);
}

#[trust_vc::ensures(true)]
fn l8_trait_path_liar(mut x: u64) {
    AddAssign::add_assign(&mut x, 1u64);
}

#[trust_vc::ensures(true)]
fn l9_trait_path_reference_liar(r: &mut u64) {
    AddAssign::add_assign(r, 1u64);
}

#[trust_vc::ensures(true)]
fn l10_fn_item_value_liar(mut x: u64) {
    let f = u64::add_assign;
    f(&mut x, 1u64);
}

#[trust_vc::ensures(true)]
fn l11_sub_reference_liar(r: &mut u64) {
    r.sub_assign(1u64);
}

#[trust_vc::ensures(true)]
fn l12_div_field_liar(mut s: S, d: u64) {
    s.c.div_assign(d);
}

#[trust_vc::ensures(true)]
fn l13_shl_path_liar(mut x: u64) {
    ShlAssign::shl_assign(&mut x, 70u32);
}

#[trust_vc::ensures(true)]
fn l14_generic_liar<T: AddAssign>(x: &mut T, y: T) {
    x.add_assign(y);
}

#[trust_vc::ensures(true)]
fn l15_if_let_shadow_liar(v: V, o: Option<u64>) {
    if let Some(mut v) = o {
        v.add_assign(u64::MAX);
    }
}

#[trust_vc::ensures(true)]
fn l16_match_shadow_liar(v: V, o: Option<u64>) {
    match o {
        Some(mut v) => v.add_assign(u64::MAX),
        None => {}
    }
}

#[trust_vc::ensures(true)]
fn l17_let_shadow_liar(v: V) {
    let mut v = 5u64;
    v.add_assign(u64::MAX);
}

#[trust_vc::ensures(true)]
fn l18_for_shadow_liar(v: V) {
    for mut v in 1u64..2u64 {
        v.add_assign(u64::MAX);
    }
}

#[trust_vc::ensures(true)]
fn l19_closure_shadow_liar(v: V) {
    let f = |mut v: u64| v.add_assign(u64::MAX);
    f(1u64);
}

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(true)]
fn t1_rebound_ctrl(x: u64) {
    let mut x = x;
    x.add_assign(1u64);
}

#[trust_vc::requires(*old(r) < 100u64)]
#[trust_vc::ensures(true)]
fn t2_reference_ctrl(r: &mut u64) {
    r.add_assign(1u64);
}

#[trust_vc::requires(s.c < 100u64)]
#[trust_vc::ensures(true)]
fn t3_field_ctrl(mut s: S) {
    s.c.add_assign(1u64);
}

#[trust_vc::requires(x == 5u64)]
#[trust_vc::ensures(true)]
fn t4_ufcs_ctrl(mut x: u64) {
    std::ops::AddAssign::add_assign(&mut x, 1u64);
}

#[trust_vc::requires(x == 5u64)]
#[trust_vc::ensures(true)]
fn t5_explicit_borrow_ctrl(mut x: u64) {
    (&mut x).add_assign(1u64);
}

#[trust_vc::ensures(true)]
fn t6_file_type_ctrl(mut v: V, w: V) {
    v.add_assign(w);
}

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(true)]
fn t7_single_typed_ctrl(mut x: u64) {
    x.add_assign(1u64);
}

#[trust_vc::requires(d > 0u64)]
#[trust_vc::ensures(true)]
fn t8_div_field_ctrl(mut s: S, d: u64) {
    s.c.div_assign(d);
}

#[trust_vc::requires(*old(r) < 100u64)]
#[trust_vc::ensures(true)]
fn t9_trait_path_reference_ctrl(r: &mut u64) {
    AddAssign::add_assign(r, 1u64);
}
"#;

/// Each liar was `Verified` before this fix: the method spelling carried the
/// overflow obligation only on a binding the function binds once, to a
/// written primitive integer type, and the path spellings never did.
///
/// `l14` writes a generic value, whose `+` the lane cannot encode, so it is
/// not verified. `l15`, `l16`, `l18` and `l19` shadow the parameter `v: V`
/// with an integer binding of the same name: the file type's own
/// `add_assign` must not exempt the call, so the obligation is emitted. The
/// lane reads those pattern bindings as the outer `v`, so the obligation
/// fails to encode rather than being refuted.
#[test]
fn every_operator_assign_method_call_is_checked() {
    check_table(
        SRC,
        &[
            ("b1_rebound_liar", Counterexample),
            ("b2_reference_liar", Counterexample),
            ("b9_field_liar", Counterexample),
            ("u1_ufcs_liar", Counterexample),
            ("u2_explicit_borrow_liar", Counterexample),
            ("l1_untyped_let_liar", Counterexample),
            ("l2_deref_liar", Counterexample),
            ("l3_deref_of_borrow_liar", Counterexample),
            ("l4_tuple_element_liar", Counterexample),
            ("l5_local_reference_liar", Counterexample),
            ("l6_type_path_liar", Counterexample),
            ("l7_qualified_path_liar", Counterexample),
            ("l8_trait_path_liar", Counterexample),
            ("l9_trait_path_reference_liar", Counterexample),
            ("l10_fn_item_value_liar", FailClosed),
            ("l11_sub_reference_liar", Counterexample),
            ("l12_div_field_liar", Counterexample),
            ("l13_shl_path_liar", Counterexample),
            ("l14_generic_liar", NotVerified),
            ("l15_if_let_shadow_liar", NotVerified),
            ("l16_match_shadow_liar", NotVerified),
            ("l17_let_shadow_liar", Counterexample),
            ("l18_for_shadow_liar", NotVerified),
            ("l19_closure_shadow_liar", NotVerified),
        ],
    );
}

/// The true twins: the same places and spellings under a precondition that
/// rules the panic out, and a file type whose own impl declares the method.
#[test]
fn true_operator_assign_method_calls_still_verify() {
    check_table(
        SRC,
        &[
            ("t1_rebound_ctrl", Verified),
            ("t2_reference_ctrl", Verified),
            ("t3_field_ctrl", Verified),
            ("t4_ufcs_ctrl", Verified),
            ("t5_explicit_borrow_ctrl", Verified),
            ("t6_file_type_ctrl", Verified),
            ("t7_single_typed_ctrl", Verified),
            ("t8_div_field_ctrl", Verified),
            ("t9_trait_path_reference_ctrl", Verified),
        ],
    );
}
