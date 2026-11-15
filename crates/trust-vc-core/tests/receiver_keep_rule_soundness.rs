// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The receiver rule: when a method call KEEPS its receiver's binding.
//!
//! A method call `r.m(..)` on a path receiver `r` keeps `r`'s binding (no
//! poison, no havoc, nothing for a loop, block or branch join to re-apply)
//! only when one of three arms proves the call cannot change the value `r`
//! denotes (`AssertionCollector::method_receiver_treatment` states the rule).
//! Every other call is poisoned or havocked, and a loop body that poisons a
//! binding the loop frame does not havoc is refused.
//!
//! 1. Immutable binding. Every binding of the name in the function is a
//!    parameter or `let` written as a plain identifier with no `mut` / `ref` /
//!    `@`, its type is written (or fixed by a literal, or copied from a
//!    parameter bound once) and holds no interior mutability, no item or
//!    import of the file binds the name, and the method is positively known
//!    to take `&self` or `self` on every type the binding has: for a
//!    primitive scalar, any method but its few `&mut self` ones; for `Option`,
//!    `Vec`, a tuple or an array, a method on the extractor's non-mutating
//!    list; for a file type, a method the file declares for it with such a
//!    receiver. A call to any other method (an unlisted std method may take
//!    `&mut self`, which on an immutable binding means the input is
//!    ill-typed) is poisoned as before. Admitted types: primitive scalars,
//!    std `Option` / `Vec`, tuples, arrays, and non-generic file-scope structs
//!    and enums built from them, all resolved under the file's closed-world
//!    name table. References, raw pointers, type parameters, other std types
//!    (`Cell`, `RefCell`, `Box`, ...) and every type of an unenumerable file
//!    are refused.
//! 2. Std `Option` / `Result` with a scope-exact type and a closure-free
//!    tester or unwrap-family method the file does not shadow.
//! 3. A collection receiver with a pure ghost-collection combinator. A
//!    binding whose current value is a declared collection-typed symbol (the
//!    fresh symbol a `&mut` call argument havocs a slice parameter to) counts
//!    as a collection.
//!
//! Separately, a `for` loop does not refuse a poison of a name its own pattern
//! binds: inside the body that name is the per-iteration binding.
//!
//! Each control below is a true program that must verify. Each liar changes
//! it so the claim is false and must not verify. Each test's doc comment says
//! what its liars returned, measured, with one condition of the rule switched
//! off.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn verify(func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_receiver_keep_{}_{}_{seq}.rs",
        std::process::id(),
        func
    ));
    std::fs::write(&path, SRC).expect("write fixture");
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
    /// A false claim refuted with a counterexample.
    Counterexample,
    /// A false claim the extractor refuses (an extraction or lowering error).
    FailClosed,
}

fn render(r: &Result<VerifyResult, String>) -> String {
    match r {
        Ok(VerifyResult::Verified) => "Verified".into(),
        Ok(VerifyResult::Counterexample {
            obligation_name, ..
        }) => format!("Counterexample({obligation_name})"),
        Ok(VerifyResult::Error { message }) => {
            format!("Error({})", message.chars().take(200).collect::<String>())
        }
        Ok(other) => format!("{:.200}", format!("{other:?}")),
        Err(e) => format!("Err({})", e.chars().take(200).collect::<String>()),
    }
}

fn matches_expect(r: &Result<VerifyResult, String>, expect: Expect) -> bool {
    match expect {
        Expect::Verified => matches!(r, Ok(VerifyResult::Verified)),
        Expect::Counterexample => matches!(r, Ok(VerifyResult::Counterexample { .. })),
        Expect::FailClosed => matches!(r, Ok(VerifyResult::Error { .. }) | Err(_)),
    }
}

fn check_table(table: &[(&str, Expect)]) {
    let mut failures = Vec::new();
    for (func, expect) in table {
        let r = verify(func);
        let ok = matches_expect(&r, *expect);
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

const SRC: &str = r#"
#![allow(dead_code, unused, unused_mut)]
use std::cell::Cell;
use std::ops::AddAssign;

struct W {
    o: Option<u64>,
}
impl W {
    fn bump(&mut self) {
        self.o = None;
    }
    fn peek(&self) -> bool {
        self.o.is_some()
    }
}

struct PlainU {
    c: u64,
}
impl PlainU {
    #[trust_vc::external_body]
    fn zero(&self) {}
    #[trust_vc::external_body]
    fn read(&self) -> u64 {
        self.c
    }
}

struct CellU {
    c: Cell<u64>,
}
impl CellU {
    #[trust_vc::external_body]
    fn zero(&self) {
        self.c.set(0u64);
    }
    #[trust_vc::external_body]
    fn read(&self) -> u64 {
        self.c.get()
    }
}

fn zero(r: &mut u8) {
    *r = 0u8;
}

// ---- arm 1: immutable binding ----

#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn k1_immutable_local_peek_ctrl(w: W) {
    let p = w;
    let _b = p.peek();
    p.o.unwrap();
}

#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn k1_mut_local_bump_liar(w: W) {
    let mut p = w;
    p.bump();
    p.o.unwrap();
}

#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn k1_two_immutable_bindings_ctrl(w: W, b: bool) {
    let p = w;
    if b {
        let p: u64 = 5u64;
    }
    let _x = p.peek();
    p.o.unwrap();
}

#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn k1_rebound_mut_liar(w: W) {
    let p = w;
    let mut p = p;
    p.bump();
    p.o.unwrap();
}

#[trust_vc::ensures(true)]
fn k1_ill_typed_take_liar() {
    let o: Option<u64> = Some(1u64);
    o.take();
    o.unwrap();
}

#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn k1_mut_ref_param_liar(w: &mut W) {
    w.bump();
    w.o.unwrap();
}

#[trust_vc::ensures(true)]
fn k1_plain_field_read_ctrl(w: PlainU) {
    let p = w;
    let before = p.c;
    p.zero();
    let after = p.c;
    trust_vc::assert!(before == after);
}

#[trust_vc::ensures(true)]
fn k1_cell_field_read_liar(w: CellU) {
    let p = w;
    let before = p.read();
    p.zero();
    let after = p.read();
    trust_vc::assert!(before == after);
}

#[trust_vc::ensures(true)]
fn k1_unlisted_std_mutator_liar() {
    let v: Vec<u32> = vec![1u32, 1u32];
    v.dedup_by_key(|x| *x);
    trust_vc::assert!(v.len() == 2usize);
}

#[trust_vc::ensures(true)]
fn k1_unlisted_std_sort_liar() {
    let v: Vec<u32> = vec![2u32, 1u32];
    v.sort_unstable_by_key(|x| *x);
    trust_vc::assert!(v[0usize] == 2u32);
}

#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn k1_undeclared_file_type_method_liar(w: W) {
    let p = w;
    p.reset();
    p.o.unwrap();
}

#[trust_vc::ensures(true)]
fn k1_scalar_ascii_mutator_liar() {
    let c: u8 = 97u8;
    c.make_ascii_uppercase();
    trust_vc::assert!(c == 97u8);
}

#[trust_vc::ensures(true)]
fn k1_listed_std_read_ctrl() {
    let v: Vec<u32> = vec![2u32, 1u32];
    let _s = v.is_sorted();
    trust_vc::assert!(v[0usize] == 2u32);
}

#[trust_vc::ensures(true)]
fn k1_listed_std_read_twin_cx() {
    let v: Vec<u32> = vec![2u32, 1u32];
    let _s = v.is_sorted();
    trust_vc::assert!(v[0usize] == 1u32);
}

#[trust_vc::ensures(true)]
fn k1_scalar_method_ctrl() {
    let x = 5u64;
    let _y = x.count_ones();
    trust_vc::assert!(x == 5u64);
}

#[trust_vc::ensures(true)]
fn k1_scalar_method_twin_cx() {
    let x = 5u64;
    let _y = x.count_ones();
    trust_vc::assert!(x == 6u64);
}

// ---- arm 3: a collection whose value is a havoc symbol ----

#[trust_vc::requires(s.len() > 0usize)]
#[trust_vc::ensures(true)]
fn k3_havoc_len_read_ctrl(s: &mut [u8]) {
    zero(&mut s[0usize]);
    if s.len() > 0usize {
        let _n = s.len();
        trust_vc::assert!(s.len() > 0usize);
    }
}

#[trust_vc::requires(v.len() == 1usize)]
#[trust_vc::ensures(true)]
fn k3_havoc_extend_liar(v: &mut Vec<u8>) {
    zero(&mut v[0usize]);
    if v.len() == 1usize {
        v.extend_from_slice(&[7u8]);
        trust_vc::assert!(v.len() == 1usize);
    }
}

#[trust_vc::requires(s.len() > 0usize && s[0usize] == 1u8)]
#[trust_vc::ensures(true)]
fn k3_havoc_value_not_entry_liar(s: &mut [u8]) {
    zero(&mut s[0usize]);
    let _n = s.len();
    trust_vc::assert!(s[0usize] == 1u8);
}

// ---- a `for` pattern binding is not an outer receiver ----

#[trust_vc::ensures(true)]
fn h1_for_binding_method_ctrl(ws: Vec<Vec<u64>>) {
    for w in ws {
        let _n = w.len();
    }
    trust_vc::assert!(true);
}

#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn h1_for_outer_receiver_liar(ws: Vec<Vec<u64>>, mut x: u64) {
    for w in ws {
        x.add_assign(1u64);
    }
    trust_vc::assert!(x == 0u64);
}
"#;

use Expect::{Counterexample, FailClosed, Verified};

/// Arm 1. Discriminators, each measured with one condition switched off:
/// admitting `mut` bindings makes `k1_mut_local_bump_liar` (and
/// `h1_for_outer_receiver_liar`) `Verified`; admitting a name that has any
/// other binding makes `k1_rebound_mut_liar` `Verified`; skipping the type
/// check makes `k1_mut_ref_param_liar` (and `k3_havoc_extend_liar`, whose `v`
/// is a `&mut` parameter) `Verified`; dropping the known-`&mut`-method guard
/// makes `k1_ill_typed_take_liar` `Verified` (rustc rejects that program, which
/// is why the arm must not keep its binding).
///
/// The positive method rule. `k1_unlisted_std_mutator_liar`,
/// `k1_unlisted_std_sort_liar` and `k1_undeclared_file_type_method_liar` call a
/// method no list knows (`Vec::dedup_by_key` and `Vec::sort_unstable_by_key`
/// take `&mut self`; `reset` is not declared for `W`), and
/// `k1_scalar_ascii_mutator_liar` calls `u8::make_ascii_uppercase`, which
/// takes `&mut self`. Each program is ill-typed and the old binding is stale
/// after the call. Keeping the binding for every method no deny list names
/// made all four `Verified`, and dropping only the primitive scalar's
/// `make_ascii_*` exclusion makes the last one `Verified` again; the receiver
/// is now poisoned, so each fails closed. `k1_listed_std_read_ctrl`
/// and `k1_scalar_method_ctrl` are the same shapes with a `&self` / by-value
/// method and must still verify; their one-line twins (`_twin_cx`) claim the
/// wrong value after the call and are refuted. `k1_two_immutable_bindings_ctrl` calls a
/// method declared `&self` for `W` on a name that is also bound to a `u64`, so
/// it holds only because a primitive scalar's `&mut self` methods are known.
///
/// `k1_plain_field_read_ctrl` reads the field before and after `p.zero()`.
/// Two calls of the `external_body` `read` may return different values, so a
/// `Verified` answer that compares them is refused (`bodiless_call_repeat`).
///
/// `k1_cell_field_read_liar` stays `FailClosed` with the type check off too:
/// the extractor has no model of a `Cell`-bearing struct's methods, so no
/// interior-mutability liar reaches a verdict. It is kept so the type check
/// has a liar once such a model exists.
#[test]
fn arm1_immutable_interior_mutability_free_binding() {
    check_table(&[
        ("k1_immutable_local_peek_ctrl", Verified),
        ("k1_mut_local_bump_liar", FailClosed),
        ("k1_two_immutable_bindings_ctrl", Verified),
        ("k1_rebound_mut_liar", FailClosed),
        ("k1_ill_typed_take_liar", FailClosed),
        ("k1_mut_ref_param_liar", Counterexample),
        ("k1_plain_field_read_ctrl", Verified),
        ("k1_cell_field_read_liar", FailClosed),
        ("k1_listed_std_read_ctrl", Verified),
        ("k1_listed_std_read_twin_cx", Counterexample),
        ("k1_scalar_method_ctrl", Verified),
        ("k1_scalar_method_twin_cx", Counterexample),
        ("k1_unlisted_std_mutator_liar", FailClosed),
        ("k1_unlisted_std_sort_liar", FailClosed),
        ("k1_undeclared_file_type_method_liar", FailClosed),
        ("k1_scalar_ascii_mutator_liar", FailClosed),
    ]);
}

/// Arm 3 on a havocked collection. Discriminators: without the havoc-symbol
/// case `k3_havoc_len_read_ctrl` fails closed; keeping the receiver for any
/// method name (not only a pure combinator) makes `k3_havoc_extend_liar`
/// `Verified`. `k3_havoc_value_not_entry_liar` pins that the kept value is the
/// post-call symbol: unbinding the receiver instead, which reverts it to its
/// entry value, makes both liars `Verified` (it reads `s[0] == 1` and
/// `v.len() == 1` from the precondition).
#[test]
fn arm3_havocked_collection_pure_read() {
    check_table(&[
        ("k3_havoc_len_read_ctrl", Verified),
        ("k3_havoc_extend_liar", FailClosed),
        ("k3_havoc_value_not_entry_liar", Counterexample),
    ]);
}

/// The `for` pattern exclusion. Discriminator: without it
/// `h1_for_binding_method_ctrl` is refused as an unframed loop receiver. The
/// liar calls the method on an outer binding, which the loop still refuses.
#[test]
fn for_pattern_binding_is_not_an_outer_receiver() {
    check_table(&[
        ("h1_for_binding_method_ctrl", Verified),
        ("h1_for_outer_receiver_liar", FailClosed),
    ]);
}
