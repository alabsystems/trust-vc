// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! `let ref mut r = s;` borrows `s`; writes through `r` are writes to `s`.
//!
//! A `ref` / `ref mut` identifier pattern binds a reference to the matched
//! place, so `let ref mut r = s;` is exactly `let r = &mut s;`. The extractor
//! read the binding mode nowhere and modeled `r` as an owned COPY of `s`:
//! `let mut s = S64 { f: 5u64 }; let ref mut r = s; r.f += 1u64;
//! assert!(s.f == 5u64);` VERIFIED, as did the tuple form, a plain field write,
//! the typed `let ref mut r: S64 = s;`, a deref write through a scalar borrow,
//! and an overflow split across `r.f += 50u8; s.f += 50u8;`. The binding now
//! desugars to the explicit borrow (`ref_binding_desugar.rs`), so the `&mut`
//! alias machinery models the write or fails closed.
//!
//! SCOPE, pinned below: only a bare VARIABLE initializer is rewritten. An
//! index place would be handed to the `&mut` machinery's pre-existing
//! out-of-bounds-borrow hole (`let r = &mut x[5usize]; *r = 20u64;` on
//! `x: [u64; 3]` VERIFIES when nothing later reads `x`), so `let ref mut r =
//! x[5usize];` — and every other non-variable initializer — keeps the
//! rejection it already had.
//!
//! Every positive has a liar refuted in the same file context.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_lrbb_{}_{}.rs", std::process::id(), id));
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
struct S64 { f: u64 }
struct S8 { f: u8 }
fn mk64() -> S64 { S64 { f: 5u64 } }

#[trust_vc::ensures(true)]
fn struct_compound_through_ref_mut() { let mut s = S64 { f: 5u64 }; let ref mut r = s; r.f += 1u64; trust_vc::assert!(s.f == 5u64); }
#[trust_vc::ensures(true)]
fn tuple_compound_through_ref_mut() { let mut t = (5u64, 0u64); let ref mut r = t; r.0 += 1u64; trust_vc::assert!(t.0 == 5u64); }
#[trust_vc::ensures(true)]
fn split_overflow_through_ref_mut() { let mut s = S8 { f: 200u8 }; let ref mut r = s; r.f += 50u8; s.f += 50u8; }

#[trust_vc::ensures(true)]
fn struct_field_write_through_ref_mut() { let mut s = S64 { f: 5u64 }; let ref mut r = s; r.f = 6u64; trust_vc::assert!(s.f == 6u64); }
#[trust_vc::ensures(true)]
fn struct_field_write_through_ref_mut_liar() { let mut s = S64 { f: 5u64 }; let ref mut r = s; r.f = 6u64; trust_vc::assert!(s.f == 5u64); }
#[trust_vc::ensures(true)]
fn typed_struct_field_write_through_ref_mut() { let mut s = S64 { f: 5u64 }; let ref mut r: S64 = s; r.f = 6u64; trust_vc::assert!(s.f == 6u64); }
#[trust_vc::ensures(true)]
fn typed_struct_field_write_through_ref_mut_liar() { let mut s = S64 { f: 5u64 }; let ref mut r: S64 = s; r.f = 6u64; trust_vc::assert!(s.f == 5u64); }
#[trust_vc::ensures(true)]
fn scalar_deref_compound_through_ref_mut() { let mut x = 5u64; let ref mut r = x; *r += 1u64; trust_vc::assert!(x == 6u64); }
#[trust_vc::ensures(true)]
fn scalar_deref_compound_through_ref_mut_liar() { let mut x = 5u64; let ref mut r = x; *r += 1u64; trust_vc::assert!(x == 5u64); }
#[trust_vc::ensures(true)]
fn typed_scalar_deref_write_through_ref_mut() { let mut x = 5u64; let ref mut r: u64 = x; *r = 7u64; trust_vc::assert!(x == 7u64); }
#[trust_vc::ensures(true)]
fn typed_scalar_deref_write_through_ref_mut_liar() { let mut x = 5u64; let ref mut r: u64 = x; *r = 7u64; trust_vc::assert!(x == 5u64); }
#[trust_vc::ensures(true)]
fn shared_ref_binding_reads_the_place() { let x = 5u64; let ref r = x; trust_vc::assert!(*r == 5u64); }
#[trust_vc::ensures(true)]
fn shared_ref_binding_reads_the_place_liar() { let x = 5u64; let ref r = x; trust_vc::assert!(*r == 6u64); }

#[trust_vc::ensures(true)]
fn index_place_ref_mut_binding_in_bounds() { let mut x: [u64; 3] = [5u64, 7u64, 8u64]; let ref mut r = x[1usize]; *r = 20u64; trust_vc::assert!(x[1usize] == 20u64); }
#[trust_vc::ensures(true)]
fn index_place_ref_mut_binding_out_of_bounds() { let mut x: [u64; 3] = [5u64, 7u64, 8u64]; let ref mut r = x[5usize]; *r = 20u64; }
#[trust_vc::ensures(true)]
fn field_place_ref_mut_binding() { let mut t = (5u64, 6u64); let ref mut r = t.0; *r = 20u64; trust_vc::assert!(t.0 == 20u64); }
#[trust_vc::ensures(true)]
fn value_initializer_ref_binding() { let a = 2u64; let b = 3u64; let ref q = a + b; trust_vc::assert!(*q == 5u64); }
#[trust_vc::ensures(true)]
fn call_initializer_ref_mut_binding() { let ref mut r = mk64(); r.f = 6u64; trust_vc::assert!(r.f == 6u64); }
"#;

#[test]
fn a_write_through_a_ref_mut_binding_is_not_modeled_on_a_copy() {
    let mut failures = Vec::new();
    for (index, func) in [
        "struct_compound_through_ref_mut",
        "tuple_compound_through_ref_mut",
        "split_overflow_through_ref_mut",
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
        "CARDINAL: a write through `let ref mut r = s` changes `s`; these must not verify:\n{}",
        failures.join("\n")
    );
}

#[test]
fn ref_bindings_model_the_borrowed_place() {
    let mut failures = Vec::new();
    for (index, func) in [
        "struct_field_write_through_ref_mut",
        "typed_struct_field_write_through_ref_mut",
        "scalar_deref_compound_through_ref_mut",
        "typed_scalar_deref_write_through_ref_mut",
        "shared_ref_binding_reads_the_place",
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

#[test]
fn a_non_variable_ref_binding_initializer_keeps_its_rejection() {
    // The rewrite is deliberately limited to a bare variable initializer (see
    // the module docs): an index place would be handed to the `&mut`
    // machinery's pre-existing out-of-bounds-borrow hole.
    let mut failures = Vec::new();
    for (index, func) in [
        "index_place_ref_mut_binding_in_bounds",
        "index_place_ref_mut_binding_out_of_bounds",
        "field_place_ref_mut_binding",
        "value_initializer_ref_binding",
        "call_initializer_ref_mut_binding",
    ]
    .into_iter()
    .enumerate()
    {
        let r = verify(&format!("n{index}"), func, SRC);
        if !matches!(r, VerifyResult::Error { .. }) {
            failures.push(format!("{func} must fail closed: {r:?}"));
        }
    }
    assert!(
        failures.is_empty(),
        "CARDINAL: a `ref` / `ref mut` binding of a non-variable place is not rewritten and must keep its rejection:\n{}",
        failures.join("\n")
    );
}
