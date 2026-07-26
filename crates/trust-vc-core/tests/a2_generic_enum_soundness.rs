// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Phase A2-generic — GENERIC ENUM inherent methods. A generic inherent method
//! (`impl<A> GOpt<A> { fn label(self) -> u64 }`) called on a CONCRETE enum
//! instantiation (`GOpt::<u64>::Some(x)` / `GOpt::<u64>::None`) is monomorphized
//! (`A -> u64`) and its conformance-checked contract applied at the call site —
//! exactly as for a generic STRUCT (see `a2_generic_soundness.rs`).
//!
//! The enabling change is CARRIER DISCOVERY: the concrete instantiation of an
//! enum receiver rides on a QUALIFIER path segment (`GOpt::<u64>::Some`), not a
//! struct literal, so `collect_concrete_receiver_carriers` learned to read it
//! from the path. Everything downstream — the `record_carrier` type-param/opaque
//! skip, the `Conflict` fail-close on a second instantiation, and the registry
//! same-leaf collision guard — is shared with the struct path, so this widens
//! DISCOVERY only, never the trust surface.
//!
//! CARDINAL: every TRUE post-monomorphization fact VERIFIES; every FALSE fact
//! (a wrong result, an unsound contract laundered through monomorphization, a
//! same-leaf cross-impl collision) must NOT verify. Covers both the no-`match`
//! method body AND a `match self`-inspecting body with PAYLOAD EXTRACTION — the
//! existing match lowering handles the monomorphized enum once its carrier is
//! discovered, so variant discrimination and per-variant payload binding are
//! sound (a wrong arm binding would false-verify `some_not_default`).

use trust_vc_core::{verify_function_from_file, VerifyResult};

// `tmp_id` is a per-test-unique temp-file key (tests run in parallel and would
// otherwise collide on the same path); `func` is the fixture function to verify.
fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_a2enum_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}

const ENUM_METHOD: &str = r#"
enum GOpt<A> { Some(A), None }
impl<A> GOpt<A> {
    #[trust_vc::ensures(result == 7u64)]
    fn label(self: GOpt<A>) -> u64 { 7u64 }
    #[trust_vc::ensures(result == 8u64)]
    fn label_bad(self: GOpt<A>) -> u64 { 7u64 }
}
"#;

fn src(body: &str) -> String {
    format!("{ENUM_METHOD}\n{body}\n")
}

#[test]
fn tuple_variant_receiver_monomorphizes() {
    let s = src(r#"#[trust_vc::ensures(true)]
fn f(x: u64) { let g = GOpt::<u64>::Some(x); trust_vc::assert!(g.label() == 7u64); }"#);
    assert!(matches!(verify("tuple", "f", &s), VerifyResult::Verified));
}

#[test]
fn unit_variant_receiver_monomorphizes() {
    // `GOpt::<u64>::None` is a bare unit-variant PATH (no Call) — the carrier
    // must be discovered from it too.
    let s = src(r#"#[trust_vc::ensures(true)]
fn f(_x: u64) { let g: GOpt<u64> = GOpt::<u64>::None; trust_vc::assert!(g.label() == 7u64); }"#);
    assert!(matches!(verify("unit", "f", &s), VerifyResult::Verified));
}

#[test]
fn false_fact_counterexamples() {
    let s = src(r#"#[trust_vc::ensures(true)]
fn f(x: u64) { let g = GOpt::<u64>::Some(x); trust_vc::assert!(g.label() == 8u64); }"#);
    assert!(
        matches!(
            verify("false", "f", &s),
            VerifyResult::Counterexample { .. }
        ),
        "CARDINAL: a false post-monomorphization fact must COUNTEREXAMPLE"
    );
}

#[test]
fn unsound_contract_cannot_be_laundered() {
    // `label_bad` ensures `result == 8` over a `7` body — it CEs at its OWN
    // verification, so a caller asserting the false ensures must NOT verify.
    let s = src(r#"#[trust_vc::ensures(true)]
fn f(x: u64) { let g = GOpt::<u64>::Some(x); trust_vc::assert!(g.label_bad() == 8u64); }"#);
    assert!(
        !matches!(verify("bad", "f", &s), VerifyResult::Verified),
        "CARDINAL: an unsound contract must not be laundered through monomorphization"
    );
}

#[test]
fn same_leaf_enum_collision_fails_closed() {
    // Two same-leaf generic enums `E<A>` with a `tag` method of DIFFERENT bodies:
    // the registry collision guard drops both, so the call must fail closed —
    // never launder `sa::E`'s `1u64` contract onto the top-level `E`.
    let s = r#"
mod sa { pub enum E<A> { V(A) } impl<A> E<A> { #[trust_vc::ensures(result == 1u64)] pub fn tag(self: E<A>) -> u64 { 1u64 } } }
enum E<A> { V(A) }
impl<A> E<A> { #[trust_vc::ensures(result == 2u64)] fn tag(self: E<A>) -> u64 { 2u64 } }
#[trust_vc::ensures(true)]
fn f(x: u64) { let e = E::<u64>::V(x); trust_vc::assert!(e.tag() == 1u64); }
"#;
    assert!(
        !matches!(verify("xleak", "f", s), VerifyResult::Verified),
        "CARDINAL: a same-leaf enum collision must fail closed, never launder the wrong body"
    );
}

// A `match self`-inspecting method with per-variant PAYLOAD binding. The existing
// match lowering handles the monomorphized enum once its carrier is discovered.
const MATCH_METHOD: &str = r#"
enum GOpt<A> { Some(A), None }
impl<A> GOpt<A> {
    #[trust_vc::ensures(true)]
    fn get_or(self: GOpt<A>, d: A) -> A { match self { GOpt::Some(v) => v, GOpt::None => d } }
}
"#;

fn match_src(body: &str) -> String {
    format!("{MATCH_METHOD}\n{body}\n")
}

#[test]
fn match_some_binds_payload() {
    let s = match_src(
        r#"#[trust_vc::ensures(true)]
fn f(x: u64) { let g = GOpt::<u64>::Some(x); trust_vc::assert!(g.get_or(9u64) == x); }"#,
    );
    assert!(matches!(verify("msome", "f", &s), VerifyResult::Verified));
}

#[test]
fn match_some_payload_is_not_default() {
    // The Some arm binds the payload `x` (≠ 9), NOT the default. A wrong arm
    // binding would false-verify this.
    let s = match_src(
        r#"#[trust_vc::requires(x != 9u64)]
#[trust_vc::ensures(true)]
fn f(x: u64) { let g = GOpt::<u64>::Some(x); trust_vc::assert!(g.get_or(9u64) == 9u64); }"#,
    );
    assert!(
        matches!(
            verify("msomecx", "f", &s),
            VerifyResult::Counterexample { .. }
        ),
        "CARDINAL: the Some arm must bind the payload, not the default"
    );
}

#[test]
fn match_none_returns_default() {
    let s = match_src(
        r#"#[trust_vc::ensures(true)]
fn f(_x: u64) { let g: GOpt<u64> = GOpt::<u64>::None; trust_vc::assert!(g.get_or(9u64) == 9u64); }"#,
    );
    assert!(matches!(verify("mnone", "f", &s), VerifyResult::Verified));
}

#[test]
fn match_none_default_is_exact() {
    let s = match_src(
        r#"#[trust_vc::ensures(true)]
fn f(_x: u64) { let g: GOpt<u64> = GOpt::<u64>::None; trust_vc::assert!(g.get_or(9u64) == 5u64); }"#,
    );
    assert!(
        matches!(
            verify("mnonecx", "f", &s),
            VerifyResult::Counterexample { .. }
        ),
        "CARDINAL: the None arm returns the default exactly, not an arbitrary value"
    );
}
