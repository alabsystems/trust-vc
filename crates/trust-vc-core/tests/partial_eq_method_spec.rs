// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! `PartialEq` methods `.eq(&other)` / `.ne(&other)` in spec context, for
//! structural-equality receivers (integer/bool/char and recursively structural
//! tuples), where `==` is structural SMT equality — matching Verus. Mirrors the
//! already-supported `.lt()`/`.gt()` PartialOrd methods.
//!
//! CARDINAL: a custom-type `.eq()` stays FAIL-CLOSED — a user `PartialEq` impl
//! may be non-structural, so desugaring its `.eq()` to a structural `==` would
//! false-verify; only canonical tuple carriers and primitive components (where
//! `==` is unconditionally structural) are modeled.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_peq_{}_{}.rs", std::process::id(), id));
    std::fs::write(&p, src).expect("write fixture");
    // The override is process-wide and these tests run in parallel. Serialize
    // and restore it so this lane cannot race unrelated verifier tests or leak
    // cache-off state into later cases.
    let r =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            verify_function_from_file(p.to_str().unwrap(), func).unwrap_or_else(|e| {
                VerifyResult::Error {
                    message: e.to_string(),
                }
            })
        });
    let _ = std::fs::remove_file(&p);
    r
}
fn verified(r: &VerifyResult) -> bool {
    matches!(r, VerifyResult::Verified)
}

const SRC: &str = r#"
#[trust_vc::ensures(x.eq(&y) == (x == y))]
fn u64_eq_matches(x: u64, y: u64) -> bool { x == y }
#[trust_vc::ensures(a.ne(&b) == (a != b))]
fn u64_ne_matches(a: u64, b: u64) -> bool { a != b }
#[trust_vc::ensures(p.eq(&q) == (p == q))]
fn bool_eq_matches(p: bool, q: bool) -> bool { p == q }
#[trust_vc::ensures(c.eq(&d) == (c == d))]
fn char_eq_matches(c: char, d: char) -> bool { c == d }

// CARDINAL LIAR: an unconditional `.eq()` postcondition over arbitrary params.
#[trust_vc::ensures(x.eq(&y))]
fn u64_eq_liar(x: u64, y: u64) -> bool { x == y }

// Tuples of structural-eq components: `.eq()`/`.ne()` ARE structural (a tuple
// can't carry a custom PartialEq; its derived one compares components structurally).
#[trust_vc::ensures((a, b).eq(&(c, d)) == ((a, b) == (c, d)))]
fn tuple_eq_matches(a: u64, b: bool, c: u64, d: bool) -> bool { a == c && b == d }
#[trust_vc::ensures((a, b).ne(&(c, d)) == ((a, b) != (c, d)))]
fn tuple_ne_matches(a: u64, b: u64, c: u64, d: u64) -> bool { a != c || b != d }

// Option<integer>: structural `.eq()`/`.ne()` via the same encoder the Option
// ordering methods use (completes the lt/le/gt/ge/eq/ne surface for Option<int>).
#[trust_vc::ensures(o.eq(&o))]
fn option_eq_reflexive(o: Option<u64>) {}
#[trust_vc::ensures(o.eq(&q) == (o == q))]
fn option_eq_matches(o: Option<u64>, q: Option<u64>) -> bool { true }
#[trust_vc::ensures(o.ne(&q) == !(o == q))]
fn option_ne_matches(o: Option<u64>, q: Option<u64>) -> bool { true }

// A tuple whose component is a std Option (structural recursively).
#[trust_vc::ensures(t.eq(&t))]
fn tuple_option_eq_reflexive(t: (Option<u64>, bool)) {}

// Result<integer, integer>: structural `.eq()`/`.ne()` (both payloads structural).
#[trust_vc::ensures(r.eq(&r))]
fn result_eq_reflexive(r: Result<u64, u64>) {}
#[trust_vc::ensures(a.eq(&b) == (a == b))]
fn result_eq_matches(a: Result<u64, u64>, b: Result<u64, u64>) -> bool { true }
#[trust_vc::ensures(a.ne(&b) == !(a == b))]
fn result_ne_matches(a: Result<u64, u64>, b: Result<u64, u64>) -> bool { true }

// A user struct that DERIVES PartialEq: its `.eq()` is the structural `==`.
#[derive(PartialEq)]
struct Point { x: u64, y: bool }
#[trust_vc::ensures(a.eq(&b) == (a == b))]
fn derived_struct_eq(a: Point, b: Point) -> bool { true }

// A user ENUM that DERIVES PartialEq (incl. payloads).
#[derive(PartialEq)]
enum Shape { Circle(u64), Square(u64, u64) }
#[trust_vc::ensures(a.eq(&b) == (a == b))]
fn derived_enum_eq(a: Shape, b: Shape) -> bool { true }

// CARDINAL: a custom type's `.eq()` must FAIL CLOSED (custom PartialEq may be
// non-structural), so even this reflexive claim must NOT verify.
struct Wrap(u64);
#[trust_vc::ensures(w.eq(&w))]
fn custom_eq_fail_closed(w: Wrap) {}

// CARDINAL: a tuple CONTAINING a custom type must also fail closed — its derived
// PartialEq would use the custom component's (possibly non-structural) impl.
#[trust_vc::ensures((w, n).eq(&(w, n)))]
fn tuple_with_custom_fail_closed(w: Wrap, n: u64) {}

// CARDINAL: a user datatype is not a tuple merely because its only variant is
// named `Tuple`. Its PartialEq can be non-structural and must stay fail-closed.
enum UserTupleName { Tuple(u64) }
impl PartialEq for UserTupleName {
    fn eq(&self, _other: &Self) -> bool { false }
}
#[trust_vc::ensures(x.eq(&x))]
fn user_tuple_variant_name_fail_closed(x: UserTupleName) {}
"#;

const BUILTIN_SHADOW_SRC: &str = r#"
enum Option<T> { None, Some(T) }
impl<T> PartialEq for Option<T> {
    fn eq(&self, _other: &Self) -> bool { false }
}
#[trust_vc::ensures(x.eq(&x))]
fn user_option_shadow_fail_closed(x: Option<u64>) {}

enum Result<T, E> { Ok(T), Err(E) }
impl<T, E> PartialEq for Result<T, E> {
    fn eq(&self, _other: &Self) -> bool { false }
}
#[trust_vc::ensures(x.eq(&x))]
fn user_result_shadow_fail_closed(x: Result<u64, u64>) {}
"#;

#[test]
fn primitive_eq_ne_match_structural_equality() {
    for f in [
        "u64_eq_matches",
        "u64_ne_matches",
        "bool_eq_matches",
        "char_eq_matches",
        "tuple_eq_matches",
        "tuple_ne_matches",
        "option_eq_reflexive",
        "option_eq_matches",
        "option_ne_matches",
        "result_eq_reflexive",
        "result_eq_matches",
        "result_ne_matches",
        "tuple_option_eq_reflexive",
        "derived_struct_eq",
        "derived_enum_eq",
    ] {
        assert!(
            verified(&verify(f, f, SRC)),
            "`{f}` should verify: `.eq()`/`.ne()` on a structural-eq receiver is ==/!=; got {:?}",
            verify(f, f, SRC)
        );
    }
}

#[test]
fn eq_liar_is_not_verified() {
    assert!(
        !verified(&verify("l", "u64_eq_liar", SRC)),
        "CARDINAL: an unconditional `x.eq(&y)` over arbitrary x,y must NOT verify"
    );
}

#[test]
fn custom_type_eq_fails_closed() {
    for f in [
        "custom_eq_fail_closed",
        "tuple_with_custom_fail_closed",
        "user_tuple_variant_name_fail_closed",
    ] {
        assert!(
            !verified(&verify(f, f, SRC)),
            "CARDINAL: `{f}` must fail closed (a custom / custom-containing PartialEq may be \
             non-structural) — even a reflexive claim must not verify"
        );
    }

    for f in [
        "user_option_shadow_fail_closed",
        "user_result_shadow_fail_closed",
    ] {
        assert!(
            !verified(&verify(f, f, BUILTIN_SHADOW_SRC)),
            "CARDINAL: `{f}` must not inherit std Option/Result structural equality"
        );
    }
}
