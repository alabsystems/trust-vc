// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! A requires-bearing inherent method now publishes a GUARDED definitional body
//! axiom (`requires ==> method == body`) instead of no axiom (previously
//! fail-closed / result unconstrained). CARDINAL: publishing `method == body`
//! UNCONDITIONALLY would be a false-verify — the body only holds under the
//! precondition — so a caller that has NOT established the requires must not be
//! able to read the body value.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_req_{}_{}.rs", std::process::id(), id));
    std::fs::write(&p, src).expect("write");
    let r = verify_function_from_file(p.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}
fn verified(r: &VerifyResult) -> bool {
    matches!(r, VerifyResult::Verified)
}

const SRC: &str = r#"
struct S { x: u64 }
impl S {
    #[trust_vc::requires(d != 0u64)]
    #[trust_vc::ensures(result == self.x / d)]
    fn safe_div(&self, d: u64) -> u64 { self.x / d }
}
#[trust_vc::requires(d != 0u64)]
#[trust_vc::ensures(true)]
fn pos(s: S, d: u64) { trust_vc::assert!(s.safe_div(d) == s.x / d); }
#[trust_vc::ensures(true)]
fn liar_no_req(s: S, d: u64) { trust_vc::assert!(s.safe_div(d) == s.x / d); }
#[trust_vc::requires(d != 0u64)]
#[trust_vc::ensures(true)]
fn liar_body(s: S, d: u64) { trust_vc::assert!(s.safe_div(d) == 999u64); }
"#;

// The same, on a generic-struct INSTANTIATION (row-390 target).
const GENERIC: &str = r#"
struct W<T> { v: T }
impl<T> W<T> {
    #[trust_vc::requires(k != 0u64)]
    #[trust_vc::ensures(result == 7u64)]
    fn checked(&self, k: u64) -> u64 { 7u64 }
}
#[trust_vc::requires(k != 0u64)]
#[trust_vc::ensures(true)]
fn gpos(w: W<u64>, k: u64) { trust_vc::assert!(w.checked(k) == 7u64); }
#[trust_vc::ensures(true)]
fn gliar_no_req(w: W<u64>, k: u64) { trust_vc::assert!(w.checked(k) == 7u64); }
"#;

#[test]
fn requires_bearing_method_verifies_under_its_precondition() {
    assert!(
        verified(&verify("pos", "pos", SRC)),
        "with the requires established, the guarded body axiom applies; got {:?}",
        verify("pos", "pos", SRC)
    );
    assert!(
        verified(&verify("gpos", "gpos", GENERIC)),
        "generic-instantiation requires-bearing method under its precondition; got {:?}",
        verify("gpos", "gpos", GENERIC)
    );
}

#[test]
fn body_value_is_unreadable_without_the_precondition() {
    // The load-bearing CARDINAL case: an UNGUARDED axiom would let these verify.
    assert!(
        !verified(&verify("lnr", "liar_no_req", SRC)),
        "CARDINAL: without establishing the requires, the body value must NOT be provable"
    );
    assert!(
        !verified(&verify("glnr", "gliar_no_req", GENERIC)),
        "CARDINAL: generic-instantiation — body value unreadable without the precondition"
    );
}

#[test]
fn body_contradiction_under_precondition_fails_closed() {
    assert!(
        !verified(&verify("lb", "liar_body", SRC)),
        "CARDINAL: a false consequence of the body must NOT verify even under the requires"
    );
}

// Comprehensive inherent-impl SURFACE — the evidence backing row 390 = FULL:
// instance methods, associated fns (with args / no self), constructors (`-> P` /
// `-> Self`), Self resolution, multi-field/multi-method impls, generic-struct
// instantiation methods + constructors. mut-ref (`&mut self`) is out of scope
// (separately scored under Mut-refs, re-routed to trust-wp).
const SURFACE: &str = r#"
struct P { a: u64, b: u64 }
impl P {
    #[trust_vc::ensures(result == self.a)] fn geta(&self) -> u64 { self.a }
    #[trust_vc::ensures(result.a == x && result.b == y)] fn mk(x: u64, y: u64) -> P { P { a: x, b: y } }
    #[trust_vc::ensures(result.a == self.a + 1u64 && result.b == self.b)] fn inca(&self) -> Self { P { a: self.a + 1u64, b: self.b } }
    #[trust_vc::ensures(result == self.a + self.b)] fn sum(&self) -> u64 { self.a + self.b }
}
struct W<T> { v: T }
impl<T> W<T> {
    #[trust_vc::ensures(result == self.v)] fn get(&self) -> T { self.v }
    #[trust_vc::ensures(result.v == x)] fn new(x: T) -> Self { W { v: x } }
}
#[trust_vc::ensures(true)] fn s_method(p: P) { trust_vc::assert!(p.geta() == p.a); }
#[trust_vc::ensures(true)] fn s_assoc_args() { trust_vc::assert!(P::mk(3u64,4u64).b == 4u64); }
#[trust_vc::requires(p.a < 100u64)] #[trust_vc::ensures(true)] fn s_self_ret(p: P) { trust_vc::assert!(p.inca().a == p.a + 1u64); }
#[trust_vc::requires(p.a < 50u64 && p.b < 50u64)] #[trust_vc::ensures(true)] fn s_sum(p: P) { trust_vc::assert!(p.sum() == p.a + p.b); }
#[trust_vc::ensures(true)] fn g_method(w: W<u64>) { trust_vc::assert!(w.get() == w.v); }
#[trust_vc::ensures(true)] fn g_ctor(x: u64) { trust_vc::assert!(W::<u64>::new(x).v == x); }
#[trust_vc::ensures(true)] fn l_method(p: P) { trust_vc::assert!(p.geta() == p.b); }
#[trust_vc::ensures(true)] fn l_gctor(x: u64) { trust_vc::assert!(W::<u64>::new(x).v == 0u64); }
"#;

#[test]
fn inherent_impl_surface_is_comprehensive() {
    for f in [
        "s_method",
        "s_assoc_args",
        "s_self_ret",
        "s_sum",
        "g_method",
        "g_ctor",
    ] {
        assert!(
            verified(&verify(f, f, SURFACE)),
            "`{f}` should verify; got {:?}",
            verify(f, f, SURFACE)
        );
    }
    for f in ["l_method", "l_gctor"] {
        assert!(
            !verified(&verify(f, f, SURFACE)),
            "CARDINAL: liar `{f}` must fail closed"
        );
    }
}
