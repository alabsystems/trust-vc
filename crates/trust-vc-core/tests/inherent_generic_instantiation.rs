// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Phase-A WALL #1 inherent slice: an inherent method on a CONCRETE INSTANTIATION
//! of a generic struct (`impl W<u64> { fn m(&self) .. }`, no impl generics) now
//! resolves at a `w: W<u64>` receiver. Previously the registry dropped it (its
//! non-generic path skips a type-args self-type; its generic path needs impl
//! `<A>` generics), so `w.m()` failed closed even though `W<u64>` is a registered
//! datatype whose fields already encode.
//!
//! SOUNDNESS MODEL: the published fact is the DEFINITIONAL BODY AXIOM
//! (`m(self) == <body>`), the actual computation — not an unchecked contract.
//! Registration is gated on a whole-file leaf-count of exactly 1 for
//! `(base, method)`, which tallies EVERY inherent declaration (generic AND
//! concrete). A count of 1 proves no other body can own the method's UF symbol,
//! so a two-bodies-on-one-symbol false-verify is impossible by construction; any
//! ambiguity fails closed.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_gsi_{}_{}.rs", std::process::id(), id));
    std::fs::write(&p, src).expect("write fixture");
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

// Single concrete instantiation — the method resolves and its body axiom applies.
const SINGLE: &str = r#"
struct W<P> { v: P }
impl W<u64> {
    #[trust_vc::ensures(result == self.v)] fn inh(&self) -> u64 { self.v }
}
#[trust_vc::ensures(true)]
fn pos(w: W<u64>) { trust_vc::assert!(w.inh() == w.v); }

// CARDINAL LIAR: ensures result == self.v, so a fixed wrong value must fail closed
// (this also proves the positive is non-vacuous).
#[trust_vc::requires(w.v == 5u64)]
#[trust_vc::ensures(true)]
fn liar(w: W<u64>) { trust_vc::assert!(w.inh() == 6u64); }
"#;

// Two DIFFERENT concrete instantiations declaring the same method → leaf-count 2
// → BOTH excluded (fail closed): the collision-free gate.
const TWO_CONCRETE: &str = r#"
struct W<P> { v: P }
impl W<u64> { #[trust_vc::ensures(result == self.v)] fn m(&self) -> u64 { self.v } }
impl W<i32> { #[trust_vc::ensures(result == self.v)] fn m(&self) -> i32 { self.v } }
#[trust_vc::ensures(true)]
fn two(w: W<u64>) { trust_vc::assert!(w.m() == w.v); }
"#;

// A GENERIC impl AND a concrete impl declaring the same method → leaf-count 2 →
// the concrete registration is excluded AND the generic monomorphization is
// dropped by the cross-map guard. This is the exact two-bodies-one-symbol
// false-verify the gate exists to prevent: it MUST fail closed.
const GENERIC_PLUS_CONCRETE: &str = r#"
struct W<P> { v: P }
impl<A> W<A> { #[trust_vc::ensures(true)] fn m(&self) -> u64 { 1u64 } }
impl W<u64> { #[trust_vc::ensures(result == self.v)] fn m(&self) -> u64 { self.v } }
#[trust_vc::ensures(true)]
fn gc(w: W<u64>) { trust_vc::assert!(w.m() == w.v); }
"#;

// A GENERIC impl that RENAMES the carrier's type param (`impl<A> W<A>` over
// `struct W<P>`) monomorphized at a concrete PARAMETER receiver `w: W<u64>`. The
// impl's body mentions `A`, not the struct's `P`, so the monomorphization must
// bind `A→u64` (via the positional carrier→impl param remap), including for a
// `-> A` return.
const RENAMED_PARAMS: &str = r#"
struct W<P> { v: P }
impl<A> W<A> {
    #[trust_vc::ensures(result == 0u64)] fn m(&self) -> u64 { 0u64 }
    #[trust_vc::ensures(result == self.v)] fn get(&self) -> A { self.v }
}
#[trust_vc::ensures(true)]
fn rn_const(w: W<u64>) { trust_vc::assert!(w.m() == 0u64); }
#[trust_vc::ensures(true)]
fn rn_ret_param(w: W<u64>) { trust_vc::assert!(w.get() == w.v); }
#[trust_vc::ensures(true)]
fn rn_liar(w: W<u64>) { trust_vc::assert!(w.m() == 1u64); }
"#;

// A generic-impl CONSTRUCTOR (`impl<T> W<T> { fn new(v: T) -> Self }`) called via
// the turbofish associated path `W::<u64>::new(x)`. The body-axiom trigger and the
// caller both lower (via `expr_path_to_string`) to the base name `W::new`, so the
// associated symbol is registered under that base form (`W<u64>::new` would
// reparse as the chained comparison `W < u64 > :: new`).
const GENERIC_CONSTRUCTOR: &str = r#"
struct W<T> { v: T }
impl<T> W<T> {
    #[trust_vc::ensures(result.v == val)] fn new(val: T) -> Self { W { v: val } }
}
#[trust_vc::ensures(true)]
fn ctor_pos(x: u64) { trust_vc::assert!(W::<u64>::new(x).v == x); }
#[trust_vc::ensures(true)]
fn ctor_liar(x: u64) { trust_vc::assert!(W::<u64>::new(x).v == x + 1u64); }
"#;

#[test]
fn generic_impl_constructor_via_turbofish_resolves() {
    assert!(
        verified(&verify("ctor", "ctor_pos", GENERIC_CONSTRUCTOR)),
        "a generic-impl constructor `impl<T> W<T> {{ fn new(v: T) -> Self }}` called as \
         `W::<u64>::new(x)` should resolve; got {:?}",
        verify("ctor", "ctor_pos", GENERIC_CONSTRUCTOR)
    );
    assert!(
        !verified(&verify("ctorl", "ctor_liar", GENERIC_CONSTRUCTOR)),
        "CARDINAL: a false consequence of the generic constructor's ensures must NOT verify"
    );
}

#[test]
fn concrete_instantiation_inherent_method_resolves() {
    assert!(
        verified(&verify("pos", "pos", SINGLE)),
        "an inherent method on a concrete instantiation `impl W<u64>` should resolve at a \
         `w: W<u64>` receiver; got {:?}",
        verify("pos", "pos", SINGLE)
    );
}

#[test]
fn contract_liar_fails_closed_and_proves_non_vacuity() {
    assert!(
        !verified(&verify("liar", "liar", SINGLE)),
        "CARDINAL: a false consequence of the body axiom must NOT verify"
    );
}

#[test]
fn generic_impl_renaming_carrier_param_monomorphizes_at_parameter_receiver() {
    for f in ["rn_const", "rn_ret_param"] {
        assert!(
            verified(&verify(f, f, RENAMED_PARAMS)),
            "`{f}`: a generic impl that renames the carrier's type param (`impl<A> W<A>` over \
             `struct W<P>`) should monomorphize at a `w: W<u64>` receiver; got {:?}",
            verify(f, f, RENAMED_PARAMS)
        );
    }
    assert!(
        !verified(&verify("rn_liar", "rn_liar", RENAMED_PARAMS)),
        "CARDINAL: a false consequence of the monomorphized body must NOT verify"
    );
}

#[test]
fn two_concrete_instantiations_of_one_method_fail_closed() {
    assert!(
        !verified(&verify("two", "two", TWO_CONCRETE)),
        "CARDINAL: two concrete instantiations declaring the same method (leaf-count 2) must \
         fail closed — the wrong instantiation's body must never be readable"
    );
}

#[test]
fn generic_plus_concrete_same_method_fails_closed() {
    assert!(
        !verified(&verify("gc", "gc", GENERIC_PLUS_CONCRETE)),
        "CARDINAL: a generic impl and a concrete impl declaring the same method must fail \
         closed — this is the two-bodies-one-symbol collision the leaf-count gate prevents"
    );
}
