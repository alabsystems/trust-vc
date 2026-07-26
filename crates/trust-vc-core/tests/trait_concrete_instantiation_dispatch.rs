// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Phase-A WALL #1: a TRAIT method on a CONCRETE INSTANTIATION of a generic
//! struct (`#[trait_impl] impl Fetch for W<u64> { fn fetch(&self) .. }`, a
//! NON-parameterized trait, no impl generics) now resolves at a `w: W<u64>`
//! receiver. The concrete-receiver trait path does not model a generic-struct
//! instantiation self type, so `w.fetch()` previously failed closed.
//!
//! SOUNDNESS MODEL: the method registers its DEFINITIONAL BODY AXIOM
//! (`fetch(self) == <body>`, the actual computation), keyed by the receiver's
//! canonical `to_type_string`. Conformance for the instantiation is enforced
//! SEPARATELY — a non-conformant `impl Fetch for W<u64>` fails its `trait impl
//! conformance ... (generic struct)` obligation, so the caller never reads an
//! unproven trait `ensures`; it reads only the true body. `from_impl_method`
//! declines a requires-bearing method, so the trait-requires machinery is never
//! perturbed. COLLISION GATE: a generic trait impl `impl<A> Fetch for W<A>` of the
//! same (trait, base) is skipped (its monomorphization could own the same UF).

use trust_vc_core::{
    list_trait_conformance_obligations, verify_function_from_file,
    verify_trait_conformance_obligation, VerifyResult,
};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_tci_{}_{}.rs", std::process::id(), id));
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

const OK: &str = r#"
struct W<P> { v: P }
#[trust_vc::trait_spec]
trait Zero { #[trust_vc::ensures(result == 0u64)] fn z(&self) -> u64; }
#[trust_vc::trait_impl]
impl Zero for W<u64> { fn z(&self) -> u64 { 0u64 } }
#[trust_vc::ensures(true)]
fn zero_pos(w: W<u64>) { trust_vc::assert!(w.z() == 0u64); }
#[trust_vc::ensures(true)]
fn zero_liar(w: W<u64>) { trust_vc::assert!(w.z() == 1u64); }

#[trust_vc::trait_spec]
trait Add1 { #[trust_vc::ensures(result == x + 1u64)] fn add1(&self, x: u64) -> u64; }
#[trust_vc::trait_impl]
impl Add1 for W<u64> { fn add1(&self, x: u64) -> u64 { x + 1u64 } }
#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(true)]
fn add1_pos(w: W<u64>, x: u64) { trust_vc::assert!(w.add1(x) == x + 1u64); }
"#;

// A GENERIC trait impl AND a concrete one of the same (trait, base): the collision
// gate skips the concrete registration → `w.fetch()` fails closed.
const COLLISION: &str = r#"
struct W<P> { v: P }
#[trust_vc::trait_spec]
trait Marker { #[trust_vc::ensures(true)] fn fetch(&self) -> u64; }
#[trust_vc::trait_impl]
impl<A> Marker for W<A> { fn fetch(&self) -> u64 { 1u64 } }
#[trust_vc::trait_impl]
impl Marker for W<u64> { fn fetch(&self) -> u64 { 2u64 } }
#[trust_vc::ensures(true)]
fn coll(w: W<u64>) { trust_vc::assert!(w.fetch() == 2u64); }
"#;

// A LYING impl (body 7, trait ensures 0): a caller reading the BODY (7) is a true
// modular verdict, but a caller reading the false trait ENSURES (0) must fail
// closed, and the impl's OWN conformance obligation must be rejected.
const LYING: &str = r#"
struct W<P> { v: P }
#[trust_vc::trait_spec]
trait Zero { #[trust_vc::ensures(result == 0u64)] fn z(&self) -> u64; }
#[trust_vc::trait_impl]
impl Zero for W<u64> { fn z(&self) -> u64 { 7u64 } }
#[trust_vc::ensures(true)]
fn reads_false_ensures(w: W<u64>) { trust_vc::assert!(w.z() == 0u64); }
"#;

#[test]
fn concrete_instantiation_trait_methods_resolve() {
    for f in ["zero_pos", "add1_pos"] {
        assert!(
            verified(&verify(f, f, OK)),
            "`{f}` should verify (trait method on a concrete instantiation); got {:?}",
            verify(f, f, OK)
        );
    }
    assert!(
        !verified(&verify("liar", "zero_liar", OK)),
        "CARDINAL: a false consequence of the body axiom must NOT verify"
    );
}

#[test]
fn generic_plus_concrete_trait_impl_fails_closed() {
    assert!(
        !verified(&verify("coll", "coll", COLLISION)),
        "CARDINAL: a generic trait impl and a concrete one of the same (trait, base) must fail \
         closed — the collision gate prevents two bodies owning one symbol"
    );
}

#[test]
fn caller_cannot_read_the_false_trait_ensures() {
    // The caller reads the definitional body (7), never the impl's false trait
    // `ensures result == 0`. Asserting the false ensures must fail closed.
    assert!(
        !verified(&verify("rfe", "reads_false_ensures", LYING)),
        "CARDINAL: a caller must not be able to read a lying impl's trait `ensures` — only its \
         true body"
    );
}

#[test]
fn lying_instantiation_impl_conformance_is_rejected() {
    // The impl's OWN conformance obligation (`body ⊨ trait ensures`) must be
    // rejected, so the file is rejected exactly as Verus rejects the impl.
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_tci_conf_{}.rs", std::process::id()));
    std::fs::write(&p, LYING).expect("write");
    let obs = list_trait_conformance_obligations(p.to_str().unwrap()).expect("list");
    assert!(
        !obs.is_empty(),
        "a concrete-instantiation trait impl must produce a conformance obligation"
    );
    for ob in &obs {
        let r = verify_trait_conformance_obligation(p.to_str().unwrap(), ob).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
        assert!(
            !verified(&r),
            "CARDINAL: the lying instantiation impl's conformance obligation `{ob}` must be \
             rejected; got {r:?}"
        );
    }
    let _ = std::fs::remove_file(&p);
}
