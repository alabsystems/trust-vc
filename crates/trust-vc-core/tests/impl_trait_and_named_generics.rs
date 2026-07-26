// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Two coupled Phase-A trait-keystone advances:
//!
//! 1. ARGUMENT-position `impl Trait` (`fn f(x: impl Tr)`) is desugared to a
//!    synthetic generic type parameter (`fn f<__TrustVcAPIT0: Tr>(x: __TrustVcAPIT0)`)
//!    before extraction, so `x.spec_method()` resolves via the already-sound
//!    generic-trait-bound path (impl_trait_desugar.rs).
//!
//! 2. DESCRIPTIVELY-named generic type parameters (`Item`, `Key`, `Value`, …)
//!    are now recognized as type parameters. Previously only the context-free
//!    ≤2-char-uppercase heuristic in `TrustVcType::parse_or_opaque` classified a
//!    bare name as a type param, so `fn f<Item: Tr>(x: Item)` fell to
//!    `Opaque("Item")` and failed closed. Parameter typing now consults the
//!    signature's DECLARED generic parameters (context-aware), which is what also
//!    lets the synthetic APIT param resolve.
//!
//! CARDINAL: both advances desugar/reduce to the same generic path that is
//! already sound — a false consequence of the trait contract fails closed, and an
//! UNREGISTERED concrete type is never misclassified as a type parameter.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_apit_{}_{}.rs", std::process::id(), id));
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

const SRC: &str = r#"
#[trust_vc::trait_spec]
trait Tr { #[trust_vc::ensures(result == 5u64)] fn g(&self) -> u64; }
struct S;
#[trust_vc::trait_impl]
impl Tr for S { fn g(&self) -> u64 { 5u64 } }
#[trust_vc::trait_spec]
trait Marker { #[trust_vc::ensures(true)] fn m(&self) -> u64; }

// 1a — argument-position impl Trait resolves the trait contract at the call.
#[trust_vc::ensures(true)]
fn apit_pos(x: impl Tr) { trust_vc::assert!(x.g() == 5u64); }

// 1b — two impl-Trait args get DISTINCT synthetic params, both resolve.
#[trust_vc::ensures(true)]
fn apit_two(x: impl Tr, y: impl Tr) {
    trust_vc::assert!(x.g() == 5u64 && y.g() == 5u64);
}

// 1c — multi-bound impl Trait carries every trait bound.
#[trust_vc::ensures(true)]
fn apit_multi(x: impl Tr + Marker) { trust_vc::assert!(x.g() == 5u64); }

// 2a — descriptively-named generic type parameter.
#[trust_vc::ensures(true)]
fn named_pos<Item: Tr>(x: Item) { trust_vc::assert!(x.g() == 5u64); }

// ---- CARDINAL liars: a false consequence of the contract must fail closed ----
#[trust_vc::ensures(true)]
fn apit_liar(x: impl Tr) { trust_vc::assert!(x.g() == 6u64); }
#[trust_vc::ensures(true)]
fn named_liar<Item: Tr>(x: Item) { trust_vc::assert!(x.g() == 6u64); }

// ---- CARDINAL soundness: an UNREGISTERED concrete type (NOT a declared type
// param) must NOT be treated as a type parameter — it must stay fail-closed. ----
#[trust_vc::ensures(true)]
fn unknown_concrete(x: NotADeclaredTypeName) { trust_vc::assert!(x.g() == 5u64); }
"#;

// A SUPERTRAIT method reachable through a subtrait bound (`T: Ext` where
// `Ext: Base`) — `x.base()` must resolve to `Base__base` and its contract apply.
const SUPERTRAIT_SRC: &str = r#"
#[trust_vc::trait_spec]
trait Base { #[trust_vc::ensures(result == 1u64)] fn base(&self) -> u64; }
#[trust_vc::trait_spec]
trait Ext: Base { #[trust_vc::ensures(result == 2u64)] fn ext(&self) -> u64; }

// Positive: the supertrait method's contract applies through the subtrait bound.
#[trust_vc::ensures(true)]
fn super_pos<T: Ext>(x: T) { trust_vc::assert!(x.base() == 1u64); }

// The subtrait's own method still resolves alongside the supertrait's.
#[trust_vc::ensures(true)]
fn super_own<T: Ext>(x: T) { trust_vc::assert!(x.ext() == 2u64); }

// CARDINAL LIAR: base ensures result == 1, so asserting == 9 must fail closed.
#[trust_vc::ensures(true)]
fn super_liar<T: Ext>(x: T) { trust_vc::assert!(x.base() == 9u64); }
"#;

#[test]
fn impl_trait_and_named_generics_verify() {
    for f in ["apit_pos", "apit_two", "apit_multi", "named_pos"] {
        assert!(
            verified(&verify(f, f, SRC)),
            "`{f}` should verify (impl-Trait / named-generic trait dispatch); got {:?}",
            verify(f, f, SRC)
        );
    }
}

#[test]
fn contract_liars_fail_closed() {
    for f in ["apit_liar", "named_liar"] {
        assert!(
            !verified(&verify(f, f, SRC)),
            "CARDINAL: `{f}` asserts a false consequence of the trait contract — must NOT verify"
        );
    }
}

#[test]
fn supertrait_methods_resolve_through_subtrait_bound() {
    for f in ["super_pos", "super_own"] {
        assert!(
            verified(&verify(f, f, SUPERTRAIT_SRC)),
            "`{f}` should verify (supertrait/subtrait method via `T: Ext: Base`); got {:?}",
            verify(f, f, SUPERTRAIT_SRC)
        );
    }
    assert!(
        !verified(&verify("sl", "super_liar", SUPERTRAIT_SRC)),
        "CARDINAL: a false consequence of the supertrait contract must NOT verify"
    );
}

#[test]
fn unregistered_concrete_type_is_not_a_type_param() {
    // The declared-type-param recognition is context-aware: a name the signature
    // does NOT declare as a generic must never be reclassified as a type param.
    assert!(
        !verified(&verify("uc", "unknown_concrete", SRC)),
        "CARDINAL: an unregistered concrete param type must stay fail-closed, not \
         be treated as a universally-quantified type parameter"
    );
}
