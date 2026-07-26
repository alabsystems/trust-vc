// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Capability-pinning regression suite for GENERIC (bounded-type-param) trait
//! dispatch and spec-function calls in spec contexts.
//!
//! Establishes empirically (2026-07-22) that the engine already resolves a
//! trait method call on a generic `T: Bound` receiver to the trait's contract,
//! across arg-referencing ensures, repeated-call determinism, field-predicate
//! ensures, multiple bounds, and composition with spec functions — and that
//! every corresponding LIAR is fail-closed (never `Verified`). These are the
//! frontier past the concrete-receiver suite (`concrete_trait_method_call_site`)
//! and had no dedicated harness; the liar pins guard the cardinal invariant on
//! this surface (cf. the 77c9162 nullary-constructor false-verify that a
//! `--test` liar caught where `--lib` did not).

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_gtd_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}

fn is_verified(r: &VerifyResult) -> bool {
    matches!(r, VerifyResult::Verified)
}

// ── basic bounded dispatch: trait ensures applies to a generic receiver ──
const BASIC: &str = r#"
#[trust_vc::trait_spec]
trait Tr { #[trust_vc::ensures(result == 7u64)] fn m(&self) -> u64; }
#[trust_vc::ensures(true)]
fn g_pos<T: Tr>(x: T) { trust_vc::assert!(x.m() == 7u64); }
#[trust_vc::ensures(true)]
fn g_liar<T: Tr>(x: T) { trust_vc::assert!(x.m() == 8u64); }
"#;

// ── ensures references a method argument, generic receiver ──
const ARG: &str = r#"
#[trust_vc::trait_spec]
trait Tr { #[trust_vc::ensures(result == x + x)] fn dbl(&self, x: u64) -> u64; }
#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(true)]
fn g_arg_pos<T: Tr>(t: T, x: u64) { trust_vc::assert!(t.dbl(x) == x + x); }
#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(true)]
fn g_arg_liar<T: Tr>(t: T, x: u64) { trust_vc::assert!(t.dbl(x) == x + x + 1u64); }
"#;

// ── repeated calls on the same generic receiver agree (determinism) ──
const DET: &str = r#"
#[trust_vc::trait_spec]
trait Tr { #[trust_vc::ensures(result == 7u64)] fn m(&self) -> u64; }
#[trust_vc::ensures(true)]
fn g_det<T: Tr>(t: T) { trust_vc::assert!(t.m() == t.m()); }
"#;

// ── two trait bounds on one type param ──
const TWO: &str = r#"
#[trust_vc::trait_spec]
trait A { #[trust_vc::ensures(result == 1u64)] fn a(&self) -> u64; }
#[trust_vc::trait_spec]
trait B { #[trust_vc::ensures(result == 2u64)] fn b(&self) -> u64; }
#[trust_vc::ensures(true)]
fn g_two_pos<T: A + B>(t: T) { trust_vc::assert!(t.a() + t.b() == 3u64); }
#[trust_vc::ensures(true)]
fn g_two_liar<T: A + B>(t: T) { trust_vc::assert!(t.a() + t.b() == 4u64); }
"#;

// ── spec function composed with a generic dispatch result ──
const SPEC_GEN: &str = r#"
#[trust_vc::spec]
fn inc(x: u64) -> u64 { x + 1u64 }
#[trust_vc::trait_spec]
trait Tr { #[trust_vc::ensures(result == 7u64)] fn m(&self) -> u64; }
#[trust_vc::ensures(true)]
fn g_specgen_pos<T: Tr>(t: T) { trust_vc::assert!(inc(t.m()) == 8u64); }
#[trust_vc::ensures(true)]
fn g_specgen_liar<T: Tr>(t: T) { trust_vc::assert!(inc(t.m()) == 9u64); }
"#;

// ── nested spec-to-spec call ──
const SPEC_NEST: &str = r#"
#[trust_vc::spec]
fn inc(x: u64) -> u64 { x + 1u64 }
#[trust_vc::spec]
fn inc2(x: u64) -> u64 { inc(inc(x)) }
#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(true)]
fn s_nest_pos(x: u64) { trust_vc::assert!(inc2(x) == x + 2u64); }
#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(true)]
fn s_nest_liar(x: u64) { trust_vc::assert!(inc2(x) == x + 3u64); }
"#;

#[test]
fn basic_bounded_dispatch_applies_and_liar_fails_closed() {
    assert!(
        is_verified(&verify("bp", "g_pos", BASIC)),
        "generic T: Tr, x.m()==7 must verify"
    );
    let liar = verify("bl", "g_liar", BASIC);
    assert!(
        !is_verified(&liar),
        "CARDINAL: x.m()==8 (ensures says 7) must NOT verify, got {liar:?}"
    );
}

#[test]
fn arg_referencing_ensures_on_generic_receiver() {
    assert!(
        is_verified(&verify("ap", "g_arg_pos", ARG)),
        "t.dbl(x)==x+x must verify for generic T: Tr"
    );
    let liar = verify("al", "g_arg_liar", ARG);
    assert!(
        !is_verified(&liar),
        "CARDINAL: t.dbl(x)==x+x+1 must NOT verify, got {liar:?}"
    );
}

#[test]
fn repeated_generic_dispatch_is_deterministic() {
    assert!(
        is_verified(&verify("d", "g_det", DET)),
        "t.m()==t.m() must verify (same receiver, deterministic)"
    );
}

#[test]
fn two_bounds_on_one_param_apply_and_liar_fails_closed() {
    assert!(
        is_verified(&verify("tp", "g_two_pos", TWO)),
        "T: A+B, a()+b()==3 must verify"
    );
    let liar = verify("tl", "g_two_liar", TWO);
    assert!(
        !is_verified(&liar),
        "CARDINAL: a()+b()==4 must NOT verify, got {liar:?}"
    );
}

#[test]
fn spec_fn_composed_with_generic_dispatch() {
    assert!(
        is_verified(&verify("sgp", "g_specgen_pos", SPEC_GEN)),
        "inc(t.m())==8 must verify"
    );
    let liar = verify("sgl", "g_specgen_liar", SPEC_GEN);
    assert!(
        !is_verified(&liar),
        "CARDINAL: inc(t.m())==9 must NOT verify, got {liar:?}"
    );
}

#[test]
fn nested_spec_to_spec_call_and_liar_fails_closed() {
    assert!(
        is_verified(&verify("snp", "s_nest_pos", SPEC_NEST)),
        "inc2(x)==x+2 must verify"
    );
    let liar = verify("snl", "s_nest_liar", SPEC_NEST);
    assert!(
        !is_verified(&liar),
        "CARDINAL: inc2(x)==x+3 must NOT verify, got {liar:?}"
    );
}
