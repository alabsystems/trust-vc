// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The `#[cfg]` refusal reads a signature projection the way extraction does.
//!
//! `vc_extraction::refuse_unevaluated_cfg` refuses a target that reaches a
//! name declared by an item carrying or containing a `cfg` / `cfg_attr`
//! attribute. It starts its reach from the target's tokens with the signature
//! replaced by the one extraction typed (`cfg_reach_seed`):
//!
//! * a projection `<Q as P>::A` the projection resolver rewrote is reached
//!   through its bound type, so the bound's names are checked;
//! * a projection that is the whole type of a parameter or of the return and
//!   that the resolver left alone lowers to an opaque type and fails closed,
//!   so none of its names is reached.
//!
//! The resolver is the only reader of such a projection, and it never binds
//! through an impl or `type` item that carries a `cfg`, nor in a module path
//! that names more than one inline module. The pins in
//! `assoc_projection_impl_identity_soundness.rs` (F5a, F5b, F11) hold those
//! rules, and with the blanket refusal narrowed they reach the resolver again.
//! Measured with one resolver rule switched off at a time: with `cfg` admitted
//! on impls and `type` items, the F5a liar `f5a_cfg_impl_le255` is `Verified`;
//! with a duplicated module path accepted, the F11 liar `f11_dup_mod_le255` is
//! `Verified`. The F5b liar stays `OpaqueTypes` with `cfg` admitted, because
//! both `type X` items then bind and the resolver requires exactly one. The
//! liars here hold the bound rule and the parts of the reach the narrowing
//! does not touch.
//!
//! Each control is a true program that must verify. Each liar changes one line
//! of its control so the claim is false and must not verify. Where a liar was
//! measured with the rule switched off, its doc comment says what it returned.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn verdict(fixture: &str, src: &str, func: &str) -> VerifyResult {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_cfg_reach_projection_{}_{fixture}_{seq}.rs",
        std::process::id()
    ));
    std::fs::write(&path, src).expect("write fixture");
    let result =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            verify_function_from_file(path.to_str().expect("utf8 path"), func)
        })
        .unwrap_or_else(|e| VerifyResult::Error {
            message: format!("{e:?}"),
        });
    let _ = std::fs::remove_file(&path);
    result
}

fn assert_verified(fixture: &str, src: &str, func: &str) {
    let v = verdict(fixture, src, func);
    assert!(
        matches!(v, VerifyResult::Verified),
        "{fixture}::{func}: expected Verified (a true claim), got {v:?}"
    );
}

fn assert_refuted(fixture: &str, src: &str, func: &str) {
    let v = verdict(fixture, src, func);
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "{fixture}::{func}: expected a Counterexample (a false claim), got {v:?}"
    );
}

/// The file refusal, naming the tainted declaration `name` the target reaches.
fn assert_cfg_refused(fixture: &str, src: &str, func: &str, name: &str) {
    let refusal = format!(
        "`{name}` reaches a declaration in this file that carries a `#[cfg]` / `#[cfg_attr]` \
         attribute; vc_extraction does not evaluate `cfg`, so it may read a compiled-out \
         definition; this is unsupported in vc_extraction"
    );
    match verdict(fixture, src, func) {
        VerifyResult::Error { message } if message.contains(&refusal) => {}
        other => {
            panic!("{fixture}::{func}: expected the fail-closed error {refusal:?}, got {other:?}")
        }
    }
}

// ---------------------------------------------------------------------------
// A resolved projection is reached through its bound.
// ---------------------------------------------------------------------------

/// The shared prefix: a trait, a self type, a `cfg`-selected alias `W` whose
/// live definition is `u16`, and a `cfg`-selected const `N` whose live value
/// is `2`.
macro_rules! bound_fixture {
    ($binding:literal, $claim:literal) => {
        concat!(
            r#"
#[trust_vc::trait_spec]
trait Tr2 {
    type X;
}

struct S;

#[cfg(any())]
type W = u8;
#[cfg(not(any()))]
type W = u16;

#[cfg(any())]
const N: usize = 1;
#[cfg(not(any()))]
const N: usize = 2;

#[trust_vc::trait_impl]
impl Tr2 for S {
"#,
            $binding,
            r#"
}

#[trust_vc::ensures(result)]
fn rb_bound(x: <S as Tr2>::X) -> bool {
"#,
            $claim,
            r#"
}
"#
        )
    };
}

const RB_BOUND_U8: &str = bound_fixture!("    type X = u8;", "    x <= 255");
const RB_BOUND_W: &str = bound_fixture!("    type X = W;", "    x <= 255");
const RB_ARRAY_1: &str = bound_fixture!("    type X = [u8; 1];", "    x.len() == 1");
const RB_ARRAY_N: &str = bound_fixture!("    type X = [u8; N];", "    x.len() == 1");

/// Controls: the projection resolves to a bound that names nothing the `cfg`
/// pairs declare, so the target is not refused and verifies.
#[test]
fn rb_bound_plain_controls_verify() {
    assert_verified("rb_u8", RB_BOUND_U8, "rb_bound");
    assert_verified("rb_arr1", RB_ARRAY_1, "rb_bound");
}

/// Liar: the binding line puts `N`, whose live value is `2`, in the bound, so
/// `x.len() == 1` is false. The bound is reached and `N` refuses. Measured
/// with the lowered signature ignored (every whole-type projection dropped
/// whether or not it resolved): `Verified`.
#[test]
fn rb_bound_cfg_const_liar_is_refused() {
    assert_cfg_refused("rb_arrn", RB_ARRAY_N, "rb_bound", "N");
}

/// Liar: the binding line names `W`, whose live definition is `u16`, so
/// `x <= 255` is false at `x = 300`. The bound is reached and `W` refuses.
/// This liar does not discriminate: with the lowered signature ignored the
/// encoder fails on `W`'s sort, which is an error, not a verdict.
#[test]
fn rb_bound_cfg_alias_liar_is_refused() {
    assert_cfg_refused("rb_w", RB_BOUND_W, "rb_bound", "W");
}

// ---------------------------------------------------------------------------
// Only the projection is dropped; the rest of the target is still reached.
// ---------------------------------------------------------------------------

macro_rules! body_fixture {
    ($claim:literal) => {
        concat!(
            r#"
#[trust_vc::trait_spec]
trait Tr {
    type X;
}

#[trust_vc::trait_spec]
trait Tr2 {
    type X;
}

struct S;

#[cfg(any())]
#[trust_vc::trait_impl]
impl Tr for S {
    type X = u8;
}

#[cfg(not(any()))]
impl Tr for S {
    type X = u16;
}

#[trust_vc::trait_impl]
impl Tr2 for S {
    type X = u8;
}

#[cfg(any())]
const K: u64 = 1u64;
#[cfg(not(any()))]
const K: u64 = 2u64;

const L: u64 = 2u64;

#[trust_vc::ensures(result)]
fn rp_opaque(x: <S as Tr>::X) -> bool {
    L == 2u64
}

#[trust_vc::ensures(L == 2u64)]
fn rp_opaque_result(x: u16) -> <S as Tr>::X {
    x
}

#[trust_vc::ensures(result)]
fn rp_body_read(x: <S as Tr2>::X) -> bool {
"#,
            $claim,
            r#"
}
"#
        )
    };
}

const RP_BODY_L: &str = body_fixture!("    L == 2u64");
const RP_BODY_L_FALSE: &str = body_fixture!("    L == 1u64");
const RP_BODY_K: &str = body_fixture!("    K == 1u64");

/// An unresolved projection is dropped from the reach because the lowering
/// cannot type it: the parameter or result is opaque and the whole context
/// fails closed, whether or not the claim reads it.
#[test]
fn rp_unresolved_projection_is_opaque_not_refused() {
    for func in ["rp_opaque", "rp_opaque_result"] {
        let v = verdict("rp_opaque", RP_BODY_L, func);
        assert!(
            matches!(
                v,
                VerifyResult::Unknown {
                    category: trust_vc_core::UnknownCategory::OpaqueTypes,
                    ..
                }
            ),
            "{func}: expected the OpaqueTypes Unknown of an unresolved projection, got {v:?}"
        );
    }
}

/// Control: the projection resolves to `u8`; the body reads only the ungated
/// `L`, so the target is not refused. The true claim verifies and the false
/// one is refuted.
#[test]
fn rp_resolved_projection_body_control_verifies() {
    assert_verified("rp_l", RP_BODY_L, "rp_body_read");
    assert_refuted("rp_l_false", RP_BODY_L_FALSE, "rp_body_read");
}

/// Liar: the body line reads `K`, whose live definition is `2`. Dropping or
/// resolving the projection does not drop the body, so `K` refuses.
#[test]
fn rp_resolved_projection_body_liar_is_refused() {
    assert_cfg_refused("rp_k", RP_BODY_K, "rp_body_read", "K");
}

// ---------------------------------------------------------------------------
// A projection nested in another type keeps its names.
// ---------------------------------------------------------------------------

const RN_NESTED: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    type X;
}

struct S;

#[cfg(any())]
#[trust_vc::trait_impl]
impl Tr for S {
    type X = u8;
}

#[cfg(not(any()))]
impl Tr for S {
    type X = u16;
}

#[trust_vc::ensures(result)]
fn rn_nested_le255(x: (<S as Tr>::X, u8)) -> bool {
    x.1 <= 255
}
"#;

/// Only a projection that is the whole type of a parameter or of the return is
/// dropped. One inside a tuple keeps `S`, `Tr` and `X` in the reach, and they
/// are declared by the gated impl, so the target is refused as before.
#[test]
fn rn_nested_projection_is_still_refused() {
    assert_cfg_refused("rn", RN_NESTED, "rn_nested_le255", "S");
}

const RG_GENERIC: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    type X;
}

struct S;

#[cfg(any())]
#[trust_vc::trait_impl]
impl Tr for S {
    type X = u8;
}

#[cfg(not(any()))]
impl Tr for S {
    type X = u16;
}

#[trust_vc::ensures(result)]
fn rg_generic_le255<T>(t: T, x: <S as Tr>::X) -> bool {
    true
}
"#;

/// In a signature with a type parameter the resolver does not run, and a
/// projection there is not dropped: `S`, `Tr` and `X` stay in the reach, so
/// the target is refused as before.
#[test]
fn rg_generic_signature_projection_is_still_refused() {
    assert_cfg_refused("rg", RG_GENERIC, "rg_generic_le255", "S");
}
