// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! CARDINAL: `assert forall` binder-type inference read the callee's type off a
//! spec function the program does not name.
//!
//! `collect_spec_signatures` walked `file.items` alone and keyed every spec fn
//! by its BARE name; `collect_binder_arg_types` then took the callee to be "the
//! identifier token immediately before `(`". So in `m::f1(x)` the `m::` was
//! discarded and the call matched a same-named TOP-LEVEL spec fn, whose
//! parameter type was then stamped onto the binder.
//!
//! With `mod m { spec fn f1(i: int) -> int { i } }` beside a top-level
//! `spec fn f1(i: nat) -> int`, the binder in
//! `assert_forall_by!(|x| m::f1(x) >= 0, {})` was annotated `nat`, narrowing the
//! quantifier domain from `int`. `m::f1` is the identity, so the claim is FALSE
//! at `x = -1` — and it VERIFIED.
//!
//! `nat` and `int` share the SMT Int sort, which is why this shape got through:
//! the same confusion between `u64` and `u8` produces a sort mismatch and fails
//! closed. A soundness argument that leans on a downstream sort check only
//! covers the cases where the sorts happen to differ.
//!
//! The module doc on `assert_forall_binder_inference.rs` already names this as
//! the unsound direction — "guessing WIDER than the truth (say `nat` where the
//! program means `int`) … would prove MORE than Verus" — and argues it cannot
//! happen because the type is read off the callee's signature. It was, just not
//! off the callee the program names. Resolution now runs through `SpecFnScopes`.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_afbs_{}_{}.rs", std::process::id(), id));
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

/// `m::f1` is the identity on `int`. The top-level `f1` takes `nat` — the
/// narrower domain that made the false claim provable.
const NAT_INT_SHADOW: &str = r#"
mod m {
    #[trust_vc::spec]
    pub fn f1(i: int) -> int { i }
}

#[trust_vc::spec]
fn f1(i: nat) -> int { 0 }

#[trust_vc::ensures(true)]
fn qualified_callee_false() -> u64 {
    trust_vc::assert_forall_by!(|x| m::f1(x) >= 0, {});
    0u64
}
"#;

/// The SAME file with the top-level `f1` taking `int`. The binder is then typed
/// `int` either way, so this is the control that proves the engine can refute
/// this exact claim when the domain is right — the flip between this and
/// `NAT_INT_SHADOW` is attributable to the binder domain and nothing else.
const NAT_INT_CONTROL: &str = r#"
mod m {
    #[trust_vc::spec]
    pub fn f1(i: int) -> int { i }
}

#[trust_vc::spec]
fn f1(i: int) -> nat { 0 }

#[trust_vc::ensures(true)]
fn qualified_callee_false() -> u64 {
    trust_vc::assert_forall_by!(|x| m::f1(x) >= 0, {});
    0u64
}
"#;

#[test]
fn qualified_callee_must_not_be_typed_by_a_top_level_spec_fn() {
    let r = verify("shadow", "qualified_callee_false", NAT_INT_SHADOW);
    eprintln!("[AFB-SCOPE-1] qualified_callee_false (nat shadow) => {r:?}");
    assert!(
        !verified(&r),
        "FALSE-VERIFY: `m::f1` is the identity on `int`, so the claim is false at \
         x = -1; the top-level `f1(i: nat)` narrowed the binder's domain; got {r:?}"
    );
}

#[test]
fn control_proves_the_flip_is_the_binder_domain() {
    let r = verify("control", "qualified_callee_false", NAT_INT_CONTROL);
    eprintln!("[AFB-SCOPE-2] qualified_callee_false (int control) => {r:?}");
    assert!(
        !verified(&r),
        "the same claim under an `int` binder must be refuted; got {r:?}"
    );
}

/// NARROWNESS PIN. The fix must RESOLVE `m::f1` to the module's own signature,
/// not merely refuse to type the binder. A pass that declined every qualified
/// callee would leave the binder untyped and produce the "binders must be typed"
/// ERROR — this pin demands a real counterexample, which only a correctly typed
/// `int` binder can produce.
#[test]
fn a_qualified_callee_is_resolved_not_merely_declined() {
    let r = verify("resolve", "qualified_callee_false", NAT_INT_SHADOW);
    eprintln!("[AFB-SCOPE-PIN1] resolution check => {r:?}");
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "NARROWNESS PIN: `m::f1(i: int)` must be resolved and the binder typed \
         `int`, yielding a counterexample — a blanket decline would error \
         instead; got {r:?}"
    );
}

/// NARROWNESS PIN: the ordinary unqualified top-level case must keep working.
const PLAIN: &str = r#"
#[trust_vc::spec]
fn f1(i: int) -> int { i + 1 }

#[trust_vc::ensures(true)]
fn plain_truth() -> u64 {
    trust_vc::assert_forall_by!(|x| f1(x) > x, {});
    0u64
}

#[trust_vc::ensures(true)]
fn plain_false() -> u64 {
    trust_vc::assert_forall_by!(|x| f1(x) > x + 1, {});
    0u64
}
"#;

#[test]
fn unqualified_top_level_inference_still_verifies() {
    let r = verify("plain_t", "plain_truth", PLAIN);
    eprintln!("[AFB-SCOPE-PIN2] plain_truth => {r:?}");
    assert!(
        verified(&r),
        "NARROWNESS PIN: `f1(x) > x` for `f1(i) = i + 1` is TRUE and the binder \
         must still be inferred; got {r:?}"
    );
}

#[test]
fn unqualified_top_level_inference_still_refutes() {
    let r = verify("plain_f", "plain_false", PLAIN);
    eprintln!("[AFB-SCOPE-PIN3] plain_false => {r:?}");
    assert!(!verified(&r), "`f1(x) > x + 1` is FALSE; got {r:?}");
}

/// A BARE `f1` written INSIDE `mod m` denotes `m::f1`, not the top-level `f1`.
/// `m::f1` is the identity on `int`, so the claim is FALSE at `x = -1`; typing
/// the binder from the top-level `f1(i: nat)` is what made it provable.
///
/// This shape currently fails CLOSED rather than producing a counterexample: a
/// module-declared spec fn is not registered in the downstream `TypeEnv`
/// ("unknown return type for function 'f1'"), which is a separate capability gap
/// in the spec-function catalog, not in this pass. The pin is therefore on
/// soundness only — `qualified_callee_*` above pins that resolution really
/// happens.
const IN_MODULE: &str = r#"
#[trust_vc::spec]
fn f1(i: nat) -> int { 0 }

mod m {
    #[trust_vc::spec]
    pub fn f1(i: int) -> int { i }

    #[trust_vc::ensures(true)]
    pub fn inner_false() -> u64 {
        trust_vc::assert_forall_by!(|x| f1(x) >= 0, {});
        0u64
    }
}
"#;

#[test]
fn in_module_bare_callee_is_not_typed_by_the_top_level_spec_fn() {
    let r = verify("inmod", "inner_false", IN_MODULE);
    eprintln!("[AFB-SCOPE-PIN4] inner_false => {r:?}");
    assert!(
        !verified(&r),
        "FALSE-VERIFY: inside `mod m`, `f1` is `m::f1(i: int)` — the identity — so \
         `f1(x) >= 0` is false at x = -1; the top-level `f1(i: nat)` must not \
         narrow the binder's domain; got {r:?}"
    );
}

/// A method call is not a free spec-fn call and must never be typed as one.
const METHOD_CALL: &str = r#"
#[trust_vc::spec]
fn f1(i: int) -> int { i + 1 }

#[trust_vc::ensures(true)]
fn method_shape() -> u64 {
    trust_vc::assert_forall_by!(|x| x.f1() > x, {});
    0u64
}
"#;

#[test]
fn a_method_call_does_not_supply_a_binder_type() {
    let r = verify("method", "method_shape", METHOD_CALL);
    eprintln!("[AFB-SCOPE-DECLINE1] method_shape => {r:?}");
    assert!(
        !verified(&r),
        "`x.f1()` is not a call to the free spec fn `f1` and must not type the \
         binder; got {r:?}"
    );
}
