// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A `#[trust_vc::spec]` method on an INHERENT impl — `impl S { spec fn
//! inv(&self) -> bool { .. } }`, the ubiquitous Verus invariant-predicate shape
//! — was registered NOWHERE, so every `self.inv()` / `s.inv()` in a spec
//! position died as
//!
//! ```text
//! unsupported method `inv() on type `S`` — this method is not available in
//! specification context
//! ```
//!
//! ROOT: two lanes each assumed the other owned it.
//! `InherentImplRegistry::collect_items` skipped any method carrying
//! `has_spec_attr`, and `SpecFunctionCatalog::collect_items` collects
//! `syn::Item::Fn` ONLY — it never walks `syn::ImplItem::Fn`. The gap is NOT
//! trait-specific: it reproduces on a plain inherent `impl`.
//!
//! FIX: the inherent registry admits a `#[spec]` method and routes it through
//! the SAME `InherentMethodDef` pipeline as a plain method — a typed UF plus a
//! definitional body axiom that is already requires-GUARDED, shadow-gated and
//! ill-founded-recursion-gated. Two spec-lane markers still decline, so the
//! change only ever adds a definition whose semantics are the plain one:
//! `#[opaque]` (definition deliberately hidden until revealed) and
//! `#[uninterp]` (no body to publish).
//!
//! CARDINAL, enforced on every shape below: the TRUE contract verifies AND the
//! same-shape FALSE contract is REFUTED. A capability that also proves the liar
//! is not a capability.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_ispec_{}_{}.rs", std::process::id(), tmp_id));
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

/// The reported symptom: `self.inv()` inside the `requires` of a SIBLING method
/// of the same inherent impl, plus the same predicate read from a free function.
const PREDICATE: &str = r#"
struct SP { v: u64 }
impl SP {
    #[trust_vc::spec]
    fn inv(&self) -> bool { self.v < 100u64 }

    #[trust_vc::requires(self.inv())]
    #[trust_vc::ensures(result < 200u64)]
    fn bump_true(&self) -> u64 { self.v + 1u64 }

    // LIAR: `inv()` only bounds v by 100, so `v + 1 < 2` does not follow.
    #[trust_vc::requires(self.inv())]
    #[trust_vc::ensures(result < 2u64)]
    fn bump_liar(&self) -> u64 { self.v + 1u64 }
}
#[trust_vc::requires(s.inv())]
#[trust_vc::ensures(true)]
fn free_true(s: SP) { trust_vc::assert!(s.v < 100u64); }
#[trust_vc::requires(s.inv())]
#[trust_vc::ensures(true)]
fn free_liar(s: SP) { trust_vc::assert!(s.v < 50u64); }
"#;

#[test]
fn spec_method_in_sibling_requires_verifies() {
    assert!(
        verified(&verify("bt", "bump_true", PREDICATE)),
        "an inherent `#[spec]` method must resolve in a sibling method's requires"
    );
}

#[test]
fn spec_method_in_sibling_requires_liar_refuted() {
    assert!(
        !verified(&verify("bl", "bump_liar", PREDICATE)),
        "CARDINAL: `inv()` bounds v by 100 — `result < 2` must NOT verify"
    );
}

#[test]
fn spec_method_from_free_function_verifies() {
    assert!(
        verified(&verify("ft", "free_true", PREDICATE)),
        "an inherent `#[spec]` method must resolve at a free-function call site"
    );
}

#[test]
fn spec_method_from_free_function_liar_refuted() {
    assert!(
        !verified(&verify("fl", "free_liar", PREDICATE)),
        "CARDINAL: `inv()` gives v < 100, not v < 50 — must NOT verify"
    );
}

/// Two inherent impls declaring the same spec-method name: each receiver must
/// read ITS OWN definition. A cross-wired registration would prove `p.v < 5`
/// from `SP::inv` (which only says `v < 100`).
const TWO_TYPES: &str = r#"
struct SP { v: u64 }
struct SQ { v: u64 }
impl SP { #[trust_vc::spec] fn inv(&self) -> bool { self.v < 100u64 } }
impl SQ { #[trust_vc::spec] fn inv(&self) -> bool { self.v < 5u64 } }
#[trust_vc::requires(q.inv())]
#[trust_vc::ensures(true)]
fn sq_true(q: SQ) { trust_vc::assert!(q.v < 100u64); }
#[trust_vc::requires(p.inv())]
#[trust_vc::ensures(true)]
fn cross_liar(p: SP) { trust_vc::assert!(p.v < 5u64); }
"#;

#[test]
fn same_named_spec_methods_resolve_per_receiver_type() {
    assert!(
        verified(&verify("qt", "sq_true", TWO_TYPES)),
        "SQ::inv (v < 5) must imply v < 100"
    );
}

#[test]
fn same_named_spec_methods_do_not_cross_wire() {
    assert!(
        !verified(&verify("cl", "cross_liar", TWO_TYPES)),
        "CARDINAL: SQ::inv's `v < 5` must NOT be applied to an SP receiver"
    );
}

/// A `#[spec]` method carrying its OWN `requires`: the definitional body axiom
/// must stay GUARDED by that precondition. Publishing `guarded(s) == s.v - 10`
/// unconditionally is a false-verify whenever `s.v <= 10`.
const GUARDED: &str = r#"
struct SP { v: u64 }
impl SP {
    #[trust_vc::requires(self.v > 10u64)]
    #[trust_vc::spec]
    fn guarded(&self) -> u64 { self.v - 10u64 }
}
#[trust_vc::requires(s.v == 20u64)]
#[trust_vc::ensures(true)]
fn in_guard_true(s: SP) { trust_vc::assert!(s.guarded() == 10u64); }
#[trust_vc::requires(s.v == 20u64)]
#[trust_vc::ensures(true)]
fn in_guard_liar(s: SP) { trust_vc::assert!(s.guarded() == 11u64); }
#[trust_vc::requires(s.v == 0u64)]
#[trust_vc::ensures(true)]
fn out_of_guard_liar(s: SP) { trust_vc::assert!(s.guarded() == 0u64); }
"#;

#[test]
fn requires_bearing_spec_method_definition_applies_inside_its_guard() {
    assert!(
        verified(&verify("gt", "in_guard_true", GUARDED)),
        "inside its own requires the spec method's definition must be available"
    );
}

#[test]
fn requires_bearing_spec_method_liar_refuted() {
    assert!(
        !verified(&verify("gl", "in_guard_liar", GUARDED)),
        "CARDINAL: 20 - 10 is 10, not 11 — must NOT verify"
    );
}

#[test]
fn requires_bearing_spec_method_definition_stays_guarded() {
    assert!(
        !verified(&verify("go", "out_of_guard_liar", GUARDED)),
        "CARDINAL: the body axiom must not fire where the method's own requires \
         is violated — an unguarded `guarded == v - 10` proves anything at v == 0"
    );
}

/// NARROWNESS PIN. `#[opaque]` hides the definition until an explicit reveal;
/// admitting the method must NOT publish its body. If this test flips to
/// "verified", opacity has been defeated.
const OPAQUE: &str = r#"
struct SP { v: u64 }
impl SP {
    #[trust_vc::opaque]
    #[trust_vc::spec]
    fn hidden(&self) -> bool { self.v < 100u64 }
}
#[trust_vc::requires(s.hidden())]
#[trust_vc::ensures(true)]
fn opaque_leak(s: SP) { trust_vc::assert!(s.v < 100u64); }
"#;

#[test]
fn opaque_spec_method_body_is_not_published() {
    assert!(
        !verified(&verify("op", "opaque_leak", OPAQUE)),
        "NARROWNESS: an `#[opaque]` spec method's body must stay hidden"
    );
}

/// NARROWNESS PIN. A self-recursive `#[spec]` method with no termination
/// measure has no sound definitional axiom; both directions must stay refuted.
const RECURSIVE: &str = r#"
struct SP { v: u64 }
impl SP {
    #[trust_vc::spec]
    fn rec(&self, n: u64) -> u64 { if n == 0u64 { 0u64 } else { self.rec(n - 1u64) } }
}
#[trust_vc::ensures(true)]
fn rec_liar(s: SP) { trust_vc::assert!(s.rec(3u64) == 99u64); }
"#;

#[test]
fn ill_founded_recursive_spec_method_stays_fail_closed() {
    assert!(
        !verified(&verify("rl", "rec_liar", RECURSIVE)),
        "NARROWNESS: a decreases-free self-recursive spec method publishes no axiom"
    );
}

/// NARROWNESS PIN. Two inherent impls of the SAME type declaring the same spec
/// method: source order must never pick a winner. Both readings stay refuted.
const AMBIGUOUS: &str = r#"
struct SP { v: u64 }
impl SP { #[trust_vc::spec] fn inv(&self) -> bool { self.v < 100u64 } }
impl SP { #[trust_vc::spec] fn inv(&self) -> bool { self.v < 3u64 } }
#[trust_vc::requires(s.inv())]
#[trust_vc::ensures(true)]
fn ambig_first(s: SP) { trust_vc::assert!(s.v < 100u64); }
#[trust_vc::requires(s.inv())]
#[trust_vc::ensures(true)]
fn ambig_second(s: SP) { trust_vc::assert!(s.v < 3u64); }
"#;

#[test]
fn ambiguous_spec_method_declarations_fail_closed() {
    assert!(
        !verified(&verify("am1", "ambig_first", AMBIGUOUS)),
        "NARROWNESS: a colliding registry key must not resolve to the first declaration"
    );
    assert!(
        !verified(&verify("am2", "ambig_second", AMBIGUOUS)),
        "NARROWNESS: a colliding registry key must not resolve to the second declaration"
    );
}

/// Spec method taking an ARGUMENT and one reading a second field — the typed-UF
/// signature and the body axiom must both carry through.
const ARGS: &str = r#"
struct SP { v: u64, w: u64 }
impl SP {
    #[trust_vc::spec]
    fn atleast(&self, k: u64) -> bool { self.v >= k }
    #[trust_vc::spec]
    fn sum(&self) -> u64 { self.v + self.w }
}
#[trust_vc::requires(s.atleast(10u64))]
#[trust_vc::ensures(true)]
fn arg_true(s: SP) { trust_vc::assert!(s.v >= 10u64); }
#[trust_vc::requires(s.atleast(10u64))]
#[trust_vc::ensures(true)]
fn arg_liar(s: SP) { trust_vc::assert!(s.v >= 11u64); }
#[trust_vc::requires(s.v == 3u64 && s.w == 4u64)]
#[trust_vc::ensures(true)]
fn sum_true(s: SP) { trust_vc::assert!(s.sum() == 7u64); }
#[trust_vc::requires(s.v == 3u64 && s.w == 4u64)]
#[trust_vc::ensures(true)]
fn sum_liar(s: SP) { trust_vc::assert!(s.sum() == 8u64); }
"#;

#[test]
fn spec_method_with_argument_verifies_and_liar_refuted() {
    assert!(verified(&verify("gt1", "arg_true", ARGS)));
    assert!(
        !verified(&verify("gl1", "arg_liar", ARGS)),
        "CARDINAL: `atleast(10)` does not give `v >= 11`"
    );
}

#[test]
fn spec_method_over_two_fields_verifies_and_liar_refuted() {
    assert!(verified(&verify("st1", "sum_true", ARGS)));
    assert!(
        !verified(&verify("sl1", "sum_liar", ARGS)),
        "CARDINAL: 3 + 4 is 7, not 8"
    );
}

/// NARROWNESS PIN, arithmetic model. `inc()` is `self.v + 1`; at `v == u64::MAX`
/// neither the mathematical nor the wrapping reading makes `inc() > v` valid, so
/// the unbounded claim must be refuted while the bounded one verifies.
const ARITH: &str = r#"
struct SP { v: u64 }
impl SP {
    #[trust_vc::spec]
    fn inc(&self) -> u64 { self.v + 1u64 }
}
#[trust_vc::ensures(true)]
fn unbounded_liar(s: SP) { trust_vc::assert!(s.inc() > s.v); }
#[trust_vc::requires(s.v < 10u64)]
#[trust_vc::ensures(true)]
fn bounded_true(s: SP) { trust_vc::assert!(s.inc() == s.v + 1u64); }
"#;

#[test]
fn spec_method_arithmetic_bounded_case_verifies() {
    assert!(
        verified(&verify("at", "bounded_true", ARITH)),
        "a bounded spec-method arithmetic fact must verify"
    );
}

#[test]
fn spec_method_arithmetic_unbounded_liar_refuted() {
    assert!(
        !verified(&verify("al", "unbounded_liar", ARITH)),
        "CARDINAL: `inc() > v` fails at u64::MAX under either arithmetic model"
    );
}
