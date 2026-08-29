// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Guard for a CARDINAL false verify: a TRAIT method's `ensures` answered an
//! INHERENT method's call site, and a same-named method on a second trait was
//! conformance-checked against the FIRST trait's body.
//!
//! Both defects share one root — `format!("{type}__{method}")` carries the self
//! type but NOT the trait, so it is not an identity. `impl B1 for T { fn w }`
//! and `impl T { fn w }` mint the same `T__w`; so do `impl A1 for S { fn v }`
//! and `impl A2 for S { fn v }`.
//!
//! ## Defect 1 — the receiver surface (CARDINAL)
//!
//! ```text
//! #[trait_spec] trait B1 { #[ensures(result == 9)] fn w(&self) -> u64; }
//! #[trait_impl] impl B1 for T { fn w(&self) -> u64 { 9 } }
//! impl T { #[ensures(result == 4)] fn w(&self) -> u64 { 4 } }
//!
//! #[ensures(result == 4)] fn f(t: &T) -> u64 { t.w() }   // -> counterexample
//! #[ensures(result == 9)] fn g(t: &T) -> u64 { t.w() }   // -> VERIFIED
//! ```
//!
//! Ground truth, compiled and run under stock `rustc --edition 2021`:
//! `t.w() == 4` (an inherent method takes precedence over a trait method of the
//! same name) while `B1::w(&t) == 9`. So the false claim VERIFIED and the true
//! claim was REFUTED, simultaneously — the confident-wrong-value signature.
//!
//! The mechanism is worth stating because it inverts the usual intuition: the
//! inherent-wins rule is implemented as REGISTRATION ORDER over a shared
//! `(type, method)` map in `prepared_context::type_env`
//! (`register_trait_impl_methods_for_concrete_types` is registered last and
//! "never overrides an existing binding"). `20e12591` closed the no-`self`
//! associated-fn collision with a gate that dropped the inherent registration
//! whenever ANY trait impl for the type declared that name. Dropping the
//! shadowing entry does not fail closed — it PROMOTES the shadowed one. The
//! previous instalment's fix is what opened this one.
//!
//! ## Defect 2 — the conformance lane (over-rejection, same root)
//!
//! Three traits declaring `fn v(&self) -> u64` with `ensures` 1/2/3, all
//! implemented for one struct returning 1/2/3, measured through the production
//! CLI, cache off:
//!
//! ```text
//! trait impl conformance A1::v for S -> verified
//! trait impl conformance A2::v for S -> counterexample   (model: result = 1)
//! trait impl conformance A3::v for S -> counterexample   (model: result = 1)
//! ```
//!
//! The counterexample model naming `1` is the proof of misattribution: A1's
//! captured body answered A2's and A3's obligations, because
//! `trait_impl_method_bodies` was keyed by the trait-erased concrete name and
//! inserted first-registration-wins.
//!
//! ## The fix, and what these tests actually pin
//!
//! `MethodSymbolCensus` is the sole resolution authority: an exhaustive enum
//! over the declarations competing for one symbol, resolved against an
//! exhaustive `MethodCallSurface`. `Receiver` applies Rust's shadowing rule;
//! `AssociatedPath` (where `<S as Tr>::m()` and `S::m()` render to the SAME
//! string) resolves nothing on a collision. Anything that does not resolve to
//! exactly ONE declaration is DROPPED so the caller fails closed. A trait that
//! loses the symbol also stops publishing its linking axiom and its
//! concrete-sorted ensures axiom about it — required, not optional: with the
//! inherent body axiom `T__w(t) == 4` and the trait postcondition
//! `B1__w(_) == 9` both in scope, the linking axiom `B1__w(Box_T(t)) == T__w(t)`
//! asserts `4 == 9`, and a contradiction proves everything.
//!
//! The NARROWNESS pins below are the point of this file as much as the cardinal
//! ones. A gate that declines everything satisfies every false-claim test and is
//! a capability disaster, so each true claim must VERIFY while its same-shape
//! liar REFUTES.

use trust_vc_core::{verify_function_from_file, verify_trait_conformance_obligation, VerifyResult};

// ---------------------------------------------------------------------------
// Fixtures.
// ---------------------------------------------------------------------------

/// The cardinal reproducer: one trait, one inherent, same name, same type.
const INHERENT_SHADOWS_TRAIT: &str = r#"
#[trust_vc::trait_spec]
pub trait B1 { #[trust_vc::ensures(result == 9u64)] fn w(&self) -> u64; }
pub struct T;
#[trust_vc::trait_impl]
impl B1 for T { fn w(&self) -> u64 { 9u64 } }
impl T { #[trust_vc::ensures(result == 4u64)] pub fn w(&self) -> u64 { 4u64 } }

#[trust_vc::ensures(result == 4u64)]
pub fn inherent_true(t: &T) -> u64 { t.w() }

#[trust_vc::ensures(result == 9u64)]
pub fn inherent_liar(t: &T) -> u64 { t.w() }

#[trust_vc::ensures(result == 9u64)]
pub fn ufcs_qualified_true(t: &T) -> u64 { <T as B1>::w(t) }

#[trust_vc::ensures(result == 4u64)]
pub fn ufcs_qualified_liar(t: &T) -> u64 { <T as B1>::w(t) }

#[trust_vc::ensures(result == 9u64)]
pub fn ufcs_path_true(t: &T) -> u64 { B1::w(t) }

#[trust_vc::ensures(result == 4u64)]
pub fn ufcs_path_liar(t: &T) -> u64 { B1::w(t) }
"#;

/// TWO traits plus an inherent. The inherent still wins, and neither trait's
/// answer may leak.
const INHERENT_SHADOWS_TWO_TRAITS: &str = r#"
#[trust_vc::trait_spec]
pub trait B1 { #[trust_vc::ensures(result == 9u64)] fn w(&self) -> u64; }
#[trust_vc::trait_spec]
pub trait B2 { #[trust_vc::ensures(result == 7u64)] fn w(&self) -> u64; }
pub struct T;
#[trust_vc::trait_impl]
impl B1 for T { fn w(&self) -> u64 { 9u64 } }
#[trust_vc::trait_impl]
impl B2 for T { fn w(&self) -> u64 { 7u64 } }
impl T { #[trust_vc::ensures(result == 4u64)] pub fn w(&self) -> u64 { 4u64 } }

#[trust_vc::ensures(result == 4u64)]
pub fn inherent_true(t: &T) -> u64 { t.w() }

#[trust_vc::ensures(result == 9u64)]
pub fn liar_b1(t: &T) -> u64 { t.w() }

#[trust_vc::ensures(result == 7u64)]
pub fn liar_b2(t: &T) -> u64 { t.w() }
"#;

/// The competing trait impl lives in an inline `mod`. The census must see it —
/// a `mod`-local view would report the pair unshadowed and re-open the defect.
const INHERENT_SHADOWS_NESTED_TRAIT: &str = r#"
#[trust_vc::trait_spec]
pub trait B1 { #[trust_vc::ensures(result == 9u64)] fn w(&self) -> u64; }
pub struct T;
pub mod nested {
    #[trust_vc::trait_impl]
    impl super::B1 for super::T { fn w(&self) -> u64 { 9u64 } }
}
impl T { #[trust_vc::ensures(result == 4u64)] pub fn w(&self) -> u64 { 4u64 } }

#[trust_vc::ensures(result == 4u64)]
pub fn inherent_true(t: &T) -> u64 { t.w() }

#[trust_vc::ensures(result == 9u64)]
pub fn inherent_liar(t: &T) -> u64 { t.w() }
"#;

/// TWO traits declaring the name, NO inherent. Nothing can pick between them on
/// the receiver surface, so both directions must fail closed.
const TWO_TRAITS_NO_INHERENT: &str = r#"
#[trust_vc::trait_spec]
pub trait A1 { #[trust_vc::ensures(result == 1u64)] fn v(&self) -> u64; }
#[trust_vc::trait_spec]
pub trait A2 { #[trust_vc::ensures(result == 2u64)] fn v(&self) -> u64; }
pub struct S;
#[trust_vc::trait_impl]
impl A1 for S { fn v(&self) -> u64 { 1u64 } }
#[trust_vc::trait_impl]
impl A2 for S { fn v(&self) -> u64 { 2u64 } }

#[trust_vc::ensures(result == 1u64)]
pub fn claims_one(s: &S) -> u64 { s.v() }

#[trust_vc::ensures(result == 2u64)]
pub fn claims_two(s: &S) -> u64 { s.v() }
"#;

/// NARROWNESS: inherent only, nothing competing.
const INHERENT_ONLY: &str = r#"
pub struct T;
impl T { #[trust_vc::ensures(result == 4u64)] pub fn w(&self) -> u64 { 4u64 } }

#[trust_vc::ensures(result == 4u64)]
pub fn only_true(t: &T) -> u64 { t.w() }

#[trust_vc::ensures(result == 9u64)]
pub fn only_liar(t: &T) -> u64 { t.w() }
"#;

/// NARROWNESS: a single trait, no inherent — the ordinary trait-dispatch case
/// that must be byte-for-byte unaffected.
const TRAIT_ONLY: &str = r#"
#[trust_vc::trait_spec]
pub trait B1 { #[trust_vc::ensures(result == 9u64)] fn w(&self) -> u64; }
pub struct T;
#[trust_vc::trait_impl]
impl B1 for T { fn w(&self) -> u64 { 9u64 } }

#[trust_vc::ensures(result == 9u64)]
pub fn only_true(t: &T) -> u64 { t.w() }

#[trust_vc::ensures(result == 4u64)]
pub fn only_liar(t: &T) -> u64 { t.w() }
"#;

/// The conformance lane: THREE traits, one method name, one type. Every
/// obligation is honest and every one must verify.
const THREE_TRAITS_HONEST: &str = r#"
#[trust_vc::trait_spec]
pub trait A1 { #[trust_vc::ensures(result == 1u64)] fn v(&self) -> u64; }
#[trust_vc::trait_spec]
pub trait A2 { #[trust_vc::ensures(result == 2u64)] fn v(&self) -> u64; }
#[trust_vc::trait_spec]
pub trait A3 { #[trust_vc::ensures(result == 3u64)] fn v(&self) -> u64; }
pub struct S;
#[trust_vc::trait_impl]
impl A1 for S { fn v(&self) -> u64 { 1u64 } }
#[trust_vc::trait_impl]
impl A2 for S { fn v(&self) -> u64 { 2u64 } }
#[trust_vc::trait_impl]
impl A3 for S { fn v(&self) -> u64 { 3u64 } }

#[trust_vc::ensures(result == 0u64)]
pub fn unrelated_probe() -> u64 { 0u64 }
"#;

/// The conformance lane, MIDDLE impl lying. Only that obligation may fail.
const THREE_TRAITS_MIDDLE_LIES: &str = r#"
#[trust_vc::trait_spec]
pub trait A1 { #[trust_vc::ensures(result == 1u64)] fn v(&self) -> u64; }
#[trust_vc::trait_spec]
pub trait A2 { #[trust_vc::ensures(result == 2u64)] fn v(&self) -> u64; }
#[trust_vc::trait_spec]
pub trait A3 { #[trust_vc::ensures(result == 3u64)] fn v(&self) -> u64; }
pub struct S;
#[trust_vc::trait_impl]
impl A1 for S { fn v(&self) -> u64 { 1u64 } }
#[trust_vc::trait_impl]
impl A2 for S { fn v(&self) -> u64 { 99u64 } }
#[trust_vc::trait_impl]
impl A3 for S { fn v(&self) -> u64 { 3u64 } }

#[trust_vc::ensures(result == 0u64)]
pub fn unrelated_probe() -> u64 { 0u64 }
"#;

/// The conformance lane, FIRST impl lying. Source order must not decide which
/// obligation is checked against which body.
const THREE_TRAITS_FIRST_LIES: &str = r#"
#[trust_vc::trait_spec]
pub trait A1 { #[trust_vc::ensures(result == 1u64)] fn v(&self) -> u64; }
#[trust_vc::trait_spec]
pub trait A2 { #[trust_vc::ensures(result == 2u64)] fn v(&self) -> u64; }
#[trust_vc::trait_spec]
pub trait A3 { #[trust_vc::ensures(result == 3u64)] fn v(&self) -> u64; }
pub struct S;
#[trust_vc::trait_impl]
impl A1 for S { fn v(&self) -> u64 { 99u64 } }
#[trust_vc::trait_impl]
impl A2 for S { fn v(&self) -> u64 { 2u64 } }
#[trust_vc::trait_impl]
impl A3 for S { fn v(&self) -> u64 { 3u64 } }

#[trust_vc::ensures(result == 0u64)]
pub fn unrelated_probe() -> u64 { 0u64 }
"#;

/// A trait impl whose symbol is SHADOWED by an inherent method must still be
/// conformance-checked. Losing the symbol must not buy the impl an exemption.
const SHADOWED_TRAIT_IMPL_LIES: &str = r#"
#[trust_vc::trait_spec]
pub trait B1 { #[trust_vc::ensures(result == 9u64)] fn w(&self) -> u64; }
pub struct T;
#[trust_vc::trait_impl]
impl B1 for T { fn w(&self) -> u64 { 77u64 } }
impl T { #[trust_vc::ensures(result == 4u64)] pub fn w(&self) -> u64 { 4u64 } }

#[trust_vc::ensures(result == 4u64)]
pub fn inherent_true(t: &T) -> u64 { t.w() }
"#;

/// An ASSOCIATED-TYPE-returning trait method shadowed by an inherent method.
/// This is the fixture that pins the shared-symbol gate:
/// `assert_impl_trait_ensures_concrete_axioms` publishes the TRAIT's `ensures`
/// directly about the bare `T__p` symbol with NO box guard, and
/// `assoc_concrete_method_candidate` points `t.p()` at that same bare symbol. With
/// the gate removed, the inherent body axiom `T__p(t) == 4` and the trait axiom
/// `T__p(t) == 9` are BOTH in scope and the context reports
/// "Assumptions are contradictory — all assertions would be vacuously true"
/// for the TRUE claim and the FALSE one alike (measured).
const ASSOC_RETURN_SHADOWED: &str = r#"
#[trust_vc::trait_spec]
pub trait Prod { type Out; #[trust_vc::ensures(result == 9u64)] fn p(&self) -> Self::Out; }
pub struct T;
#[trust_vc::trait_impl]
impl Prod for T { type Out = u64; fn p(&self) -> u64 { 9u64 } }
impl T { #[trust_vc::ensures(result == 4u64)] pub fn p(&self) -> u64 { 4u64 } }

#[trust_vc::ensures(result == 4u64)]
pub fn assoc_inherent_true(t: &T) -> u64 { t.p() }

#[trust_vc::ensures(result == 9u64)]
pub fn assoc_inherent_liar(t: &T) -> u64 { t.p() }
"#;

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_inhshadow_{}_{}.rs",
        std::process::id(),
        tmp_id
    ));
    std::fs::write(&path, src).expect("write fixture");
    let result =
        verify_function_from_file(path.to_str().expect("utf8 path"), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
    let _ = std::fs::remove_file(&path);
    result
}

/// Conformance obligations are NOT addressable through `verify_function_from_file`
/// (they are not source functions); they have their own entry point.
fn conformance(tmp_id: &str, obligation: &str, src: &str) -> VerifyResult {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_inhshadow_{}_{}.rs",
        std::process::id(),
        tmp_id
    ));
    std::fs::write(&path, src).expect("write fixture");
    let result = verify_trait_conformance_obligation(path.to_str().expect("utf8 path"), obligation)
        .unwrap_or_else(|e| VerifyResult::Error {
            message: e.to_string(),
        });
    let _ = std::fs::remove_file(&path);
    result
}

/// Stricter than `!Verified` on purpose: an `Error` would mean the obligation
/// stopped being CHECKED, which hollows the guard out — it would "pass" while
/// testing nothing. Only a real refutation counts.
fn assert_refuted(label: &str, result: VerifyResult) {
    match result {
        VerifyResult::Counterexample { .. } => {}
        other => panic!("{label} Got: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// CARDINAL — the false claim must never verify.
// ---------------------------------------------------------------------------

/// `t.w()` is the INHERENT 4, not the trait's 9.
#[test]
fn inherent_shadowed_receiver_call_does_not_take_the_trait_ensures() {
    let result = verify("shadow_liar", "inherent_liar", INHERENT_SHADOWS_TRAIT);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "CARDINAL REGRESSION: `t.w()` resolves to the INHERENT method and returns 4 \
         (verified under stock rustc), so `result == 9` is FALSE. Verifying means the \
         trait `B1`'s `ensures` reached the inherent call site again — either because \
         the inherent registration was dropped (which PROMOTES the trait binding in \
         `type_env`, it does not fail closed) or because the per-impl linking axiom \
         `B1__w(Box_T(t)) == T__w(t)` still claims the shared symbol. Got: {result:?}"
    );
}

/// The same with TWO competing traits: neither answer may leak.
#[test]
fn inherent_shadowed_receiver_call_rejects_both_competing_traits() {
    for (id, func) in [("two_b1", "liar_b1"), ("two_b2", "liar_b2")] {
        let result = verify(id, func, INHERENT_SHADOWS_TWO_TRAITS);
        assert!(
            !matches!(result, VerifyResult::Verified),
            "CARDINAL REGRESSION: `t.w()` is the inherent 4; `{func}` claims a TRAIT's \
             value. Got: {result:?}"
        );
    }
}

/// The census must recurse into inline `mod` bodies.
#[test]
fn inherent_shadow_resolution_sees_a_nested_mod_trait_impl() {
    let result = verify(
        "nested_liar",
        "inherent_liar",
        INHERENT_SHADOWS_NESTED_TRAIT,
    );
    assert!(
        !matches!(result, VerifyResult::Verified),
        "REGRESSION: a `mod`-nested `impl B1 for T` competes for `T__w` exactly as a \
         sibling one does. Verifying means the census stopped at `file.items`. \
         Got: {result:?}"
    );
}

/// Two traits, no inherent: nothing resolves the receiver call, so BOTH claims —
/// including the one that happens to be true for one of the traits — must fail
/// closed. Verifying either means source order chose an impl.
#[test]
fn two_traits_no_inherent_receiver_call_fails_closed_both_ways() {
    for (id, func) in [("tt_one", "claims_one"), ("tt_two", "claims_two")] {
        let result = verify(id, func, TWO_TRAITS_NO_INHERENT);
        assert!(
            !matches!(result, VerifyResult::Verified),
            "REGRESSION: `s.v()` names two different declarations (`A1::v` = 1 and \
             `A2::v` = 2); `{func}` must fail closed rather than resolve first-wins. \
             Got: {result:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// CARDINAL, other direction — the TRUE claim must verify.
// ---------------------------------------------------------------------------

/// The half a fail-closed-everything gate would silently trade away.
#[test]
fn inherent_shadowed_receiver_call_verifies_the_inherent_value() {
    let result = verify("shadow_true", "inherent_true", INHERENT_SHADOWS_TRAIT);
    assert!(
        matches!(result, VerifyResult::Verified),
        "REGRESSION: `t.w()` IS the inherent 4 (stock rustc), so `result == 4` is TRUE \
         and must verify. Refusing it means the resolution declined a case Rust \
         resolves unambiguously — the capability half of this fix. Got: {result:?}"
    );
}

#[test]
fn inherent_shadowed_by_two_traits_still_verifies_the_inherent_value() {
    let result = verify("two_true", "inherent_true", INHERENT_SHADOWS_TWO_TRAITS);
    assert!(
        matches!(result, VerifyResult::Verified),
        "REGRESSION: two competing traits do not change Rust's answer — `t.w()` is the \
         inherent 4. Got: {result:?}"
    );
}

#[test]
fn nested_mod_shadow_still_verifies_the_inherent_value() {
    let result = verify(
        "nested_true",
        "inherent_true",
        INHERENT_SHADOWS_NESTED_TRAIT,
    );
    assert!(
        matches!(result, VerifyResult::Verified),
        "REGRESSION: `t.w()` is the inherent 4 regardless of where the trait impl is \
         written. Got: {result:?}"
    );
}

// ---------------------------------------------------------------------------
// UFCS — the trait spellings must keep reading the TRAIT, both directions.
// ---------------------------------------------------------------------------

/// `<T as B1>::w(&t)` and `B1::w(&t)` name the TRAIT even when an inherent
/// method of that name exists. If restoring the inherent body axiom had leaked
/// onto the trait UF, these would flip.
#[test]
fn ufcs_spellings_still_read_the_trait_beside_an_inherent_method() {
    for (id, func) in [
        ("ufcs_q_true", "ufcs_qualified_true"),
        ("ufcs_p_true", "ufcs_path_true"),
    ] {
        let result = verify(id, func, INHERENT_SHADOWS_TRAIT);
        assert!(
            matches!(result, VerifyResult::Verified),
            "REGRESSION: `{func}` calls the TRAIT method, which returns 9 (verified \
             under stock rustc). Got: {result:?}"
        );
    }
}

#[test]
fn ufcs_spellings_refute_the_inherent_value_beside_an_inherent_method() {
    for (id, func) in [
        ("ufcs_q_liar", "ufcs_qualified_liar"),
        ("ufcs_p_liar", "ufcs_path_liar"),
    ] {
        let result = verify(id, func, INHERENT_SHADOWS_TRAIT);
        assert!(
            !matches!(result, VerifyResult::Verified),
            "CARDINAL REGRESSION: `{func}` calls the TRAIT method (9) but claims the \
             INHERENT value (4). Verifying means the inherent body axiom leaked onto \
             the trait UF through the linking axiom — the contradiction direction, \
             which proves everything. Got: {result:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// NARROWNESS — the uncontested cases must be untouched, BOTH directions.
// ---------------------------------------------------------------------------

#[test]
fn inherent_only_true_claim_still_verifies() {
    let result = verify("inh_true", "only_true", INHERENT_ONLY);
    assert!(
        matches!(result, VerifyResult::Verified),
        "REGRESSION: an inherent method with nothing competing must be unaffected. \
         Got: {result:?}"
    );
}

#[test]
fn inherent_only_false_claim_still_refuted() {
    let result = verify("inh_liar", "only_liar", INHERENT_ONLY);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "REGRESSION: `t.w()` is 4, so `result == 9` is FALSE. Got: {result:?}"
    );
}

#[test]
fn single_trait_true_claim_still_verifies() {
    let result = verify("tr_true", "only_true", TRAIT_ONLY);
    assert!(
        matches!(result, VerifyResult::Verified),
        "REGRESSION: ordinary single-trait concrete dispatch must be unaffected. \
         Got: {result:?}"
    );
}

#[test]
fn single_trait_false_claim_still_refuted() {
    let result = verify("tr_liar", "only_liar", TRAIT_ONLY);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "REGRESSION: `t.w()` is 9, so `result == 4` is FALSE. Got: {result:?}"
    );
}

/// The shared-symbol gate's own pin. Removing
/// `TraitImplDecl::may_claim_concrete_symbol` makes BOTH of these report
/// "Assumptions are contradictory" — the `4 == 9` the linking / concrete-ensures
/// axioms assert once an inherent method also defines the symbol. A
/// contradiction proves everything, so this is the most dangerous shape in the
/// class even though the engine currently notices it.
#[test]
fn assoc_return_shadowed_by_inherent_resolves_instead_of_contradicting() {
    let result = verify("assoc_true", "assoc_inherent_true", ASSOC_RETURN_SHADOWED);
    assert!(
        matches!(result, VerifyResult::Verified),
        "REGRESSION: `t.p()` is the inherent 4. An `Unknown` naming contradictory \
         assumptions means the trait's `ensures` is being asserted about the same bare \
         `T__p` symbol the inherent body axiom defines — restore the shared-symbol \
         gate. Got: {result:?}"
    );
}

#[test]
fn assoc_return_shadowed_by_inherent_refutes_the_trait_value() {
    let result = verify("assoc_liar", "assoc_inherent_liar", ASSOC_RETURN_SHADOWED);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "CARDINAL REGRESSION: `t.p()` is the inherent 4, so `result == 9` is FALSE. \
         Got: {result:?}"
    );
}

// ---------------------------------------------------------------------------
// THE CONFORMANCE LANE — same root, over-rejection direction.
// ---------------------------------------------------------------------------

/// Every obligation is honest, so every obligation must verify. At `20e12591`
/// only the FIRST-declared trait's did; the others counterexampled against
/// A1's body with a model naming `1`.
#[test]
fn three_traits_one_method_all_conformance_obligations_verify() {
    for (id, trait_name) in [("c_a1", "A1"), ("c_a2", "A2"), ("c_a3", "A3")] {
        let obligation = format!("trait impl conformance {trait_name}::v for S");
        let result = conformance(id, &obligation, THREE_TRAITS_HONEST);
        assert!(
            matches!(result, VerifyResult::Verified),
            "REGRESSION: `{obligation}` is honest ({trait_name}'s body returns exactly \
             what its `ensures` claims). A counterexample means the body was looked up \
             under the trait-ERASED `S__v` key and answered with another impl's body — \
             first-registration-wins. Got: {result:?}"
        );
    }
}

/// The over-rejection fix must not have made conformance vacuous: exactly the
/// LYING impl must be refuted, and only it.
#[test]
fn three_traits_one_method_refutes_exactly_the_lying_impl() {
    for (source_case, liar, src) in [
        ("middle", "A2", THREE_TRAITS_MIDDLE_LIES),
        ("first", "A1", THREE_TRAITS_FIRST_LIES),
    ] {
        for trait_name in ["A1", "A2", "A3"] {
            let obligation = format!("trait impl conformance {trait_name}::v for S");
            let id = format!("{source_case}_{trait_name}");
            let result = conformance(&id, &obligation, src);
            if trait_name == liar {
                assert_refuted(
                    &format!(
                        "CARDINAL REGRESSION: `{obligation}`'s body returns 99, which \
                         violates its own `ensures`. A `Verified` means the conformance \
                         lane stopped checking; an `Error` means it never ran."
                    ),
                    result,
                );
            } else {
                assert!(
                    matches!(result, VerifyResult::Verified),
                    "REGRESSION: `{obligation}` is honest; only `{liar}` lies in this \
                     fixture. A counterexample means the lying body was misattributed \
                     to an innocent trait — source position deciding the verdict. \
                     Got: {result:?}"
                );
            }
        }
    }
}

/// Losing the shared concrete symbol to an inherent method must NOT exempt a
/// trait impl from conformance. Its body still has to establish the trait's
/// `ensures`, or the trait contract published to UFCS callers is unjustified.
#[test]
fn a_shadowed_trait_impl_is_still_conformance_checked() {
    let result = conformance(
        "shadowed_conf",
        "trait impl conformance B1::w for T",
        SHADOWED_TRAIT_IMPL_LIES,
    );
    assert_refuted(
        "CARDINAL REGRESSION: `impl B1 for T` returns 77 while `B1::w`'s `ensures` says \
         9. The impl loses the shared `T__w` symbol to the inherent method, but the \
         trait UF `B1__w` still carries its contract to `B1::w(&t)` callers — so the \
         body must still be checked. A `Verified` means the shadow gate bought the impl \
         a conformance exemption.",
        result,
    );
}

/// And the same file's inherent call must still verify — the shadow gate must
/// not sink the function it exists to make correct.
#[test]
fn a_shadowed_trait_impl_does_not_sink_the_inherent_call() {
    let result = verify("shadowed_inh", "inherent_true", SHADOWED_TRAIT_IMPL_LIES);
    assert!(
        matches!(result, VerifyResult::Verified),
        "REGRESSION: the inherent `t.w()` is 4 regardless of whether the trait impl \
         conforms. Got: {result:?}"
    );
}
