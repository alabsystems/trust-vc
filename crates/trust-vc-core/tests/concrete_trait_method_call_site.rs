// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Concrete-receiver trait-method CALL-SITE contract application. A call
//! `s.g()` where `s: S` and `#[trust_vc::trait_impl] impl T for S` now resolves
//! to the trait UF `T__g` (boxed receiver) AND applies `T::g`'s declared ensures
//! at the call site — previously a fail-closed "unsupported method `g()` on type
//! `S`".
//!
//! ROOT + FIX: `impl T for S`'s self type is classified `TypeParam("S")` at
//! macro-expand time (no struct registry there). The two verify-time resolvers —
//! `resolve_trait_impl_concrete_types` (prepared_context.rs, feeds the encoder's
//! box bridge + linking axiom) and `resolvable_concrete_type_name`
//! (type_env.rs, feeds the value metadata) — handled only `Opaque`, so a
//! `TypeParam`-named struct never resolved to its datatype. Both now resolve a
//! `TypeParam(name)` that IS a registered struct (a genuine blanket-impl type
//! param matches no struct → stays fail-closed).
//!
//! CARDINAL: a true post-contract fact VERIFIES; a false one must NOT verify.
//! Conformance (impl body vs the trait contract) stays a SEPARATE obligation —
//! this only trusts the trait's declared contract at the call site, exactly as
//! the generic trait-bound path does.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_ctm_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}

const CONST_ENSURES: &str = r#"
#[trust_vc::trait_spec]
trait T { #[trust_vc::ensures(result == 5u64)] fn g(&self) -> u64; }
struct S;
#[trust_vc::trait_impl]
impl T for S { fn g(&self) -> u64 { 5u64 } }
#[trust_vc::ensures(true)]
fn t_pos(s: S) { trust_vc::assert!(s.g() == 5u64); }
#[trust_vc::ensures(true)]
fn t_neg(s: S) { trust_vc::assert!(s.g() == 6u64); }
"#;

const ARG_ENSURES: &str = r#"
#[trust_vc::trait_spec]
trait Doubler { #[trust_vc::ensures(result == x + x)] fn double(&self, x: u64) -> u64; }
struct D;
#[trust_vc::trait_impl]
impl Doubler for D { fn double(&self, x: u64) -> u64 { x + x } }
#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(true)]
fn d_pos(d: D, x: u64) { trust_vc::assert!(d.double(x) == x + x); }
#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(true)]
fn d_neg(d: D, x: u64) { trust_vc::assert!(d.double(x) == x + x + 1u64); }
"#;

#[test]
fn constant_ensures_applies_at_concrete_call_site() {
    assert!(
        matches!(
            verify("const", "t_pos", CONST_ENSURES),
            VerifyResult::Verified
        ),
        "a concrete trait method's declared ensures must apply at the call site"
    );
}

#[test]
fn constant_ensures_false_fact_not_verified() {
    assert!(
        !matches!(
            verify("constneg", "t_neg", CONST_ENSURES),
            VerifyResult::Verified
        ),
        "CARDINAL: `s.g() == 6` with `ensures result == 5` must NOT verify"
    );
}

#[test]
fn argument_dependent_ensures_applies() {
    assert!(
        matches!(verify("arg", "d_pos", ARG_ENSURES), VerifyResult::Verified),
        "an argument-dependent trait ensures (`result == x + x`) must apply at the call site"
    );
}

#[test]
fn argument_dependent_false_fact_not_verified() {
    assert!(
        !matches!(
            verify("argneg", "d_neg", ARG_ENSURES),
            VerifyResult::Verified
        ),
        "CARDINAL: `d.double(x) == x + x + 1` must NOT verify"
    );
}

// A constant ensures declared on the IMPL (the trait declares none) — propagated
// to the concrete call site by the `Box_S`-guarded impl-postcondition axiom,
// sound because the SEPARATE conformance obligation proves body ⊨ impl-ensures.
const IMPL_CONST_ENSURES: &str = r#"
#[trust_vc::trait_spec]
trait Fetch { fn fetch(&self) -> u64; }
struct S;
#[trust_vc::trait_impl]
impl Fetch for S {
    #[trust_vc::ensures(result == 5u64)]
    fn fetch(&self) -> u64 { 5u64 }
}
#[trust_vc::ensures(true)]
fn i_pos(s: S) { trust_vc::assert!(s.fetch() == 5u64); }
#[trust_vc::ensures(true)]
fn i_neg(s: S) { trust_vc::assert!(s.fetch() == 6u64); }
"#;

#[test]
fn impl_strengthened_constant_ensures_applies() {
    assert!(
        matches!(
            verify("iconst", "i_pos", IMPL_CONST_ENSURES),
            VerifyResult::Verified
        ),
        "an impl-declared (trait-undeclared) constant ensures must apply at the concrete call site"
    );
}

#[test]
fn impl_strengthened_constant_false_fact_not_verified() {
    assert!(
        !matches!(
            verify("iconstneg", "i_neg", IMPL_CONST_ENSURES),
            VerifyResult::Verified
        ),
        "CARDINAL: impl-strengthened `s.fetch() == 6` with `ensures result == 5` must NOT verify"
    );
}

// An impl ensures that references a concrete FIELD (`result == self.tag`) — the
// common useful shape (a trait can't declare it; fields aren't trait members).
// The impl-postcondition axiom's `self.tag` lowers to the datatype field
// SELECTOR, which the minimal trait-expr encoder now resolves (the selectors are
// declared in `fn_ctx` before encoding). Sound via the separate conformance
// obligation. Before this, the axiom was dropped and the method UF unconstrained,
// yielding a spurious counterexample on the TRUE ensures — `field_direct` guards
// exactly that regression.
const IMPL_FIELD_ENSURES: &str = r#"
#[trust_vc::trait_spec]
trait Fetch { fn fetch(&self) -> u64; }
struct S { tag: u64 }
#[trust_vc::trait_impl]
impl Fetch for S {
    #[trust_vc::ensures(result == self.tag)]
    fn fetch(&self) -> u64 { self.tag }
}
#[trust_vc::requires(t < 100u64)]
#[trust_vc::ensures(true)]
fn field_pos(t: u64) { let s = S { tag: t }; trust_vc::assert!(s.fetch() == t); }
#[trust_vc::ensures(true)]
fn field_direct(s: S) { trust_vc::assert!(s.fetch() == s.tag); }
#[trust_vc::requires(s.tag < 100u64)]
#[trust_vc::ensures(true)]
fn field_bad(s: S) { trust_vc::assert!(s.fetch() == 999u64); }
"#;

#[test]
fn impl_field_access_ensures_applies() {
    assert!(
        matches!(verify("fld", "field_pos", IMPL_FIELD_ENSURES), VerifyResult::Verified),
        "an impl ensures referencing a field (`result == self.tag`) must apply at the concrete call site"
    );
}

#[test]
fn impl_field_access_direct_ensures_verifies_true_fact() {
    // Regression guard: this asserts the ensures itself (`s.fetch() == s.tag`), a
    // TRUE fact, which previously produced a SPURIOUS counterexample.
    assert!(
        matches!(verify("flddir", "field_direct", IMPL_FIELD_ENSURES), VerifyResult::Verified),
        "the impl field-access ensures must VERIFY its own true fact, not spuriously counterexample"
    );
}

#[test]
fn impl_field_access_false_fact_not_verified() {
    assert!(
        !matches!(
            verify("fldbad", "field_bad", IMPL_FIELD_ENSURES),
            VerifyResult::Verified
        ),
        "CARDINAL: `s.fetch() == 999` (arbitrary s) must NOT verify"
    );
}

// The WITH-SELF UFCS spelling `<S as Trait>::method(&s)` — an explicit receiver,
// so it flows through the same concrete-receiver metadata as `s.method()` (no
// phantom self needed, unlike a no-self associated `<S as Trait>::assoc()`).
const UFCS_WITH_SELF: &str = r#"
#[trust_vc::trait_spec]
trait Fetch { #[trust_vc::ensures(result == 5u64)] fn fetch(&self) -> u64; }
struct S;
#[trust_vc::trait_impl]
impl Fetch for S { fn fetch(&self) -> u64 { 5u64 } }
#[trust_vc::ensures(true)]
fn w_pos(s: S) { let v: u64 = <S as Fetch>::fetch(&s); trust_vc::assert!(v == 5u64); }
#[trust_vc::ensures(true)]
fn w_neg(s: S) { let v: u64 = <S as Fetch>::fetch(&s); trust_vc::assert!(v == 6u64); }
"#;

#[test]
fn with_self_ufcs_value_call_applies_ensures() {
    assert!(
        matches!(
            verify("ufcs", "w_pos", UFCS_WITH_SELF),
            VerifyResult::Verified
        ),
        "a with-self UFCS `<S as Fetch>::fetch(&s)` must apply the trait ensures at the call site"
    );
}

#[test]
fn with_self_ufcs_false_fact_not_verified() {
    assert!(
        !matches!(
            verify("ufcsneg", "w_neg", UFCS_WITH_SELF),
            VerifyResult::Verified
        ),
        "CARDINAL: `<S as Fetch>::fetch(&s) == 6` with `ensures result == 5` must NOT verify"
    );
}

// Two structs implement the SAME trait with DIFFERENT impl-strengthened ensures.
// The `Box_S`/`Box_T` self guard on each impl-postcondition axiom must keep them
// apart: `t.fetch()` (T's impl → 7) must NOT pick up S's `result == 5` contract.
const CROSS_IMPL: &str = r#"
#[trust_vc::trait_spec]
trait Fetch { fn fetch(&self) -> u64; }
struct S;
#[trust_vc::trait_impl]
impl Fetch for S { #[trust_vc::ensures(result == 5u64)] fn fetch(&self) -> u64 { 5u64 } }
struct T;
#[trust_vc::trait_impl]
impl Fetch for T { #[trust_vc::ensures(result == 7u64)] fn fetch(&self) -> u64 { 7u64 } }
#[trust_vc::ensures(true)]
fn s_ok(s: S) { trust_vc::assert!(s.fetch() == 5u64); }
#[trust_vc::ensures(true)]
fn t_ok(t: T) { trust_vc::assert!(t.fetch() == 7u64); }
#[trust_vc::ensures(true)]
fn t_leak(t: T) { trust_vc::assert!(t.fetch() == 5u64); }
"#;

#[test]
fn distinct_impls_each_apply_their_own_ensures() {
    assert!(matches!(
        verify("xls", "s_ok", CROSS_IMPL),
        VerifyResult::Verified
    ));
    assert!(matches!(
        verify("xlt", "t_ok", CROSS_IMPL),
        VerifyResult::Verified
    ));
}

#[test]
fn cross_impl_contract_does_not_leak() {
    assert!(
        !matches!(verify("xlleak", "t_leak", CROSS_IMPL), VerifyResult::Verified),
        "CARDINAL: `t.fetch() == 5` (T's impl returns 7) must NOT verify — S's contract must not leak to T"
    );
}

// The realistic shape: an impl ensures relating the result to BOTH a self FIELD
// and an ARGUMENT (`result == self.base + x`) — exercises the selector fix and
// argument substitution together.
const IMPL_FIELD_AND_ARG: &str = r#"
#[trust_vc::trait_spec]
trait Add { fn add(&self, x: u64) -> u64; }
struct S { base: u64 }
#[trust_vc::trait_impl]
impl Add for S {
    #[trust_vc::ensures(result == self.base + x)]
    fn add(&self, x: u64) -> u64 { self.base + x }
}
#[trust_vc::requires(b < 50u64 && x < 50u64)]
#[trust_vc::ensures(true)]
fn fa_pos(b: u64, x: u64) { let s = S { base: b }; trust_vc::assert!(s.add(x) == b + x); }
#[trust_vc::requires(b < 50u64 && x < 50u64)]
#[trust_vc::ensures(true)]
fn fa_neg(b: u64, x: u64) { let s = S { base: b }; trust_vc::assert!(s.add(x) == b + x + 1u64); }
"#;

#[test]
fn impl_ensures_over_field_and_argument_applies() {
    assert!(
        matches!(verify("faa", "fa_pos", IMPL_FIELD_AND_ARG), VerifyResult::Verified),
        "an impl ensures over BOTH a self field and an argument (`result == self.base + x`) must apply"
    );
}

#[test]
fn impl_ensures_over_field_and_argument_false_fact_not_verified() {
    assert!(
        !matches!(
            verify("faaneg", "fa_neg", IMPL_FIELD_AND_ARG),
            VerifyResult::Verified
        ),
        "CARDINAL: `s.add(x) == b + x + 1` must NOT verify"
    );
}

// A concrete trait method carrying BOTH a `requires` and an `ensures`: the
// requires-discharge (concrete_impl_method_requires) and the ensures application
// (this session's impl-postcondition path) must interact soundly — the requires
// obligation fires at the call site AND the ensures applies once discharged.
const REQUIRES_AND_ENSURES: &str = r#"
#[trust_vc::trait_spec]
trait Bump { #[trust_vc::requires(x < 100u64)] #[trust_vc::ensures(result == x + 1u64)] fn bump(&self, x: u64) -> u64; }
struct S;
#[trust_vc::trait_impl]
impl Bump for S { fn bump(&self, x: u64) -> u64 { x + 1u64 } }
#[trust_vc::ensures(true)]
fn rq_ok(s: S) { trust_vc::assert!(s.bump(50u64) == 51u64); }
#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(true)]
fn rq_discharged(s: S, x: u64) { trust_vc::assert!(s.bump(x) == x + 1u64); }
#[trust_vc::ensures(true)]
fn rq_undischarged(s: S, x: u64) { trust_vc::assert!(s.bump(x) == x + 1u64); }
"#;

#[test]
fn concrete_trait_method_requires_and_ensures_both_apply() {
    assert!(matches!(
        verify("rqok", "rq_ok", REQUIRES_AND_ENSURES),
        VerifyResult::Verified
    ));
    assert!(matches!(
        verify("rqd", "rq_discharged", REQUIRES_AND_ENSURES),
        VerifyResult::Verified
    ));
}

#[test]
fn concrete_trait_method_undischarged_requires_not_verified() {
    assert!(
        !matches!(verify("rqu", "rq_undischarged", REQUIRES_AND_ENSURES), VerifyResult::Verified),
        "CARDINAL: an unestablished `requires(x < 100)` must fire at the call site — must NOT verify"
    );
}

// NO-SELF UFCS: a trait associated function WITHOUT a `self` receiver, called
// via the fully-qualified `<S as Trait>::assoc()` spelling. Two-part fix (this
// session):
//   1. `format_call_expr` (body_extract.rs) renders a no-arg qself call as the
//      CONCRETE `S::make` (from `qself.ty`), not the trait-named `Maker::make` —
//      so the obligation names the same associated symbol the inherent path uses.
//   2. `apply_inherent_impl_methods` (vc_extraction.rs) no longer early-returns
//      on a file whose INHERENT registry is empty when it still carries
//      `#[trait_impl]` impls; its trait-impl loop registers each referenced
//      no-`self` associated method (`S::make`) into TypeEnv with its body axiom.
// No phantom-self boxing is involved — the associated symbol is a plain 0-arg
// helper, exactly like an inherent `S::make()`.
const NOSELF_UFCS: &str = r#"
#[trust_vc::trait_spec]
trait Maker { #[trust_vc::ensures(result == 5u64)] fn make() -> u64; }
struct S;
#[trust_vc::trait_impl]
impl Maker for S { fn make() -> u64 { 5u64 } }
#[trust_vc::ensures(true)]
fn ufcs_pos() { let v: u64 = <S as Maker>::make(); trust_vc::assert!(v == 5u64); }
#[trust_vc::ensures(true)]
fn ufcs_neg() { let v: u64 = <S as Maker>::make(); trust_vc::assert!(v == 6u64); }
"#;

#[test]
fn noself_ufcs_associated_ensures_applies() {
    assert!(
        matches!(
            verify("ufpos", "ufcs_pos", NOSELF_UFCS),
            VerifyResult::Verified
        ),
        "a no-self trait assoc fn's ensures must apply at a `<S as Maker>::make()` call site"
    );
}

#[test]
fn noself_ufcs_false_fact_not_verified() {
    assert!(
        !matches!(
            verify("ufneg", "ufcs_neg", NOSELF_UFCS),
            VerifyResult::Verified
        ),
        "CARDINAL: `<S as Maker>::make() == 6` with `ensures result == 5` must NOT verify"
    );
}

// A concrete trait PREDICATE method — a `-> bool` impl method whose ensures is a
// COMPARISON over a field (`result == (self.x > 0)`). Combines the concrete-
// receiver postcondition path (21fa0c9 impl field-access ensures) with the
// body-axiom parenthesization fix (3b8ec7f: a comparison body/ensures must be
// parenthesized). CARDINAL: the true predicate + its negation VERIFY; the false
// predicate must NOT verify (it fail-closes to NotProved here — a sound
// over-rejection, not a counterexample, which is acceptable).
const TRAIT_PREDICATE: &str = r#"
#[trust_vc::trait_spec]
trait Checker { fn check(&self) -> bool; }
struct S { x: u64 }
#[trust_vc::trait_impl]
impl Checker for S { #[trust_vc::ensures(result == (self.x > 0u64))] fn check(&self) -> bool { self.x > 0u64 } }
#[trust_vc::requires(s.x == 5u64)]
#[trust_vc::ensures(true)]
fn tp_pos(s: S) { trust_vc::assert!(s.check()); }
#[trust_vc::requires(s.x == 0u64)]
#[trust_vc::ensures(true)]
fn tp_false(s: S) { trust_vc::assert!(s.check()); }
#[trust_vc::requires(s.x == 0u64)]
#[trust_vc::ensures(true)]
fn tp_negation(s: S) { trust_vc::assert!(!s.check()); }
"#;

#[test]
fn concrete_trait_predicate_comparison_ensures_applies() {
    assert!(
        matches!(
            verify("tppos", "tp_pos", TRAIT_PREDICATE),
            VerifyResult::Verified
        ),
        "s.check() with `ensures result == (self.x > 0)` and s.x == 5 must verify"
    );
    assert!(
        matches!(
            verify("tpnegation", "tp_negation", TRAIT_PREDICATE),
            VerifyResult::Verified
        ),
        "!s.check() with s.x == 0 must verify"
    );
}

#[test]
fn concrete_trait_predicate_false_fact_not_verified() {
    assert!(
        !matches!(
            verify("tpfalse", "tp_false", TRAIT_PREDICATE),
            VerifyResult::Verified
        ),
        "CARDINAL: s.check() when s.x == 0 is false — asserting it must NOT verify"
    );
}

// A3: a concrete-receiver call to a trait method RETURNING AN ASSOCIATED TYPE
// (`fn produce(&self) -> Self::Out` with `type Out = u64`). The shared per-trait
// UF `Producer__produce(self: Poly)` cannot carry the per-impl-resolved return
// sort (u64 here, bool in another impl), so the concrete-receiver UF path
// deliberately bails and the encoder skips its linking axiom (would "sort
// mismatch in eq"). Instead the impl method — which writes the CONCRETE return —
// is registered through its definitional body axiom (`S::produce(s) == self.seed`),
// the same mechanism the inherent path uses. Gated to no-`self`-args + no-requires
// so it can't drop a precondition. CARDINAL: true fact + negation VERIFY, false
// fact does NOT verify; a LIAR impl (body != declared ensures) is caught.
const ASSOC_RETURN: &str = r#"
#[trust_vc::trait_spec]
trait Producer { type Out; fn produce(&self) -> Self::Out; }
struct S { seed: u64 }
#[trust_vc::trait_impl]
impl Producer for S {
    type Out = u64;
    #[trust_vc::ensures(result == self.seed)]
    fn produce(&self) -> u64 { self.seed }
}
#[trust_vc::requires(s.seed == 7u64)]
#[trust_vc::ensures(true)]
fn ar_pos(s: S) { let v: u64 = s.produce(); trust_vc::assert!(v == 7u64); }
#[trust_vc::requires(s.seed == 7u64)]
#[trust_vc::ensures(true)]
fn ar_neg(s: S) { let v: u64 = s.produce(); trust_vc::assert!(v == 8u64); }
#[trust_vc::requires(s.seed == 7u64)]
#[trust_vc::ensures(true)]
fn ar_negation(s: S) { let v: u64 = s.produce(); trust_vc::assert!(v != 8u64); }
"#;

const ASSOC_RETURN_LIAR: &str = r#"
#[trust_vc::trait_spec]
trait Producer { type Out; fn produce(&self) -> Self::Out; }
struct S { seed: u64 }
#[trust_vc::trait_impl]
impl Producer for S {
    type Out = u64;
    #[trust_vc::ensures(result == self.seed)]
    fn produce(&self) -> u64 { self.seed + 1u64 }
}
#[trust_vc::requires(s.seed == 7u64)]
#[trust_vc::ensures(true)]
fn ar_liar(s: S) { let v: u64 = s.produce(); trust_vc::assert!(v == 7u64); }
"#;

#[test]
fn assoc_type_return_method_verifies_via_body_axiom() {
    assert!(
        matches!(
            verify("arpos", "ar_pos", ASSOC_RETURN),
            VerifyResult::Verified
        ),
        "s.produce() with `type Out = u64` and impl `ensures result == self.seed` must verify"
    );
    assert!(
        matches!(
            verify("arnegation", "ar_negation", ASSOC_RETURN),
            VerifyResult::Verified
        ),
        "s.produce() != 8 when seed == 7 must verify"
    );
}

#[test]
fn assoc_type_return_false_fact_not_verified() {
    assert!(
        !matches!(
            verify("arneg", "ar_neg", ASSOC_RETURN),
            VerifyResult::Verified
        ),
        "CARDINAL: s.produce() == 8 when seed == 7 is false — must NOT verify"
    );
}

#[test]
fn assoc_type_return_liar_impl_not_verified() {
    assert!(
        !matches!(
            verify("arliar", "ar_liar", ASSOC_RETURN_LIAR),
            VerifyResult::Verified
        ),
        "CARDINAL: a liar impl (body seed+1) must NOT let `produce() == seed` verify"
    );
}

// A3 assoc-type-return method WITH ARGUMENTS: `s.combine(x)` where `combine(&self,
// x: u64) -> Self::Out` (`type Out = u64`). A with-`self` receiver method is an
// ordinary method call (no UFCS render ambiguity), so it may take parameters; its
// body axiom `S::combine(self, x) == self.seed + x` is the actual computation
// (the parenthesization fix makes an operator body lower correctly). A `requires`
// remains excluded, so no precondition is dropped.
const ASSOC_RETURN_ARGS: &str = r#"
#[trust_vc::trait_spec]
trait Combiner { type Out; fn combine(&self, x: u64) -> Self::Out; }
struct S { seed: u64 }
#[trust_vc::trait_impl]
impl Combiner for S {
    type Out = u64;
    #[trust_vc::ensures(result == self.seed + x)]
    fn combine(&self, x: u64) -> u64 { self.seed + x }
}
#[trust_vc::requires(s.seed == 7u64)]
#[trust_vc::ensures(true)]
fn ara_pos(s: S) { let v: u64 = s.combine(3u64); trust_vc::assert!(v == 10u64); }
#[trust_vc::requires(s.seed == 7u64)]
#[trust_vc::ensures(true)]
fn ara_neg(s: S) { let v: u64 = s.combine(3u64); trust_vc::assert!(v == 11u64); }
"#;

// A requires-bearing assoc-type-return method must stay FAIL-CLOSED (excluded from
// the body-axiom path): its precondition for a no-`self`/associated trait call is
// not enforced elsewhere, so admitting an unconditional body axiom while dropping
// the requires would let a precondition-violating call verify.
const ASSOC_RETURN_REQUIRES: &str = r#"
#[trust_vc::trait_spec]
trait Gated { type Out; #[trust_vc::requires(x < 5u64)] fn get(&self, x: u64) -> Self::Out; }
struct T { base: u64 }
#[trust_vc::trait_impl]
impl Gated for T {
    type Out = u64;
    #[trust_vc::ensures(result == self.base + x)]
    fn get(&self, x: u64) -> u64 { self.base + x }
}
#[trust_vc::requires(t.base == 0u64)]
#[trust_vc::ensures(true)]
fn gated_requires_violation(t: T) { let v: u64 = t.get(10u64); trust_vc::assert!(v == 10u64); }
"#;

#[test]
fn assoc_type_return_with_args_verifies() {
    assert!(
        matches!(
            verify("arapos", "ara_pos", ASSOC_RETURN_ARGS),
            VerifyResult::Verified
        ),
        "s.combine(3) == 10 when seed == 7 (7 + 3) must verify"
    );
}

#[test]
fn assoc_type_return_with_args_false_fact_not_verified() {
    assert!(
        !matches!(
            verify("araneg", "ara_neg", ASSOC_RETURN_ARGS),
            VerifyResult::Verified
        ),
        "CARDINAL: s.combine(3) == 11 when seed == 7 is false — must NOT verify"
    );
}

#[test]
fn assoc_type_return_requires_bearing_stays_fail_closed() {
    assert!(
        !matches!(
            verify(
                "gatedreq",
                "gated_requires_violation",
                ASSOC_RETURN_REQUIRES
            ),
            VerifyResult::Verified
        ),
        "CARDINAL: a requires-bearing assoc-return method must not drop its precondition — \
         a violating call (x=10, requires x<5) must NOT verify"
    );
}

// A3 assoc-type-return via NO-`self` UFCS: `<S as Maker>::make()` where
// `make() -> Self::Out` (`type Out = u64`). Emergent from combining the no-`self`
// UFCS render (`<S as Maker>::make()` → `S::make`) with the assoc-return
// body-axiom machinery + encoder linking-axiom skip — no dedicated code path.
// Pinned because it had no coverage. CARDINAL: true fact VERIFIES, false fact and
// a LIAR impl do NOT.
const ASSOC_RETURN_UFCS: &str = r#"
#[trust_vc::trait_spec]
trait Maker { type Out; fn make() -> Self::Out; }
struct S;
#[trust_vc::trait_impl]
impl Maker for S {
    type Out = u64;
    #[trust_vc::ensures(result == 5u64)]
    fn make() -> u64 { 5u64 }
}
#[trust_vc::ensures(true)]
fn aru_pos() { let v: u64 = <S as Maker>::make(); trust_vc::assert!(v == 5u64); }
#[trust_vc::ensures(true)]
fn aru_neg() { let v: u64 = <S as Maker>::make(); trust_vc::assert!(v == 6u64); }
"#;

const ASSOC_RETURN_UFCS_LIAR: &str = r#"
#[trust_vc::trait_spec]
trait Maker { type Out; fn make() -> Self::Out; }
struct S;
#[trust_vc::trait_impl]
impl Maker for S {
    type Out = u64;
    #[trust_vc::ensures(result == 5u64)]
    fn make() -> u64 { 6u64 }
}
#[trust_vc::ensures(true)]
fn aru_liar() { let v: u64 = <S as Maker>::make(); trust_vc::assert!(v == 5u64); }
"#;

#[test]
fn assoc_type_return_via_noself_ufcs_verifies() {
    assert!(
        matches!(
            verify("arupos", "aru_pos", ASSOC_RETURN_UFCS),
            VerifyResult::Verified
        ),
        "`<S as Maker>::make() == 5` with `type Out = u64` and `ensures result == 5` must verify"
    );
}

#[test]
fn assoc_type_return_via_noself_ufcs_false_and_liar_not_verified() {
    assert!(
        !matches!(
            verify("aruneg", "aru_neg", ASSOC_RETURN_UFCS),
            VerifyResult::Verified
        ),
        "CARDINAL: `<S as Maker>::make() == 6` is false — must NOT verify"
    );
    assert!(
        !matches!(
            verify("aruliar", "aru_liar", ASSOC_RETURN_UFCS_LIAR),
            VerifyResult::Verified
        ),
        "CARDINAL: a liar impl (body 6) must NOT let `make() == 5` verify"
    );
}

// A concrete trait method returning a NON-PRIMITIVE type — a struct (`-> W`) or
// `Self` — the builder/wrapper/clone shape. The shared per-trait UF cannot carry
// the concrete datatype/`Poly` result sort (the UF path + encoder linking axiom
// both skip it), so the impl method — which WRITES the concrete return — is
// registered through its definitional body axiom, exactly as the inherent path
// already handles a struct-returning method. Both impls coexist for the same
// struct S. CARDINAL: true facts + negation-CE hold; a LIAR impl is caught.
const NONPRIMITIVE_RETURN: &str = r#"
struct S { x: u64 }
struct W { v: u64 }
#[trust_vc::trait_spec]
trait Wrap { fn wrap(&self) -> W; }
#[trust_vc::trait_impl]
impl Wrap for S { #[trust_vc::ensures(result.v == self.x)] fn wrap(&self) -> W { W { v: self.x } } }
#[trust_vc::trait_spec]
trait Dup { fn dup(&self) -> Self; }
#[trust_vc::trait_impl]
impl Dup for S { #[trust_vc::ensures(result.x == self.x)] fn dup(&self) -> S { S { x: self.x } } }
#[trust_vc::requires(s.x == 7u64)]
#[trust_vc::ensures(true)]
fn wrap_pos(s: S) { let w = s.wrap(); trust_vc::assert!(w.v == 7u64); }
#[trust_vc::requires(s.x == 7u64)]
#[trust_vc::ensures(true)]
fn wrap_neg(s: S) { let w = s.wrap(); trust_vc::assert!(w.v == 8u64); }
#[trust_vc::requires(s.x == 7u64)]
#[trust_vc::ensures(true)]
fn dup_pos(s: S) { let d = s.dup(); trust_vc::assert!(d.x == 7u64); }
"#;

const NONPRIMITIVE_LIAR: &str = r#"
struct S { x: u64 }
struct W { v: u64 }
#[trust_vc::trait_spec]
trait Wrap { fn wrap(&self) -> W; }
#[trust_vc::trait_impl]
impl Wrap for S { #[trust_vc::ensures(result.v == self.x)] fn wrap(&self) -> W { W { v: self.x + 1u64 } } }
#[trust_vc::requires(s.x == 7u64)]
#[trust_vc::ensures(true)]
fn wrap_liar(s: S) { let w = s.wrap(); trust_vc::assert!(w.v == 7u64); }
"#;

#[test]
fn nonprimitive_return_struct_and_self_verify() {
    assert!(
        matches!(
            verify("wrappos", "wrap_pos", NONPRIMITIVE_RETURN),
            VerifyResult::Verified
        ),
        "s.wrap().v == 7 (struct return, seed 7) must verify"
    );
    assert!(
        matches!(
            verify("duppos", "dup_pos", NONPRIMITIVE_RETURN),
            VerifyResult::Verified
        ),
        "s.dup().x == 7 (Self return, seed 7) must verify"
    );
}

#[test]
fn nonprimitive_return_false_fact_not_verified() {
    assert!(
        !matches!(
            verify("wrapneg", "wrap_neg", NONPRIMITIVE_RETURN),
            VerifyResult::Verified
        ),
        "CARDINAL: s.wrap().v == 8 when seed == 7 is false — must NOT verify"
    );
}

#[test]
fn nonprimitive_return_liar_impl_not_verified() {
    assert!(
        !matches!(
            verify("wrapliar", "wrap_liar", NONPRIMITIVE_LIAR),
            VerifyResult::Verified
        ),
        "CARDINAL: a liar impl (body v = x + 1) must NOT let `wrap().v == x` verify"
    );
}

// A concrete trait method returning a TUPLE (`-> (u64, u64)`) or a GENERIC
// datatype (`-> Option<u64>`). Unlike struct/Self returns (which the UF path
// leaves unregistered), the UF path DID register these but never applied the
// compound-return postcondition — a spurious counterexample on a TRUE fact.
// Routing them through the body axiom (they are non-primitive) applies the real
// ensures. CARDINAL: true fact VERIFIES, false fact + liar fail-closed.
const COMPOUND_RETURN: &str = r#"
struct S { x: u64 }
#[trust_vc::trait_spec]
trait Pairer { fn pair(&self) -> (u64, u64); }
#[trust_vc::trait_impl]
impl Pairer for S { #[trust_vc::ensures(result.0 == self.x)] fn pair(&self) -> (u64, u64) { (self.x, self.x) } }
#[trust_vc::trait_spec]
trait Mayber { fn maybe(&self) -> Option<u64>; }
#[trust_vc::trait_impl]
impl Mayber for S { #[trust_vc::ensures(result == Some(self.x))] fn maybe(&self) -> Option<u64> { Some(self.x) } }
#[trust_vc::requires(s.x == 7u64)]
#[trust_vc::ensures(true)]
fn pair_pos(s: S) { let p = s.pair(); trust_vc::assert!(p.0 == 7u64); }
#[trust_vc::requires(s.x == 7u64)]
#[trust_vc::ensures(true)]
fn pair_neg(s: S) { let p = s.pair(); trust_vc::assert!(p.0 == 8u64); }
#[trust_vc::requires(s.x == 7u64)]
#[trust_vc::ensures(true)]
fn maybe_pos(s: S) { let m = s.maybe(); trust_vc::assert!(m == Some(7u64)); }
"#;

const COMPOUND_LIAR: &str = r#"
struct S { x: u64 }
#[trust_vc::trait_spec]
trait Pairer { fn pair(&self) -> (u64, u64); }
#[trust_vc::trait_impl]
impl Pairer for S { #[trust_vc::ensures(result.0 == self.x)] fn pair(&self) -> (u64, u64) { (self.x + 1u64, self.x) } }
#[trust_vc::requires(s.x == 7u64)]
#[trust_vc::ensures(true)]
fn pair_liar(s: S) { let p = s.pair(); trust_vc::assert!(p.0 == 7u64); }
"#;

#[test]
fn compound_return_tuple_and_option_verify() {
    assert!(
        matches!(
            verify("pairpos", "pair_pos", COMPOUND_RETURN),
            VerifyResult::Verified
        ),
        "s.pair().0 == 7 (tuple return, seed 7) must verify"
    );
    assert!(
        matches!(
            verify("maybepos", "maybe_pos", COMPOUND_RETURN),
            VerifyResult::Verified
        ),
        "s.maybe() == Some(7) (Option return, seed 7) must verify"
    );
}

#[test]
fn compound_return_false_fact_not_verified() {
    assert!(
        !matches!(
            verify("pairneg", "pair_neg", COMPOUND_RETURN),
            VerifyResult::Verified
        ),
        "CARDINAL: s.pair().0 == 8 when seed == 7 is false — must NOT verify"
    );
}

#[test]
fn compound_return_liar_impl_not_verified() {
    assert!(
        !matches!(
            verify("pairliar", "pair_liar", COMPOUND_LIAR),
            VerifyResult::Verified
        ),
        "CARDINAL: a liar impl (body .0 = x + 1) must NOT let `pair().0 == x` verify"
    );
}

// ROBUSTNESS: a GENERIC datatype return with a STRUCT type argument (`-> Option<W>`)
// is a deeper monomorphization axis (registering `Option<W>` conflicts) and is
// deliberately NOT routed through the body axiom — it stays on the UF path,
// FAIL-CLOSED PER-FUNCTION. Critically, that must not poison an unrelated function
// in the same file (an earlier revision routed it to the body axiom and produced a
// whole-file "conflicting variant metadata" encoder-setup error). Meanwhile a
// primitive-argument generic (`-> Option<u64>`) still verifies.
const GENERIC_ARG_MIX: &str = r#"
struct S { x: u64 }
struct W { v: u64 }
#[trust_vc::trait_spec]
trait Mayber { fn maybe(&self) -> Option<u64>; }
#[trust_vc::trait_impl]
impl Mayber for S { #[trust_vc::ensures(result == Some(self.x))] fn maybe(&self) -> Option<u64> { Some(self.x) } }
#[trust_vc::trait_spec]
trait Nester { fn nest(&self) -> Option<W>; }
#[trust_vc::trait_impl]
impl Nester for S { #[trust_vc::ensures(result == Some(W { v: self.x }))] fn nest(&self) -> Option<W> { Some(W { v: self.x }) } }
#[trust_vc::requires(s.x == 7u64)]
#[trust_vc::ensures(true)]
fn gam_maybe(s: S) { let m = s.maybe(); trust_vc::assert!(m == Some(7u64)); }
#[trust_vc::requires(a == 3u64)]
#[trust_vc::ensures(true)]
fn gam_unrelated(a: u64) { trust_vc::assert!(a == 3u64); }
"#;

#[test]
fn generic_primitive_arg_return_verifies_and_struct_arg_does_not_poison_file() {
    assert!(
        matches!(
            verify("gammaybe", "gam_maybe", GENERIC_ARG_MIX),
            VerifyResult::Verified
        ),
        "Option<u64> return must verify"
    );
    // The Option<W> method in the same file must NOT sink the whole file — an
    // unrelated function still verifies.
    assert!(
        matches!(verify("gamunrel", "gam_unrelated", GENERIC_ARG_MIX), VerifyResult::Verified),
        "an unrelated function must not be poisoned by an Option<W>-returning method in the same file"
    );
}

// A concrete trait method returning an ENUM (`-> E`) — the same non-primitive
// bare-path routing as a struct return, but exercising variant construction /
// equality in the ensures (`result == E::A(self.x)`). Pins that the return-shape
// coverage includes enums. CARDINAL: the true variant VERIFIES, a wrong variant /
// wrong payload / liar impl do NOT.
const ENUM_RETURN: &str = r#"
struct S { x: u64 }
enum E { A(u64), B }
#[trust_vc::trait_spec]
trait Classify { fn classify(&self) -> E; }
#[trust_vc::trait_impl]
impl Classify for S { #[trust_vc::ensures(result == E::A(self.x))] fn classify(&self) -> E { E::A(self.x) } }
#[trust_vc::requires(s.x == 7u64)]
#[trust_vc::ensures(true)]
fn cls_pos(s: S) { let c = s.classify(); trust_vc::assert!(c == E::A(7u64)); }
#[trust_vc::requires(s.x == 7u64)]
#[trust_vc::ensures(true)]
fn cls_wrong_variant(s: S) { let c = s.classify(); trust_vc::assert!(c == E::B); }
#[trust_vc::requires(s.x == 7u64)]
#[trust_vc::ensures(true)]
fn cls_wrong_payload(s: S) { let c = s.classify(); trust_vc::assert!(c == E::A(8u64)); }
"#;

const ENUM_RETURN_LIAR: &str = r#"
struct S { x: u64 }
enum E { A(u64), B }
#[trust_vc::trait_spec]
trait Classify { fn classify(&self) -> E; }
#[trust_vc::trait_impl]
impl Classify for S { #[trust_vc::ensures(result == E::A(self.x))] fn classify(&self) -> E { E::B } }
#[trust_vc::requires(s.x == 7u64)]
#[trust_vc::ensures(true)]
fn cls_liar(s: S) { let c = s.classify(); trust_vc::assert!(c == E::A(7u64)); }
"#;

#[test]
fn enum_return_true_variant_verifies() {
    assert!(
        matches!(
            verify("clspos", "cls_pos", ENUM_RETURN),
            VerifyResult::Verified
        ),
        "s.classify() == E::A(7) when seed == 7 must verify"
    );
}

#[test]
fn enum_return_wrong_variant_or_payload_not_verified() {
    assert!(
        !matches!(
            verify("clswv", "cls_wrong_variant", ENUM_RETURN),
            VerifyResult::Verified
        ),
        "CARDINAL: s.classify() == E::B is false (it is A(7)) — must NOT verify"
    );
    assert!(
        !matches!(
            verify("clswp", "cls_wrong_payload", ENUM_RETURN),
            VerifyResult::Verified
        ),
        "CARDINAL: s.classify() == E::A(8) is false (payload is 7) — must NOT verify"
    );
}

#[test]
fn enum_return_liar_impl_not_verified() {
    assert!(
        !matches!(
            verify("clsliar", "cls_liar", ENUM_RETURN_LIAR),
            VerifyResult::Verified
        ),
        "CARDINAL: a liar impl (body E::B) must NOT let `classify() == E::A(7)` verify"
    );
}

// A concrete trait method taking a STRUCT ARGUMENT (`fn merge(&self, o: Other)`).
// A single-uppercase struct name in a trait method parameter is classified
// `TypeParam("Other")` at macro-expand time (same heuristic that gave the self
// type `TypeParam("S")` before it was resolved) — unresolved, the UF path skips
// the method and the synthesized helper context rejects the param, sinking the
// WHOLE file. Fixed in two parts: (1) `resolve_trait_decl_param_types` resolves a
// struct-name param → its `Datatype` at extraction end (mirrors the self-type
// resolution), so every consumer sees an ay-encodable sort and NO file poison;
// (2) the method is routed through its definitional body axiom (non-primitive
// param) so the ensures (`result == self.x + o.y`, referencing the param field
// `o.y`) applies. CARDINAL: true fact VERIFIES, false + liar do NOT, and — the
// robustness property — an UNRELATED function in the same file is not poisoned.
const STRUCT_ARG: &str = r#"
struct S { x: u64 }
struct Other { y: u64 }
#[trust_vc::trait_spec]
trait Merge { fn merge(&self, o: Other) -> u64; }
#[trust_vc::trait_impl]
impl Merge for S { #[trust_vc::ensures(result == self.x + o.y)] fn merge(&self, o: Other) -> u64 { self.x + o.y } }
#[trust_vc::requires(s.x == 7u64)]
#[trust_vc::requires(o.y == 3u64)]
#[trust_vc::ensures(true)]
fn merge_pos(s: S, o: Other) { let r = s.merge(o); trust_vc::assert!(r == 10u64); }
#[trust_vc::requires(s.x == 7u64)]
#[trust_vc::requires(o.y == 3u64)]
#[trust_vc::ensures(true)]
fn merge_neg(s: S, o: Other) { let r = s.merge(o); trust_vc::assert!(r == 11u64); }
#[trust_vc::requires(a == 3u64)]
#[trust_vc::ensures(true)]
fn merge_unrelated(a: u64) { trust_vc::assert!(a == 3u64); }
"#;

const STRUCT_ARG_LIAR: &str = r#"
struct S { x: u64 }
struct Other { y: u64 }
#[trust_vc::trait_spec]
trait Merge { fn merge(&self, o: Other) -> u64; }
#[trust_vc::trait_impl]
impl Merge for S { #[trust_vc::ensures(result == self.x + o.y)] fn merge(&self, o: Other) -> u64 { self.x + o.y + 1u64 } }
#[trust_vc::requires(s.x == 7u64)]
#[trust_vc::requires(o.y == 3u64)]
#[trust_vc::ensures(true)]
fn merge_liar(s: S, o: Other) { let r = s.merge(o); trust_vc::assert!(r == 10u64); }
"#;

#[test]
fn struct_argument_method_verifies_and_does_not_poison_file() {
    assert!(
        matches!(
            verify("mergepos", "merge_pos", STRUCT_ARG),
            VerifyResult::Verified
        ),
        "s.merge(o) == 10 (x=7, o.y=3) must verify"
    );
    assert!(
        matches!(
            verify("mergeunrel", "merge_unrelated", STRUCT_ARG),
            VerifyResult::Verified
        ),
        "an unrelated function must not be poisoned by a struct-arg trait method in the same file"
    );
}

#[test]
fn struct_argument_false_fact_and_liar_not_verified() {
    assert!(
        !matches!(
            verify("mergeneg", "merge_neg", STRUCT_ARG),
            VerifyResult::Verified
        ),
        "CARDINAL: s.merge(o) == 11 (x=7, o.y=3) is false — must NOT verify"
    );
    assert!(
        !matches!(
            verify("mergeliar", "merge_liar", STRUCT_ARG_LIAR),
            VerifyResult::Verified
        ),
        "CARDINAL: a liar impl (body x+y+1) must NOT let `merge(o) == x+y` verify"
    );
}

// Robustness of the struct-argument fix across combinations: MULTIPLE struct
// params, a struct param combined with a struct RETURN, and an ENUM param — all
// resolved (params) + body-axiom-routed (non-primitive param/return) uniformly.
const STRUCT_ARG_COMBOS: &str = r#"
struct S { x: u64 }
struct A { a: u64 }
struct B { b: u64 }
enum E { P(u64), Q }
#[trust_vc::trait_spec]
trait Sum3 { fn sum3(&self, p: A, q: B) -> u64; }
#[trust_vc::trait_impl]
impl Sum3 for S { #[trust_vc::ensures(result == self.x + p.a + q.b)] fn sum3(&self, p: A, q: B) -> u64 { self.x + p.a + q.b } }
#[trust_vc::trait_spec]
trait Wrap2 { fn wrap2(&self, p: A) -> B; }
#[trust_vc::trait_impl]
impl Wrap2 for S { #[trust_vc::ensures(result.b == self.x + p.a)] fn wrap2(&self, p: A) -> B { B { b: self.x + p.a } } }
#[trust_vc::trait_spec]
trait UseE { fn use_e(&self, e: E) -> bool; }
#[trust_vc::trait_impl]
impl UseE for S { #[trust_vc::ensures(result == (e == E::Q))] fn use_e(&self, e: E) -> bool { e == E::Q } }
#[trust_vc::requires(s.x == 1u64)] #[trust_vc::requires(p.a == 2u64)] #[trust_vc::requires(q.b == 3u64)]
#[trust_vc::ensures(true)]
fn sum3_pos(s: S, p: A, q: B) { trust_vc::assert!(s.sum3(p, q) == 6u64); }
#[trust_vc::requires(s.x == 1u64)] #[trust_vc::requires(p.a == 2u64)] #[trust_vc::requires(q.b == 3u64)]
#[trust_vc::ensures(true)]
fn sum3_neg(s: S, p: A, q: B) { trust_vc::assert!(s.sum3(p, q) == 7u64); }
#[trust_vc::requires(s.x == 1u64)] #[trust_vc::requires(p.a == 2u64)]
#[trust_vc::ensures(true)]
fn wrap2_pos(s: S, p: A) { let w = s.wrap2(p); trust_vc::assert!(w.b == 3u64); }
#[trust_vc::requires(s.x == 1u64)]
#[trust_vc::ensures(true)]
fn usee_pos(s: S) { trust_vc::assert!(s.use_e(E::Q)); }
#[trust_vc::requires(s.x == 1u64)]
#[trust_vc::ensures(true)]
fn usee_neg(s: S) { trust_vc::assert!(s.use_e(E::P(5u64))); }
"#;

#[test]
fn struct_argument_combinations_verify() {
    assert!(
        matches!(
            verify("sum3p", "sum3_pos", STRUCT_ARG_COMBOS),
            VerifyResult::Verified
        ),
        "multiple struct params: s.sum3(p,q) == 1+2+3 must verify"
    );
    assert!(
        matches!(
            verify("wrap2p", "wrap2_pos", STRUCT_ARG_COMBOS),
            VerifyResult::Verified
        ),
        "struct param + struct return: s.wrap2(p).b == 1+2 must verify"
    );
    assert!(
        matches!(
            verify("useep", "usee_pos", STRUCT_ARG_COMBOS),
            VerifyResult::Verified
        ),
        "enum param: s.use_e(E::Q) must verify"
    );
}

#[test]
fn struct_argument_combinations_false_facts_not_verified() {
    assert!(
        !matches!(
            verify("sum3n", "sum3_neg", STRUCT_ARG_COMBOS),
            VerifyResult::Verified
        ),
        "CARDINAL: s.sum3(p,q) == 7 (true sum 6) must NOT verify"
    );
    assert!(
        !matches!(
            verify("useen", "usee_neg", STRUCT_ARG_COMBOS),
            VerifyResult::Verified
        ),
        "CARDINAL: s.use_e(E::P(5)) (not E::Q) must NOT verify"
    );
}

// A concrete trait method taking a SHARED-REFERENCE struct argument
// (`fn rmerge(&self, o: &Other)`) — the PartialEq-style shape. A `&`-struct param
// behaves like a by-value struct param in a spec context (the reference is
// erased), so `type_routes_to_body_axiom` looks THROUGH the reference and routes
// the method to the body axiom (it was NotProved on the bare UF path). CARDINAL:
// true fact VERIFIES, false + liar do NOT.
const REF_ARG: &str = r#"
struct S { x: u64 }
struct Other { y: u64 }
#[trust_vc::trait_spec]
trait RefMerge { fn rmerge(&self, o: &Other) -> u64; }
#[trust_vc::trait_impl]
impl RefMerge for S { #[trust_vc::ensures(result == self.x + o.y)] fn rmerge(&self, o: &Other) -> u64 { self.x + o.y } }
#[trust_vc::requires(s.x == 7u64)]
#[trust_vc::requires(o.y == 3u64)]
#[trust_vc::ensures(true)]
fn rmerge_pos(s: S, o: Other) { let r = s.rmerge(&o); trust_vc::assert!(r == 10u64); }
#[trust_vc::requires(s.x == 7u64)]
#[trust_vc::requires(o.y == 3u64)]
#[trust_vc::ensures(true)]
fn rmerge_neg(s: S, o: Other) { let r = s.rmerge(&o); trust_vc::assert!(r == 11u64); }
"#;

const REF_ARG_LIAR: &str = r#"
struct S { x: u64 }
struct Other { y: u64 }
#[trust_vc::trait_spec]
trait RefMerge { fn rmerge(&self, o: &Other) -> u64; }
#[trust_vc::trait_impl]
impl RefMerge for S { #[trust_vc::ensures(result == self.x + o.y)] fn rmerge(&self, o: &Other) -> u64 { self.x + o.y + 1u64 } }
#[trust_vc::requires(s.x == 7u64)]
#[trust_vc::requires(o.y == 3u64)]
#[trust_vc::ensures(true)]
fn rmerge_liar(s: S, o: Other) { let r = s.rmerge(&o); trust_vc::assert!(r == 10u64); }
"#;

#[test]
fn reference_struct_argument_verifies() {
    assert!(
        matches!(
            verify("rmergepos", "rmerge_pos", REF_ARG),
            VerifyResult::Verified
        ),
        "s.rmerge(&o) == 10 (x=7, o.y=3) must verify"
    );
}

#[test]
fn reference_struct_argument_false_and_liar_not_verified() {
    assert!(
        !matches!(
            verify("rmergeneg", "rmerge_neg", REF_ARG),
            VerifyResult::Verified
        ),
        "CARDINAL: s.rmerge(&o) == 11 is false — must NOT verify"
    );
    assert!(
        !matches!(
            verify("rmergeliar", "rmerge_liar", REF_ARG_LIAR),
            VerifyResult::Verified
        ),
        "CARDINAL: a liar impl (body x+y+1) must NOT let `rmerge(&o) == x+y` verify"
    );
}

// CARDINAL / SOUNDNESS REGRESSION (da02cb7): a PARAMETERIZED trait
// (`impl Param<u64> for S`, trait `Param<A>`) must NEVER be routed through the
// concrete-receiver body axiom — it is owned by the generic-trait path, which
// deliberately fail-closes such a non-instantiable shape. da28e51's struct-arg
// param routing regressed this (a `Seq<u64>`/struct param made it instantiable →
// false-verify, trait_generic_soundness `nested_param_stays_closed`); the fix
// skips a trait impl whose trait carries type arguments. This pins that a
// parameterized-trait method with a NON-PRIMITIVE return AND a NON-PRIMITIVE
// param stays FAIL-CLOSED, and does not poison the file.
const PARAMETERIZED_TRAIT_STAYS_CLOSED: &str = r#"
struct S { x: u64 }
struct Other { y: u64 }
struct W { v: u64 }
#[trust_vc::trait_spec]
trait Param<A> { fn f(&self, o: Other) -> W; }
#[trust_vc::trait_impl]
impl Param<u64> for S { #[trust_vc::ensures(result.v == self.x + o.y)] fn f(&self, o: Other) -> W { W { v: self.x + o.y } } }
#[trust_vc::requires(s.x == 7u64)]
#[trust_vc::requires(o.y == 3u64)]
#[trust_vc::ensures(true)]
fn param_stays_closed(s: S, o: Other) { let w = s.f(o); trust_vc::assert!(w.v == 10u64); }
#[trust_vc::requires(a == 3u64)]
#[trust_vc::ensures(true)]
fn param_unrelated(a: u64) { trust_vc::assert!(a == 3u64); }
"#;

#[test]
fn parameterized_trait_non_primitive_method_stays_fail_closed() {
    assert!(
        !matches!(
            verify("paramclosed", "param_stays_closed", PARAMETERIZED_TRAIT_STAYS_CLOSED),
            VerifyResult::Verified
        ),
        "CARDINAL: a parameterized-trait method (non-primitive return + param) is non-instantiable — \
         it must NOT be body-axiom-routed into a false-verify"
    );
    assert!(
        matches!(
            verify(
                "paramunrel",
                "param_unrelated",
                PARAMETERIZED_TRAIT_STAYS_CLOSED
            ),
            VerifyResult::Verified
        ),
        "an unrelated function must not be poisoned by the fail-closed parameterized-trait impl"
    );
}
