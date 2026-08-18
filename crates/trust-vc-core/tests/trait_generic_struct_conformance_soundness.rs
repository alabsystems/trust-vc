// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Adversarial regression guards for the round-8 TRAIT cluster (findings 18/19):
//! GENERIC-struct trait-impl conformance.
//!
//! A generic-struct trait impl `impl<P> Tr for W<P>` lowers its `self` type to an
//! `Opaque` sort with no ay datatype, so the concrete-surface per-impl
//! conformance path (`build_impl_conformance_context`) could not run and the impl
//! was SKIPPED wholesale (the `contains_opaque()` guard at the top of
//! `verify_trait_conformance_inner`). Meanwhile `register_trait` publishes the
//! quantified trait postcondition axiom `forall self. Tr__m(self) <ensures>`
//! UNCONDITIONALLY, and `verify_implless_trait_defaults` skips any trait that has
//! an impl in the file. Net result: neither the overriding method body
//! (finding 18) nor an inherited default body (finding 19) was ever checked
//! against the trait `ensures`, so a generic-bounded caller `fn g<T: Tr>(t: T) {
//! t.m() }` false-Verified an unestablished/contradictory `ensures`.
//!
//! `verify_generic_struct_impl_conformance` (trait_conformance.rs) closes the
//! hole: for a generic-struct impl it checks each method's EFFECTIVE body (the
//! captured override body, or the inherited default body) against the trait
//! `ensures` on an abstract (`Poly`) self — `result == (<body>)` asserted against
//! the `ensures`. A non-establishing body Counterexamples (fail closed); a
//! conforming body still Verifies (no over-rejection).

use std::path::PathBuf;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn write_fixture(label: &str, source: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "trust_vc_trait_generic_struct_{label}_{}.rs",
        std::process::id()
    ));
    std::fs::write(&path, source).expect("write fixture");
    path
}

fn verify(label: &str, source: &str, case: &str) -> VerifyResult {
    let path = write_fixture(label, source);
    let path_str = path.to_str().expect("fixture path utf-8");
    let result =
        verify_function_from_file(path_str, case).unwrap_or_else(|err| VerifyResult::Error {
            message: err.to_string(),
        });
    let _ = std::fs::remove_file(&path);
    result
}

/// The file's CONFORMANCE verdict — the channel through which `cargo trust-vc
/// check` reports an impl.
///
/// ATTRIBUTION (per the internal conformance-attribution design note): a
/// conformance failure is an obligation of the IMPL, not of whatever function
/// happens to share the file. It used to be folded into every function's verdict,
/// so one violating impl sank every unrelated function — which made upstream
/// trait files structurally unportable (upstream `returns_postcondition.rs::
/// trait_returns_on_trait_method_decl` pins a GENERIC caller `test_call<T: Tr>`
/// VERIFYING while impls Y/Z/W of that same trait FAIL). Every impl is still
/// CHECKED, always; only the BLAME moved. So a guard asking "was the violating
/// body CAUGHT?" must ask the impl's own obligation — which is exactly what this
/// does: ENUMERATE every conformance obligation of the file, then verify each one
/// BY NAME, returning the first non-`Verified` result. The file still FAILS.
fn conformance_verdict(label: &str, source: &str, _case: &str) -> VerifyResult {
    let path = write_fixture(label, source);
    let path_str = path.to_str().expect("fixture path utf-8");
    let result = conformance_verdict_for_path(path_str);
    let _ = std::fs::remove_file(&path);
    result
}

/// Enumerate + verify-by-name, exactly as `cargo trust-vc check` drives it.
fn conformance_verdict_for_path(path: &str) -> VerifyResult {
    let names = match trust_vc_core::list_trait_conformance_obligations(path) {
        Ok(names) => names,
        Err(err) => {
            return VerifyResult::Error {
                message: err.to_string(),
            }
        }
    };
    for name in names {
        match trust_vc_core::verify_trait_conformance_obligation(path, &name) {
            Ok(result) if result.is_verified() => {}
            Ok(result) => return result,
            Err(err) => {
                return VerifyResult::Error {
                    message: err.to_string(),
                }
            }
        }
    }
    VerifyResult::Verified
}

// ===========================================================================
// SOUNDNESS — genuinely false goals must NOT Verify.
// ===========================================================================

// Finding 18: an OVERRIDING generic-struct impl method body that violates the
// trait `ensures`. `W<u8>{inner:0}` is a legal `T: Positive`, so
// `leak_caller(W<u8>)` returns `0` and `0 > 0` is false.
const F18_OVERRIDE_VIOLATE: &str = r#"
#[trust_vc::trait_spec]
trait Positive {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result > 0u32)]
    fn p(&self) -> u32;
}
struct W<P> { inner: P }
#[trust_vc::trait_impl]
impl<P> Positive for W<P> {
    fn p(&self) -> u32 { 0u32 }
}
#[trust_vc::ensures(result > 0u32)]
fn leak_caller<T: Positive>(t: T) -> u32 { t.p() }
"#;

#[test]
fn generic_struct_overriding_body_violating_ensures_does_not_verify() {
    let result = conformance_verdict("f18_override", F18_OVERRIDE_VIOLATE, "leak_caller");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "an overriding `impl<P> Positive for W<P>` body `0u32` cannot establish \
         ensures(result > 0); a generic-bounded caller relying on it is a genuinely \
         false goal that must be refuted; got: {result:?}"
    );
}

// Finding 18 variant: the self-using override body `{ let z = 0u32; z }` (the
// reported `let z = 0u32 then z` form) must also be refuted.
const F18_OVERRIDE_LET: &str = r#"
#[trust_vc::trait_spec]
trait Positive {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result > 0u32)]
    fn p(&self) -> u32;
}
struct W<P> { inner: P }
#[trust_vc::trait_impl]
impl<P> Positive for W<P> {
    fn p(&self) -> u32 { let z = 0u32; z }
}
#[trust_vc::ensures(result > 0u32)]
fn letz_caller<T: Positive>(t: T) -> u32 { t.p() }
"#;

#[test]
fn generic_struct_overriding_let_body_violating_ensures_does_not_verify() {
    let result = conformance_verdict("f18_let", F18_OVERRIDE_LET, "letz_caller");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "an overriding body `{{ let z = 0u32; z }}` returns 0 and cannot establish \
         ensures(result > 0); must be refuted; got: {result:?}"
    );
}

// Finding 19: an ALL-DEFAULTS generic-struct impl inheriting a trait DEFAULT body
// that violates its own `ensures`. `impl<P> Positive for W<P> {}` inherits the
// default `p()==0`, so at `T=W<u8>`, `v4_caller(w)==0` and `0 > 0` is false.
const F19_DEFAULT_VIOLATE: &str = r#"
#[trust_vc::trait_spec]
trait Positive {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result > 0u32)]
    fn p(&self) -> u32 { 0u32 }
}
struct W<P> { inner: P }
#[trust_vc::trait_impl]
impl<P> Positive for W<P> {}
#[trust_vc::ensures(result > 0u32)]
fn v4_caller<T: Positive>(t: T) -> u32 { t.p() }
"#;

#[test]
fn generic_struct_all_defaults_inheriting_violating_default_does_not_verify() {
    let result = conformance_verdict("f19_default", F19_DEFAULT_VIOLATE, "v4_caller");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "an all-defaults `impl<P> Positive for W<P> {{}}` inherits default `p()==0`, \
         which cannot establish ensures(result > 0); must be refuted; got: {result:?}"
    );
}

// SOUNDNESS — the false fact must not be laundered into arithmetic. Default body
// `3u32`, `ensures(result == 7)`; a generic caller deriving `r * 2 == 14`.
const F19_LAUNDER: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn p(&self) -> u32 { 3u32 }
}
struct W<P> { inner: P }
#[trust_vc::trait_impl]
impl<P> Tr for W<P> {}
#[trust_vc::ensures(true)]
fn launder_caller<T: Tr>(t: T) {
    let r = t.p();
    trust_vc::assert!(r * 2u32 == 14u32);
}
"#;

#[test]
fn generic_struct_default_does_not_launder_derived_fact() {
    let result = conformance_verdict("f19_launder", F19_LAUNDER, "launder_caller");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "the unjustified `result == 7` axiom (default body is 3) must not survive to \
         prove `r * 2 == 14`; got: {result:?}"
    );
}

// SOUNDNESS — a PARAM-bearing override exercises the positional param-name
// restore. Body returns `x`; `ensures(result > x)` is false (x > x).
const PARAM_OVERRIDE_VIOLATE: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result > x)]
    fn p(&self, x: u32) -> u32;
}
struct W<P> { inner: P }
#[trust_vc::trait_impl]
impl<P> Tr for W<P> {
    fn p(&self, x: u32) -> u32 { x }
}
#[trust_vc::requires(y < 4000000000u32)]
#[trust_vc::ensures(result > y)]
fn param_bad_caller<T: Tr>(t: T, y: u32) -> u32 { t.p(y) }
"#;

/// WAS KNOWN RED — now GREEN via an ENCODING fix, and the analysis that made it
/// red is retained because it is the justification for the fix.
///
/// It used to report `NotProved { category: Incompleteness }`: the conformance
/// query carried `register_trait`'s postcondition axiom
/// `forall s: Poly, x: BV32. bvult x (Tr__p s x)` alongside the body definition.
/// Over `u32` that axiom is UNSATISFIABLE — at `x = 0xFFFFFFFF` nothing is
/// `bvult`-above it (confirmed standalone: `forall v: BV4. bvult v (f v)`
/// answers `unsat`), so no interpretation of `Tr__p` exists at all and ay
/// correctly deferred rather than fabricate one. Making ay complete on that
/// shape would have made things strictly WORSE: the query would decide UNSAT and
/// trust-vc reads UNSAT as "conformance proved", so the violating impl would have
/// VERIFIED from an inconsistent premise. Only ay's BV-quantifier incompleteness
/// stood between this fixture and a false verify.
///
/// The defect was in the ENCODING: the conformance check asserted the very trait
/// postcondition it was trying to discharge. `build_implless_default_conformance_
/// context` now strips the method-under-check's own `ensures` from the trait it
/// registers (`trait_decl_without_own_postcondition`), leaving exactly
/// `body_definition ∧ ¬ensures`, which is SAT with a real witness. Sibling method
/// axioms are kept (each is discharged by its own conformance obligation) and
/// every method UF is still declared.
///
/// The assertion below pins the WITNESS, not just the verdict: the model must
/// bind `__trust_vc_impl_result` and `__trust_vc_impl_param_x_0` to EQUAL values
/// (currently `0xFFFFFFFF` for both), because `result == x` is precisely what
/// makes `ensures(result > x)` false for the body `p(&self, x) { x }`. A
/// "counterexample" whose model did not falsify the obligation would fail here.
#[test]
fn generic_struct_param_override_violating_ensures_does_not_verify() {
    let result = conformance_verdict("param_bad", PARAM_OVERRIDE_VIOLATE, "param_bad_caller");
    let VerifyResult::Counterexample { ref model, .. } = result else {
        panic!(
            "the param-bearing override `p(&self, x) {{ x }}` cannot establish \
             ensures(result > x); the positional param restore must keep the obligation \
             genuinely false; got: {result:?}"
        );
    };
    let model = model
        .as_ref()
        .unwrap_or_else(|| panic!("refutation must carry a model; got: {result:?}"));

    let witness_result = bv_witness(model, "__trust_vc_impl_result")
        .unwrap_or_else(|| panic!("model must bind the impl result; model: {model}"));
    let witness_x = bv_witness(model, "__trust_vc_impl_param_x_0")
        .unwrap_or_else(|| panic!("model must bind the impl param `x`; model: {model}"));

    // (1) The witness must be CONSISTENT WITH THE BODY. `p(&self, x) { x }`
    //     returns its argument, so any model of the body has result == x.
    assert_eq!(
        witness_result, witness_x,
        "the witness must satisfy the impl BODY: `{{ x }}` forces result == x. \
         Got result={witness_result}, x={witness_x}; model: {model}"
    );
    // (2) The witness must ACTUALLY FALSIFY the ensures. Evaluate the clause
    //     `result > x` at the witness values and demand it comes out FALSE —
    //     this is the check that a "counterexample" which refutes nothing
    //     cannot pass. At the values the solver currently returns
    //     (result = x = 4294967295 = u32::MAX) the clause reads
    //     `4294967295 > 4294967295`, which is false.
    assert!(
        !(witness_result > witness_x),
        "the counterexample must FALSIFY ensures(result > x), but evaluating the \
         clause at the witness gives {witness_result} > {witness_x} = TRUE, i.e. the \
         model satisfies the postcondition and refutes nothing; model: {model}"
    );
}

/// Reads a bitvector witness value out of the rendered counterexample model,
/// which prints as `"<name>": (<value>, <width>)`.
fn bv_witness(model: &str, name: &str) -> Option<u128> {
    let needle = format!("\"{name}\": (");
    let rest = &model[model.find(&needle)? + needle.len()..];
    let digits = rest.split(',').next()?.trim();
    digits.parse().ok()
}

// SOUNDNESS — multiple methods: a conforming `good` must not mask a violating
// `bad` consumed by the caller.
const TWO_METHODS_VIOLATE: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result > 0u32)]
    fn good(&self) -> u32;
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result > 0u32)]
    fn bad(&self) -> u32;
}
struct W<P> { inner: P }
#[trust_vc::trait_impl]
impl<P> Tr for W<P> {
    fn good(&self) -> u32 { 5u32 }
    fn bad(&self) -> u32 { 0u32 }
}
#[trust_vc::ensures(result > 0u32)]
fn two_caller<T: Tr>(t: T) -> u32 { t.bad() }
"#;

#[test]
fn generic_struct_violating_method_among_conforming_does_not_verify() {
    let result = conformance_verdict("two_methods", TWO_METHODS_VIOLATE, "two_caller");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "the violating `bad()==0` (ensures > 0) must be caught even though sibling \
         `good()==5` conforms; got: {result:?}"
    );
}

// SOUNDNESS — a concrete impl of the SAME trait conforming must not mask a
// generic impl that violates.
const COEXIST_GENERIC_VIOLATE: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result > 0u32)]
    fn p(&self) -> u32;
}
struct Q;
#[trust_vc::trait_impl]
impl Tr for Q { fn p(&self) -> u32 { 9u32 } }
struct W<P> { inner: P }
#[trust_vc::trait_impl]
impl<P> Tr for W<P> { fn p(&self) -> u32 { 0u32 } }
#[trust_vc::ensures(result > 0u32)]
fn coexist_bad_caller<T: Tr>(t: T) -> u32 { t.p() }
"#;

#[test]
fn generic_struct_violation_not_masked_by_conforming_concrete_impl() {
    let result = conformance_verdict("coexist_bad", COEXIST_GENERIC_VIOLATE, "coexist_bad_caller");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "a conforming concrete `impl Tr for Q` must not mask the violating generic \
         `impl<P> Tr for W<P>` body `0u32`; got: {result:?}"
    );
}

// ===========================================================================
// NO OVER-REJECTION — every VALID analog must STILL Verify.
// ===========================================================================

// A conforming overriding generic-struct impl body (the candidate's `7u32`).
const F18_OVERRIDE_CONFORM: &str = r#"
#[trust_vc::trait_spec]
trait Positive {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result > 0u32)]
    fn p(&self) -> u32;
}
struct W<P> { inner: P }
#[trust_vc::trait_impl]
impl<P> Positive for W<P> {
    fn p(&self) -> u32 { 7u32 }
}
#[trust_vc::ensures(result > 0u32)]
fn conform_caller<T: Positive>(t: T) -> u32 { t.p() }
"#;

#[test]
fn conforming_generic_struct_override_still_verifies() {
    let result = verify("f18_conform", F18_OVERRIDE_CONFORM, "conform_caller");
    assert!(
        matches!(result, VerifyResult::Verified),
        "a conforming overriding body `7u32` establishing ensures(result > 0) must \
         still Verify through a generic caller — no over-rejection; got: {result:?}"
    );
}

// A conforming all-defaults generic-struct impl (the candidate's `1u32`).
const F19_DEFAULT_CONFORM: &str = r#"
#[trust_vc::trait_spec]
trait Positive {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result > 0u32)]
    fn p(&self) -> u32 { 1u32 }
}
struct W<P> { inner: P }
#[trust_vc::trait_impl]
impl<P> Positive for W<P> {}
#[trust_vc::ensures(result > 0u32)]
fn conform4_caller<T: Positive>(t: T) -> u32 { t.p() }
"#;

#[test]
fn conforming_generic_struct_all_defaults_still_verifies() {
    let result = verify("f19_conform", F19_DEFAULT_CONFORM, "conform4_caller");
    assert!(
        matches!(result, VerifyResult::Verified),
        "a conforming inherited default body `1u32` establishing ensures(result > 0) \
         must still Verify — no over-rejection; got: {result:?}"
    );
}

// A conforming PARAM-bearing override (value-sensitivity dual of the soundness
// case): body returns `x`, `ensures(result == x)` is true.
const PARAM_OVERRIDE_CONFORM: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == x)]
    fn p(&self, x: u32) -> u32;
}
struct W<P> { inner: P }
#[trust_vc::trait_impl]
impl<P> Tr for W<P> {
    fn p(&self, x: u32) -> u32 { x }
}
#[trust_vc::ensures(result == y)]
fn param_good_caller<T: Tr>(t: T, y: u32) -> u32 { t.p(y) }
"#;

#[test]
fn conforming_generic_struct_param_override_still_verifies() {
    let result = verify("param_good", PARAM_OVERRIDE_CONFORM, "param_good_caller");
    assert!(
        matches!(result, VerifyResult::Verified),
        "the param-bearing override `p(&self, x) {{ x }}` conformingly establishes \
         ensures(result == x) — must still Verify (value-sensitive, no \
         over-rejection); got: {result:?}"
    );
}

// Both a conforming concrete AND a conforming generic impl of the same trait.
const COEXIST_BOTH_CONFORM: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result > 0u32)]
    fn p(&self) -> u32;
}
struct Q;
#[trust_vc::trait_impl]
impl Tr for Q { fn p(&self) -> u32 { 9u32 } }
struct W<P> { inner: P }
#[trust_vc::trait_impl]
impl<P> Tr for W<P> { fn p(&self) -> u32 { 3u32 } }
#[trust_vc::ensures(result > 0u32)]
fn coexist_good_caller<T: Tr>(t: T) -> u32 { t.p() }
"#;

#[test]
fn conforming_coexisting_concrete_and_generic_impls_still_verify() {
    let result = verify("coexist_good", COEXIST_BOTH_CONFORM, "coexist_good_caller");
    assert!(
        matches!(result, VerifyResult::Verified),
        "a conforming concrete impl AND a conforming generic impl of the same trait \
         must both Verify — no over-rejection; got: {result:?}"
    );
}

// A trait method with NO `ensures`: nothing to conformance-check; the generic
// impl and its caller must still Verify.
const NO_ENSURES: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    fn p(&self) -> u32;
}
struct W<P> { inner: P }
#[trust_vc::trait_impl]
impl<P> Tr for W<P> {
    fn p(&self) -> u32 { 0u32 }
}
#[trust_vc::ensures(true)]
fn noens_caller<T: Tr>(t: T) {
    let _ = t.p();
    trust_vc::assert!(true);
}
"#;

#[test]
fn generic_struct_method_without_ensures_still_verifies() {
    let result = verify("noens", NO_ENSURES, "noens_caller");
    assert!(
        matches!(result, VerifyResult::Verified),
        "a trait method with no `ensures` carries no conformance obligation; the \
         generic impl must not be over-rejected; got: {result:?}"
    );
}

// A generic-struct impl whose overriding method declares its OWN `requires` is
// ill-formed and rejected via its dedicated error when verified directly; it is
// conformance-EXEMPT, so it must NOT sink an UNRELATED trivially-true function.
const REQUIRES_EXEMPT_UNRELATED: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result > 0u32)]
    fn p(&self) -> u32;
}
struct W<P> { inner: P }
#[trust_vc::trait_impl]
impl<P> Tr for W<P> {
    #[trust_vc::requires(true)]
    fn p(&self) -> u32 { 0u32 }
}
#[trust_vc::ensures(true)]
fn unrelated_true() {
    trust_vc::assert!(1u32 + 1u32 == 2u32);
}
"#;

#[test]
fn requires_bearing_generic_override_does_not_sink_unrelated_function() {
    let result = verify("req_exempt", REQUIRES_EXEMPT_UNRELATED, "unrelated_true");
    assert!(
        matches!(result, VerifyResult::Verified),
        "an ill-formed (own-`requires`) generic override is conformance-exempt and \
         must not Counterexample while verifying an UNRELATED function; got: {result:?}"
    );
}

// A generic struct carrying a CONCRETE field; a literal conforming body must
// still Verify (the abstract-self check does not touch the field).
const CONCRETE_FIELD_LITERAL: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result > 0u32)]
    fn p(&self) -> u32;
}
struct W<P> { n: u32, inner: P }
#[trust_vc::trait_impl]
impl<P> Tr for W<P> { fn p(&self) -> u32 { 42u32 } }
#[trust_vc::ensures(result > 0u32)]
fn field_lit_caller<T: Tr>(t: T) -> u32 { t.p() }
"#;

#[test]
fn generic_struct_with_concrete_field_literal_body_still_verifies() {
    let result = verify("field_lit", CONCRETE_FIELD_LITERAL, "field_lit_caller");
    assert!(
        matches!(result, VerifyResult::Verified),
        "a generic struct with a concrete field and a conforming literal body must \
         still Verify; got: {result:?}"
    );
}
