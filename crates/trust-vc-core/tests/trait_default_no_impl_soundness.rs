// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Adversarial regression guards for the round-4 trait surface cluster: a trait
//! DEFAULT method with a postcondition, with NO `#[trait_impl]` in the file,
//! exercised by a GENERIC-BOUNDED caller `fn g<T: DT>(t: T) { ... t.dm() ... }`.
//!
//! `register_trait` publishes the quantified postcondition axiom `forall self.
//! DT__dm(self) <ensures>` for EVERY trait method unconditionally, and a generic
//! caller consumes it directly. The round-3 #60 fix only verified a default body
//! against its `ensures` INSIDE the per-impl conformance loop — with zero impls
//! that loop body never runs, so a default whose body does NOT establish its
//! `ensures` (a contradictory literal, or a call to a contract-less
//! declaration-only sibling) left the postcondition axiom published-but-unchecked
//! => a generic caller relying on it false-Verified.
//!
//! `verify_implless_trait_defaults` (trait_conformance.rs) closes the no-impl
//! residual: it checks each default body against its `ensures` on an abstract
//! receiver, inlining non-overridden sibling defaults and modeling un-inlined
//! siblings through the trait method UF + its postcondition axiom. A
//! non-establishing default Counterexamples (fail closed); a conforming default
//! still Verifies (no over-rejection).

use std::path::PathBuf;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn write_fixture(label: &str, source: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "trust_vc_trait_default_noimpl_{label}_{}.rs",
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
// SOUNDNESS DIRECTION — genuinely false goals must NOT Verify.
// ===========================================================================

// Hole #11: default body `0u32`, `ensures(result > 100)`, no impl. A concrete
// `impl DT for Z {}` inherits the default => Z::dm() == 0, so `0 > 100` is false.
const VIOLATE_GT: &str = r#"
#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result > 100u32)]
    fn dm(&self) -> u32 { 0u32 }
}
#[trust_vc::ensures(true)]
fn gtv<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r > 100u32);
}
"#;

#[test]
fn default_body_violating_gt_does_not_verify() {
    let result = conformance_verdict("violate_gt", VIOLATE_GT, "gtv");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "default body 0u32 cannot establish ensures(result > 100); a generic caller \
         relying on it is a genuinely false goal that must be refuted; got: {result:?}"
    );
}

// Hole #12: default body `3u32`, `ensures(result == 7)`, no impl.
const VIOLATE_EQ: &str = r#"
#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { 3u32 }
}
#[trust_vc::ensures(true)]
fn dv_caller<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r == 7u32);
}
"#;

#[test]
fn default_body_contradicting_eq_does_not_verify() {
    let result = conformance_verdict("violate_eq", VIOLATE_EQ, "dv_caller");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "default body 3u32 contradicts ensures(result == 7); must be refuted; got: {result:?}"
    );
}

// Hole #12 derived: the false fact must not be laundered into arithmetic.
const VIOLATE_EQ_DERIVED: &str = r#"
#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { 3u32 }
}
#[trust_vc::ensures(true)]
fn dv_derived<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r * 2u32 == 14u32);
}
"#;

#[test]
fn default_body_contradicting_eq_does_not_launder_derived_fact() {
    let result = conformance_verdict("violate_eq_derived", VIOLATE_EQ_DERIVED, "dv_derived");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "the unjustified `result == 7` axiom must not survive to prove `r * 2 == 14`; \
         got: {result:?}"
    );
}

// Hole #13: default body `self.helper()` where `helper` is a contract-less
// declaration-only sibling. `helper` is unconstrained, so `result == 7` is
// underivable. A valid `impl DT2 for S { fn helper(&self) -> u32 { 3 } }`
// inherits dm2's default => dm2() == 3 != 7.
const VIOLATE_DECL_ONLY_SIBLING: &str = r#"
#[trust_vc::trait_spec]
trait DT2 {
    fn helper(&self) -> u32;
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm2(&self) -> u32 { self.helper() }
}
#[trust_vc::ensures(true)]
fn du_caller<T: DT2>(t: T) {
    let r = t.dm2();
    trust_vc::assert!(r == 7u32);
}
"#;

#[test]
fn default_body_calling_contractless_decl_only_sibling_does_not_verify() {
    let result = conformance_verdict("violate_decl_only", VIOLATE_DECL_ONLY_SIBLING, "du_caller");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "default body self.helper() (helper contract-less, declaration-only) cannot \
         establish ensures(result == 7); must fail closed; got: {result:?}"
    );
}

// Soundness: a non-conforming sibling DEFAULT chain (no impl). `g` default body
// 3u32, `dm3` body `self.g()` promising `>= 10`. Inlining g's default (3) into
// dm3's body => 3 >= 10 is false.
const VIOLATE_SIBLING_DEFAULT_CHAIN: &str = r#"
#[trust_vc::trait_spec]
trait DT3 {
    fn g(&self) -> u32 { 3u32 }
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result >= 10u32)]
    fn dm3(&self) -> u32 { self.g() }
}
#[trust_vc::ensures(true)]
fn dg_caller<T: DT3>(t: T) {
    let r = t.dm3();
    trust_vc::assert!(r >= 10u32);
}
"#;

#[test]
fn nonconforming_sibling_default_chain_does_not_verify() {
    let result = conformance_verdict(
        "violate_sibling_chain",
        VIOLATE_SIBLING_DEFAULT_CHAIN,
        "dg_caller",
    );
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "default body self.g() with sibling default g()==3 cannot establish \
         ensures(result >= 10); must be refuted; got: {result:?}"
    );
}

// ===========================================================================
// NON-VACUITY — the refutations above are genuine, not vacuous fail-close.
// The published `ensures` axiom pins the result; asserting the body's TRUE value
// must NOT Verify (the generic-caller model is constrained by the axiom), and the
// body assert is genuinely checked.
// ===========================================================================

const VIOLATE_EQ_ASSERT_TRUE_BODY: &str = r#"
#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { 3u32 }
}
#[trust_vc::ensures(true)]
fn dv_true_body<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r == 3u32);
}
"#;

#[test]
fn refutation_is_not_globally_vacuous() {
    // Asserting the body's true value (3) must NOT Verify: the only model of the
    // unjustified `result == 7` axiom pins r to 7, so `r == 3` cannot be proven —
    // and the default-conformance pass independently refuses to bless the axiom.
    let result = verify(
        "violate_eq_true_body",
        VIOLATE_EQ_ASSERT_TRUE_BODY,
        "dv_true_body",
    );
    assert!(
        !matches!(result, VerifyResult::Verified),
        "asserting the body's true value 3 must not Verify against a `result == 7` \
         axiom (proves the engine is constrained, not vacuous); got: {result:?}"
    );
}

// ===========================================================================
// NO OVER-REJECTION — every VALID analog must STILL Verify.
// ===========================================================================

// A conforming default literal (==).
const CONFORM_EQ: &str = r#"
#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { 7u32 }
}
#[trust_vc::ensures(true)]
fn cf_caller<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r == 7u32);
}
"#;

#[test]
fn conforming_default_eq_still_verifies() {
    let result = verify("conform_eq", CONFORM_EQ, "cf_caller");
    assert!(
        matches!(result, VerifyResult::Verified),
        "a conforming default body 7u32 establishing ensures(result == 7) must still \
         Verify through a generic caller; got: {result:?}"
    );
}

// A conforming default literal (>).
const CONFORM_GT: &str = r#"
#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result > 100u32)]
    fn dm(&self) -> u32 { 150u32 }
}
#[trust_vc::ensures(true)]
fn cfg_caller<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r > 100u32);
}
"#;

#[test]
fn conforming_default_gt_still_verifies() {
    let result = verify("conform_gt", CONFORM_GT, "cfg_caller");
    assert!(
        matches!(result, VerifyResult::Verified),
        "a conforming default body 150u32 establishing ensures(result > 100) must still \
         Verify; got: {result:?}"
    );
}

// A conforming sibling DEFAULT chain (no impl): inlining g's default 20 into
// dm3's body establishes `>= 10`.
const CONFORM_SIBLING_DEFAULT_CHAIN: &str = r#"
#[trust_vc::trait_spec]
trait DT3 {
    fn g(&self) -> u32 { 20u32 }
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result >= 10u32)]
    fn dm3(&self) -> u32 { self.g() }
}
#[trust_vc::ensures(true)]
fn dg_good_caller<T: DT3>(t: T) {
    let r = t.dm3();
    trust_vc::assert!(r >= 10u32);
}
"#;

#[test]
fn conforming_sibling_default_chain_still_verifies() {
    let result = verify(
        "conform_sibling_chain",
        CONFORM_SIBLING_DEFAULT_CHAIN,
        "dg_good_caller",
    );
    assert!(
        matches!(result, VerifyResult::Verified),
        "a conforming sibling default chain (g()==20, dm3 body self.g(), ensures >= 10) \
         must still Verify — no over-rejection; got: {result:?}"
    );
}

// A conforming default that relies on a declaration-only sibling's OWN `ensures`
// (no impl). `helper` is declaration-only but carries `ensures(result == 7)`;
// dm4's body `self.helper()` establishes `result == 7` via that spec.
const CONFORM_DECL_ONLY_SIBLING_WITH_ENSURES: &str = r#"
#[trust_vc::trait_spec]
trait DT4 {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn helper(&self) -> u32;
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm4(&self) -> u32 { self.helper() }
}
#[trust_vc::ensures(true)]
fn dh_caller<T: DT4>(t: T) {
    let r = t.dm4();
    trust_vc::assert!(r == 7u32);
}
"#;

#[test]
fn conforming_default_via_decl_only_sibling_ensures_still_verifies() {
    let result = verify(
        "conform_decl_only_ensures",
        CONFORM_DECL_ONLY_SIBLING_WITH_ENSURES,
        "dh_caller",
    );
    assert!(
        matches!(result, VerifyResult::Verified),
        "dm4's default body self.helper() establishes ensures(result == 7) via helper's \
         OWN ensures(result == 7) — must still Verify; got: {result:?}"
    );
}

// A purely DECLARATION-ONLY (abstract, non-default) method with an `ensures`,
// no impl, generic caller. This is SOUND to trust: every impl of DT5 must
// provide a `dm5` body satisfying ensures(result == 7), so for any T: DT5
// `t.dm5() == 7`. The no-impl default pass must NOT touch it (has_default ==
// false) — must still Verify.
const ABSTRACT_METHOD_NO_DEFAULT: &str = r#"
#[trust_vc::trait_spec]
trait DT5 {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm5(&self) -> u32;
}
#[trust_vc::ensures(true)]
fn da_caller<T: DT5>(t: T) {
    let r = t.dm5();
    trust_vc::assert!(r == 7u32);
}
"#;

#[test]
fn abstract_declaration_only_method_ensures_still_verifies() {
    let result = verify(
        "abstract_no_default",
        ABSTRACT_METHOD_NO_DEFAULT,
        "da_caller",
    );
    assert!(
        matches!(result, VerifyResult::Verified),
        "a declaration-only (abstract) trait method's ensures is a per-impl obligation \
         every impl must discharge, so a generic caller relying on it is sound and must \
         still Verify — the no-impl default pass must leave it alone; got: {result:?}"
    );
}

// ===========================================================================
// IMPL-PRESENT NON-REGRESSION — a trait WITH a conforming impl in the file and a
// generic caller must still Verify (handled by the existing per-impl path, NOT
// the new no-impl pass).
// ===========================================================================

const IMPL_PRESENT_CONFORMING: &str = r#"
#[trust_vc::trait_spec]
trait DT6 {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm6(&self) -> u32 { 7u32 }
}
struct S;
#[trust_vc::trait_impl]
impl DT6 for S {}
#[trust_vc::ensures(true)]
fn di_caller<T: DT6>(t: T) {
    let r = t.dm6();
    trust_vc::assert!(r == 7u32);
}
"#;

#[test]
fn impl_present_conforming_default_still_verifies() {
    let result = verify("impl_present", IMPL_PRESENT_CONFORMING, "di_caller");
    assert!(
        matches!(result, VerifyResult::Verified),
        "a conforming default with a concrete all-defaults impl in the file must still \
         Verify (existing per-impl path); got: {result:?}"
    );
}

// ===========================================================================
// ROUND-6 — a default body that CALLS A FREE FUNCTION (spec or exec).
//
// The round-5 implless pass only LOWERED default bodies whose calls resolve in
// the conformance context (literals, sibling defaults). A free-function call
// (`fn dm(&self) -> u32 { helper() }`) does NOT resolve there — the verified
// generic caller never references `helper` directly, so it is absent from the
// context — the conformance build Errs, the Err is swallowed (fail-safe), and
// the unjustified trait postcondition axiom is trusted unchecked => a generic
// caller false-Verifies.
//
// `register_default_body_free_function_helpers` (vc_extraction/trait_contracts)
// threads those free functions into the context: SPEC callees transparently
// (defining body axiom) so a conforming default still Verifies, EXEC callees as
// opaque UFs so a default relying on the exec value fails CLOSED (Verus-faithful
// — an exec call with no postcondition is opaque). `referenced_body_axiom_broadcasts`
// (trait_conformance) carries the spec body axiom as a broadcast so E-matching
// grounds it for literal/constant-argument calls too (no over-rejection).
// ===========================================================================

// SOUNDNESS — free SPEC fn returns 3, ensures(result == 7): genuinely false
// (an all-defaults impl runs the default body == bad_spec() == 3 != 7).
const FREE_SPEC_VIOLATE_EQ: &str = r#"
#[trust_vc::spec]
fn bad_spec() -> u32 { 3u32 }
#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { bad_spec() }
}
#[trust_vc::ensures(true)]
fn fs_caller<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r == 7u32);
}
"#;

#[test]
fn default_body_calling_free_spec_fn_violating_eq_does_not_verify() {
    let result = conformance_verdict("free_spec_violate", FREE_SPEC_VIOLATE_EQ, "fs_caller");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "default body bad_spec() == 3 contradicts ensures(result == 7); a generic caller \
         relying on the unjustified postcondition axiom must be refuted; got: {result:?}"
    );
}

// SOUNDNESS — the false fact must not be laundered through arithmetic.
const FREE_SPEC_VIOLATE_DERIVED: &str = r#"
#[trust_vc::spec]
fn bad_spec() -> u32 { 3u32 }
#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { bad_spec() }
}
#[trust_vc::ensures(true)]
fn fsd_caller<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r + 1u32 == 8u32);
}
"#;

#[test]
fn default_body_calling_free_spec_fn_does_not_launder_derived_fact() {
    let result = conformance_verdict("free_spec_derived", FREE_SPEC_VIOLATE_DERIVED, "fsd_caller");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "the false r == 7 must not be laundered into r + 1 == 8; got: {result:?}"
    );
}

// SOUNDNESS — free EXEC fn (no spec, no postcondition) returns 3,
// ensures(result == 7). An exec call with no postcondition is opaque, so the
// default cannot establish the ensures — must fail CLOSED.
const FREE_EXEC_VIOLATE_EQ: &str = r#"
fn bad_exec() -> u32 { 3u32 }
#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { bad_exec() }
}
#[trust_vc::ensures(true)]
fn fe_caller<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r == 7u32);
}
"#;

#[test]
fn default_body_calling_free_exec_fn_does_not_verify() {
    let result = conformance_verdict("free_exec_violate", FREE_EXEC_VIOLATE_EQ, "fe_caller");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "an exec call with no postcondition is opaque; the default cannot establish \
         ensures(result == 7) and must fail closed; got: {result:?}"
    );
}

// NO OVER-REJECTION — free SPEC fn returns 7, ensures(result == 7): conforming.
const FREE_SPEC_CONFORM_EQ: &str = r#"
#[trust_vc::spec]
fn good_spec() -> u32 { 7u32 }
#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { good_spec() }
}
#[trust_vc::ensures(true)]
fn fsc_caller<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r == 7u32);
}
"#;

#[test]
fn conforming_default_calling_free_spec_fn_still_verifies() {
    let result = verify("free_spec_conform", FREE_SPEC_CONFORM_EQ, "fsc_caller");
    assert!(
        matches!(result, VerifyResult::Verified),
        "good_spec() == 7 genuinely establishes ensures(result == 7) — must still \
         Verify (no over-rejection); got: {result:?}"
    );
}

// NO OVER-REJECTION — free SPEC fn with LITERAL arguments: add(2, 5) == 7,
// ensures(result == 7). Exercises the broadcast-grounding path for
// constant-argument calls that the variable-only grounder cannot instantiate.
const FREE_SPEC_CONFORM_ARGS: &str = r#"
#[trust_vc::spec]
fn add(a: u32, b: u32) -> u32 { a + b }
#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { add(2u32, 5u32) }
}
#[trust_vc::ensures(true)]
fn fsa_caller<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r == 7u32);
}
"#;

#[test]
fn conforming_default_calling_free_spec_fn_with_literal_args_still_verifies() {
    let result = verify("free_spec_args", FREE_SPEC_CONFORM_ARGS, "fsa_caller");
    assert!(
        matches!(result, VerifyResult::Verified),
        "add(2, 5) == 7 conformingly establishes ensures(result == 7) even with literal \
         arguments — must still Verify (no over-rejection); got: {result:?}"
    );
}

// SOUNDNESS — free SPEC fn with LITERAL arguments contradicting the ensures:
// add(2, 5) == 7 but ensures(result == 8).
const FREE_SPEC_VIOLATE_ARGS: &str = r#"
#[trust_vc::spec]
fn add(a: u32, b: u32) -> u32 { a + b }
#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 8u32)]
    fn dm(&self) -> u32 { add(2u32, 5u32) }
}
#[trust_vc::ensures(true)]
fn fsav_caller<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r == 8u32);
}
"#;

#[test]
fn default_body_calling_free_spec_fn_with_literal_args_violating_does_not_verify() {
    let result = conformance_verdict("free_spec_args_bad", FREE_SPEC_VIOLATE_ARGS, "fsav_caller");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "add(2, 5) == 7 contradicts ensures(result == 8); must fail closed; got: {result:?}"
    );
}

/// The refutation above must be a REAL one, not merely "some model came back".
///
/// This is the shape that used to degrade to `NotProved/Incompleteness`: the
/// spec fn's definitional axiom `forall a b. add(a,b) == a + b` survived to ay's
/// fail-closed quantified-model gate with no interpretation for `add`, so the
/// gate deferred and the verdict downgraded to `unknown (incomplete)`. Asserting
/// only `Counterexample` would pass again the moment ay handed back a model that
/// named no value for the call — which is exactly the failure mode the gate
/// exists to catch. So pin the WITNESS: the counterexample must report the
/// result as 7, the value `add(2, 5)` actually has, which is what falsifies
/// `ensures(result == 8)`. A witness carrying 8 would satisfy the postcondition
/// and refute nothing.
#[test]
fn free_spec_fn_literal_args_counterexample_witness_actually_falsifies_the_ensures() {
    let result = conformance_verdict(
        "free_spec_args_bad_witness",
        FREE_SPEC_VIOLATE_ARGS,
        "fsav_caller",
    );
    let VerifyResult::Counterexample { ref model, .. } = result else {
        panic!("expected a genuine refutation with a model; got: {result:?}");
    };
    let model = model
        .as_ref()
        .unwrap_or_else(|| panic!("refutation carries no model at all; got: {result:?}"));
    assert!(
        model.contains("\"__trust_vc_impl_result\": (7, 32)"),
        "the witness must name the value add(2, 5) really has (7), which FALSIFIES \
         ensures(result == 8); a witness of 8 would satisfy it and refute nothing. \
         model: {model}"
    );
}

// NO OVER-REJECTION — transitive free SPEC deps: f() == g() == 7,
// ensures(result == 7). The transitive callee g must also be registered.
const FREE_SPEC_TRANSITIVE: &str = r#"
#[trust_vc::spec]
fn g() -> u32 { 7u32 }
#[trust_vc::spec]
fn f() -> u32 { g() }
#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { f() }
}
#[trust_vc::ensures(true)]
fn ft_caller<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r == 7u32);
}
"#;

#[test]
fn conforming_default_calling_transitive_free_spec_fns_still_verifies() {
    let result = verify("free_spec_transitive", FREE_SPEC_TRANSITIVE, "ft_caller");
    assert!(
        matches!(result, VerifyResult::Verified),
        "f() == g() == 7 conformingly establishes ensures(result == 7) through the \
         transitive spec dependency — must still Verify; got: {result:?}"
    );
}

// ===========================================================================
// ROUND-7 NARROWING — a default body that CALLS A FREE *EXEC* FUNCTION THAT
// CARRIES AN `#[ensures]`.
//
// The round-6 fix registered every exec callee via
// `register_source_function_signature`, which declares ONLY the signature and
// DROPS the callee's `#[ensures]`. That over-rejected a CONFORMING default
// `fn dm(&self) -> u32 { exec_post() }` whose own `ensures` is `result == 7`
// when `exec_post` carries `#[ensures(result == 7)]`: the call was an
// unconstrained UF, free to take any value, so a generic caller regressed
// `Verified -> Counterexample`.
//
// `register_exec_callee_postcondition_axioms` (vc_extraction/trait_contracts)
// closes that over-rejection by ALSO publishing the callee's DEFINITIONAL
// postcondition (`exec_post() == 7`) as a body-axiom-shaped broadcast — the same
// modular-contract fact the normal-caller path and Verus use for an exec call
// with a postcondition. The callee is independently verified against that same
// `#[ensures]`, so assuming it admits no value the callee could not return; a
// postcondition-LESS exec callee gets NO axiom and stays opaque (the round-6
// free-exec-call holes remain Counterexamples).
// ===========================================================================

// NO OVER-REJECTION (the previously regressed case) — free EXEC fn with a
// definitional `#[ensures(result == 7)]` and a body that establishes it.
const FREE_EXEC_ENSURES_CONFORM: &str = r#"
#[trust_vc::ensures(result == 7u32)]
fn exec_post() -> u32 { 7u32 }
#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { exec_post() }
}
#[trust_vc::ensures(true)]
fn ep_caller<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r == 7u32);
}
"#;

#[test]
fn conforming_default_calling_free_exec_fn_with_ensures_still_verifies() {
    let result = verify("free_exec_ensures", FREE_EXEC_ENSURES_CONFORM, "ep_caller");
    assert!(
        matches!(result, VerifyResult::Verified),
        "exec_post's `#[ensures(result == 7)]` (which it is independently verified \
         against) lets the conforming default establish its own ensures — must Verify \
         (the round-7 over-rejection regression); got: {result:?}"
    );
}

// NO OVER-REJECTION — free EXEC fn with LITERAL ARGUMENTS and a definitional
// postcondition `result == a + b`: exercises the quantified (param-bearing)
// postcondition axiom and its bound-var declaration.
const FREE_EXEC_ENSURES_ARGS: &str = r#"
#[trust_vc::ensures(result == a + b)]
fn add(a: u32, b: u32) -> u32 { a + b }
#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { add(2u32, 5u32) }
}
#[trust_vc::ensures(true)]
fn ea_caller<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r == 7u32);
}
"#;

#[test]
fn conforming_default_calling_free_exec_fn_with_args_still_verifies() {
    let result = verify("free_exec_args", FREE_EXEC_ENSURES_ARGS, "ea_caller");
    assert!(
        matches!(result, VerifyResult::Verified),
        "add(2, 5) == 7 via the callee's `#[ensures(result == a + b)]` conformingly \
         establishes ensures(result == 7) — must Verify (no over-rejection); got: {result:?}"
    );
}

// SOUNDNESS — exec callee conforms to ITS OWN contract, but the trait default's
// `ensures` is wrong: exec_post() == 7, dm `ensures(result == 8)`. Genuinely
// false (an all-defaults impl runs dm() == exec_post() == 7 != 8); must fail
// closed. Proves the published postcondition is the callee's real value, not a
// laundered pass.
const FREE_EXEC_ENSURES_WRONG_DM: &str = r#"
#[trust_vc::ensures(result == 7u32)]
fn exec_post() -> u32 { 7u32 }
#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 8u32)]
    fn dm(&self) -> u32 { exec_post() }
}
#[trust_vc::ensures(true)]
fn epw_caller<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r == 8u32);
}
"#;

#[test]
fn default_calling_free_exec_fn_with_wrong_dm_ensures_does_not_verify() {
    let result = conformance_verdict(
        "free_exec_wrong_dm",
        FREE_EXEC_ENSURES_WRONG_DM,
        "epw_caller",
    );
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "exec_post() == 7 contradicts dm's ensures(result == 8); the generic caller \
         must be refuted; got: {result:?}"
    );
}

// SOUNDNESS — a NON-definitional exec `#[ensures(result > 0)]` is NOT carried
// (only a top-level `result == <rhs>` is). exec_pos() == 5, dm `ensures == 7`
// is genuinely false (dm() == 5 != 7); the callee stays opaque and the default
// fails closed.
const FREE_EXEC_NONDEFINITIONAL: &str = r#"
#[trust_vc::ensures(result > 0u32)]
fn exec_pos() -> u32 { 5u32 }
#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { exec_pos() }
}
#[trust_vc::ensures(true)]
fn ei_caller<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r == 7u32);
}
"#;

#[test]
fn default_calling_free_exec_fn_with_nondefinitional_ensures_does_not_verify() {
    let result = conformance_verdict("free_exec_nondef", FREE_EXEC_NONDEFINITIONAL, "ei_caller");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "a non-definitional `ensures(result > 0)` is not carried; exec_pos stays opaque \
         and the default cannot establish ensures(result == 7); got: {result:?}"
    );
}

// MODULAR SAFETY NET — a LYING exec callee (`#[ensures(result == 7)]` but body
// `3`) is what makes assuming its postcondition sound: the callee FAILS ITS OWN
// verification, so a full run rejects the program exactly where Verus would (at
// the callee). Documents the boundary the postcondition assumption rests on.
const FREE_EXEC_LYING: &str = r#"
#[trust_vc::ensures(result == 7u32)]
fn exec_post() -> u32 { 3u32 }
#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { exec_post() }
}
#[trust_vc::ensures(true)]
fn epl_caller<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r == 7u32);
}
"#;

#[test]
fn lying_free_exec_callee_fails_its_own_verification() {
    // The postcondition we assume of `exec_post` at the default-body call site is
    // discharged by `exec_post`'s OWN verification — which a lying body fails.
    let result = verify("free_exec_lying_self", FREE_EXEC_LYING, "exec_post");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "exec_post's body (3) violates its own `#[ensures(result == 7)]`; it must fail \
         its own verification (the modular safety net for the assumed postcondition); \
         got: {result:?}"
    );
}

// ===========================================================================
// ROUND-7 REQUIRES-GUARD — a default body that CALLS A FREE *EXEC* FUNCTION
// THAT CARRIES BOTH A `#[requires]` AND A DEFINITIONAL `#[ensures]`.
//
// `register_exec_callee_postcondition_axioms` publishes the UNGUARDED axiom
// `forall params. <callee>(params) == <rhs>`. That equality is the callee's
// postcondition only WHERE the callee's `#[requires]` holds — the callee is
// verified against its `#[ensures]` only under that precondition. Publishing it
// unguarded for a requires-bearing callee would let a default
// `fn dm(&self) -> u32 { exec_req(7) }` "establish" `result == 100` from
// `forall a. exec_req(a) == 100` even though `7` violates `requires(a == 5)` and
// the real impl returns 140 (and would panic) — a false `Verified`.
//
// The requires-guard takes the SAFE FALLBACK: it carries the definitional
// postcondition axiom ONLY for a `#[requires]`-FREE exec callee (whose
// postcondition is unconditional). A requires-bearing exec callee stays OPAQUE
// (signature only), so a default relying on its value fails CLOSED — exactly the
// round-6 sound behavior — rather than false-Verifying.
// ===========================================================================

// SOUNDNESS (the smoking gun) — exec_req is SELF-CONFORMING under its own
// contract (`requires(a == 5)`, `5 * 20 == 100`), but the default calls it with
// `7`, which VIOLATES `requires(a == 5)`. The real impl runs dm() ==
// exec_req(7) == 140 != 100 (and the call would even be a precondition error in
// Verus). The default must NOT be able to launder the requires-guarded
// postcondition into an unconditional `result == 100`.
const FREE_EXEC_REQUIRES_FALSE: &str = r#"
#[trust_vc::requires(a == 5u32)]
#[trust_vc::ensures(result == 100u32)]
fn exec_req(a: u32) -> u32 { a * 20u32 }
#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 100u32)]
    fn dm(&self) -> u32 { exec_req(7u32) }
}
#[trust_vc::ensures(true)]
fn er_caller<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r == 100u32);
}
"#;

#[test]
fn requires_bearing_exec_callee_false_case_does_not_verify() {
    let result = conformance_verdict(
        "free_exec_requires_false",
        FREE_EXEC_REQUIRES_FALSE,
        "er_caller",
    );
    assert!(
        matches!(
            result,
            VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. }
        ),
        "exec_req carries `#[requires(a == 5)]`, so its `#[ensures(result == 100)]` is \
         NOT an unconditional fact; the default `dm() {{ exec_req(7) }}` (7 violates the \
         precondition; the real result is 140) must NOT establish `result == 100` — the \
         requires-bearing callee stays opaque and the default fails closed; got: {result:?}"
    );
}

// SOUNDNESS (milder) — `requires(a == 5)` / `ensures(result == a)`,
// `dm() { exec_req(7) }`, dm `ensures(result == 7)`. The laundered value would
// be `exec_req(7) == 7`; the guard must prevent it.
const FREE_EXEC_REQUIRES_FALSE_MILD: &str = r#"
#[trust_vc::requires(a == 5u32)]
#[trust_vc::ensures(result == a)]
fn exec_req(a: u32) -> u32 { a }
#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { exec_req(7u32) }
}
#[trust_vc::ensures(true)]
fn erm_caller<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r == 7u32);
}
"#;

#[test]
fn requires_bearing_exec_callee_milder_false_case_does_not_verify() {
    let result = conformance_verdict(
        "free_exec_requires_false_mild",
        FREE_EXEC_REQUIRES_FALSE_MILD,
        "erm_caller",
    );
    assert!(
        matches!(
            result,
            VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. }
        ),
        "exec_req's `#[ensures(result == a)]` is guarded by `#[requires(a == 5)]`; \
         calling it with `7` (which violates the precondition) must NOT yield \
         `exec_req(7) == 7` — the default must fail closed; got: {result:?}"
    );
}

// MODULAR BOUNDARY — the requires-bearing callee is SELF-CONFORMING: under
// `requires(a == 5)`, `a * 20 == 5 * 20 == 100` satisfies `ensures(result == 100)`.
// So the callee verifies on its own; the unsoundness above was purely the
// UNGUARDED call-site assumption, which the requires-guard removes.
const FREE_EXEC_REQUIRES_SELF: &str = r#"
#[trust_vc::requires(a == 5u32)]
#[trust_vc::ensures(result == 100u32)]
fn exec_req(a: u32) -> u32 { a * 20u32 }
#[trust_vc::ensures(true)]
fn dummy() { trust_vc::assert!(true); }
"#;

#[test]
fn requires_bearing_exec_callee_is_self_conforming() {
    let result = verify(
        "free_exec_requires_self",
        FREE_EXEC_REQUIRES_SELF,
        "exec_req",
    );
    assert!(
        matches!(result, VerifyResult::Verified),
        "under `requires(a == 5)`, `a * 20 == 100` conformingly establishes \
         `ensures(result == 100)`; the callee verifies on its own — the boundary the \
         (now requires-guarded) call-site assumption rests on; got: {result:?}"
    );
}

// NO OVER-REJECTION (the requires-FREE conforming case, explicit) — a
// `#[requires]`-FREE exec callee with a definitional `#[ensures(result == 7)]`
// still gets its postcondition axiom, so a conforming default establishes its
// ensures. Mirrors the prompt's `exec_post` example; complements the round-7
// `conforming_default_calling_free_exec_fn_with_ensures_still_verifies` above.
const FREE_EXEC_NO_REQUIRES_CONFORM: &str = r#"
#[trust_vc::ensures(result == 7u32)]
fn exec_post() -> u32 { 7u32 }
#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { exec_post() }
}
#[trust_vc::ensures(true)]
fn enr_caller<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r == 7u32);
}
"#;

#[test]
fn no_requires_conforming_exec_callee_still_verifies() {
    let result = verify(
        "free_exec_no_requires_conform",
        FREE_EXEC_NO_REQUIRES_CONFORM,
        "enr_caller",
    );
    assert!(
        matches!(result, VerifyResult::Verified),
        "exec_post has NO `#[requires]`, so its `#[ensures(result == 7)]` is \
         unconditional; the conforming default must still establish its ensures — the \
         requires-guard must not regress the requires-free path; got: {result:?}"
    );
}
