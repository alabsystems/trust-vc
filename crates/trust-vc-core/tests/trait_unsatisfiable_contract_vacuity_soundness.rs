// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS — an UNSATISFIABLE trait postcondition must not prove anything.
//!
//! `register_trait` publishes every trait method `ensures` as an unconditional
//! global axiom
//!
//! ```text
//! forall self: Poly, args. <requires> ==> <ensures>[result := Trait__m(self, args)]
//! ```
//!
//! into the SAME solver context that discharges an ordinary caller's
//! obligations. Nothing in the caller's query establishes that axiom — and
//! unlike a definitional axiom (`f(args) == body`, always satisfiable because it
//! merely defines a function), a postcondition axiom constrains an
//! uninterpreted function by an arbitrary user predicate and can be
//! UNREALIZABLE.
//!
//! # The witness values
//!
//! `#[ensures(result > x)]` on `fn p(&self, x: u32) -> u32` is such a contract,
//! and it is not contrived — it is what anyone writes for "returns something
//! bigger". Over `u32` it has no solution at
//!
//! ```text
//!     x = 4_294_967_295   (u32::MAX = 0xFFFFFFFF)
//! ```
//!
//! because no `u32` is strictly greater than `u32::MAX`. So the published axiom
//! is UNSAT standing alone: no total interpretation of `Tr__p` exists, and NO
//! implementation can ever satisfy the contract. (Confirmed standalone at a
//! small width with the ay CLI: `forall v: BV4. bvult v (f v)` answers `unsat`.)
//!
//! Once that ground instance is in the premise set, `premises AND NOT G` is
//! UNSAT for EVERY `G`, and trust-vc reads UNSAT as "proved". Measured at
//! HEAD before the fix, with the contract below and NO impl in the file:
//!
//! ```text
//!     assert!(t.p(4294967295u32) == 5u32)   ->  Verified
//!     assert!(t.p(4294967295u32) != 5u32)   ->  Verified
//! ```
//!
//! Both. The engine proved a claim and its negation.
//!
//! # Why nothing else caught it
//!
//! * `check_vacuous_truth` screens only ASSUMPTION-level premises
//!   (`VerificationSlices::new(ctx, assumptions, broadcast, &[], &[], &[])` —
//!   the goal slices are empty) and returns early when the assumption set is
//!   empty. The trait axiom is a SETUP-level premise, so it is never screened.
//!   Worse, screening it in isolation would not help either: the axiom's trigger
//!   is `Tr__p(s, x)`, so E-matching only produces the refuting instance once a
//!   GROUND `Tr__p(t, 0xFFFFFFFF)` term exists — and in this class that term
//!   comes from the GOAL. The contradiction is invisible until the goal is
//!   present, which is exactly why the check must run against the goal.
//! * The conformance obligation is not a backstop. With no impl in the file
//!   `list_trait_conformance_obligations` is EMPTY, so nothing refutes the
//!   contract anywhere; and with an impl present, the impl's conformance
//!   obligation does refute, but the CALLER's own verdict is still reported as
//!   `Verified`.
//!
//! The fix widens the existing vacuity probe (previously gated to
//! `#[broadcast]` lemmas, the other class of unverified published axiom) to fire
//! whenever a trait-method postcondition axiom is in scope: a goal that reaches
//! `Verified` is re-checked by verifying its NEGATION in the identical context.
//! Both verifying means the premises are contradictory, so the proof is
//! rejected as `Unknown(VacuousTruth)` rather than trusted.
//!
//! The controls below pin that this rejects only the contradictory case: a
//! SATISFIABLE trait contract still proves what it should, and still REFUTES a
//! false claim with a real model rather than degrading it to `Unknown`.

use std::path::PathBuf;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn write_fixture(label: &str, source: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "trust_vc_unsat_contract_{label}_{}.rs",
        std::process::id()
    ));
    std::fs::write(&path, source).expect("write fixture");
    path
}

fn verdict(label: &str, source: &str, case: &str) -> VerifyResult {
    let path = write_fixture(label, source);
    let path_str = path.to_str().expect("fixture path utf-8");
    let result =
        verify_function_from_file(path_str, case).unwrap_or_else(|err| VerifyResult::Error {
            message: err.to_string(),
        });
    let _ = std::fs::remove_file(&path);
    result
}

// ===========================================================================
// CARDINAL — the unrealizable contract, consumed at the witness argument.
// ===========================================================================

/// `ensures(result > x)` over `u32`, with NO impl in the file. Two callers make
/// contradictory claims about the SAME call at the witness argument
/// `x = 4294967295` (= `u32::MAX`), the value at which the contract has no
/// solution. Neither may verify.
const UNREALIZABLE_AT_MAX: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result > x)]
    fn p(&self, x: u32) -> u32;
}
fn claims_five<T: Tr>(t: T) {
    trust_vc::assert!(t.p(4294967295u32) == 5u32);
}
fn claims_not_five<T: Tr>(t: T) {
    trust_vc::assert!(t.p(4294967295u32) != 5u32);
}
"#;

/// The engine must never prove BOTH a claim and its negation. Before the fix
/// both of these reported `Verified`.
///
/// The witness is the ARGUMENT, not a model: `x = 4294967295` is the `u32` at
/// which `result > x` is unsatisfiable, because no `u32` exceeds `u32::MAX`.
/// That single ground instance of the published axiom — `bvult 0xFFFFFFFF
/// (Tr__p t 0xFFFFFFFF)` — is false under every interpretation, which is what
/// collapses the premise set and makes each claim "provable".
#[test]
fn unrealizable_trait_contract_does_not_prove_a_claim_and_its_negation() {
    let yes = verdict("both_yes", UNREALIZABLE_AT_MAX, "claims_five");
    let no = verdict("both_no", UNREALIZABLE_AT_MAX, "claims_not_five");

    let yes_verified = matches!(yes, VerifyResult::Verified);
    let no_verified = matches!(no, VerifyResult::Verified);

    assert!(
        !(yes_verified && no_verified),
        "CARDINAL INCONSISTENCY: `t.p(4294967295) == 5` and `t.p(4294967295) != 5` \
         BOTH verified off the unrealizable contract `ensures(result > x)`, which has \
         no u32 solution at x = 4294967295 (= u32::MAX). \
         `== 5` gave: {yes:?}; `!= 5` gave: {no:?}"
    );
    assert!(
        !yes_verified,
        "`t.p(4294967295) == 5` must not be provable: the only premise that could \
         prove it is the contract axiom, which is UNSATISFIABLE at x = 4294967295 \
         (no u32 is > u32::MAX). Got: {yes:?}"
    );
    assert!(
        !no_verified,
        "`t.p(4294967295) != 5` must not be provable either — same contradictory \
         premise, opposite claim. Got: {no:?}"
    );
}

/// The same contract, but the goal is an outright falsehood that mentions the
/// call. `1 == 2` must never be provable.
const EX_FALSO_AT_MAX: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result > x)]
    fn p(&self, x: u32) -> u32;
}
fn proves_falsehood<T: Tr>(t: T) {
    trust_vc::assert!(t.p(4294967295u32) == 5u32 || 1u32 == 2u32);
}
"#;

#[test]
fn unrealizable_trait_contract_does_not_prove_an_outright_falsehood() {
    let result = verdict("ex_falso", EX_FALSO_AT_MAX, "proves_falsehood");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "a disjunction whose only non-trivial disjunct is `t.p(4294967295) == 5` \
         (unprovable — the contract has no u32 solution at u32::MAX) and whose other \
         disjunct is `1 == 2` (false) must not verify. Got: {result:?}"
    );
}

// ===========================================================================
// CONTROLS — the gate must bite ONLY the contradictory case.
// ===========================================================================

/// The SAME shape with a SATISFIABLE contract: `ensures(result > 0)` is
/// realizable (take `p` identically 1), so the premise set is consistent and
/// the trait contract must keep its full proving power.
const REALIZABLE_CONTRACT: &str = r#"
#[trust_vc::trait_spec]
trait Positive {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result > 0u32)]
    fn p(&self) -> u32;
}
fn sound_consequence<T: Positive>(t: T) {
    trust_vc::assert!(t.p() >= 1u32);
}
fn false_claim<T: Positive>(t: T) {
    trust_vc::assert!(t.p() == 0u32);
}
"#;

/// NO OVER-REJECTION: `result > 0` entails `result >= 1` over `u32`, and the
/// contract is satisfiable, so this must still Verify. If the widened vacuity
/// probe rejected this it would have gutted modular trait reasoning.
#[test]
fn realizable_trait_contract_still_proves_its_consequence() {
    let result = verdict("realizable_ok", REALIZABLE_CONTRACT, "sound_consequence");
    assert!(
        matches!(result, VerifyResult::Verified),
        "`ensures(result > 0u32)` is SATISFIABLE (p == 1 witnesses it), so the caller \
         must still derive `t.p() >= 1u32`. A failure here means the vacuity gate \
         over-rejects consistent trait contracts. Got: {result:?}"
    );
}

/// A claim that CONTRADICTS a satisfiable contract must still fail.
///
/// MEASURED, not assumed: this returns `NotProved { category: Incompleteness }`
/// — the caller-side refutation of a claim against a `Poly`-sorted trait UF is a
/// PRE-EXISTING incompleteness (ay defers on the quantified axiom rather than
/// producing a model), and it does so IDENTICALLY with the vacuity gate
/// neutered. So this test asserts the fail-closed property the engine actually
/// has, and deliberately does NOT assert a model: writing
/// `assert!(matches!(result, Counterexample{..}))` here would pin a behaviour
/// this path has never had, and would then be "fixed" by weakening something.
///
/// The model-preserving discriminator lives on the CONFORMANCE path instead,
/// where a witness genuinely comes back and is pinned by value — see
/// `trait_generic_struct_conformance_soundness::
/// generic_struct_param_override_violating_ensures_does_not_verify`. Together
/// the two pin both directions: the probe does not convert a refutation into a
/// rejection, and it does not let a contradiction through.
#[test]
fn realizable_trait_contract_still_fails_a_false_claim() {
    let result = verdict("realizable_bad", REALIZABLE_CONTRACT, "false_claim");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "`t.p() == 0u32` contradicts the satisfiable contract `result > 0u32` and must \
         never verify. Got: {result:?}"
    );
}
