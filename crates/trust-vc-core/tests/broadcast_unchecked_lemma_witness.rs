// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! WITNESS FOR A KNOWN DEFECT — this file asserts the CURRENT, UNSOUND behaviour
//! on purpose, so that fixing it makes this test fail loudly and deliberately.
//!
//! `#[trust_vc::broadcast]` publishes a lemma's `ensures!` as a global `forall`
//! axiom WITHOUT verifying that the body establishes it. The engine documents
//! this against itself in `encoder/verification/assertion.rs`:
//!
//!   > a bogus lemma (e.g. `ensures!(x * x < 0)`) injects a contradictory
//!   > premise ... a CATASTROPHIC false `Verified` that proves false.
//!
//! The `vacuity_probe_result` backstop is partial BY CONSTRUCTION: it
//! downgrades only when both `G` and `¬G` verify, i.e. when the assumption set is
//! INCONSISTENT. A lemma that is consistent but simply unestablished sails
//! through — and that is the ORDINARY case, an `ensures` over an `#[opaque]` spec
//! fn, whose body establishes nothing by definition.
//!
//! Until now this was a code-reading argument. The pair below demonstrates it,
//! and the control is what makes it airtight: the two goals are identical in
//! shape and differ only in whether an unchecked broadcast lemma is in scope.
//!
//! Verus verifies broadcast lemma bodies. This is strictly weaker than the tool
//! trust-vc measures itself against.
//!
//! THE FIX (landed). `suppress_unestablished_broadcast_lemma_axioms` in
//! `vc_extraction.rs` discharges `guard |- ensures` for every
//! `__source_broadcast_*` axiom in a DISCARDED child and drops the axiom unless
//! it verifies. Vacuity counts as a pass — an unsatisfiable guard makes the
//! published `guard ==> ensures` inert.
//!
//! TWO THINGS WERE MEASURED, NOT ASSUMED, AND BOTH CHANGED THE DESIGN:
//!
//! 1. IT CANNOT RUN AT THE PUBLISH SITE. `collect_source_broadcast_lemmas` looks
//!    like the natural home, but at collector time the context holds ZERO
//!    obligations: a spec fn referenced only from inside `ensures!()` /
//!    `assert!()` macro tokens is registered during BODY EXTRACTION, which runs
//!    later. A check placed there proves `bcf(c) == c` knowing nothing about
//!    `bcf` and suppresses every legitimate lemma. (The earlier claim in this
//!    header that re-entrancy was the blocker was wrong on its own terms — the
//!    collector already triggers a nested solver query on its first line, via
//!    `ill_founded_recursive_function_names`.)
//!
//! 2. THE CHECK MUST SEE THROUGH OPACITY. An `#[trust_vc::opaque]` spec fn
//!    contributes NO body axiom to an ordinary context, so `ensures!(bcf(x) == x)`
//!    over an opaque `bcf` is indistinguishable from `ensures!(bcf(x) == 42)` —
//!    both unprovable, both dropped. That is a mass over-rejection wearing the
//!    costume of a working fix: the defect witness still flips while
//!    `broadcast_use_soundness` and the corpus quietly go red. The check base is
//!    therefore seeded via `apply_all_specs_revealed`, judging each lemma against
//!    the TRUE definitions. Sound because a definitional body axiom is a true
//!    fact; opacity is an abstraction control, not a soundness gate.
//!
//! THE OTHER DIRECTION IS PINNED BELOW, AND IT IS THE POINT. "Verify lemma
//! bodies" can be implemented as "stop publishing broadcast axioms" — that
//! passes the defect witness above and silently deletes a working capability.
//! The three capability tests at the end of this file are what stop that. They
//! pass TODAY and must still pass after the fix:
//!
//! | fixture                                    | today    | after the fix |
//! |--------------------------------------------|----------|---------------|
//! | lemma over a TRANSPARENT spec fn           | Verified | Verified      |
//! | guarded lemma, consumer HAS the `requires`  | Verified | Verified      |
//! | guarded lemma, consumer LACKS it           | NotProved| NotProved     |
//! | lemma over an OPAQUE spec fn (the defect)  | Verified | NOT Verified  |
//!
//! Only the last row may move. The third row also shows the `requires`->guard
//! fold is already sound and load-bearing: a caller that has not established the
//! lemma's `requires` cannot use its `ensures`.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_bcw_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
    let _ = std::fs::remove_file(&p);
    result
}

/// `bcf` is opaque, so the lemma body establishes nothing about it. The lemma
/// nonetheless declares `bcf(x) == 42` for all `x`.
const WITH_BOGUS_LEMMA: &str = r#"
#[trust_vc::opaque]
#[trust_vc::spec]
fn bcf(x: u64) -> u64 { x }

#[trust_vc::broadcast]
#[trust_vc::trigger(bcf(x))]
fn bogus(x: u64) { trust_vc::ensures!(bcf(x) == 42u64); }

#[trust_vc::ensures(result == 42u64)]
pub fn consumes_unchecked_lemma() -> u64 { bcf(7u64) }
"#;

/// Identical shape, no broadcast lemma in scope.
const WITHOUT_LEMMA: &str = r#"
#[trust_vc::opaque]
#[trust_vc::spec]
fn bcg(x: u64) -> u64 { x }

#[trust_vc::ensures(result == 42u64)]
pub fn control_no_lemma() -> u64 { bcg(7u64) }
"#;

/// The control. Without a lemma, `bcg(7) == 42` is not provable — as it should
/// not be, since `bcg` is opaque. This is what makes the witness below
/// attributable to the lemma rather than to anything else in the fixture.
#[test]
fn without_a_lemma_the_same_goal_is_refuted() {
    let result = verify("ctl", "control_no_lemma", WITHOUT_LEMMA);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "an opaque spec fn must not yield a concrete value without a lemma: {result:?}"
    );
}

/// THE GUARD (was the defect witness; the fix landed and flipped it).
///
/// The only difference from the control is a `#[trust_vc::broadcast]` lemma whose
/// contract cannot establish its own `ensures` — `bcf` is opaque, so nothing
/// justifies `bcf(x) == 42`.
///
/// Before the fix this VERIFIED: the lemma's `ensures` was published as a global
/// axiom and consumed without ever being checked, and since the axiom is false of
/// the actual body it is a contradictory premise that proves anything.
#[test]
fn unchecked_broadcast_lemma_is_trusted_by_a_caller() {
    let result = verify("witness", "consumes_unchecked_lemma", WITH_BOGUS_LEMMA);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "REGRESSION: a broadcast lemma whose contract does not establish its own `ensures` \
         must not have its axiom published. Verifying here means the unchecked axiom is \
         being trusted again — a contradictory premise that proves anything. Got: {result:?}"
    );
}

// ---------------------------------------------------------------------------
// CAPABILITY PINS — the other direction of the pending fix.
//
// These pass TODAY and must STILL pass after broadcast lemma bodies are
// verified. Without them, the fix can be implemented as "stop publishing
// broadcast axioms": that satisfies the defect witness above while deleting a
// working capability, and no test would object.
// ---------------------------------------------------------------------------

/// A LEGITIMATE lemma: `sq` is transparent, so its own defining axiom already
/// establishes the lemma's `ensures`. A body check must accept this.
const GOOD_TRANSPARENT: &str = r#"
#[trust_vc::spec]
fn sq(x: u64) -> u64 { x * x }

#[trust_vc::broadcast]
#[trust_vc::trigger(sq(x))]
fn sq_zero_is_zero(x: u64) { trust_vc::ensures!(sq(0u64) == 0u64); }

#[trust_vc::ensures(result == 0u64)]
pub fn consumes_good_lemma() -> u64 { sq(0u64) }
"#;

/// A legitimate GUARDED lemma plus two consumers: one that establishes the
/// lemma's `requires` and one that does not.
const GOOD_GUARDED: &str = r#"
#[trust_vc::spec]
fn idf(x: u64) -> u64 { x }

#[trust_vc::broadcast]
#[trust_vc::trigger(idf(x))]
fn idf_ge(x: u64) { trust_vc::requires!(x > 5u64); trust_vc::ensures!(idf(x) > 5u64); }

#[trust_vc::requires(k > 5u64)]
#[trust_vc::ensures(result > 5u64)]
pub fn consumes_guarded(k: u64) -> u64 { idf(k) }

#[trust_vc::ensures(result > 5u64)]
pub fn consumes_unguarded(k: u64) -> u64 { idf(k) }
"#;

/// A lemma whose `ensures` genuinely follows from a transparent spec fn must
/// keep working. If this fails after the fix, the fix suppressed a SOUND axiom —
/// that is over-rejection, and it means the body check is too strict rather than
/// that the capability should go.
#[test]
fn a_legitimate_lemma_over_a_transparent_spec_fn_still_verifies() {
    let result = verify("good", "consumes_good_lemma", GOOD_TRANSPARENT);
    assert!(
        matches!(result, VerifyResult::Verified),
        "CAPABILITY: a broadcast lemma whose `ensures` follows from a transparent spec fn's \
         own definition must remain usable — losing this means the fix deleted the feature \
         rather than justifying it: {result:?}"
    );
}

/// Same, for the guarded form: a consumer that HAS established the lemma's
/// `requires` may use its `ensures`.
#[test]
fn a_guarded_lemma_is_usable_by_a_caller_that_establishes_its_requires() {
    let result = verify("guarded", "consumes_guarded", GOOD_GUARDED);
    assert!(
        matches!(result, VerifyResult::Verified),
        "CAPABILITY: a caller that establishes the lemma's `requires` must be able to use its \
         `ensures`: {result:?}"
    );
}

/// The counterpart, already sound today: a caller that has NOT established the
/// lemma's `requires` must not get its `ensures`. This is the `requires`->guard
/// fold, and it is what makes the pin above safe to assert — without it, "usable"
/// would mean "usable unconditionally", which is itself a hole.
#[test]
fn a_guarded_lemma_is_not_usable_by_a_caller_lacking_its_requires() {
    let result = verify("unguarded", "consumes_unguarded", GOOD_GUARDED);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "SOUNDNESS: the `requires`->guard fold must keep a caller that has not established \
         `x > 5` from concluding `idf(k) > 5`; verifying here would mean the lemma published a \
         bare unconditional `ensures`: {result:?}"
    );
}

/// A legitimate lemma over an `#[trust_vc::opaque]` spec fn: `ofn(x) == x` IS
/// true of the body, it just cannot be seen without revealing.
const GOOD_OPAQUE: &str = r#"
#[trust_vc::opaque]
#[trust_vc::spec]
fn ofn(x: u64) -> u64 { x }

#[trust_vc::broadcast]
#[trust_vc::trigger(ofn(x))]
fn ofn_is_identity(x: u64) { trust_vc::ensures!(ofn(x) == x); }

#[trust_vc::ensures(result == 7u64)]
pub fn consumes_opaque_lemma() -> u64 { ofn(7u64) }
"#;

/// THE PIN FOR THE REVEAL DECISION — the one this change could most easily get
/// wrong in a way that still looks correct.
///
/// An opaque spec fn contributes no body axiom to an ordinary context. If the
/// check does not seed the TRUE definitions (`apply_all_specs_revealed`), then
/// `ensures!(ofn(x) == x)` is as unprovable as the bogus `bcf(x) == 42` above,
/// and BOTH get dropped. The defect witness still flips, so the change looks
/// like a working fix while silently deleting every legitimate lemma over an
/// opaque function — `broadcast_use_soundness` and the `broadcast_forall`
/// corpus rows are the only other alarms.
///
/// Distinct from `a_legitimate_lemma_over_a_transparent_spec_fn_still_verifies`:
/// a transparent fn's axiom is present anyway, so that pin passes even with the
/// reveal omitted. This one does not.
#[test]
fn a_legitimate_lemma_over_an_opaque_spec_fn_still_verifies() {
    let result = verify("goodopaque", "consumes_opaque_lemma", GOOD_OPAQUE);
    assert!(
        matches!(result, VerifyResult::Verified),
        "CAPABILITY: `ofn(x) == x` is TRUE of the opaque body, so the lemma must still \
         publish. Failing here means the check no longer seeds the revealed definitions and \
         is dropping every lemma over an opaque spec fn: {result:?}"
    );
}

/// A lemma that does its work in the BODY: the `ensures` follows from an
/// `assert!` proof step, not from the contract alone.
const PROOF_STEP_LEMMA: &str = r#"
#[trust_vc::opaque]
#[trust_vc::spec]
fn psf(x: u64) -> u64 { x + 1u64 }

#[trust_vc::broadcast]
#[trust_vc::trigger(psf(x))]
fn psf_step(x: u64) {
    trust_vc::requires!(x < 100u64);
    trust_vc::assert!(psf(x) == x + 1u64);
    trust_vc::ensures!(psf(x) > x);
}

#[trust_vc::requires(k < 100u64)]
#[trust_vc::ensures(result > k)]
pub fn consumes_proof_step_lemma(k: u64) -> u64 { psf(k) }
"#;

/// A PROOF-STEP-CARRYING lemma must still publish.
///
/// `body_broadcast_clause_exprs` reads only top-level contract macros, so the
/// check judged every lemma on its contract alone. A lemma carrying `assert!`
/// steps was therefore judged as if those steps were not there — over-rejection,
/// never a hole. Body asserts are now discharged IN ORDER before the `ensures`,
/// each becoming a usable fact once proven. They are ASSERTED, never assumed:
/// assuming them would let a lemma bootstrap itself from an unproven step, which
/// is exactly the hole this check exists to close.
///
/// WHAT THIS TEST DOES AND DOES NOT SHOW — measured, not assumed. It pins that a
/// lemma carrying a proof step still publishes, i.e. the step does not break
/// admission. It does NOT demonstrate that the step is LOAD-BEARING: with the
/// step-threading neutered this fixture still passes, because the check base
/// seeds revealed definitions and `psf(x) == x + 1` is already known, making the
/// `assert!` redundant. Constructing a case where a step is genuinely required
/// means relying on the solver needing a hint (e.g. nonlinear instantiation),
/// which is exactly the kind of fixture that goes flaky across an ay pin — so it
/// is deliberately not attempted here. Treat the ordering/assert-not-assume
/// semantics as reviewed-by-construction, and this test as the admission guard.
fn a_lemma_that_proves_its_ensures_in_the_body_still_publishes() {
    let result = verify("proofstep", "consumes_proof_step_lemma", PROOF_STEP_LEMMA);
    assert!(
        matches!(result, VerifyResult::Verified),
        "CAPABILITY: a broadcast lemma whose `ensures` follows from an `assert!` proof step \
         must still publish its axiom. Failing here means the check is judging lemmas on \
         their contract alone again: {result:?}"
    );
}
