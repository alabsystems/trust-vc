// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! FV-4 — an exec callee's UNCHECKED `#[ensures]` consumed as a global axiom.
//!
//! `register_exec_callee_postcondition_axioms` (vc_extraction/trait_contracts)
//! publishes the definitional postcondition of a free EXEC function called from
//! a trait DEFAULT body as a body-axiom-shaped broadcast
//! `forall params. <callee>(params) == <rhs>`, so that a conforming default can
//! establish its own `ensures` through the call.
//!
//! THE DEFECT. Nothing checked that the callee's BODY establishes the
//! `#[ensures]` being published, so a LYING callee injected a FALSE axiom:
//!
//!     #[trust_vc::ensures(result == 100u32)] fn liar(a: u32) -> u32 { 3u32 }
//!     #[trust_vc::trait_spec] trait Tr {
//!         #[trust_vc::returns(result)] #[trust_vc::ensures(result == 100u32)]
//!         fn dm(&self) -> u32 { liar(7u32) } }
//!
//! `forall a. liar(a) == 100` is false of the body (`3`), and it is what let the
//! default `dm` "establish" `result == 100`. Same shape as the unchecked
//! broadcast lemma fixed at `63ac39c0`: an unestablished `ensures` published as
//! an axiom and consumed before it is discharged.
//!
//! WHICH CHANNEL — MEASURED, and the measurement moved the test. The defect is
//! observable on the trait default's CONFORMANCE obligation, which is the
//! impl-side report channel `cargo trust-vc check` enumerates (see the
//! attribution note in `trait_default_no_impl_soundness.rs`): before the fix
//! `trait default conformance Tr::dm (no impl)` VERIFIED for the fixture above,
//! so the whole file passed. It is NOT observable on a generic caller's own
//! verdict: `fn consumer<T: Tr>(t: T)` consumes the postcondition axiom
//! `register_trait` publishes for every trait method unconditionally, and it
//! answers `Verified` even with this entire publish site compiled out — that
//! caller-side behaviour belongs to the trait-axiom lane, not here, and asserting
//! it in this file would be a test that passes for a reason unrelated to its
//! subject.
//!
//! THE FIX. The axiom is published only when it is BODY-JUSTIFIED: the callee's
//! single definitional tail expression must BE the `rhs` the postcondition pins
//! the result to. The published equality is then the callee's definition — true
//! by construction, like a spec fn's body axiom — rather than a trusted claim.
//!
//! WHY NOT THE BROADCAST-LEMMA MECHANISM (discharge in a discarded child, drop
//! unless it verifies). MEASURED, and the measurement rejected it: the honest,
//! already pinned callee `#[ensures(result == a + b)] fn add(a: u32, b: u32)
//! -> u32 { a + b }` does NOT verify on its own — its postcondition obligation
//! carries a `possible addition overflow` side condition and Counterexamples at
//! `a = b = u32::MAX`. A verdict gate would have dropped that axiom too and
//! taken the whole parameterised lane red
//! (`trait_default_no_impl_soundness::conforming_default_calling_free_exec_fn_with_args_still_verifies`).
//!
//! THE NARROWNESS PINS ARE THE POINT. "Check the callee" can be implemented as
//! "stop publishing the axiom", which satisfies the witnesses below and silently
//! deletes the round-7 over-rejection fix. The three capability tests at the end
//! are what stop that — each was confirmed to go RED with the publish site
//! neutered, so they are attributable to it and not to the ambient trait axiom.

use trust_vc_core::VerifyResult;

fn write_fixture(label: &str, source: &str) -> std::path::PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "trust_vc_exec_callee_body_justified_{label}_{}.rs",
        std::process::id()
    ));
    std::fs::write(&path, source).expect("write fixture");
    path
}

/// The file's CONFORMANCE verdict: enumerate every conformance obligation and
/// verify each BY NAME, exactly as `cargo trust-vc check` drives it, returning
/// the first non-`Verified` result. This is the channel the trait default's own
/// obligation reports on.
fn conformance_verdict(label: &str, source: &str) -> VerifyResult {
    let path = write_fixture(label, source);
    let path_str = path.to_str().expect("fixture path utf-8");
    let result = match trust_vc_core::list_trait_conformance_obligations(path_str) {
        Ok(names) => {
            assert!(
                !names.is_empty(),
                "fixture declares no conformance obligation at all — the guard would be vacuous"
            );
            let mut verdict = VerifyResult::Verified;
            for name in names {
                match trust_vc_core::verify_trait_conformance_obligation(path_str, &name) {
                    Ok(result) if result.is_verified() => {}
                    Ok(result) => {
                        verdict = result;
                        break;
                    }
                    Err(err) => {
                        verdict = VerifyResult::Error {
                            message: err.to_string(),
                        };
                        break;
                    }
                }
            }
            verdict
        }
        Err(err) => VerifyResult::Error {
            message: err.to_string(),
        },
    };
    let _ = std::fs::remove_file(&path);
    result
}

fn verify_fn(label: &str, source: &str, case: &str) -> VerifyResult {
    let path = write_fixture(label, source);
    let path_str = path.to_str().expect("fixture path utf-8");
    let result = trust_vc_core::verify_function_from_file(path_str, case).unwrap_or_else(|err| {
        VerifyResult::Error {
            message: err.to_string(),
        }
    });
    let _ = std::fs::remove_file(&path);
    result
}

// ===========================================================================
// THE WITNESSES — a lying exec callee must not buy the default a proof.
// ===========================================================================

/// `liar`'s body returns `3`, its `#[ensures]` claims `100`. The trait default
/// `dm` calls it and claims `100` in turn; an all-defaults impl really returns
/// `3`, so the default does NOT establish its postcondition.
const LYING_CALLEE: &str = r#"
#[trust_vc::ensures(result == 100u32)]
fn liar(a: u32) -> u32 { 3u32 }
#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 100u32)]
    fn dm(&self) -> u32 { liar(7u32) }
}
pub fn consumer<T: Tr>(t: T) { trust_vc::assert!(t.dm() == 100u32); }
"#;

/// THE REGRESSION GUARD — this is the exact reproducer, and it VERIFIED on this
/// channel before the fix.
#[test]
fn lying_exec_callee_ensures_does_not_discharge_the_default_conformance() {
    let result = conformance_verdict("witness", LYING_CALLEE);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "CARDINAL FALSE-VERIFY: `liar`'s body returns 3, so the default `dm() {{ liar(7) }}` \
         returns 3 and cannot establish `ensures(result == 100)`. Verifying here means the \
         callee's UNCHECKED `#[ensures(result == 100)]` is being published as a global axiom \
         again and consumed before it is discharged. Got: {result:?}"
    );
}

/// The attribution control: the callee is refuted on its own query, so the
/// fixture's lie is real and the guard above is about the axiom, not about a
/// fixture that cannot be lowered.
#[test]
fn the_lying_callee_is_itself_refuted() {
    let result = verify_fn("witness_callee", LYING_CALLEE, "liar");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "`liar`'s body (3) violates its own `#[ensures(result == 100)]` and must be refuted \
         on its own query; got: {result:?}"
    );
}

/// The same lie in the PARAMETERISED shape, so the fix cannot be a special case
/// for nullary callees: `misadd`'s body returns `a` while its `#[ensures]`
/// claims `a + b`. `misadd(2, 5)` is really 2, so `ensures(result == 7)` on the
/// default is false.
const LYING_CALLEE_WITH_ARGS: &str = r#"
#[trust_vc::ensures(result == a + b)]
fn misadd(a: u32, b: u32) -> u32 { a }
#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { misadd(2u32, 5u32) }
}
pub fn args_consumer<T: Tr>(t: T) { trust_vc::assert!(t.dm() == 7u32); }
"#;

#[test]
fn lying_parameterised_exec_callee_does_not_discharge_the_default_conformance() {
    let result = conformance_verdict("witness_args", LYING_CALLEE_WITH_ARGS);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "`misadd(2, 5)` really returns 2, so the default cannot establish \
         `ensures(result == 7)`; the callee's unchecked `#[ensures(result == a + b)]` must \
         not be published. Got: {result:?}"
    );
}

// ===========================================================================
// NARROWNESS PINS — an HONEST exec callee must STAY usable in a default body.
//
// Each of these was confirmed to go RED with the publish site neutered, so it
// is attributable to this lane. Without them the fix degenerates into "never
// publish the axiom", which re-opens the round-7 over-rejection the publish site
// exists to close.
// ===========================================================================

/// An honest nullary callee: body `7u32`, `ensures(result == 7u32)`.
const HONEST_NULLARY: &str = r#"
#[trust_vc::ensures(result == 7u32)]
fn honest() -> u32 { 7u32 }
#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { honest() }
}
pub fn honest_consumer<T: Tr>(t: T) { trust_vc::assert!(t.dm() == 7u32); }
"#;

#[test]
fn honest_exec_callee_is_still_usable_in_a_trait_default_body() {
    let result = conformance_verdict("pin_nullary", HONEST_NULLARY);
    assert!(
        matches!(result, VerifyResult::Verified),
        "CAPABILITY: `honest`'s body IS the value its `#[ensures]` pins, so the definitional \
         axiom `honest() == 7` is true by construction and the conforming default must still \
         establish its own `ensures`. Failing here means the fix blanket-dropped the lane \
         rather than justifying it: {result:?}"
    );
}

/// An honest PARAMETERISED callee: body `a + b`, `ensures(result == a + b)`.
/// This is the pin the discarded-child mechanism would have broken — `addp`
/// does not verify on its own (overflow at `u32::MAX`), yet its postcondition
/// is literally its definition.
const HONEST_WITH_ARGS: &str = r#"
#[trust_vc::ensures(result == a + b)]
fn addp(a: u32, b: u32) -> u32 { a + b }
#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { addp(2u32, 5u32) }
}
pub fn addp_consumer<T: Tr>(t: T) { trust_vc::assert!(t.dm() == 7u32); }
"#;

#[test]
fn honest_parameterised_exec_callee_is_still_usable_in_a_trait_default_body() {
    let result = conformance_verdict("pin_args", HONEST_WITH_ARGS);
    assert!(
        matches!(result, VerifyResult::Verified),
        "CAPABILITY: `addp`'s body IS its postcondition's `rhs`, so `addp(2, 5) == 7` must \
         still be available to the default. Failing here means the gate is judging the callee \
         on its own VERDICT (which `addp` fails on an unrelated overflow side condition) \
         instead of on whether the axiom is body-justified: {result:?}"
    );
}

/// Notation-only differences must not cost the capability: `return (7);` with a
/// suffix-free literal is the same definition as `ensures(result == 7u32)`.
const HONEST_NOTATION_VARIANT: &str = r#"
#[trust_vc::ensures(result == 7u32)]
fn honest_ret() -> u32 { return (7); }
#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { honest_ret() }
}
pub fn ret_consumer<T: Tr>(t: T) { trust_vc::assert!(t.dm() == 7u32); }
"#;

#[test]
fn honest_callee_written_with_return_and_parens_is_still_usable() {
    let result = conformance_verdict("pin_notation", HONEST_NOTATION_VARIANT);
    assert!(
        matches!(result, VerifyResult::Verified),
        "CAPABILITY: `return (7);` is the same definition as the `rhs` `7u32`; parens, the \
         `return` form and a literal's suffix are notation, not value. Got: {result:?}"
    );
}
