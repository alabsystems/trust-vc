// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Adversarial soundness regression for Phase C part 2 DIRECT APPLICATION
//! `f(arg)` of a KNOWN LOCAL `trust_vc::closure!` literal (unary, over modelable
//! value sorts). The call lowers to the OPAQUE, DISJOINT `spec_fn_apply` UF the
//! `.call` method path already uses; the extraction seam
//! `record_closure_application_obligations` PROVES `f.requires(arg)` (an
//! obligation) and ASSUMES `f.ensures(arg, f(arg))` binding the REAL returned
//! term.
//!
//! CARDINAL INVARIANT: the assumed ensures is ONLY ever the def-side-CHECKED
//! written clause. A closure is `SpecFn`-typed AND registered iff
//! `emit_closure_reflection_axioms` ran, co-located with the independent def-side
//! obligation whose failure poisons the parent (`record_closure_def_side_failure`
//! -> `closure_def_side_failure`, which short-circuits the whole verdict). So a
//! lying closure (body does not establish its ensures) sinks the entire function
//! regardless of what the call site assumes — see `d2_cardinal_unchecked_ensures_cx`.
//!
//! CACHE DISCIPLINE (mandatory): the persistent on-disk verification cache stores
//! only `Verified` results and survives `cargo clean -p`. A soundness probe that
//! asserts a NON-verifying verdict must never trust a stale `Verified`, so the
//! verify helper disables the cache (`TRUST_VC_DISABLE_VC_CACHE=1`). ALL probes
//! run cache-off.
//!
//! `assert_not_verified` treats an extraction `Err` and any solver non-`Verified`
//! (including `Unknown`) as a sound non-verify; acceptance probes require exactly
//! `Verified` (an `Unknown` is a FAILURE).
//!
//! See `dispatch/calls.rs` (unary SpecFn application guard),
//! `vc_extraction/body_extract.rs::record_closure_application_obligations`, and
//! the reflection / def-side companion suites `closure_reflection_soundness.rs`,
//! `closure_spec_soundness.rs`.

use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn repro_path() -> String {
    format!(
        "{}/tests/data/closure_direct_application_soundness_repro.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verify(func: &str) -> Result<VerifyResult, trust_vc_core::TrustVcError> {
    // SOUNDNESS-CRITICAL: recompute every verdict cache-off. A single stale
    // `Verified` — e.g. one written before this increment compiled in — would
    // otherwise be served forever and mask a real false-verify.
    trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
        verify_function_from_file(&repro_path(), func)
    })
}

fn verdict(func: &str) -> VerifyResult {
    verify(func).unwrap_or_else(|e| panic!("extract+verify `{func}` failed: {e:?}"))
}

fn assert_not_verified(func: &str) {
    match verify(func) {
        Ok(VerifyResult::Verified) => {
            panic!("DIRECT-APPLICATION FALSE-VERIFY: `{func}` must not verify")
        }
        // An extraction Err (capture guard / deferred application) is a sound
        // non-verify; a solver non-Verified verdict (incl Unknown) likewise.
        _ => {}
    }
}

/// The number of proof obligations `func` collects (cache-independent; extraction
/// only). Used to pin that the bad-call-requires probe actually EMITS the
/// prove-requires obligation rather than vacuously passing.
fn obligation_count(func: &str) -> usize {
    let source = std::fs::read_to_string(repro_path()).expect("repro fixture should be readable");
    let file = syn::parse_file(&source).expect("repro fixture should parse");
    let item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(f) if f.sig.ident == func => Some(f),
            _ => None,
        })
        .unwrap_or_else(|| panic!("`{func}` should exist in the repro fixture"));
    extract_verification_conditions_with_file_context(&file, item)
        .unwrap_or_else(|e| panic!("`{func}` should extract: {e:?}"))
        .obligations()
        .len()
}

#[test]
fn d1_direct_application_verified() {
    // The increment's success signal / the old reflection probe7 FLIP: verifies
    // ONLY if the relaxed guard lowers `f(2)` to `spec_fn_apply`, the seam wires
    // prove-requires (2 == 2) + assume-ensures (f(2) == 2), AND the assert reads
    // the identical `spec_fn_apply` term. A solver `Unknown` here is a FAILURE.
    let v = verdict("d1_direct_application_verified");
    assert!(
        matches!(v, VerifyResult::Verified),
        "direct application of a def-side-valid unary closure should verify; got {v:?}"
    );
}

#[test]
fn d1b_assert_embedded_application_verified() {
    // The assert-EMBEDDED acceptance (the flipped corpus-row shape): the call is
    // directly inside `assert!(f(2) == 2)`, exercising the assert-condition seam.
    let v = verdict("d1b_assert_embedded_application_verified");
    assert!(
        matches!(v, VerifyResult::Verified),
        "assert-embedded direct application of a def-side-valid closure should verify; got {v:?}"
    );
}

#[test]
fn d2b_assert_embedded_unchecked_ensures_cx() {
    // Cardinal, assert-embedded: the def-side counterexample poisons the parent
    // even though the assert-condition assume would pin `f(3) == 100`.
    assert_not_verified("d2b_assert_embedded_unchecked_ensures_cx");
}

#[test]
fn d2_cardinal_unchecked_ensures_cx() {
    // THE cardinal unchecked-ensures probe: the def-side COUNTEREXAMPLES (body `y`
    // does not establish `z == 100`) and poisons the parent; the call-site assume
    // `f(3) == 100` NEVER rescues it. A `Verified` here HALTS the increment.
    assert_not_verified("d2_cardinal_unchecked_ensures_cx");
}

#[test]
fn d3_consume_ensures_cx() {
    // The mutation-sensitive probe: the assume pins ONLY `f(2) == 2`, so the
    // perturbed assert `t == 3` counterexamples.
    let v = verdict("d3_consume_ensures_cx");
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "a perturbed direct-application result should counterexample; got {v:?}"
    );
}

#[test]
fn d4_bad_call_requires_cx() {
    // The prove-requires obligation `3 == 2` must be EMITTED (>= 1 obligation) and
    // must COUNTEREXAMPLE.
    assert!(
        obligation_count("d4_bad_call_requires_cx") >= 1,
        "the bad-call-requires probe must emit at least the prove-requires obligation"
    );
    let v = verdict("d4_bad_call_requires_cx");
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "an argument violating the closure requires should counterexample; got {v:?}"
    );
}

#[test]
fn d5_vacuous_requires_blocks_cx() {
    // Def-side is a VacuousTruth-PASS, but the call-site prove-requires asserts
    // `false` and counterexamples; ensures is never reached.
    let v = verdict("d5_vacuous_requires_blocks_cx");
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "a vacuous `requires(false)` must still block at the call site; got {v:?}"
    );
}

#[test]
fn d6_capture_stays_fail_closed() {
    assert_not_verified("d6_capture_stays_fail_closed");
}

#[test]
fn d7_bare_literal_capture_free_verifies() {
    // A BARE (non-`closure!`) capture-free closure applied by name is now inlined
    // at the call site — `f(2)` models as its body `2`, so the TRUE assertion
    // `t == 2` VERIFIES (was fail-closed "unknown return type for function 'f'").
    // This is a value substitution of the REAL body (no trusted/unchecked ensures
    // to poison), so it is sound where the `closure!`-literal contract path needs
    // a def-side check. Captures (`d6`) and free callees still fail closed — see
    // the adversarial `closure_inline_capture_free_capability.rs` companion suite
    // (false ensures must Counterexample; captured `a` must NOT verify).
    let v = verdict("d7_bare_literal_stays_fail_closed");
    assert!(
        matches!(v, VerifyResult::Verified),
        "a bare capture-free closure applied to 2 (`|y| y`) with a true `t == 2` \
         assert should inline+verify; got {v:?}"
    );
}

#[test]
fn d8_loop_body_drop_fails_closed() {
    // Regression witness for the call-ensures leak class: a `Verified` here means
    // the loop-body assume-ensures leaked out of the loop.
    assert_not_verified("d8_loop_body_drop_fails_closed");
}

#[test]
fn d9a_zero_arg_application_deferred() {
    assert_not_verified("d9a_zero_arg_application_deferred");
}

#[test]
fn d9b_two_arg_application_deferred() {
    assert_not_verified("d9b_two_arg_application_deferred");
}

#[test]
fn d10_unmodelable_param_deferred() {
    assert_not_verified("d10_unmodelable_param_deferred");
}
