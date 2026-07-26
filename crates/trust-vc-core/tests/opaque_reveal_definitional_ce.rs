// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Opaque/reveal definitional-unfolding battery (upstream Verus basic.rs
//! `test_spec_fn`, pinned ref a40d57c73650cd3648b09386bfdb96ab5c270626).
//!
//! The gap this pins closed: a REVEALED opaque (or nested non-opaque) spec-fn
//! refutation used to degrade to `Unknown{Incompleteness}` ("(incomplete
//! quantifier-ematching-exists)") instead of the model-bearing
//! `Counterexample` upstream Verus reports (`assert_one_fails`). Root cause:
//! ay fail-closes SAT finalization when the candidate model cannot be
//! certified against a two-level definitional `forall` chain
//! (`f3-def` whose RHS applies `f1` to the bound variables). Fix: the
//! demand-inline retry (#2655) now adopts a model-validated `Counterexample`
//! from the exact inline-substituted query when the baseline outcome was a
//! fail-closed `Unknown` — definitional unfolding in the refutation
//! direction, mirroring the Verified direction it always had.
//!
//! SOUNDNESS PINS (must stay red-on-leak forever):
//!  * an UNREVEALED opaque body must never prove OR refute a goal
//!    (`test_opaque_no_leak*`) — the cardinal proves-more-than-Verus
//!    direction;
//!  * reveal! in one function must not apply to another
//!    (`test_reveal_does_not_leak_across_fns`).

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn battery_path() -> String {
    format!(
        "{}/tests/data/opaque_reveal_definitional_ce.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verdict(func: &str) -> VerifyResult {
    verify_function_from_file(&battery_path(), func)
        .unwrap_or_else(|err| panic!("extract/verify {func} must not error: {err:?}"))
}

/// (a) The faithful upstream `test_spec_fn` sequence: the final
/// `assert(f3(a,b))` is the ONE failing assertion, and it must surface as a
/// genuine model-bearing Counterexample (upstream `assert_one_fails`), not a
/// model-less Unknown.
#[test]
fn upstream_test_spec_fn_shape_fails_with_counterexample() {
    let result = verdict("test_spec_fn_full");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "test_spec_fn_full: the failing assert must be a genuine \
         Counterexample (upstream assert_one_fails), got {result:?}"
    );
}

/// (a) The same sequence WITHOUT the failing assert verifies — pins that the
/// first two asserts (`f1(a,b)` under the revealed f2 assumption, and the
/// revealed `f3(b,a)`) are Verified, so the full-shape failure above is
/// attributable to exactly the last assert.
#[test]
fn upstream_test_spec_fn_verified_prefix_verifies() {
    let result = verdict("test_spec_fn_verified_only");
    assert!(
        matches!(result, VerifyResult::Verified),
        "test_spec_fn_verified_only must verify, got {result:?}"
    );
}

/// (b) Revealed-opaque refutation (the exact two-level definitional-chain
/// class) and its controls are all model-bearing Counterexamples.
#[test]
fn revealed_and_nested_refutations_are_counterexamples() {
    for func in [
        "test_ce_revealed_opaque_only", // revealed opaque, two-level chain
        "test_ce_plain_spec_fn",        // plain spec fn control
        "test_ce_let_body_spec_fn",     // let-body control
        "test_ce_nested_plain_chain",   // non-opaque two-level chain
    ] {
        let result = verdict(func);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{func}: expected a genuine Counterexample, got {result:?}"
        );
    }
}

/// (b) Revealed-opaque verified direction still verifies.
#[test]
fn revealed_opaque_verifies() {
    let result = verdict("test_opaque_revealed_verifies");
    assert!(
        matches!(result, VerifyResult::Verified),
        "test_opaque_revealed_verifies must verify, got {result:?}"
    );
}

/// (c) OPACITY PIN, prove direction: an assert provable only via the hidden
/// body must NOT verify without reveal!. Guards the demand-inline catalog
/// (an unrevealed opaque body must never be inlined) and the broadcast gate.
#[test]
fn unrevealed_opaque_never_proves_from_its_body() {
    let result = verdict("test_opaque_no_leak");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "test_opaque_no_leak: unrevealed opaque body leaked into a proof \
         (proves more than Verus!), got {result:?}"
    );
}

/// (c) OPACITY PIN, refute direction: the negated goal must not verify from
/// the hidden body either — definitional unfolding is forbidden in BOTH
/// directions while unrevealed.
#[test]
fn unrevealed_opaque_never_refutes_from_its_body() {
    let result = verdict("test_opaque_no_leak_ce_direction");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "test_opaque_no_leak_ce_direction: unrevealed opaque body leaked into \
         a refutation proof, got {result:?}"
    );
}

/// (d) reveal! scoping: sibling functions in the data file reveal f3; a
/// function without its own reveal must still see f3 as strictly opaque.
#[test]
fn reveal_does_not_leak_across_functions() {
    let result = verdict("test_reveal_does_not_leak_across_fns");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "reveal! leaked across function boundaries, got {result:?}"
    );
}

/// (e) KNOWN FIDELITY DIVERGENCE (documented, NOT desired): trust-vc's
/// query-granular reveal verifies an assert placed BEFORE the reveal!, where
/// Verus's flow-ordered fuel assume rejects it. Pinned so a future
/// statement-ordered reveal implementation flips this consciously (this test
/// should then assert NOT-Verified and the divergence note in the data file
/// should be removed).
#[test]
fn assert_before_reveal_divergence_pin_currently_verifies() {
    let result = verdict("test_assert_before_reveal_divergence_pin");
    assert!(
        matches!(result, VerifyResult::Verified),
        "divergence pin moved: assert-before-reveal no longer verifies — if \
         statement-ordered reveal landed, flip this pin to NOT-Verified; got \
         {result:?}"
    );
}

/// (f) #2785: the file path now supports `hide!`. The EXACT upstream
/// `test_spec_fn` sequence WITH `hide(f2)` must still surface the last assert
/// as a genuine Counterexample (upstream `assert_one_fails`) — the hide!/reveal!
/// interleave guard admits it (the `[hide, reveal)` window brackets only an
/// `assume!`, not a checked obligation).
#[test]
fn upstream_test_spec_fn_with_hide_fails_with_counterexample() {
    let result = verdict("test_spec_fn_full_with_hide");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "test_spec_fn_full_with_hide: the failing assert must be a genuine \
         Counterexample (upstream assert_one_fails), got {result:?}"
    );
}

/// (f) #2785: `hide(f1)` with no reveal re-opaques f1 query-wide. `f1(a, a)` is
/// TRUE via the body but unprovable with f1 uninterpreted, so this must NOT
/// verify. If `hide!` were a silent no-op, f1 would stay visible and this would
/// wrongly Verify (proves-more-than-Verus).
#[test]
fn hide_without_reveal_re_opaques_body() {
    let result = verdict("test_hide_without_reveal_hides_body");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "test_hide_without_reveal_hides_body: hide! did not re-opaque f1 \
         (proves more than Verus!), got {result:?}"
    );
}

/// (f) #2785: a benign `hide(f1); reveal(f1)` pair (nothing checked bracketed)
/// restores f1's visibility, so `f1(a, a)` (a <= a) verifies. Pins that the
/// interleave guard does NOT over-reject well-formed hide/reveal pairs.
#[test]
fn hide_then_reveal_restores_visibility() {
    let result = verdict("test_hide_then_reveal_verifies");
    assert!(
        matches!(result, VerifyResult::Verified),
        "test_hide_then_reveal_verifies must verify, got {result:?}"
    );
}

/// (f) #2785 SOUNDNESS PIN (the cardinal proves-more direction): a CHECKED
/// assert `f1(a, a)` bracketed by `hide(f1) … reveal(f1)` — provable ONLY via
/// f1's body, which Verus has re-opaqued in this window, so Verus FAILS it —
/// must be REJECTED fail-closed. The SAME assert VERIFIES in
/// `hide_then_reveal_restores_visibility` (it sits after the reveal), so the
/// query-granular reveal-wins model would otherwise verify what Verus refutes.
/// The guard fails the query closed; the result must never be `Verified` (an
/// `Err` fail-closed is the expected outcome).
#[test]
fn hide_reveal_bracketing_checked_assert_is_rejected() {
    let result = verify_function_from_file(
        &battery_path(),
        "test_hide_reveal_brackets_assert_fails_closed",
    );
    match result {
        Err(_) => {} // fail-closed at prepare(): the intended, sound outcome
        Ok(verdict) => assert!(
            !matches!(verdict, VerifyResult::Verified),
            "hide!(f2) … reveal!(f2) bracketing a checked assert VERIFIED \
             (proves more than Verus!) — the interleave guard failed, got \
             {verdict:?}"
        ),
    }
}
