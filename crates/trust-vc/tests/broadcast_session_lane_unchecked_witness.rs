// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! REGRESSION GUARD for a fixed cardinal false-verify (was a defect witness;
//! the fix landed and flipped it).
//!
//! The SESSION / proc-macro broadcast lane published a lemma's `ensures` as a
//! global axiom WITHOUT checking the lemma establishes it — the same cardinal
//! false-verify closed on the FILE path at `63ac39c0`, surviving in the second
//! lane. Both lanes are now closed.
//!
//! MECHANISM. `broadcast_state.rs` (~:262) does not build an axiom from parsed
//! source; it EXECUTES the lemma body under `IN_BROADCAST_MODE`, then walks the
//! obligations recorded since `start_idx` and flips each `ObligationKind::Ensures`
//! in place to `ObligationKind::BroadcastAssume`, renaming it `broadcast_{name}`.
//! An obligation that would have been ASSERTED against the body becomes an
//! ASSUMPTION handed to every caller. Nothing checks it in between.
//!
//! WHY IT IS CARDINAL. The published axiom is not merely unproven, it is FALSE
//! of the actual body — `sess_bogus_fn`'s body is `x`, so `sess_bogus_fn(x) == 42`
//! fails for every `x != 42`. A false axiom is a contradictory premise, and a
//! contradictory premise proves anything.
//!
//! THE FIX: `suppress_unestablished_session_broadcast_axioms`
//! (`verification_bridge.rs`) discharges `guard |- ensures` per `broadcast_*`
//! axiom in a discarded child and drops the axiom unless it verifies.
//!
//! It runs AFTER collection completes, not at the flip. That is what avoids the
//! hazard: `start_idx` (`BROADCAST_OBLIGATION_START`) is an INDEX into
//! `context.obligations`, so verifying mid-harvest while that index is live
//! risks invalidating it. Same reason the file-path check runs after extraction.
//!
//! Unlike the file path, NO catalog seeding is needed here — measured, the
//! collected session context ALREADY carries the definitional `__body_axiom_*`
//! obligations, which is what lets the honest control below still verify.

mod common;

use trust_vc::{broadcast, spec};
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

#[spec]
#[trust_vc::opaque]
fn sess_bogus_fn(x: u64) -> u64 {
    x
}

#[spec]
#[trust_vc::opaque]
fn sess_honest_fn(x: u64) -> u64 {
    x
}

/// BOGUS: the body is `x`, so this `ensures` is FALSE for every `x != 42`.
#[broadcast]
#[trust_vc::trigger(sess_bogus_fn(x))]
fn lemma_sess_bogus(x: u64) {
    trust_vc::ensures!(sess_bogus_fn(x) == 42u64);
}

/// HONEST: `sess_honest_fn(x) == x` IS true of the body.
#[broadcast]
#[trust_vc::trigger(sess_honest_fn(x))]
fn lemma_sess_honest(x: u64) {
    trust_vc::ensures!(sess_honest_fn(x) == x);
}

fn verify_case<F>(case: F) -> VerifyResult
where
    F: FnOnce(),
{
    common::with_clean_verification(|| {
        verify_macro::set_proof_mode(true);
        case();
        verify_macro::set_proof_mode(false);
        VerificationPipeline::collect_from_macros().verify()
    })
}

/// The control. An HONEST lemma over an opaque spec fn publishes a true axiom
/// and its consumer verifies. This is the capability that must survive a fix,
/// and it is what makes the witness below attributable to the lemma being
/// UNCHECKED rather than to broadcast being broken generally.
#[test]
fn an_honest_session_lemma_publishes_a_usable_axiom() {
    let result = verify_case(|| {
        let _ = sess_honest_fn(0u64);
        lemma_sess_honest(0u64);
        trust_vc::assert!(sess_honest_fn(7u64) == 7u64);
    });
    assert!(
        matches!(result, VerifyResult::Verified),
        "control: an honest session-lane broadcast lemma must publish a usable axiom: {result:?}"
    );
}

/// THE GUARD. Identical shape to the control; the only difference is that the
/// lemma's `ensures` is FALSE of its own body.
///
/// Before the fix this VERIFIED — the lemma's axiom was published unchecked and
/// the caller proved `sess_bogus_fn(7) == 42`, which is false. A false axiom is
/// a contradictory premise, so it proves anything.
#[test]
fn session_lane_does_not_publish_an_unchecked_lemma_axiom() {
    let result = verify_case(|| {
        let _ = sess_bogus_fn(0u64);
        lemma_sess_bogus(0u64);
        trust_vc::assert!(sess_bogus_fn(7u64) == 42u64);
    });
    assert!(
        !matches!(result, VerifyResult::Verified),
        "REGRESSION: a session-lane broadcast lemma whose `ensures` is FALSE of its own body \
         must not have its axiom published. Verifying here means the unchecked axiom is being \
         trusted again. Got: {result:?}"
    );
}
