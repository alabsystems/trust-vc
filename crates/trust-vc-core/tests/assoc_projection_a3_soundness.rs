// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Adversarial soundness regression for Phase A3 (associated-type projection): a
//! parameter typed by a fully-qualified projection `<Concrete as Trait>::Assoc`
//! resolves to the concrete type the impl binds (`type Assoc = T;`) at target
//! lifting, landing in the parameter's OWN sort.
//!
//! The cardinal invariant (the sort-divergence trap): the resolved sort must be
//! the sort the impl ACTUALLY binds — never silently coerced to the declared
//! abstract slot's sort, nor to an unbounded `int`. So:
//!   * a u8-bound projection param verifies `x <= 255` (bounded u8 tautology),
//!   * the SAME `x <= 255` fact Counterexamples for a u16-bound projection
//!     (FALSE-VERIFY TRAP: a Verified would be the sort-divergence unsoundness),
//!   * a u16-bound projection verifies `x <= 65535` (resolved to the FULL,
//!     correctly-sized u16 — resolution is per-impl exact and load-bearing),
//!   * `x < 255` Counterexamples for the u8 projection (the u8 upper value is
//!     reachable — the sort is load-bearing, not vacuous).
//!
//! A fail-closed Error/Unknown on any Verified/Counterexample case here would
//! mean the projection was recognized-but-not-resolved (inert recognition),
//! which the strict `matches!` assertions below also catch.
//!
//! See `AssocProjectionResolver` / `collect_assoc_projection_bindings` in
//! `vc_extraction/function_discovery.rs` and the target-lifting seam in
//! `extract_verification_conditions_from_parts_inner` (`vc_extraction.rs`).

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn repro_path() -> String {
    format!(
        "{}/tests/data/assoc_projection_a3_repro.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verdict(func: &str) -> VerifyResult {
    verify_function_from_file(&repro_path(), func)
        .unwrap_or_else(|e| panic!("extract+verify `{func}` failed: {e:?}"))
}

fn assert_verified(func: &str) {
    let v = verdict(func);
    assert!(
        matches!(v, VerifyResult::Verified),
        "`{func}` should verify (projection resolved to its concrete sort); got {v:?}"
    );
}

fn assert_counterexample(func: &str) {
    let v = verdict(func);
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "`{func}` should Counterexample (projection resolved to its concrete sort); got {v:?}"
    );
}

/// TARGET analog: the u8-bound projection param verifies the u8 upper-bound
/// tautology `x <= 255`. Also proves the resolved type is a BOUNDED bitvector
/// (an unbounded `int` would Counterexample here).
#[test]
fn param_projection_u8_upper_bound_verifies() {
    assert_verified("param_projection_u8_upper_bound_verified");
}

/// LOAD-BEARING: the u8 upper value 255 is reachable, so the strict `x < 255`
/// must Counterexample — the param genuinely ranges the full u8, not a narrowed
/// or constant slot.
#[test]
fn param_projection_u8_strict_bound_counterexamples() {
    assert_counterexample("param_projection_u8_strict_bound_counterexample");
}

/// FALSE-VERIFY TRAP: the SAME `<= 255` fact that HOLDS for the u8 projection
/// must FAIL for a projection resolved to u16 (range to 65535). A Verified here
/// is the cardinal sort-divergence false-verify.
#[test]
fn param_projection_u16_overstrong_counterexamples() {
    assert_counterexample("param_projection_u16_overstrong_counterexample");
}

/// The u16 projection resolves to the FULL u16 range (`x <= 65535` verifies).
/// Together with the CX above, this proves resolution is per-impl exact:
/// `ProjU16Struct -> u16` is distinct from `ProjU8Struct -> u8`, and the resolved
/// sort — not merely the recognition of a projection — is what the verdict turns
/// on.
#[test]
fn param_projection_u16_full_bound_verifies() {
    assert_verified("param_projection_u16_full_bound_verified");
}
