// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! THE THREE-WAY PIN on `const_pattern_desugar`'s scope model.
//!
//! `ScopeScan` collected `const`/`static` names from the WHOLE syntax tree. In
//! Rust a `const` declared inside one function's BODY is not in scope in
//! another function, so a bare arm pattern of that name in an unrelated
//! function is a BINDER — and this pass called it a const-pattern marker.
//!
//! MEASURED at `0bd75360` (pre-fix), cache off, over the three fixtures below,
//! whose `cv_probe` is byte-identical in all three:
//!
//!   leg 1  the probe alone                          Verified
//!   leg 2  + an unrelated function whose BODY
//!          declares `const cv`                      NOT verified  <- the defect
//!   leg 3  + a MODULE-scope `const cv`              NOT verified
//!
//! A const in a function the probe never calls decided the probe's verdict.
//!
//! Two legs are not enough to key a fix on. "Narrow the scan to the target's
//! own body" also makes leg 2 pass, and it makes LEG 3 BIND — a false verify,
//! because a module-scope const genuinely IS in scope in every function of that
//! module. The three legs together say the model is right rather than merely
//! narrower: leg 1 and leg 2 must AGREE (an out-of-scope declaration changes
//! nothing) and leg 3 must DISAGREE with both (an in-scope one changes
//! everything).
//!
//! Each leg carries its own refuted discriminator, so "verified" here can never
//! be the vacuous answer.
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verdict(file: &str, func: &str) -> VerifyResult {
    let path = format!("{}/tests/data/{file}", env!("CARGO_MANIFEST_DIR"));
    trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
        verify_function_from_file(&path, func)
    })
    .unwrap_or_else(|e| panic!("extract+verify `{func}` in `{file}` failed: {e:?}"))
}

const ALONE: &str = "const_scope_triple_alone.rs";
const BODY_CONST: &str = "const_scope_triple_body_const.rs";
const MODULE_CONST: &str = "const_scope_triple_module_const.rs";

/// LEG 1. A bare binder arm binds the scrutinee, so `result == n` holds.
#[test]
fn leg1_the_probe_alone_binds_and_verifies() {
    let v = verdict(ALONE, "cv_probe");
    assert!(
        matches!(v, VerifyResult::Verified),
        "CAPABILITY: an ordinary binder arm must still BIND; got {v:?}"
    );
}

/// The discriminator for leg 1: a binder supplies no value fact.
#[test]
fn leg1_liar_must_not_verify() {
    let v = verdict(ALONE, "cv_probe_liar_must_not_verify");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "a binder constrains nothing, so `result == n + 1` must refute; got {v:?}"
    );
}

/// LEG 2 — THE DEFECT. A `const` in ANOTHER function's body is not in scope
/// here, so it must not move this verdict.
#[test]
fn leg2_an_unrelated_bodys_const_does_not_move_this_verdict() {
    let v = verdict(BODY_CONST, "cv_probe");
    assert!(
        matches!(v, VerifyResult::Verified),
        "SCOPE CONTAMINATION: `const cv` lives in `cv_other`'s BODY, which \
         `cv_probe` never calls and cannot see; the arm is a BINDER and the \
         verdict must equal leg 1's; got {v:?}"
    );
}

#[test]
fn leg2_liar_must_not_verify() {
    let v = verdict(BODY_CONST, "cv_probe_liar_must_not_verify");
    assert!(!matches!(v, VerifyResult::Verified), "got {v:?}");
}

/// Stated as the comparison the fixtures were built for: legs 1 and 2 differ by
/// one function the probe never calls, so their verdicts must be the same one.
#[test]
fn leg1_and_leg2_agree() {
    let alone = verdict(ALONE, "cv_probe");
    let contaminated = verdict(BODY_CONST, "cv_probe");
    assert_eq!(
        std::mem::discriminant(&alone),
        std::mem::discriminant(&contaminated),
        "the only difference between these files is a const inside a function \
         the probe never calls: {alone:?} vs {contaminated:?}"
    );
}

/// LEG 3 — THE OTHER DIRECTION, and the reason a two-leg fix is not a fix. A
/// MODULE-scope const IS in scope in every function of that module, so this arm
/// is a const pattern; `[u64; 3]` is not foldable, so it must fail CLOSED.
#[test]
fn leg3_a_module_scope_const_is_still_a_const_pattern() {
    let v = verdict(MODULE_CONST, "cv_probe");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "FALSE VERIFY: `cv` is declared at MODULE scope, so `match n {{ cv => }}` \
         is a refutable const pattern and not a binder — a scan narrowed to the \
         target's own body would bind it and verify; got {v:?}"
    );
}

/// Leg 3 must DISAGREE with leg 1, or the pin above is satisfied by a pass that
/// simply stopped working.
#[test]
fn leg3_disagrees_with_leg1() {
    let alone = verdict(ALONE, "cv_probe");
    let module_scope = verdict(MODULE_CONST, "cv_probe");
    assert_ne!(
        std::mem::discriminant(&alone),
        std::mem::discriminant(&module_scope),
        "an IN-SCOPE const must change this verdict and an out-of-scope one must \
         not; got {alone:?} vs {module_scope:?}"
    );
}

/// THE CAPABILITY PIN for leg 3: failing closed is not the same as modelling
/// the const. A foldable module-scope const must still supply its value.
#[test]
fn leg3_a_foldable_module_scope_const_supplies_its_value() {
    let v = verdict(MODULE_CONST, "cw_value_is_modeled");
    assert!(
        matches!(v, VerifyResult::Verified),
        "a file-scope `const cw: u64 = 5` arm must supply `n == 5`; got {v:?}"
    );
}

#[test]
fn leg3_capability_liar_must_not_verify() {
    let v = verdict(MODULE_CONST, "cw_value_liar_must_not_verify");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "the arm supplies `n == 5`, so `n == 6` must refute — otherwise the \
         capability pin above is vacuous; got {v:?}"
    );
}
