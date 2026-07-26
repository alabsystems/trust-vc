// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Laser wavelength must be within valid CRDS range (200-5000 nm).
#[test]
fn test_crds_wavelength_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength_nm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wavelength_bounds",
        "wavelength_nm >= 200 && wavelength_nm <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wavelength_positive",
        "wavelength_nm > 0 && wavelength_nm <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "CRDS wavelength in [200, 5000] nm is positive and bounded",
    );
}

/// Ringdown time scaled by 100 (units: x100 microseconds) must be positive and bounded.
#[test]
fn test_crds_ringdown_time() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "time_bounds",
        "time_x100 > 0 && time_x100 < 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "time_positive_bounded",
        "time_x100 >= 1 && time_x100 <= 99999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ringdown time x100 in (0, 100000) is at least 1 and at most 99999",
    );
}

/// Mirror reflectivity scaled by 10000 (percent). Typical CRDS mirrors: >99.00% reflectivity.
#[test]
fn test_crds_mirror_reflectivity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("refl_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "refl_bounds",
        "refl_x10000 > 9900 && refl_x10000 < 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "refl_high_quality",
        "refl_x10000 >= 9901 && refl_x10000 <= 9999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mirror reflectivity x10000 in (9900, 10000) is high-quality CRDS range",
    );
}

/// Cavity length scaled by 10 (units: x10 mm). Must be positive and bounded.
#[test]
fn test_crds_cavity_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("len_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "length_bounds",
        "len_x10 > 0 && len_x10 < 30000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "length_positive_bounded",
        "len_x10 >= 1 && len_x10 <= 29999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cavity length x10 in (0, 30000) mm is positive and bounded",
    );
}

/// Detection limit scaled by 10000 (units: x10000 ppb). Must be positive and bounded.
#[test]
fn test_crds_detection_limit() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("limit_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "limit_bounds",
        "limit_x10000 > 0 && limit_x10000 < 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "limit_positive_bounded",
        "limit_x10000 >= 1 && limit_x10000 <= 999999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detection limit x10000 in (0, 1000000) ppb is positive and bounded",
    );
}

/// Number of ringdown events averaged per measurement must be in [1, 100000].
#[test]
fn test_crds_ringdown_event_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("events", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "event_bounds",
        "events >= 1 && events <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "events_positive_bounded",
        "events > 0 && events <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ringdown event count in [1, 100000] is positive and bounded",
    );
}

/// Laser source type: 1=pulsed, 2=CW, 3=broadband. Must be one of these.
#[test]
fn test_crds_laser_source_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("laser", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "laser_type",
        "laser == 1 || laser == 2 || laser == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "laser_valid",
        "laser >= 1 && laser <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "laser source in {1=pulsed, 2=CW, 3=broadband} implies range [1,3]",
    );
}

/// Cavity design type: 1=linear, 2=ring, 3=V-shaped. Must be one of these.
#[test]
fn test_crds_cavity_design_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cavity", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cavity_type",
        "cavity == 1 || cavity == 2 || cavity == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cavity_valid",
        "cavity >= 1 && cavity <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cavity design in {1=linear, 2=ring, 3=V-shaped} implies range [1,3]",
    );
}

/// Detection scheme: 1=single-exponential, 2=phase-shift, 3=optical-feedback.
#[test]
fn test_crds_detection_scheme_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scheme", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "scheme_type",
        "scheme == 1 || scheme == 2 || scheme == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "scheme_valid",
        "scheme >= 1 && scheme <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detection scheme in {1=single-exp, 2=phase-shift, 3=optical-feedback} implies range [1,3]",
    );
}

/// Automatic baseline correction flag: 0=disabled, 1=enabled.
#[test]
fn test_crds_baseline_correction_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("baseline_flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_boolean",
        "baseline_flag == 0 || baseline_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_bounded",
        "baseline_flag >= 0 && baseline_flag <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "baseline correction flag in {0, 1} is a valid boolean",
    );
}
