// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Test 1: Contact potential difference (x1000 mV) — bounded [1, 5000].
/// 1 represents 0.001 mV, 5000 represents 5.000 mV (typical CPD range).
#[test]
fn test_kelvin_probe_cpd_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cpd_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cpd_a",
        "cpd_x1000 >= 1 && cpd_x1000 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cpd_c",
        "cpd_x1000 >= 1 && cpd_x1000 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "CPD x1000 in [1, 5000] representing 0.001-5.000 mV",
    );
}

/// Test 2: Probe oscillation frequency (Hz) — bounded [50, 5000].
#[test]
fn test_kelvin_probe_oscillation_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("osc_freq", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "freq_a",
        "osc_freq >= 50 && osc_freq <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "freq_c",
        "osc_freq >= 50 && osc_freq <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "oscillation frequency in [50, 5000] Hz");
}

/// Test 3: Probe-to-sample distance (x1000 um) — bounded [10, 5000].
/// 10 represents 0.010 um, 5000 represents 5.000 um.
#[test]
fn test_kelvin_probe_distance_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dist_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dist_a",
        "dist_x1000 >= 10 && dist_x1000 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dist_c",
        "dist_x1000 >= 10 && dist_x1000 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "probe distance x1000 in [10, 5000] representing 0.010-5.000 um",
    );
}

/// Test 4: Backing potential offset +5000 (mV) — bounded [0, 10000].
/// 0 represents -5000 mV, 5000 represents 0 mV, 10000 represents +5000 mV.
#[test]
fn test_kelvin_probe_backing_potential_offset5000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bp_a",
        "bp_off >= 0 && bp_off <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bp_c",
        "bp_off >= 0 && bp_off <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "backing potential offset+5000 in [0, 10000] representing -5000 to +5000 mV",
    );
}

/// Test 5: Scan area (x100 mm2) — bounded [1, 100000].
/// 1 represents 0.01 mm2, 100000 represents 1000.00 mm2.
#[test]
fn test_kelvin_probe_scan_area_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("area_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "area_a",
        "area_x100 >= 1 && area_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "area_c",
        "area_x100 >= 1 && area_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "scan area x100 in [1, 100000] representing 0.01-1000.00 mm2",
    );
}

/// Test 6: Spatial resolution (x10 um) — bounded [1, 10000].
/// 1 represents 0.1 um, 10000 represents 1000.0 um.
#[test]
fn test_kelvin_probe_spatial_resolution_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_a",
        "res_x10 >= 1 && res_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "res_c",
        "res_x10 >= 1 && res_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spatial resolution x10 in [1, 10000] representing 0.1-1000.0 um",
    );
}

/// Test 7: Probe tip material — 3-way disjunction.
/// 1=gold, 2=platinum, 3=tungsten.
#[test]
fn test_kelvin_probe_tip_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tip_mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tip_a",
        "tip_mat == 1 || tip_mat == 2 || tip_mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tip_c",
        "tip_mat >= 1 && tip_mat <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tip material 3-way (gold/platinum/tungsten)");
}

/// Test 8: Operating environment — 3-way disjunction.
/// 1=ambient, 2=inert-gas, 3=vacuum.
#[test]
fn test_kelvin_probe_environment_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("env", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "env_a",
        "env == 1 || env == 2 || env == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("env_c", "env >= 1 && env <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "environment 3-way (ambient/inert-gas/vacuum)");
}

/// Test 9: Feedback control mode — 3-way disjunction.
/// 1=null-method, 2=force-feedback, 3=amplitude-modulation.
#[test]
fn test_kelvin_probe_feedback_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fb_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fb_a",
        "fb_mode == 1 || fb_mode == 2 || fb_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fb_c",
        "fb_mode >= 1 && fb_mode <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "feedback mode 3-way (null-method/force-feedback/amplitude-modulation)",
    );
}

/// Test 10: Auto-nulling flag — boolean.
/// 0=manual, 1=auto.
#[test]
fn test_kelvin_probe_auto_nulling_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("flag_c", "flag >= 0 && flag <= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto-nulling flag is boolean (0 or 1)");
}
