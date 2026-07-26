// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_dynamic_range_db() {
    // OTDR dynamic range: measurement reach in dB, value 40, min 15, max 50
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dynamic_range", u32_ty());
    ctx.declare_var_typed("range_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "dynamic_range == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "range_ok == if dynamic_range >= 15 && dynamic_range <= 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "range_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OTDR: dynamic range 40 dB in [15, 50]");
}

#[test]
fn test_wavelength_nm() {
    // OTDR laser wavelength: 4-way non-sequential disjunction 850/1310/1550/1625 nm
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength_nm", u32_ty());
    ctx.declare_var_typed("valid_wl", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "wavelength_nm == 1550"));
    ctx.push_obligation(ProofObligation::assume(
        "vw_def",
        "valid_wl == if wavelength_nm == 850 || wavelength_nm == 1310 || wavelength_nm == 1550 || wavelength_nm == 1625 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_wl == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OTDR: 1550 nm is valid laser wavelength");
}

#[test]
fn test_dead_zone_m() {
    // OTDR event dead zone: value 1 m, min 0, max 20 m
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dead_zone_m", u32_ty());
    ctx.declare_var_typed("zone_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "dead_zone_m == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "zone_ok == if dead_zone_m >= 0 && dead_zone_m <= 20 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "zone_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OTDR: dead zone 1 m in [0, 20]");
}

#[test]
fn test_pulse_width_ns() {
    // OTDR pulse width: bounded value 100 ns, min 5, max 20000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pulse_width_ns", u32_ty());
    ctx.declare_var_typed("width_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "pulse_width_ns == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "width_ok == if pulse_width_ns >= 5 && pulse_width_ns <= 20000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "width_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OTDR: pulse width 100 ns in [5, 20000]");
}

#[test]
fn test_distance_range_km() {
    // OTDR distance range: fiber length value 200 km, min 1, max 500
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("distance_km", u32_ty());
    ctx.declare_var_typed("dist_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "distance_km == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "dist_ok == if distance_km >= 1 && distance_km <= 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "dist_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OTDR: distance range 200 km in [1, 500]");
}

#[test]
fn test_resolution_mm() {
    // OTDR spatial resolution: value 500 mm, min 10, max 10000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_mm", u32_ty());
    ctx.declare_var_typed("res_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "resolution_mm == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "res_ok == if resolution_mm >= 10 && resolution_mm <= 10000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "res_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OTDR: resolution 500 mm in [10, 10000]");
}

#[test]
fn test_fiber_type_disjunction() {
    // OTDR fiber type: 3-way disjunction 1=single-mode, 2=multimode, 3=POF
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fiber_type", u32_ty());
    ctx.declare_var_typed("valid_fiber", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "fiber_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vf_def",
        "valid_fiber == if fiber_type == 1 || fiber_type == 2 || fiber_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_fiber == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OTDR: single-mode (1) is valid fiber type");
}

#[test]
fn test_averaging_time_s() {
    // OTDR averaging/acquisition time: value 30 s, min 1, max 300
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("avg_time_s", u32_ty());
    ctx.declare_var_typed("time_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "avg_time_s == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "time_ok == if avg_time_s >= 1 && avg_time_s <= 300 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "time_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OTDR: averaging time 30 s in [1, 300]");
}

#[test]
fn test_connector_type_disjunction() {
    // OTDR connector type: 4-way disjunction 1=SC, 2=FC, 3=LC, 4=ST
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("connector", u32_ty());
    ctx.declare_var_typed("valid_conn", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "connector == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_conn == if connector == 1 || connector == 2 || connector == 3 || connector == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_conn == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OTDR: FC (2) is valid connector type");
}

#[test]
fn test_auto_test_mode_flag() {
    // OTDR auto-test mode: boolean flag using i32_ty, 1=enabled, 0=disabled
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_test_flag", i32_ty());
    ctx.declare_var_typed("pulse_width", u32_ty());
    ctx.declare_var_typed("effective_width", u32_ty());
    // Auto-test mode doubles the pulse width for extended reach; manual uses base width
    ctx.push_obligation(ProofObligation::assume("af_val", "auto_test_flag == 1"));
    ctx.push_obligation(ProofObligation::assume("pw_val", "pulse_width == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ew_def",
        "effective_width == if auto_test_flag == 1 { pulse_width + pulse_width } else { pulse_width }",
    ));
    ctx.push_obligation(ProofObligation::assert("doubled", "effective_width == 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "OTDR: auto-test mode doubles pulse width 100 -> 200 ns",
    );
}
