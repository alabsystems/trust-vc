// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// X-ray fluorescence (XRF) analyzer properties:
// Handheld/benchtop XRF instrument parameter verification.

#[test]
fn test_tube_voltage_kv() {
    let mut ctx = VerificationContext::new();
    for v in &["kv", "kv_min", "kv_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // X-ray source tube voltage in kilovolts
    ctx.push_obligation(ProofObligation::assume("kv_val", "kv == 50"));
    ctx.push_obligation(ProofObligation::assume("kv_lo", "kv_min == 10"));
    ctx.push_obligation(ProofObligation::assume("kv_hi", "kv_max == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "kv_in_range",
        "kv >= kv_min && kv <= kv_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "XRF: tube voltage 50 kV in range [10,100]");
}

#[test]
fn test_tube_current_ua() {
    let mut ctx = VerificationContext::new();
    for v in &["ua", "ua_min", "ua_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // X-ray source tube current in microamps
    ctx.push_obligation(ProofObligation::assume("ua_val", "ua == 200"));
    ctx.push_obligation(ProofObligation::assume("ua_lo", "ua_min == 10"));
    ctx.push_obligation(ProofObligation::assume("ua_hi", "ua_max == 2000"));
    ctx.push_obligation(ProofObligation::assert(
        "ua_in_range",
        "ua >= ua_min && ua <= ua_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "XRF: tube current 200 uA in range [10,2000]");
}

#[test]
fn test_element_range_z_min() {
    let mut ctx = VerificationContext::new();
    for v in &["z_min", "z_min_lo", "z_min_hi"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Minimum detectable atomic number (Z)
    ctx.push_obligation(ProofObligation::assume("zm_val", "z_min == 11"));
    ctx.push_obligation(ProofObligation::assume("zm_lo", "z_min_lo == 4"));
    ctx.push_obligation(ProofObligation::assume("zm_hi", "z_min_hi == 20"));
    ctx.push_obligation(ProofObligation::assert(
        "zm_in_range",
        "z_min >= z_min_lo && z_min <= z_min_hi",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "XRF: element Z min 11 (Na) in range [4,20]");
}

#[test]
fn test_element_range_z_max() {
    let mut ctx = VerificationContext::new();
    for v in &["z_max", "z_max_lo", "z_max_hi"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Maximum detectable atomic number (Z)
    ctx.push_obligation(ProofObligation::assume("zx_val", "z_max == 92"));
    ctx.push_obligation(ProofObligation::assume("zx_lo", "z_max_lo == 40"));
    ctx.push_obligation(ProofObligation::assume("zx_hi", "z_max_hi == 98"));
    ctx.push_obligation(ProofObligation::assert(
        "zx_in_range",
        "z_max >= z_max_lo && z_max <= z_max_hi",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "XRF: element Z max 92 (U) in range [40,98]");
}

#[test]
fn test_detector_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det_type", u32_ty());
    ctx.declare_var_typed("valid_det", i32_ty());
    // Detector type: 1=SDD (silicon drift), 2=PIN diode, 3=proportional counter
    ctx.push_obligation(ProofObligation::assume("dt_val", "det_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_det == if det_type == 1 || det_type == 2 || det_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("det_check", "valid_det == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "XRF: detector type 1 (SDD) is valid (1, 2, or 3)");
}

#[test]
fn test_resolution_ev() {
    let mut ctx = VerificationContext::new();
    for v in &["res_ev", "res_min", "res_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Energy resolution in electron-volts
    ctx.push_obligation(ProofObligation::assume("re_val", "res_ev == 140"));
    ctx.push_obligation(ProofObligation::assume("re_lo", "res_min == 50"));
    ctx.push_obligation(ProofObligation::assume("re_hi", "res_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "re_in_range",
        "res_ev >= res_min && res_ev <= res_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "XRF: resolution 140 eV in range [50,500]");
}

#[test]
fn test_measurement_time_s() {
    let mut ctx = VerificationContext::new();
    for v in &["time_s", "time_min", "time_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Acquisition measurement time in seconds
    ctx.push_obligation(ProofObligation::assume("ts_val", "time_s == 60"));
    ctx.push_obligation(ProofObligation::assume("ts_lo", "time_min == 5"));
    ctx.push_obligation(ProofObligation::assume("ts_hi", "time_max == 600"));
    ctx.push_obligation(ProofObligation::assert(
        "ts_in_range",
        "time_s >= time_min && time_s <= time_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "XRF: measurement time 60 s in range [5,600]");
}

#[test]
fn test_analysis_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("valid_mode", i32_ty());
    // Analysis mode: 1=alloy, 2=soil, 3=mining, 4=RoHS
    ctx.push_obligation(ProofObligation::assume("am_val", "mode == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mode == if mode == 1 || mode == 2 || mode == 3 || mode == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("mode_check", "valid_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "XRF: analysis mode 4 (RoHS) is valid (1, 2, 3, or 4)",
    );
}

#[test]
fn test_spot_size_mm() {
    let mut ctx = VerificationContext::new();
    for v in &["spot_mm", "spot_min", "spot_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Beam spot size (diameter) in millimeters
    ctx.push_obligation(ProofObligation::assume("ss_val", "spot_mm == 8"));
    ctx.push_obligation(ProofObligation::assume("ss_lo", "spot_min == 1"));
    ctx.push_obligation(ProofObligation::assume("ss_hi", "spot_max == 25"));
    ctx.push_obligation(ProofObligation::assert(
        "ss_in_range",
        "spot_mm >= spot_min && spot_mm <= spot_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "XRF: spot size 8 mm in range [1,25]");
}

#[test]
fn test_radiation_safety_interlock() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("interlock", i32_ty());
    // Boolean flag: 1=radiation safety interlock engaged, 0=disengaged
    ctx.push_obligation(ProofObligation::assume("il_val", "interlock == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "il_check",
        "interlock == 0 || interlock == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "XRF: radiation safety interlock flag 1 is valid boolean",
    );
}
