// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ---------- 1. Applied voltage (kV) ----------
#[test]
fn test_ce_applied_voltage() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_kv", i32_ty());
    ctx.push_obligation(ProofObligation::assume("volt_val", "voltage_kv == 25"));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_in_range",
        "voltage_kv >= 1 && voltage_kv <= 30",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "applied voltage 25 kV is within valid CE range [1, 30]",
    );
}

// ---------- 2. Capillary length (cm) ----------
#[test]
fn test_ce_capillary_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("length_cm", i32_ty());
    ctx.push_obligation(ProofObligation::assume("len_val", "length_cm == 60"));
    ctx.push_obligation(ProofObligation::assert(
        "length_in_range",
        "length_cm >= 10 && length_cm <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "capillary length 60 cm is within valid range [10, 100]",
    );
}

// ---------- 3. Capillary inner diameter (x10 um, 500 = 50.0 um) ----------
#[test]
fn test_ce_capillary_inner_diameter() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter_x10um", i32_ty());
    ctx.push_obligation(ProofObligation::assume("diam_val", "diameter_x10um == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "diameter_in_range",
        "diameter_x10um >= 50 && diameter_x10um <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "capillary ID 500 (50.0 um) is within valid range [50, 2000]",
    );
}

// ---------- 4. Detection wavelength (nm) ----------
#[test]
fn test_ce_detection_wavelength() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength_nm", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wl_val", "wavelength_nm == 214"));
    ctx.push_obligation(ProofObligation::assert(
        "wavelength_in_range",
        "wavelength_nm >= 190 && wavelength_nm <= 800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detection wavelength 214 nm is within valid range [190, 800]",
    );
}

// ---------- 5. Injection time (x10 sec, 50 = 5.0 s) ----------
#[test]
fn test_ce_injection_time() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inj_time_x10s", i32_ty());
    ctx.push_obligation(ProofObligation::assume("inj_val", "inj_time_x10s == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "injection_time_in_range",
        "inj_time_x10s >= 1 && inj_time_x10s <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "injection time 50 (5.0 s) is within valid range [1, 300]",
    );
}

// ---------- 6. Number of capillaries ----------
#[test]
fn test_ce_num_capillaries() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_capillaries", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cap_val", "num_capillaries == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "capillaries_in_range",
        "num_capillaries >= 1 && num_capillaries <= 96",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1 capillary is within valid range [1, 96]");
}

// ---------- 7. Separation mode (disjunction) ----------
#[test]
fn test_ce_separation_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sep_mode", i32_ty());
    // 1=CZE, 2=MEKC, 3=CEC
    ctx.push_obligation(ProofObligation::assume("sep_val", "sep_mode == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "sep_mode_valid",
        "sep_mode == 1 || sep_mode == 2 || sep_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "separation mode CZE (1) is a valid CE separation mode",
    );
}

// ---------- 8. Detection method (disjunction) ----------
#[test]
fn test_ce_detection_method() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det_method", i32_ty());
    // 1=UV-Vis, 2=fluorescence, 3=mass-spec
    ctx.push_obligation(ProofObligation::assume("det_val", "det_method == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "det_method_valid",
        "det_method == 1 || det_method == 2 || det_method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detection method UV-Vis (1) is a valid CE detection method",
    );
}

// ---------- 9. Injection mode (disjunction) ----------
#[test]
fn test_ce_injection_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inj_mode", i32_ty());
    // 1=hydrodynamic, 2=electrokinetic, 3=pressure
    ctx.push_obligation(ProofObligation::assume("inj_val", "inj_mode == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "inj_mode_valid",
        "inj_mode == 1 || inj_mode == 2 || inj_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "injection mode hydrodynamic (1) is a valid CE injection mode",
    );
}

// ---------- 10. Automatic buffer replenishment (boolean flag) ----------
#[test]
fn test_ce_auto_buffer_replenishment() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_buffer", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "auto_buffer == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "auto_buffer_active",
        "if auto_buffer == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic buffer replenishment is active when flag is 1",
    );
}
