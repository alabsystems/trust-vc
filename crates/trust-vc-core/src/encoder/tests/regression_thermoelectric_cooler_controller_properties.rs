// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_thermoelectric_cooling_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cap_w", u32_ty());
    // Cooling capacity in W: value 50, valid range 5 to 500
    ctx.push_obligation(ProofObligation::assume("val", "cap_w == 50"));
    ctx.push_obligation(ProofObligation::assume("lo", "cap_w >= 5"));
    ctx.push_obligation(ProofObligation::assume("hi", "cap_w <= 500"));
    ctx.push_obligation(ProofObligation::assert("ok", "cap_w >= 5 && cap_w <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cooling capacity 50 W in range [5,500]");
}

#[test]
fn test_thermoelectric_delta_t_max_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["dt_val", "dt_min", "dt_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Delta T max in tenths of degree C: value 700 (70.0C), range 200..900
    ctx.push_obligation(ProofObligation::assume("dt_val", "dt_val == 700"));
    ctx.push_obligation(ProofObligation::assume("dt_min", "dt_min == 200"));
    ctx.push_obligation(ProofObligation::assume("dt_max", "dt_max == 900"));
    ctx.push_obligation(ProofObligation::assert(
        "dt_in_range",
        "dt_val >= dt_min && dt_val <= dt_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "delta T max 700 (70.0 C) in range [200,900]");
}

#[test]
fn test_thermoelectric_module_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mod_type", u32_ty());
    ctx.declare_var_typed("valid_mod", i32_ty());
    // TEC module types: 1=single-stage, 2=two-stage, 3=multi-stage
    ctx.push_obligation(ProofObligation::assume("mt_val", "mod_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "mt_def",
        "valid_mod == if mod_type == 1 || mod_type == 2 || mod_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("mt_chk", "valid_mod == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TEC module type 2 (two-stage) is valid");
}

#[test]
fn test_thermoelectric_input_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["vin_val", "vin_min", "vin_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Input voltage in mV: value 12000 (12V), range 3000..48000
    ctx.push_obligation(ProofObligation::assume("vin_val", "vin_val == 12000"));
    ctx.push_obligation(ProofObligation::assume("vin_min", "vin_min == 3000"));
    ctx.push_obligation(ProofObligation::assume("vin_max", "vin_max == 48000"));
    ctx.push_obligation(ProofObligation::assert(
        "vin_in_range",
        "vin_val >= vin_min && vin_val <= vin_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "input voltage 12000 mV (12V) in range [3000,48000]",
    );
}

#[test]
fn test_thermoelectric_max_current_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["cur_val", "cur_min", "cur_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Max current in mA: value 6000 (6A), range 500..30000
    ctx.push_obligation(ProofObligation::assume("cur_val", "cur_val == 6000"));
    ctx.push_obligation(ProofObligation::assume("cur_min", "cur_min == 500"));
    ctx.push_obligation(ProofObligation::assume("cur_max", "cur_max == 30000"));
    ctx.push_obligation(ProofObligation::assert(
        "cur_in_range",
        "cur_val >= cur_min && cur_val <= cur_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max current 6000 mA (6A) in range [500,30000]");
}

#[test]
fn test_thermoelectric_control_method_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ctrl_type", u32_ty());
    ctx.declare_var_typed("valid_ctrl", i32_ty());
    // Control methods: 1=on/off, 2=PWM, 3=linear, 4=PID
    ctx.push_obligation(ProofObligation::assume("ct_val", "ctrl_type == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "ct_def",
        "valid_ctrl == if ctrl_type == 1 || ctrl_type == 2 || ctrl_type == 3 || ctrl_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ct_chk", "valid_ctrl == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "control method 4 (PID) is valid TEC control");
}

#[test]
fn test_thermoelectric_hot_side_temp_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["ht_val", "ht_min", "ht_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Hot side temp offset +500: value 525 (25C), min 460 (-40C), max 585 (85C)
    ctx.push_obligation(ProofObligation::assume("ht_val", "ht_val == 525"));
    ctx.push_obligation(ProofObligation::assume("ht_min", "ht_min == 460"));
    ctx.push_obligation(ProofObligation::assume("ht_max", "ht_max == 585"));
    ctx.push_obligation(ProofObligation::assert(
        "ht_in_range",
        "ht_val >= ht_min && ht_val <= ht_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "hot side temp 525 (25 C) in offset range [460,585]",
    );
}

#[test]
fn test_thermoelectric_cold_side_temp_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["ct_val", "ct_min", "ct_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Cold side temp offset +500: value 495 (-5C), min 280 (-220C), max 540 (40C)
    ctx.push_obligation(ProofObligation::assume("ct_val", "ct_val == 495"));
    ctx.push_obligation(ProofObligation::assume("ct_min", "ct_min == 280"));
    ctx.push_obligation(ProofObligation::assume("ct_max", "ct_max == 540"));
    ctx.push_obligation(ProofObligation::assert(
        "ct_in_range",
        "ct_val >= ct_min && ct_val <= ct_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cold side temp 495 (-5 C) in offset range [280,540]",
    );
}

#[test]
fn test_thermoelectric_cop_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["cop_val", "cop_min", "cop_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // COP x100: value 150 (1.50), range 20..500
    ctx.push_obligation(ProofObligation::assume("cop_val", "cop_val == 150"));
    ctx.push_obligation(ProofObligation::assume("cop_min", "cop_min == 20"));
    ctx.push_obligation(ProofObligation::assume("cop_max", "cop_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "cop_in_range",
        "cop_val >= cop_min && cop_val <= cop_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "COP 150 (1.50) in range [20,500]");
}

#[test]
fn test_thermoelectric_alarm_enable_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("alarm_en", i32_ty());
    ctx.declare_var_typed("valid_alarm", i32_ty());
    // Alarm enable: 1=enabled, 0=disabled
    ctx.push_obligation(ProofObligation::assume("ae_val", "alarm_en == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ae_def",
        "valid_alarm == if alarm_en == 0 || alarm_en == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ae_chk", "valid_alarm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "alarm enable flag 1 (enabled) is valid boolean setting",
    );
}
