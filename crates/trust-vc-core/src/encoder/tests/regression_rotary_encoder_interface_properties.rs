// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn resolution_ppr_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["ppr", "ppr_min", "ppr_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Pulses per revolution: value 1024, valid range [1, 65536]
    ctx.push_obligation(ProofObligation::assume("ppr_val", "ppr == 1024"));
    ctx.push_obligation(ProofObligation::assume("ppr_lo", "ppr_min == 1"));
    ctx.push_obligation(ProofObligation::assume("ppr_hi", "ppr_max == 65536"));
    ctx.push_obligation(ProofObligation::assert(
        "ppr_in_range",
        "ppr >= ppr_min && ppr <= ppr_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotary encoder: 1024 PPR in range [1, 65536]");
}

#[test]
fn max_speed_rpm_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["rpm", "rpm_min", "rpm_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Maximum speed in RPM: value 6000, valid range [100, 100000]
    ctx.push_obligation(ProofObligation::assume("rpm_val", "rpm == 6000"));
    ctx.push_obligation(ProofObligation::assume("rpm_lo", "rpm_min == 100"));
    ctx.push_obligation(ProofObligation::assume("rpm_hi", "rpm_max == 100000"));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_in_range",
        "rpm >= rpm_min && rpm <= rpm_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotary encoder: 6000 RPM in range [100, 100000]");
}

#[test]
fn encoder_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("enc_type", u32_ty());
    ctx.declare_var_typed("valid_type", i32_ty());
    // Encoder types: 1=incremental, 2=absolute single-turn, 3=absolute multi-turn
    ctx.push_obligation(ProofObligation::assume("et_val", "enc_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "et_def",
        "valid_type == if enc_type == 1 || enc_type == 2 || enc_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("et_chk", "valid_type == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rotary encoder: type 2 (absolute single-turn) is valid",
    );
}

#[test]
fn output_signal_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("out_sig", u32_ty());
    ctx.declare_var_typed("valid_sig", i32_ty());
    // Output signal types: 1=TTL, 2=HTL, 3=SSI, 4=BiSS-C
    ctx.push_obligation(ProofObligation::assume("os_val", "out_sig == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "os_def",
        "valid_sig == if out_sig == 1 || out_sig == 2 || out_sig == 3 || out_sig == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("os_chk", "valid_sig == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotary encoder: output signal 3 (SSI) is valid");
}

#[test]
fn supply_voltage_mv_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["voltage_mv", "v_min", "v_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Supply voltage in millivolts: value 24000 (24V), valid range [5000, 30000] (5-30V)
    ctx.push_obligation(ProofObligation::assume("v_val", "voltage_mv == 24000"));
    ctx.push_obligation(ProofObligation::assume("v_lo", "v_min == 5000"));
    ctx.push_obligation(ProofObligation::assume("v_hi", "v_max == 30000"));
    ctx.push_obligation(ProofObligation::assert(
        "v_in_range",
        "voltage_mv >= v_min && voltage_mv <= v_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rotary encoder: 24000 mV (24V) in range [5000, 30000]",
    );
}

#[test]
fn shaft_diameter_mm_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["shaft_mm", "shaft_min", "shaft_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Shaft diameter in mm: value 10, valid range [4, 50]
    ctx.push_obligation(ProofObligation::assume("s_val", "shaft_mm == 10"));
    ctx.push_obligation(ProofObligation::assume("s_lo", "shaft_min == 4"));
    ctx.push_obligation(ProofObligation::assume("s_hi", "shaft_max == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "s_in_range",
        "shaft_mm >= shaft_min && shaft_mm <= shaft_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotary encoder: 10 mm shaft in range [4, 50]");
}

#[test]
fn protection_class_non_sequential_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ip_class", u32_ty());
    ctx.declare_var_typed("valid_ip", i32_ty());
    // IP protection class: 3-way non-sequential (54, 65, 67)
    ctx.push_obligation(ProofObligation::assume("ip_val", "ip_class == 65"));
    ctx.push_obligation(ProofObligation::assume(
        "ip_def",
        "valid_ip == if ip_class == 54 || ip_class == 65 || ip_class == 67 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ip_chk", "valid_ip == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rotary encoder: IP65 is valid protection class (54, 65, or 67)",
    );
}

#[test]
fn accuracy_arc_min_x100_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x100", "acc_min", "acc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Accuracy in arc-minutes ×100: value 50 (0.50 arc-min), valid range [1, 500]
    ctx.push_obligation(ProofObligation::assume("a_val", "accuracy_x100 == 50"));
    ctx.push_obligation(ProofObligation::assume("a_lo", "acc_min == 1"));
    ctx.push_obligation(ProofObligation::assume("a_hi", "acc_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "a_in_range",
        "accuracy_x100 >= acc_min && accuracy_x100 <= acc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rotary encoder: accuracy 50 (0.50 arc-min) in range [1, 500]",
    );
}

#[test]
fn operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_off", "temp_min", "temp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Operating temperature with offset +500: 20°C → 520, valid range [250, 1000] (-250°C to +500°C)
    ctx.push_obligation(ProofObligation::assume("t_val", "temp_off == 520")); // 20°C
    ctx.push_obligation(ProofObligation::assume("t_lo", "temp_min == 250")); // -250°C
    ctx.push_obligation(ProofObligation::assume("t_hi", "temp_max == 1000")); // +500°C
    ctx.push_obligation(ProofObligation::assert(
        "t_in_range",
        "temp_off >= temp_min && temp_off <= temp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rotary encoder: 520 (20°C offset+500) in range [250, 1000]",
    );
}

#[test]
fn index_pulse_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("has_index", i32_ty());
    ctx.declare_var_typed("index_valid", i32_ty());
    // Index pulse: boolean flag encoded as i32 (0 or 1)
    ctx.push_obligation(ProofObligation::assume("hi_val", "has_index == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "iv_def",
        "index_valid == if has_index == 0 || has_index == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("iv_chk", "index_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rotary encoder: index pulse flag 1 is valid boolean (0 or 1)",
    );
}
