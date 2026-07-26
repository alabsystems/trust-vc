// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn rated_power() {
    let mut ctx = VerificationContext::new();
    for v in &["power_w", "max_power_w"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pow_ok", i32_ty());
    // Rated output power in watts
    ctx.push_obligation(ProofObligation::assume("pw", "power_w == 7500")); // 7.5kW
    ctx.push_obligation(ProofObligation::assume("mp", "max_power_w == 375000")); // 375kW
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pow_ok == if power_w <= max_power_w { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pow_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SynRM: 7.5kW ≤ 375kW max → OK");
}

#[test]
fn rated_speed() {
    let mut ctx = VerificationContext::new();
    for v in &["speed_rpm", "max_speed_rpm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("spd_ok", i32_ty());
    // Synchronous speed in RPM
    ctx.push_obligation(ProofObligation::assume("sr", "speed_rpm == 1500")); // 4-pole 50Hz
    ctx.push_obligation(ProofObligation::assume("ms", "max_speed_rpm == 6000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "spd_ok == if speed_rpm <= max_speed_rpm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "spd_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SynRM: 1500 RPM ≤ 6000 max → OK");
}

#[test]
fn efficiency_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ie_class", u32_ty());
    ctx.declare_var_typed("valid_ie", i32_ty());
    // IEC 60034-30-1 efficiency classes: 1=IE1, 2=IE2, 3=IE3, 4=IE4, 5=IE5
    ctx.push_obligation(ProofObligation::assume("ie", "ie_class == 4")); // IE4 Super Premium
    ctx.push_obligation(ProofObligation::assume(
        "vi_def",
        "valid_ie == if ie_class == 1 || ie_class == 2 || ie_class == 3 || ie_class == 4 || ie_class == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_ie == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SynRM: IE4 is valid efficiency class");
}

#[test]
fn pole_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("poles", u32_ty());
    ctx.declare_var_typed("valid_poles", i32_ty());
    // Standard SynRM pole counts (always even)
    ctx.push_obligation(ProofObligation::assume("p", "poles == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_poles == if poles == 2 || poles == 4 || poles == 6 || poles == 8 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_poles == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SynRM: 4-pole is valid configuration");
}

#[test]
fn torque_ripple() {
    let mut ctx = VerificationContext::new();
    for v in &["ripple_x10", "max_ripple_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rip_ok", i32_ty());
    // Torque ripple as % of rated torque (×10 for 0.1%)
    ctx.push_obligation(ProofObligation::assume("rx", "ripple_x10 == 80")); // 8.0%
    ctx.push_obligation(ProofObligation::assume("mr", "max_ripple_x10 == 200")); // 20.0%
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rip_ok == if ripple_x10 <= max_ripple_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rip_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SynRM: 8.0% torque ripple ≤ 20.0% max → OK");
}

#[test]
fn saliency_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["saliency_x10", "min_saliency_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sal_ok", i32_ty());
    // Ld/Lq saliency ratio (×10), SynRM needs high saliency (>4.0)
    ctx.push_obligation(ProofObligation::assume("sx", "saliency_x10 == 65")); // 6.5
    ctx.push_obligation(ProofObligation::assume("ms", "min_saliency_x10 == 40")); // 4.0
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sal_ok == if saliency_x10 >= min_saliency_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sal_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SynRM: 6.5 saliency ratio ≥ 4.0 min → OK");
}

#[test]
fn power_factor() {
    let mut ctx = VerificationContext::new();
    for v in &["pf_x100", "min_pf_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pf_ok", i32_ty());
    // Power factor (×100 for 0.01 precision)
    ctx.push_obligation(ProofObligation::assume("px", "pf_x100 == 80")); // 0.80
    ctx.push_obligation(ProofObligation::assume("mp", "min_pf_x100 == 60")); // 0.60
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pf_ok == if pf_x100 >= min_pf_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pf_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SynRM: 0.80 power factor ≥ 0.60 min → OK");
}

#[test]
fn voltage_rating() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_v", u32_ty());
    ctx.declare_var_typed("valid_voltage", i32_ty());
    // Standard supply voltages
    ctx.push_obligation(ProofObligation::assume("vv", "voltage_v == 400"));
    ctx.push_obligation(ProofObligation::assume(
        "vv_def",
        "valid_voltage == if voltage_v == 230 || voltage_v == 400 || voltage_v == 690 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_voltage == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SynRM: 400V is valid supply voltage");
}

#[test]
fn insulation_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ins_class", u32_ty());
    ctx.declare_var_typed("valid_ins", i32_ty());
    // IEC insulation classes: 1=B(130°C), 2=F(155°C), 3=H(180°C)
    ctx.push_obligation(ProofObligation::assume("ic", "ins_class == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vi_def",
        "valid_ins == if ins_class == 1 || ins_class == 2 || ins_class == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_ins == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SynRM: Class F is valid insulation class");
}

#[test]
fn frame_size() {
    let mut ctx = VerificationContext::new();
    for v in &["frame_mm", "min_frame_mm", "max_frame_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("frame_ok", i32_ty());
    // IEC frame size in mm (shaft height)
    ctx.push_obligation(ProofObligation::assume("fm", "frame_mm == 132"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_frame_mm == 71"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_frame_mm == 355"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "frame_ok == if frame_mm >= min_frame_mm && frame_mm <= max_frame_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "frame_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SynRM: 132mm frame in [71, 355] → OK");
}
