// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn flow_rate_scaled() {
    // Flow rate in ×10 L/min (0.1 L/min resolution)
    let mut ctx = VerificationContext::new();
    for v in &["speed_rpm", "displacement_x100", "flow_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // flow (L/min) = speed * displacement / 1000
    // scaled: flow_x10 = speed * displacement_x100 / 10000
    // 1500 RPM * 500 (=5.00 cc/rev) → 750000 / 10000 = 75 (=7.5 L/min)
    ctx.push_obligation(ProofObligation::assume("s", "speed_rpm == 1500"));
    ctx.push_obligation(ProofObligation::assume("d", "displacement_x100 == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "flow_x10 == speed_rpm * displacement_x100 / 10000",
    ));
    ctx.push_obligation(ProofObligation::assert("is_75", "flow_x10 == 75"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "vane pump flow: 1500*500/10000=75 (7.5 L/min)");
}

#[test]
fn max_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_bar", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("p", "pressure_bar == 210"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if pressure_bar >= 10 && pressure_bar <= 280 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vane pump pressure: 210 bar in [10, 280]");
}

#[test]
fn vane_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vane_count", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vc", "vane_count == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if vane_count >= 5 && vane_count <= 12 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vane count: 8 in [5, 12]");
}

#[test]
fn speed_rpm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_rpm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("s", "speed_rpm == 1800"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if speed_rpm >= 500 && speed_rpm <= 3600 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vane pump speed: 1800 RPM in [500, 3600]");
}

#[test]
fn displacement_scaled() {
    // Displacement in ×100 cc/rev (0.01 cc/rev resolution)
    let mut ctx = VerificationContext::new();
    for v in &["displacement_x100", "min_disp_x100", "max_disp_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    // 5.25 cc/rev → 525 in ×100 scale; range [100, 5000] → [1.00, 50.00] cc/rev
    ctx.push_obligation(ProofObligation::assume("d", "displacement_x100 == 525"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_disp_x100 == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_disp_x100 == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if displacement_x100 >= min_disp_x100 && displacement_x100 <= max_disp_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "displacement: 525 (5.25 cc/rev) in [100, 5000]");
}

#[test]
fn pump_configuration_disjunction() {
    // 1=single, 2=double, 3=variable
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("config", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("c", "config == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if config == 1 || config == 2 || config == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pump config: 2 (double) is valid {1,2,3}");
}

#[test]
fn cartridge_material_disjunction() {
    // 1=steel, 2=bronze, 3=composite
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("m", "material == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if material == 1 || material == 2 || material == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cartridge material: 3 (composite) is valid {1,2,3}",
    );
}

#[test]
fn viscosity_range_scaled() {
    // Viscosity in ×10 cSt (0.1 cSt resolution)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("viscosity_x10", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // 32.5 cSt → 325 in ×10 scale; hydraulic fluid range [100, 1000] → [10.0, 100.0] cSt
    ctx.push_obligation(ProofObligation::assume("v", "viscosity_x10 == 325"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if viscosity_x10 >= 100 && viscosity_x10 <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "viscosity: 325 (32.5 cSt) in [100, 1000]");
}

#[test]
fn motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_kw", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("p", "power_kw == 75"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if power_kw >= 1 && power_kw <= 200 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power: 75 kW in [1, 200]");
}

#[test]
fn pressure_compensation_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_bar", u32_ty());
    ctx.declare_var_typed("setpoint_bar", u32_ty());
    ctx.declare_var_typed("compensation_active", i32_ty());
    ctx.declare_var_typed("compensated", i32_ty());
    // Pressure compensation engages when pressure exceeds setpoint
    ctx.push_obligation(ProofObligation::assume("p", "pressure_bar == 250"));
    ctx.push_obligation(ProofObligation::assume("sp", "setpoint_bar == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "ca_def",
        "compensation_active == if pressure_bar > setpoint_bar { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "comp_def",
        "compensated == if compensation_active == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "active",
        "compensation_active == 1",
    ));
    ctx.push_obligation(ProofObligation::assert("engaged", "compensated == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure compensation: 250 > 200 bar setpoint");
}
