// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn flow_rate_scaled_within_range() {
    // Flow rate in ×10 L/min (0.1 L/min resolution): 50 = 5.0 L/min
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_rate_x10", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fr", "flow_rate_x10 == 50")); // 5.0 L/min
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if flow_rate_x10 >= 1 && flow_rate_x10 <= 5000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gear pump: flow 5.0 L/min (×10=50) in [0.1, 500.0]",
    );
}

#[test]
fn pressure_rating_bounded() {
    // Pressure in bar, bounded 10 to 350
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_bar", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pb", "pressure_bar == 250"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if pressure_bar >= 10 && pressure_bar <= 350 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gear pump: pressure 250 bar in [10, 350]");
}

#[test]
fn gear_speed_bounded() {
    // Gear speed in RPM, bounded 100 to 3000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_rpm", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sr", "speed_rpm == 1500"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if speed_rpm >= 100 && speed_rpm <= 3000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gear pump: speed 1500 RPM in [100, 3000]");
}

#[test]
fn displacement_scaled_within_range() {
    // Displacement in ×100 cc/rev (0.01 cc/rev resolution): 1250 = 12.50 cc/rev
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("displacement_x100", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("d", "displacement_x100 == 1250")); // 12.50 cc/rev
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if displacement_x100 >= 10 && displacement_x100 <= 25000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gear pump: displacement 12.50 cc/rev (×100=1250) in [0.10, 250.00]",
    );
}

#[test]
fn motor_power_bounded() {
    // Motor power in kW, bounded 1 to 150
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_kw", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pk", "power_kw == 75"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if power_kw >= 1 && power_kw <= 150 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gear pump: motor 75 kW in [1, 150]");
}

#[test]
fn gear_type_classification() {
    // Gear type: 1=spur, 2=helical, 3=herringbone
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gear_type", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("gt", "gear_type == 2")); // helical
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if gear_type == 1 || gear_type == 2 || gear_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gear pump: type 2 (helical) in {spur, helical, herringbone}",
    );
}

#[test]
fn seal_type_classification() {
    // Seal type: 1=lip seal, 2=mechanical, 3=mag drive
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal_type", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("st", "seal_type == 3")); // mag drive
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if seal_type == 1 || seal_type == 2 || seal_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gear pump: seal 3 (mag drive) in {lip, mechanical, mag drive}",
    );
}

#[test]
fn viscosity_max_scaled_within_range() {
    // Viscosity max in ×10 cSt (0.1 cSt resolution): 100000 = 10000.0 cSt
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("viscosity_max_x10", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vm", "viscosity_max_x10 == 100000")); // 10000.0 cSt
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if viscosity_max_x10 >= 10 && viscosity_max_x10 <= 500000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gear pump: viscosity max 10000.0 cSt (×10=100000) in [1.0, 50000.0]",
    );
}

#[test]
fn tooth_count_bounded() {
    // Tooth count per gear, bounded 6 to 24
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tooth_count", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tc", "tooth_count == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if tooth_count >= 6 && tooth_count <= 24 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gear pump: 12 teeth in [6, 24]");
}

#[test]
fn overpressure_protection_flag() {
    // Overpressure protection: boolean flag (i32, 1=enabled)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_bar", u32_ty());
    ctx.declare_var_typed("max_pressure_bar", u32_ty());
    ctx.declare_var_typed("protection_enabled", i32_ty());
    ctx.declare_var_typed("relief_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pb", "pressure_bar == 360"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_pressure_bar == 350"));
    ctx.push_obligation(ProofObligation::assume("pe", "protection_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ra_def",
        "relief_active == if protection_enabled == 1 && pressure_bar > max_pressure_bar { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "relief_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gear pump: overpressure 360 > 350 bar with protection → relief active",
    );
}
