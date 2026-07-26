// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// ---------------------------------------------------------------------------
// Industrial microwave vacuum dryer – property-based regression tests
// ---------------------------------------------------------------------------

/// Microwave power in watts — bounded range.
#[test]
fn test_microwave_vacuum_dryer_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mp_a",
        "power >= 100 && power <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mp_c",
        "power >= 100 && power <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "microwave vacuum dryer power bounded");
}

/// Chamber pressure at ×10 mbar — bounded range.
#[test]
fn test_microwave_vacuum_dryer_chamber_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vac_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cp_a",
        "vac_x10 >= 1 && vac_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cp_c",
        "vac_x10 >= 1 && vac_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "microwave vacuum dryer chamber pressure x10 bounded",
    );
}

/// Product temperature with offset +100 °C — bounded range.
#[test]
fn test_microwave_vacuum_dryer_product_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pt_a",
        "temp_off >= 80 && temp_off <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pt_c",
        "temp_off >= 80 && temp_off <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "microwave vacuum dryer product temperature offset bounded",
    );
}

/// Turntable speed at ×10 RPM — bounded range.
#[test]
fn test_microwave_vacuum_dryer_turntable_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ts_a",
        "speed_x10 >= 1 && speed_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ts_c",
        "speed_x10 >= 1 && speed_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "microwave vacuum dryer turntable speed x10 bounded",
    );
}

/// Chamber volume in liters — bounded range.
#[test]
fn test_microwave_vacuum_dryer_chamber_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("volume", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cv_a",
        "volume >= 10 && volume <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cv_c",
        "volume >= 10 && volume <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "microwave vacuum dryer chamber volume bounded");
}

/// Drying time in minutes — bounded range.
#[test]
fn test_microwave_vacuum_dryer_drying_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dt_a", "time >= 1 && time <= 600"));
    ctx.push_obligation(ProofObligation::assert("dt_c", "time >= 1 && time <= 600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "microwave vacuum dryer drying time bounded");
}

/// Magnetron type — 3-way disjunction.
#[test]
fn test_microwave_vacuum_dryer_magnetron_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("magnetron", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mt_a",
        "magnetron == 1 || magnetron == 2 || magnetron == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mt_c",
        "magnetron == 1 || magnetron == 2 || magnetron == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "microwave vacuum dryer magnetron type three-way disjunction",
    );
}

/// Vacuum pump — 3-way disjunction.
#[test]
fn test_microwave_vacuum_dryer_vacuum_pump_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pump", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vp_a",
        "pump == 1 || pump == 2 || pump == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vp_c",
        "pump == 1 || pump == 2 || pump == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "microwave vacuum dryer vacuum pump three-way disjunction",
    );
}

/// Tray material — 3-way disjunction.
#[test]
fn test_microwave_vacuum_dryer_tray_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tray", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tm_a",
        "tray == 1 || tray == 2 || tray == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tm_c",
        "tray == 1 || tray == 2 || tray == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "microwave vacuum dryer tray material three-way disjunction",
    );
}

/// Automatic power modulation — boolean flag.
#[test]
fn test_microwave_vacuum_dryer_auto_power_modulation_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pm_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("pm_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "microwave vacuum dryer auto power modulation flag");
}
