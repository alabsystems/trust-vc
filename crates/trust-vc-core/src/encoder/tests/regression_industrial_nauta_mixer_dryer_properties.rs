// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Vessel volume in liters must be bounded within [50, 50000].
#[test]
fn test_nauta_mixer_dryer_vessel_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("volume", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vv_a",
        "volume >= 50 && volume <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vv_c",
        "volume >= 50 && volume <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nauta mixer dryer vessel volume in [50, 50000] litres",
    );
}

/// Screw rotation speed in RPM must be bounded within [5, 200].
#[test]
fn test_nauta_mixer_dryer_screw_rotation_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sr_a",
        "speed >= 5 && speed <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sr_c",
        "speed >= 5 && speed <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nauta mixer dryer screw rotation speed in [5, 200] RPM",
    );
}

/// Orbit speed at x10 RPM must be bounded within [1, 100].
#[test]
fn test_nauta_mixer_dryer_orbit_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("orbit_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "os_a",
        "orbit_x10 >= 1 && orbit_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "os_c",
        "orbit_x10 >= 1 && orbit_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nauta mixer dryer orbit speed x10 in [1, 100]");
}

/// Jacket temperature with +100 offset must be bounded within [50, 400].
#[test]
fn test_nauta_mixer_dryer_jacket_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "jt_a",
        "temp_off >= 50 && temp_off <= 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "jt_c",
        "temp_off >= 50 && temp_off <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nauta mixer dryer jacket temperature offset in [50, 400]",
    );
}

/// Vacuum pressure at x10 mbar must be bounded within [1, 10000].
#[test]
fn test_nauta_mixer_dryer_vacuum_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vac_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vp_a",
        "vac_x10 >= 1 && vac_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vp_c",
        "vac_x10 >= 1 && vac_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nauta mixer dryer vacuum pressure x10 in [1, 10000] mbar",
    );
}

/// Fill level percentage must be bounded within [10, 90].
#[test]
fn test_nauta_mixer_dryer_fill_level_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("level", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fl_a",
        "level >= 10 && level <= 90",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fl_c",
        "level >= 10 && level <= 90",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nauta mixer dryer fill level in [10, 90] percent");
}

/// Heating medium must be one of three options: 1=hot-water, 2=steam, 3=thermal-oil.
#[test]
fn test_nauta_mixer_dryer_heating_medium_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("medium", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "hm_a",
        "medium == 1 || medium == 2 || medium == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "hm_c",
        "medium == 1 || medium == 2 || medium == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nauta mixer dryer heating medium must be 1=hot-water, 2=steam, or 3=thermal-oil",
    );
}

/// Vessel material must be one of three options: 1=stainless-steel, 2=hastelloy, 3=glass-lined.
#[test]
fn test_nauta_mixer_dryer_vessel_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vm_a",
        "material == 1 || material == 2 || material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vm_c",
        "material == 1 || material == 2 || material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nauta mixer dryer vessel material must be 1=stainless-steel, 2=hastelloy, or 3=glass-lined");
}

/// Discharge type must be one of three options: 1=bottom-valve, 2=side-valve, 3=tilt.
#[test]
fn test_nauta_mixer_dryer_discharge_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("discharge", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dt_a",
        "discharge == 1 || discharge == 2 || discharge == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dt_c",
        "discharge == 1 || discharge == 2 || discharge == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nauta mixer dryer discharge type must be 1=bottom-valve, 2=side-valve, or 3=tilt",
    );
}

/// Automatic vacuum control flag must be boolean (0 or 1).
#[test]
fn test_nauta_mixer_dryer_auto_vacuum_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vc_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("vc_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nauta mixer dryer automatic vacuum control flag must be 0 or 1",
    );
}
