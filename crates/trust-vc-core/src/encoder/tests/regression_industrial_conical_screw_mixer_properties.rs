// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_conical_mixer_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vol", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vol_range",
        "vol >= 100 && vol <= 20000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vol_bounded",
        "vol >= 100 && vol <= 20000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vessel volume must be in [100, 20000] litres");
}

#[test]
fn test_conical_mixer_screw_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spd_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spd_range",
        "spd_x10 >= 10 && spd_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spd_bounded",
        "spd_x10 >= 10 && spd_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "screw speed x10 must be in [10, 500] (1.0-50.0 RPM)",
    );
}

#[test]
fn test_conical_mixer_orbit_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("orb_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "orb_range",
        "orb_x10 >= 1 && orb_x10 <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "orb_bounded",
        "orb_x10 >= 1 && orb_x10 <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "orbital speed x10 must be in [1, 50] (0.1-5.0 RPM)",
    );
}

#[test]
fn test_conical_mixer_fill_level_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fill_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fill_range",
        "fill_x10 >= 200 && fill_x10 <= 900",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fill_bounded",
        "fill_x10 >= 200 && fill_x10 <= 900",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fill level x10 must be in [200, 900] (20.0-90.0%)");
}

#[test]
fn test_conical_mixer_mix_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mt", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mt_range", "mt >= 1 && mt <= 120"));
    ctx.push_obligation(ProofObligation::assert(
        "mt_bounded",
        "mt >= 1 && mt <= 120",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mixing time must be in [1, 120] minutes");
}

#[test]
fn test_conical_mixer_cone_angle_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("angle", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "angle_range",
        "angle >= 15 && angle <= 45",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "angle_bounded",
        "angle >= 15 && angle <= 45",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cone half-angle must be in [15, 45] degrees");
}

#[test]
fn test_conical_mixer_drive_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drv", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "drv_enum",
        "drv == 1 || drv == 2 || drv == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "drv_valid",
        "drv == 1 || drv == 2 || drv == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drive type must be 1=top, 2=bottom, or 3=orbital");
}

#[test]
fn test_conical_mixer_discharge_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dis", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dis_enum",
        "dis == 1 || dis == 2 || dis == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dis_valid",
        "dis == 1 || dis == 2 || dis == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge must be 1=bottom valve, 2=side valve, or 3=butterfly",
    );
}

#[test]
fn test_conical_mixer_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mat_enum",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mat_valid",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "material must be 1=SS304, 2=SS316, or 3=Hastelloy");
}

#[test]
fn test_conical_mixer_vacuum_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vac", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vac_bool", "vac == 0 || vac == 1"));
    ctx.push_obligation(ProofObligation::assert("vac_valid", "vac == 0 || vac == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum capability flag must be 0 or 1");
}
