// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn bed_area_bounded() {
    // Fluidized bed cross-sectional area must be 1-200 m²
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bed_area_m2", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ba", "bed_area_m2 == 45"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if bed_area_m2 >= 1 && bed_area_m2 <= 200 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FBC: bed area 45 m² in [1, 200]");
}

#[test]
fn bed_temperature_bounded() {
    // Bed temp 800-950°C, offset +500 → 1300-1450
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bed_temp", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bt", "bed_temp == 1350")); // 850°C + 500
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if bed_temp >= 1300 && bed_temp <= 1450 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FBC: bed temp 850°C (1350 offset) in [1300, 1450]");
}

#[test]
fn air_velocity_scaled() {
    // Fluidization velocity ×100: 150 = 1.50 m/s, range 50-600 (0.50-6.00 m/s)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_vel_x100", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("av", "air_vel_x100 == 200")); // 2.00 m/s
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if air_vel_x100 >= 50 && air_vel_x100 <= 600 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FBC: air velocity 2.00 m/s (200 ×100) in [50, 600]",
    );
}

#[test]
fn thermal_capacity_bounded() {
    // Thermal capacity 1-500 MW
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capacity_mw", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cm", "capacity_mw == 150"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if capacity_mw >= 1 && capacity_mw <= 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FBC: thermal capacity 150 MW in [1, 500]");
}

#[test]
fn fuel_type_disjunction() {
    // Fuel type: 1=coal, 2=biomass, 3=RDF
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fuel_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ft", "fuel_type == 2")); // biomass
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "fuel_type == 1 || fuel_type == 2 || fuel_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FBC: fuel type 2 (biomass) in {1,2,3}");
}

#[test]
fn bed_material_disjunction() {
    // Bed material: 1=sand, 2=limestone, 3=dolomite
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bed_material", u32_ty());
    ctx.push_obligation(ProofObligation::assume("bm", "bed_material == 3")); // dolomite
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "bed_material == 1 || bed_material == 2 || bed_material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FBC: bed material 3 (dolomite) in {1,2,3}");
}

#[test]
fn excess_air_scaled() {
    // Excess air ×10: 200 = 20.0%, typical range 150-300 (15.0%-30.0%)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("excess_air_x10", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ea", "excess_air_x10 == 200")); // 20.0%
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if excess_air_x10 >= 150 && excess_air_x10 <= 300 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FBC: excess air 20.0% (200 ×10) in [150, 300]");
}

#[test]
fn freeboard_height_bounded() {
    // Freeboard height 2000-10000 mm
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freeboard_mm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fh", "freeboard_mm == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if freeboard_mm >= 2000 && freeboard_mm <= 10000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FBC: freeboard 5000 mm in [2000, 10000]");
}

#[test]
fn combustion_efficiency_scaled() {
    // Combustion efficiency ×10: 985 = 98.5%, must be >= 950 (95.0%)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("efficiency_x10", u32_ty());
    ctx.declare_var_typed("acceptable", i32_ty());
    ctx.push_obligation(ProofObligation::assume("eff", "efficiency_x10 == 985")); // 98.5%
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "acceptable == if efficiency_x10 >= 950 && efficiency_x10 <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "acceptable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FBC: combustion efficiency 98.5% (985 ×10) in [950, 1000]",
    );
}

#[test]
fn flue_gas_recirculation_flag() {
    // FGR enabled: boolean flag (i32, 1=on, 0=off)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fgr_enabled", i32_ty());
    ctx.declare_var_typed("nox_reduction", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fgr", "fgr_enabled == 1")); // FGR on
    ctx.push_obligation(ProofObligation::assume(
        "nr_def",
        "nox_reduction == if fgr_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("reduces", "nox_reduction == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FBC: FGR enabled → NOx reduction active");
}
