// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_bed_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["bed_temp_c", "temp_min", "temp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Bed temperature in °C: value 850, valid range [200, 1200] (all positive, no offset needed)
    ctx.push_obligation(ProofObligation::assume("bt_val", "bed_temp_c == 850"));
    ctx.push_obligation(ProofObligation::assume("bt_min", "temp_min == 200"));
    ctx.push_obligation(ProofObligation::assume("bt_max", "temp_max == 1200"));
    ctx.push_obligation(ProofObligation::assert(
        "bt_in_range",
        "bed_temp_c >= temp_min && bed_temp_c <= temp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bed temp 850C in range [200,1200]");
}

#[test]
fn test_bed_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["bed_pressure_kpa", "press_min", "press_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Bed pressure in kPa: value 1200, valid range [50, 5000]
    ctx.push_obligation(ProofObligation::assume(
        "bp_val",
        "bed_pressure_kpa == 1200",
    ));
    ctx.push_obligation(ProofObligation::assume("bp_min", "press_min == 50"));
    ctx.push_obligation(ProofObligation::assume("bp_max", "press_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "bp_in_range",
        "bed_pressure_kpa >= press_min && bed_pressure_kpa <= press_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bed pressure 1200 kPa in range [50,5000]");
}

#[test]
fn test_reactor_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("reactor_type", u32_ty());
    ctx.declare_var_typed("valid_type", i32_ty());
    // 1=bubbling, 2=circulating, 3=turbulent
    ctx.push_obligation(ProofObligation::assume("rt_val", "reactor_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "rt_valid_def",
        "valid_type == if reactor_type == 1 || reactor_type == 2 || reactor_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("rt_check", "valid_type == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reactor type 2 (circulating) is valid");
}

#[test]
fn test_gas_velocity_x100_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["gas_vel_x100", "vel_min", "vel_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Gas velocity scaled x100 m/s: 1.50 m/s → 150, valid range [10, 2000]
    ctx.push_obligation(ProofObligation::assume("gv_val", "gas_vel_x100 == 150"));
    ctx.push_obligation(ProofObligation::assume("gv_min", "vel_min == 10"));
    ctx.push_obligation(ProofObligation::assume("gv_max", "vel_max == 2000"));
    ctx.push_obligation(ProofObligation::assert(
        "gv_in_range",
        "gas_vel_x100 >= vel_min && gas_vel_x100 <= vel_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gas velocity 150 (1.50 m/s) in range [10,2000]");
}

#[test]
fn test_bed_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bed_material", u32_ty());
    ctx.declare_var_typed("valid_material", i32_ty());
    // 1=sand, 2=alumina, 3=limestone, 4=catalyst
    ctx.push_obligation(ProofObligation::assume("bm_val", "bed_material == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "bm_valid_def",
        "valid_material == if bed_material == 1 || bed_material == 2 || bed_material == 3 || bed_material == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("bm_check", "valid_material == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bed material 3 (limestone) is valid");
}

#[test]
fn test_particle_size_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["particle_um", "size_min", "size_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Particle size in micrometers: value 500, valid range [50, 5000]
    ctx.push_obligation(ProofObligation::assume("ps_val", "particle_um == 500"));
    ctx.push_obligation(ProofObligation::assume("ps_min", "size_min == 50"));
    ctx.push_obligation(ProofObligation::assume("ps_max", "size_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "ps_in_range",
        "particle_um >= size_min && particle_um <= size_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "particle size 500 um in range [50,5000]");
}

#[test]
fn test_freeboard_height_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["freeboard_mm", "fb_min", "fb_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Freeboard height in mm: value 3000, valid range [500, 10000]
    ctx.push_obligation(ProofObligation::assume("fh_val", "freeboard_mm == 3000"));
    ctx.push_obligation(ProofObligation::assume("fh_min", "fb_min == 500"));
    ctx.push_obligation(ProofObligation::assume("fh_max", "fb_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "fh_in_range",
        "freeboard_mm >= fb_min && freeboard_mm <= fb_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "freeboard height 3000 mm in range [500,10000]");
}

#[test]
fn test_distributor_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dist_type", u32_ty());
    ctx.declare_var_typed("valid_dist", i32_ty());
    // 1=perforated plate, 2=bubble cap, 3=nozzle
    ctx.push_obligation(ProofObligation::assume("dt_val", "dist_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "dt_valid_def",
        "valid_dist == if dist_type == 1 || dist_type == 2 || dist_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("dt_check", "valid_dist == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "distributor type 1 (perforated plate) is valid");
}

#[test]
fn test_gas_inlet_temp_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["gas_inlet_temp_off", "inlet_min", "inlet_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Gas inlet temperature with offset +500: 200°C → 700, valid range [500, 1500] (0°C to 1000°C)
    ctx.push_obligation(ProofObligation::assume(
        "gi_val",
        "gas_inlet_temp_off == 700",
    ));
    ctx.push_obligation(ProofObligation::assume("gi_min", "inlet_min == 500"));
    ctx.push_obligation(ProofObligation::assume("gi_max", "inlet_max == 1500"));
    ctx.push_obligation(ProofObligation::assert(
        "gi_in_range",
        "gas_inlet_temp_off >= inlet_min && gas_inlet_temp_off <= inlet_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gas inlet temp 700 (200C) in range [500,1500] (0C to 1000C)",
    );
}

#[test]
fn test_cyclone_separator_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("has_cyclone", i32_ty());
    ctx.declare_var_typed("particulate_capture", i32_ty());
    // Boolean flag: 1=cyclone separator present, 0=absent
    ctx.push_obligation(ProofObligation::assume("hc_val", "has_cyclone == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "pc_def",
        "particulate_capture == if has_cyclone == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pc_check",
        "particulate_capture == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cyclone separator flag 1 → particulate capture enabled",
    );
}
