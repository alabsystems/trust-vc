// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn flow_rate_within_operating_range() {
    // Flow rate scaled ×10 (0.1 L/min resolution)
    // e.g. flow_rate_x10 = 125 means 12.5 L/min
    let mut ctx = VerificationContext::new();
    for v in &["flow_rate_x10", "min_flow_x10", "max_flow_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fr", "flow_rate_x10 == 125")); // 12.5 L/min
    ctx.push_obligation(ProofObligation::assume("mn", "min_flow_x10 == 5")); // 0.5 L/min
    ctx.push_obligation(ProofObligation::assume("mx", "max_flow_x10 == 5000")); // 500 L/min
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if flow_rate_x10 >= min_flow_x10 && flow_rate_x10 <= max_flow_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PCP: flow 12.5 L/min within 0.5-500 range");
}

#[test]
fn discharge_pressure_limit() {
    // Discharge pressure scaled ×10 (0.1 bar resolution)
    // e.g. pressure_x10 = 240 means 24.0 bar
    let mut ctx = VerificationContext::new();
    for v in &["pressure_x10", "max_pressure_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_limit", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pr", "pressure_x10 == 240")); // 24.0 bar
    ctx.push_obligation(ProofObligation::assume("mp", "max_pressure_x10 == 480")); // 48.0 bar max
    ctx.push_obligation(ProofObligation::assume(
        "wl_def",
        "within_limit == if pressure_x10 <= max_pressure_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "within_limit == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "margin",
        "pressure_x10 < max_pressure_x10",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PCP: 24.0 bar <= 48.0 bar max discharge");
}

#[test]
fn rotor_speed_bounded() {
    // Rotor speed in RPM, bounded 50-500
    let mut ctx = VerificationContext::new();
    for v in &["rotor_rpm", "min_rpm", "max_rpm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("speed_valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rr", "rotor_rpm == 300"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_rpm == 50"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_rpm == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "sv_def",
        "speed_valid == if rotor_rpm >= min_rpm && rotor_rpm <= max_rpm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "speed_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PCP: rotor 300 RPM within 50-500 bounds");
}

#[test]
fn stage_count_determines_pressure_capacity() {
    // Stage count bounded 1-8; more stages = higher pressure capacity
    // Pressure per stage ×10: 60 (i.e. 6.0 bar per stage)
    let mut ctx = VerificationContext::new();
    for v in &["stages", "pressure_per_stage_x10", "total_capacity_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("stages_valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("st", "stages == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "pps",
        "pressure_per_stage_x10 == 60",
    )); // 6.0 bar/stage
    ctx.push_obligation(ProofObligation::assume(
        "tc_def",
        "total_capacity_x10 == stages * pressure_per_stage_x10",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "sv_def",
        "stages_valid == if stages >= 1 && stages <= 8 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "stages_valid == 1"));
    ctx.push_obligation(ProofObligation::assert("cap", "total_capacity_x10 == 240")); // 24.0 bar
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "PCP: 4 stages × 6.0 bar = 24.0 bar capacity");
}

#[test]
fn motor_power_sufficient() {
    // Motor power in kW, bounded 1-200
    let mut ctx = VerificationContext::new();
    for v in &["motor_kw", "required_kw", "min_kw", "max_kw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sufficient", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mk", "motor_kw == 45"));
    ctx.push_obligation(ProofObligation::assume("rk", "required_kw == 37"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_kw == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_kw == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "sufficient == if motor_kw >= required_kw && motor_kw >= min_kw && motor_kw <= max_kw { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "sufficient == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "headroom",
        "motor_kw > required_kw",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PCP: motor 45 kW >= 37 kW required, within 1-200");
}

#[test]
fn stator_material_valid_selection() {
    // Stator material: 3-way disjunction (1=NBR, 2=EPDM, 3=FKM)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stator_material", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sm", "stator_material == 2")); // EPDM
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if stator_material == 1 || stator_material == 2 || stator_material == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PCP: stator material EPDM (2) is valid 1/2/3");
}

#[test]
fn joint_type_valid_selection() {
    // Joint type: 3-way disjunction (1=pin, 2=flex rod, 3=gear)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("joint_type", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("jt", "joint_type == 3")); // gear joint
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if joint_type == 1 || joint_type == 2 || joint_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PCP: joint type gear (3) is valid 1/2/3");
}

#[test]
fn viscosity_range_compatibility() {
    // Viscosity scaled ×10 (0.1 cP resolution)
    // e.g. viscosity_x10 = 50000 means 5000.0 cP
    let mut ctx = VerificationContext::new();
    for v in &["viscosity_x10", "min_viscosity_x10", "max_viscosity_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("compatible", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vi", "viscosity_x10 == 50000")); // 5000.0 cP
    ctx.push_obligation(ProofObligation::assume("mn", "min_viscosity_x10 == 10")); // 1.0 cP
    ctx.push_obligation(ProofObligation::assume(
        "mx",
        "max_viscosity_x10 == 1000000",
    )); // 100000.0 cP
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "compatible == if viscosity_x10 >= min_viscosity_x10 && viscosity_x10 <= max_viscosity_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "compatible == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "PCP: viscosity 5000.0 cP within 1.0-100000.0 cP range",
    );
}

#[test]
fn solids_handling_capacity() {
    // Solids handling scaled ×10 (0.1% resolution)
    // e.g. solids_x10 = 350 means 35.0%
    let mut ctx = VerificationContext::new();
    for v in &["solids_x10", "max_solids_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_limit", i32_ty());
    ctx.push_obligation(ProofObligation::assume("so", "solids_x10 == 350")); // 35.0%
    ctx.push_obligation(ProofObligation::assume("ms", "max_solids_x10 == 600")); // 60.0% max
    ctx.push_obligation(ProofObligation::assume(
        "wl_def",
        "within_limit == if solids_x10 <= max_solids_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "within_limit == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "margin",
        "solids_x10 < max_solids_x10",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PCP: solids 35.0% <= 60.0% max handling capacity");
}

#[test]
fn dry_run_protection_engages() {
    // Dry-run protection: boolean flag (i32: 1=enabled, 0=disabled)
    // If flow drops to zero and pump is running, protection must shut down
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dry_run_protection", i32_ty());
    ctx.declare_var_typed("flow_rate_x10", u32_ty());
    ctx.declare_var_typed("pump_running", i32_ty());
    ctx.declare_var_typed("shutdown", i32_ty());
    ctx.push_obligation(ProofObligation::assume("drp", "dry_run_protection == 1")); // enabled
    ctx.push_obligation(ProofObligation::assume("fr", "flow_rate_x10 == 0")); // no flow
    ctx.push_obligation(ProofObligation::assume("pr", "pump_running == 1")); // pump on
    ctx.push_obligation(ProofObligation::assume(
        "sd_def",
        "shutdown == if dry_run_protection == 1 && flow_rate_x10 == 0 && pump_running == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("trips", "shutdown == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PCP: dry-run protection shuts down on zero flow");
}
