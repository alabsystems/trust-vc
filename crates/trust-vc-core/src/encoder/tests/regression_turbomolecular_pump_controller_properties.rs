// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn pumping_speed() {
    let mut ctx = VerificationContext::new();
    for v in &["speed_ls", "speed_min", "speed_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Pumping speed in L/s (liters per second for N2): value 300, valid range 10 to 5000
    ctx.push_obligation(ProofObligation::assume("ps_val", "speed_ls == 300"));
    ctx.push_obligation(ProofObligation::assume("ps_min", "speed_min == 10"));
    ctx.push_obligation(ProofObligation::assume("ps_max", "speed_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "ps_in_range",
        "speed_ls >= speed_min && speed_ls <= speed_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pumping speed 300 L/s (N2) in range [10,5000]");
}

#[test]
fn rotation_speed() {
    let mut ctx = VerificationContext::new();
    for v in &["rpm", "rpm_min", "rpm_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Rotation speed in RPM: value 60000, valid range 10000 to 90000
    ctx.push_obligation(ProofObligation::assume("rs_val", "rpm == 60000"));
    ctx.push_obligation(ProofObligation::assume("rs_min", "rpm_min == 10000"));
    ctx.push_obligation(ProofObligation::assume("rs_max", "rpm_max == 90000"));
    ctx.push_obligation(ProofObligation::assert(
        "rs_in_range",
        "rpm >= rpm_min && rpm <= rpm_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotation speed 60000 RPM in range [10000,90000]");
}

#[test]
fn compression_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["cr_exp", "cr_min", "cr_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Compression ratio as log10 exponent (e.g., 10^9 -> 9): value 9, valid range 1 to 12
    ctx.push_obligation(ProofObligation::assume("cr_val", "cr_exp == 9"));
    ctx.push_obligation(ProofObligation::assume("cr_min_a", "cr_min == 1"));
    ctx.push_obligation(ProofObligation::assume("cr_max_a", "cr_max == 12"));
    ctx.push_obligation(ProofObligation::assert(
        "cr_in_range",
        "cr_exp >= cr_min && cr_exp <= cr_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "compression ratio exponent 9 (10^9) in range [1,12]",
    );
}

#[test]
fn bearing_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bearing", u32_ty());
    ctx.declare_var_typed("valid_bearing", i32_ty());
    // 1=ceramic ball, 2=magnetic levitation, 3=hybrid
    ctx.push_obligation(ProofObligation::assume("bt_val", "bearing == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "bt_valid_def",
        "valid_bearing == if bearing == 1 || bearing == 2 || bearing == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("bt_check", "valid_bearing == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bearing type 2 (magnetic levitation) is valid");
}

#[test]
fn backing_pump() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pump", u32_ty());
    ctx.declare_var_typed("valid_pump", i32_ty());
    // 1=rotary vane, 2=scroll, 3=diaphragm, 4=roots
    ctx.push_obligation(ProofObligation::assume("bp_val", "pump == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "bp_valid_def",
        "valid_pump == if pump == 1 || pump == 2 || pump == 3 || pump == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("bp_check", "valid_pump == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "backing pump 1 (rotary vane) is valid");
}

#[test]
fn cooling_method() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooling", u32_ty());
    ctx.declare_var_typed("valid_cooling", i32_ty());
    // 1=air-cooled, 2=water-cooled, 3=Peltier
    ctx.push_obligation(ProofObligation::assume("cl_val", "cooling == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "cl_valid_def",
        "valid_cooling == if cooling == 1 || cooling == 2 || cooling == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cl_check", "valid_cooling == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cooling method 3 (Peltier) is valid");
}

#[test]
fn power_consumption() {
    let mut ctx = VerificationContext::new();
    for v in &["watts", "watts_min", "watts_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Power consumption in W: value 250, valid range 10 to 2000
    ctx.push_obligation(ProofObligation::assume("pc_val", "watts == 250"));
    ctx.push_obligation(ProofObligation::assume("pc_min", "watts_min == 10"));
    ctx.push_obligation(ProofObligation::assume("pc_max", "watts_max == 2000"));
    ctx.push_obligation(ProofObligation::assert(
        "pc_in_range",
        "watts >= watts_min && watts <= watts_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power consumption 250 W in range [10,2000]");
}

#[test]
fn inlet_flange() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flange_dn", u32_ty());
    ctx.declare_var_typed("valid_flange", i32_ty());
    // Non-sequential DN sizes: 16, 25, 40, 63, 100 (ISO-KF)
    ctx.push_obligation(ProofObligation::assume("if_val", "flange_dn == 63"));
    ctx.push_obligation(ProofObligation::assume(
        "if_valid_def",
        "valid_flange == if flange_dn == 16 || flange_dn == 25 || flange_dn == 40 || flange_dn == 63 || flange_dn == 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("if_check", "valid_flange == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inlet flange DN63 (ISO-KF) is valid");
}

#[test]
fn vent_valve() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vent", i32_ty());
    // Boolean flag: 1=integrated, 0=external
    ctx.push_obligation(ProofObligation::assume("vv_val", "vent == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "vv_is_bool",
        "vent == 0 || vent == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vent valve 1 (integrated) is valid boolean");
}

#[test]
fn ultimate_pressure() {
    let mut ctx = VerificationContext::new();
    for v in &["upa", "upa_min", "upa_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Ultimate pressure in micro-Pascal: value 10, valid range 1 to 100000
    ctx.push_obligation(ProofObligation::assume("up_val", "upa == 10"));
    ctx.push_obligation(ProofObligation::assume("up_min", "upa_min == 1"));
    ctx.push_obligation(ProofObligation::assume("up_max", "upa_max == 100000"));
    ctx.push_obligation(ProofObligation::assert(
        "up_in_range",
        "upa >= upa_min && upa <= upa_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ultimate pressure 10 uPa in range [1,100000]");
}
