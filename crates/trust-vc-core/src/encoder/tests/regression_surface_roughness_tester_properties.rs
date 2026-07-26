// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn ra_range() {
    let mut ctx = VerificationContext::new();
    for v in &["ra_x1000", "min_ra", "max_ra"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ra_ok", i32_ty());
    // Ra roughness in x1000 um: 0.050 um -> 50, bounded [1, 50000]
    ctx.push_obligation(ProofObligation::assume("rv", "ra_x1000 == 50"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_ra == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_ra == 50000"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "ra_ok == if ra_x1000 >= min_ra && ra_x1000 <= max_ra { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ra_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SRT: Ra 0.050 um (50) in [1, 50000] -> OK");
}

#[test]
fn cutoff_length() {
    let mut ctx = VerificationContext::new();
    for v in &["cutoff_x100", "min_cutoff", "max_cutoff"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cutoff_ok", i32_ty());
    // Cutoff length in x100 mm: 0.80 mm -> 80, bounded [8, 800]
    ctx.push_obligation(ProofObligation::assume("cv", "cutoff_x100 == 80"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_cutoff == 8"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_cutoff == 800"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cutoff_ok == if cutoff_x100 >= min_cutoff && cutoff_x100 <= max_cutoff { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cutoff_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SRT: cutoff 0.80 mm (80) in [8, 800] -> OK");
}

#[test]
fn traverse_length() {
    let mut ctx = VerificationContext::new();
    for v in &["traverse_mm", "min_traverse", "max_traverse"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("trav_ok", i32_ty());
    // Traverse length in mm, bounded [1, 100]
    ctx.push_obligation(ProofObligation::assume("tv", "traverse_mm == 12"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_traverse == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_traverse == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "trav_ok == if traverse_mm >= min_traverse && traverse_mm <= max_traverse { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "trav_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SRT: traverse 12 mm in [1, 100] -> OK");
}

#[test]
fn stylus_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stylus_type", u32_ty());
    ctx.declare_var_typed("valid_stylus", i32_ty());
    // Stylus types: 1=conical, 2=chisel, 3=ball
    ctx.push_obligation(ProofObligation::assume("st", "stylus_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_stylus == if stylus_type == 1 || stylus_type == 2 || stylus_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_stylus == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SRT: conical (1) is valid stylus type");
}

#[test]
fn stylus_radius() {
    let mut ctx = VerificationContext::new();
    for v in &["radius_x10", "min_radius", "max_radius"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("radius_ok", i32_ty());
    // Stylus radius in x10 um: 2.0 um -> 20, bounded [5, 100]
    ctx.push_obligation(ProofObligation::assume("rv", "radius_x10 == 20"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_radius == 5"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_radius == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "radius_ok == if radius_x10 >= min_radius && radius_x10 <= max_radius { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "radius_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SRT: stylus radius 2.0 um (20) in [5, 100] -> OK");
}

#[test]
fn parameter_set() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("param_set", u32_ty());
    ctx.declare_var_typed("valid_param", i32_ty());
    // Parameter sets: 1=Ra/Rq, 2=Rz/Rt, 3=Rp/Rv, 4=RSm/Rmr
    ctx.push_obligation(ProofObligation::assume("ps", "param_set == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_param == if param_set == 1 || param_set == 2 || param_set == 3 || param_set == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_param == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SRT: Rz/Rt (2) is valid parameter set");
}

#[test]
fn data_output() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_type", u32_ty());
    ctx.declare_var_typed("valid_output", i32_ty());
    // Data output: 1=USB, 2=Bluetooth, 3=RS-232
    ctx.push_obligation(ProofObligation::assume("ot", "output_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "valid_output == if output_type == 1 || output_type == 2 || output_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_output == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SRT: RS-232 (3) is valid data output");
}

#[test]
fn measurement_speed() {
    let mut ctx = VerificationContext::new();
    for v in &["speed_x10", "min_speed", "max_speed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("speed_ok", i32_ty());
    // Measurement speed in x10 mm/s: 0.5 mm/s -> 5, bounded [1, 50]
    ctx.push_obligation(ProofObligation::assume("sv", "speed_x10 == 5"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_speed == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_speed == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "speed_ok == if speed_x10 >= min_speed && speed_x10 <= max_speed { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "speed_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SRT: speed 0.5 mm/s (5) in [1, 50] -> OK");
}

#[test]
fn operating_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Operating temperature: offset +500, actual 20 C -> 520, range -50 C (450) to 80 C (580)
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 520")); // 20 C
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 450")); // -50 C
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 580")); // 80 C
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "SRT: 20 C operating temp in [-50, 80] (offset +500) -> OK",
    );
}

#[test]
fn auto_calibration() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_cal", i32_ty());
    ctx.declare_var_typed("cal_valid", i32_ty());
    // Auto-calibration boolean flag: 0=disabled, 1=enabled
    ctx.push_obligation(ProofObligation::assume("ac", "auto_cal == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "cv_def",
        "cal_valid == if auto_cal == 0 || auto_cal == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cal_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "SRT: auto-calibration enabled (1) is valid boolean",
    );
}
