// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn measurement_range() {
    let mut ctx = VerificationContext::new();
    for v in &["probe_length_mm", "min_probe_mm", "max_probe_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("range_ok", i32_ty());
    // Magnetostrictive probe length in mm
    ctx.push_obligation(ProofObligation::assume("pl", "probe_length_mm == 3000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_probe_mm == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_probe_mm == 15000"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "range_ok == if probe_length_mm >= min_probe_mm && probe_length_mm <= max_probe_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "range_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Magnetostrictive: 3000mm probe in [100, 15000] -> OK",
    );
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x100", "max_accuracy_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Accuracy in mm x100 (0.50mm = 50, max 2.00mm = 200)
    ctx.push_obligation(ProofObligation::assume("ax", "accuracy_x100 == 50")); // 0.50mm
    ctx.push_obligation(ProofObligation::assume("ma", "max_accuracy_x100 == 200")); // 2.00mm
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_x100 <= max_accuracy_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Magnetostrictive: 0.50mm accuracy <= 2.00mm max -> OK",
    );
}

#[test]
fn resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["resolution_um", "max_resolution_um"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("res_ok", i32_ty());
    // Resolution in micrometers
    ctx.push_obligation(ProofObligation::assume("ru", "resolution_um == 2"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_resolution_um == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "res_ok == if resolution_um <= max_resolution_um { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "res_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Magnetostrictive: 2um resolution <= 10um max -> OK",
    );
}

#[test]
fn process_connection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conn_type", u32_ty());
    ctx.declare_var_typed("valid_conn", i32_ty());
    // Connection types: 1=flanged, 2=threaded (NPT), 3=tri-clamp, 4=compression fitting
    ctx.push_obligation(ProofObligation::assume("ct", "conn_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_conn == if conn_type == 1 || conn_type == 2 || conn_type == 3 || conn_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_conn == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Magnetostrictive: threaded NPT is valid connection",
    );
}

#[test]
fn output_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output", u32_ty());
    ctx.declare_var_typed("valid_output", i32_ty());
    // Output types: 1=4-20mA, 2=4-20mA HART, 3=Modbus RTU, 4=PROFIBUS PA, 5=Foundation Fieldbus
    ctx.push_obligation(ProofObligation::assume("ot", "output == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "valid_output == if output == 1 || output == 2 || output == 3 || output == 4 || output == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_output == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Magnetostrictive: 4-20mA HART is valid output type",
    );
}

#[test]
fn float_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ftype", u32_ty());
    ctx.declare_var_typed("valid_float", i32_ty());
    // Float types: 1=standard (liquid), 2=interface (two-liquid), 3=multi-point
    ctx.push_obligation(ProofObligation::assume("ft", "ftype == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vf_def",
        "valid_float == if ftype == 1 || ftype == 2 || ftype == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_float == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Magnetostrictive: standard liquid float is valid type",
    );
}

#[test]
fn process_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Process temperature: -40C to +150C (offset +500)
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 520")); // 20C
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 460")); // -40C
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 650")); // 150C
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Magnetostrictive: 20C process temp in [-40, 150] -> OK",
    );
}

#[test]
fn process_pressure() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure_bar", "max_pressure_bar"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("press_ok", i32_ty());
    // Max process pressure rating
    ctx.push_obligation(ProofObligation::assume("pb", "pressure_bar == 100"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_pressure_bar == 350"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "press_ok == if pressure_bar <= max_pressure_bar { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "press_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Magnetostrictive: 100 bar <= 350 max -> OK");
}

#[test]
fn specific_gravity() {
    let mut ctx = VerificationContext::new();
    for v in &["sg_x100", "min_sg_x100", "max_sg_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sg_ok", i32_ty());
    // Minimum specific gravity x100 (0.70 = 70, range 0.40-2.00)
    ctx.push_obligation(ProofObligation::assume("sg", "sg_x100 == 70")); // 0.70
    ctx.push_obligation(ProofObligation::assume("mn", "min_sg_x100 == 40")); // 0.40
    ctx.push_obligation(ProofObligation::assume("mx", "max_sg_x100 == 200")); // 2.00
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sg_ok == if sg_x100 >= min_sg_x100 && sg_x100 <= max_sg_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sg_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Magnetostrictive: SG 0.70 in [0.40, 2.00] -> OK");
}

#[test]
fn repeatability() {
    let mut ctx = VerificationContext::new();
    for v in &["repeat_um", "max_repeat_um"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rep_ok", i32_ty());
    // Repeatability in micrometers
    ctx.push_obligation(ProofObligation::assume("ru", "repeat_um == 1"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_repeat_um == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rep_ok == if repeat_um <= max_repeat_um { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rep_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Magnetostrictive: 1um repeatability <= 5um max -> OK",
    );
}
