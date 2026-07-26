// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn flow_threshold() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_ml_min", u32_ty());
    ctx.declare_var_typed("flow_ok", i32_ty());
    // Trigger flow rate in mL/min: 500, valid range 10-50000
    ctx.push_obligation(ProofObligation::assume("val", "flow_ml_min == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "flow_ok == if flow_ml_min >= 10 && flow_ml_min <= 50000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "flow_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Magnetic flow switch: 500 mL/min trigger flow rate in [10, 50000]",
    );
}

#[test]
fn pipe_diameter() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter_mm", u32_ty());
    ctx.declare_var_typed("valid_dn", i32_ty());
    // Pipe diameter DN15-DN50: 15/20/25/32/40/50 mm
    ctx.push_obligation(ProofObligation::assume("val", "diameter_mm == 25"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_dn == if diameter_mm == 15 || diameter_mm == 20 || diameter_mm == 25 || diameter_mm == 32 || diameter_mm == 40 || diameter_mm == 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_dn == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Magnetic flow switch: DN25 (25mm) is valid pipe diameter",
    );
}

#[test]
fn switch_output() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_type", u32_ty());
    ctx.declare_var_typed("valid_output", i32_ty());
    // 1=PNP NO, 2=PNP NC, 3=NPN NO, 4=NPN NC
    ctx.push_obligation(ProofObligation::assume("val", "output_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "valid_output == if output_type == 1 || output_type == 2 || output_type == 3 || output_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_output == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Magnetic flow switch: PNP NO (1) is valid switch output type",
    );
}

#[test]
fn media_viscosity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("viscosity_cst", u32_ty());
    ctx.declare_var_typed("viscosity_ok", i32_ty());
    // Max viscosity in cSt: 100, max 500
    ctx.push_obligation(ProofObligation::assume("val", "viscosity_cst == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "viscosity_ok == if viscosity_cst <= 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "viscosity_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Magnetic flow switch: 100 cSt media viscosity within max 500",
    );
}

#[test]
fn process_pressure() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_bar", u32_ty());
    ctx.declare_var_typed("pressure_ok", i32_ty());
    // Max pressure in bar: 100, max 250
    ctx.push_obligation(ProofObligation::assume("val", "pressure_bar == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "pressure_ok == if pressure_bar <= 250 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "pressure_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Magnetic flow switch: 100 bar process pressure within max 250",
    );
}

#[test]
fn process_temperature() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", u32_ty());
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Temperature offset +500: value 520 (20C), min 480 (-20C), max 580 (80C)
    ctx.push_obligation(ProofObligation::assume("val", "temp_offset == 520"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "temp_ok == if temp_offset >= 480 && temp_offset <= 580 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Magnetic flow switch: 20C (offset 520) process temperature in [-20C, 80C]",
    );
}

#[test]
fn repeatability() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("repeat_x10", u32_ty());
    ctx.declare_var_typed("repeat_ok", i32_ty());
    // Repeatability x10 (%): value 30 (3.0%), max 50 (5.0%)
    ctx.push_obligation(ProofObligation::assume("val", "repeat_x10 == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "repeat_ok == if repeat_x10 <= 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "repeat_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Magnetic flow switch: 3.0% repeatability within max 5.0%",
    );
}

#[test]
fn hysteresis() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hyst_x10", u32_ty());
    ctx.declare_var_typed("hyst_ok", i32_ty());
    // Switching hysteresis x10 (%): value 20 (2.0%), max 100 (10.0%)
    ctx.push_obligation(ProofObligation::assume("val", "hyst_x10 == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "hyst_ok == if hyst_x10 <= 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "hyst_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Magnetic flow switch: 2.0% hysteresis within max 10.0%",
    );
}

#[test]
fn connection_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conn_type", u32_ty());
    ctx.declare_var_typed("valid_conn", i32_ty());
    // 1=G thread, 2=NPT thread, 3=tri-clamp, 4=flanged
    ctx.push_obligation(ProofObligation::assume("val", "conn_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_conn == if conn_type == 1 || conn_type == 2 || conn_type == 3 || conn_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_conn == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Magnetic flow switch: tri-clamp (3) is valid connection type",
    );
}

#[test]
fn response_delay() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("delay_ms", u32_ty());
    ctx.declare_var_typed("delay_ok", i32_ty());
    // Switch response delay in ms: value 100, max 1000
    ctx.push_obligation(ProofObligation::assume("val", "delay_ms == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "delay_ok == if delay_ms <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "delay_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Magnetic flow switch: 100ms response delay within max 1000ms",
    );
}
