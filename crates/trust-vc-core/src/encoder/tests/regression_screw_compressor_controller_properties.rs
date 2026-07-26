// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn motor_power() {
    let mut ctx = VerificationContext::new();
    for v in &["kw_val", "kw_min", "kw_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Motor power in kW: value 75, valid range 5 to 500
    ctx.push_obligation(ProofObligation::assume("mp_val", "kw_val == 75"));
    ctx.push_obligation(ProofObligation::assume("mp_min", "kw_min == 5"));
    ctx.push_obligation(ProofObligation::assume("mp_max", "kw_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "mp_in_range",
        "kw_val >= kw_min && kw_val <= kw_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power 75 kW in range [5,500]");
}

#[test]
fn discharge_pressure() {
    let mut ctx = VerificationContext::new();
    for v in &["dp_val", "dp_min", "dp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Discharge pressure x10 bar (8.5 bar = 85): value 85, valid range 40 to 160
    ctx.push_obligation(ProofObligation::assume("dp_val", "dp_val == 85"));
    ctx.push_obligation(ProofObligation::assume("dp_min", "dp_min == 40"));
    ctx.push_obligation(ProofObligation::assume("dp_max", "dp_max == 160"));
    ctx.push_obligation(ProofObligation::assert(
        "dp_in_range",
        "dp_val >= dp_min && dp_val <= dp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge pressure 85 (8.5 bar) in range [40,160]");
}

#[test]
fn free_air_delivery() {
    let mut ctx = VerificationContext::new();
    for v in &["fad_val", "fad_min", "fad_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Free air delivery in L/min: value 5000, valid range 100 to 50000
    ctx.push_obligation(ProofObligation::assume("fa_val", "fad_val == 5000"));
    ctx.push_obligation(ProofObligation::assume("fa_min", "fad_min == 100"));
    ctx.push_obligation(ProofObligation::assume("fa_max", "fad_max == 50000"));
    ctx.push_obligation(ProofObligation::assert(
        "fa_in_range",
        "fad_val >= fad_min && fad_val <= fad_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "free air delivery 5000 L/min in range [100,50000]");
}

#[test]
fn compressor_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comp_type", u32_ty());
    ctx.declare_var_typed("valid_ct", i32_ty());
    // Compressor types: 1=oil-injected, 2=oil-free, 3=water-injected
    ctx.push_obligation(ProofObligation::assume("ct_val", "comp_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ct_def",
        "valid_ct == if comp_type == 1 || comp_type == 2 || comp_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ct_chk", "valid_ct == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "compressor type 1 (oil-injected) is valid screw compressor type",
    );
}

#[test]
fn drive_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drv_type", u32_ty());
    ctx.declare_var_typed("valid_dt", i32_ty());
    // Drive types: 1=fixed speed, 2=variable speed (VFD), 3=dual speed
    ctx.push_obligation(ProofObligation::assume("dt_val", "drv_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "dt_def",
        "valid_dt == if drv_type == 1 || drv_type == 2 || drv_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("dt_chk", "valid_dt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drive type 2 (variable speed VFD) is valid compressor drive",
    );
}

#[test]
fn cooling_method() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cool_flag", i32_ty());
    ctx.declare_var_typed("valid_cm", i32_ty());
    // Cooling method: 1=air-cooled, 0=water-cooled
    ctx.push_obligation(ProofObligation::assume("cm_val", "cool_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "cm_def",
        "valid_cm == if cool_flag == 0 || cool_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cm_chk", "valid_cm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cooling method 1 (air-cooled) is valid cooling type",
    );
}

#[test]
fn oil_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["ot_val", "ot_min", "ot_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Oil temperature offset +500 (20C=520, 120C=620): value 570 (70C), valid range 520 to 620
    ctx.push_obligation(ProofObligation::assume("ot_val", "ot_val == 570"));
    ctx.push_obligation(ProofObligation::assume("ot_min", "ot_min == 520"));
    ctx.push_obligation(ProofObligation::assume("ot_max", "ot_max == 620"));
    ctx.push_obligation(ProofObligation::assert(
        "ot_in_range",
        "ot_val >= ot_min && ot_val <= ot_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "oil temperature 570 (70C) in range [520,620]");
}

#[test]
fn loading_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("load_mode", u32_ty());
    ctx.declare_var_typed("valid_lm", i32_ty());
    // Loading modes: 1=load/unload, 2=modulating, 3=variable displacement
    ctx.push_obligation(ProofObligation::assume("lm_val", "load_mode == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "lm_def",
        "valid_lm == if load_mode == 1 || load_mode == 2 || load_mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("lm_chk", "valid_lm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "loading mode 1 (load/unload) is valid compressor loading mode",
    );
}

#[test]
fn maintenance_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["mi_hrs", "mi_min", "mi_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Maintenance interval in hours: value 4000, valid range 1000 to 10000
    ctx.push_obligation(ProofObligation::assume("mi_val", "mi_hrs == 4000"));
    ctx.push_obligation(ProofObligation::assume("mi_min", "mi_min == 1000"));
    ctx.push_obligation(ProofObligation::assume("mi_max", "mi_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "mi_in_range",
        "mi_hrs >= mi_min && mi_hrs <= mi_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "maintenance interval 4000 hours in range [1000,10000]",
    );
}

#[test]
fn noise_level() {
    let mut ctx = VerificationContext::new();
    for v in &["nl_dba", "nl_min", "nl_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Noise level in dBA: value 75, valid range 50 to 100
    ctx.push_obligation(ProofObligation::assume("nl_val", "nl_dba == 75"));
    ctx.push_obligation(ProofObligation::assume("nl_min", "nl_min == 50"));
    ctx.push_obligation(ProofObligation::assume("nl_max", "nl_max == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "nl_in_range",
        "nl_dba >= nl_min && nl_dba <= nl_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "noise level 75 dBA in range [50,100]");
}
