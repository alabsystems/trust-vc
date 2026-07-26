// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn target_power() {
    let mut ctx = VerificationContext::new();
    for v in &["tp_val", "tp_min", "tp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Target power in W: value 5000, valid range 100 to 20000
    ctx.push_obligation(ProofObligation::assume("tp_val", "tp_val == 5000"));
    ctx.push_obligation(ProofObligation::assume("tp_min", "tp_min == 100"));
    ctx.push_obligation(ProofObligation::assume("tp_max", "tp_max == 20000"));
    ctx.push_obligation(ProofObligation::assert(
        "tp_in_range",
        "tp_val >= tp_min && tp_val <= tp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "target power 5000 W in range [100,20000]");
}

#[test]
fn chamber_pressure() {
    let mut ctx = VerificationContext::new();
    for v in &["cp_val", "cp_min", "cp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Chamber pressure in mPa: value 400, valid range 1 to 10000
    ctx.push_obligation(ProofObligation::assume("cp_val", "cp_val == 400"));
    ctx.push_obligation(ProofObligation::assume("cp_min", "cp_min == 1"));
    ctx.push_obligation(ProofObligation::assume("cp_max", "cp_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "cp_in_range",
        "cp_val >= cp_min && cp_val <= cp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "chamber pressure 400 mPa in range [1,10000]");
}

#[test]
fn gas_flow() {
    let mut ctx = VerificationContext::new();
    for v in &["gf_val", "gf_min", "gf_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Gas flow in sccm: value 50, valid range 1 to 500
    ctx.push_obligation(ProofObligation::assume("gf_val", "gf_val == 50"));
    ctx.push_obligation(ProofObligation::assume("gf_min", "gf_min == 1"));
    ctx.push_obligation(ProofObligation::assume("gf_max", "gf_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "gf_in_range",
        "gf_val >= gf_min && gf_val <= gf_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gas flow 50 sccm in range [1,500]");
}

#[test]
fn target_material() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tm_type", u32_ty());
    ctx.declare_var_typed("valid_tm", i32_ty());
    // Target material: 1=Ti, 2=Al, 3=Cu, 4=Cr, 5=W
    ctx.push_obligation(ProofObligation::assume("tm_val", "tm_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "tm_def",
        "valid_tm == if tm_type == 1 || tm_type == 2 || tm_type == 3 || tm_type == 4 || tm_type == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("tm_chk", "valid_tm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "target material 1 (Ti) is valid sputtering target");
}

#[test]
fn power_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pm_type", u32_ty());
    ctx.declare_var_typed("valid_pm", i32_ty());
    // Power mode: 1=DC, 2=RF, 3=pulsed DC
    ctx.push_obligation(ProofObligation::assume("pm_val", "pm_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "pm_def",
        "valid_pm == if pm_type == 1 || pm_type == 2 || pm_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("pm_chk", "valid_pm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "power mode 3 (pulsed DC) is valid sputtering power mode",
    );
}

#[test]
fn substrate_temp() {
    let mut ctx = VerificationContext::new();
    for v in &["st_val", "st_min", "st_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Substrate temperature offset +500: value 750 (250°C), bounded 500-1300 (0°C to 800°C)
    ctx.push_obligation(ProofObligation::assume("st_val", "st_val == 750"));
    ctx.push_obligation(ProofObligation::assume("st_min", "st_min == 500"));
    ctx.push_obligation(ProofObligation::assume("st_max", "st_max == 1300"));
    ctx.push_obligation(ProofObligation::assert(
        "st_in_range",
        "st_val >= st_min && st_val <= st_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "substrate temp 750 (250°C offset+500) in range [500,1300] (0°C to 800°C)",
    );
}

#[test]
fn deposition_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["dr_val", "dr_min", "dr_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Deposition rate in nm/min: value 120, valid range 1 to 1000
    ctx.push_obligation(ProofObligation::assume("dr_val", "dr_val == 120"));
    ctx.push_obligation(ProofObligation::assume("dr_min", "dr_min == 1"));
    ctx.push_obligation(ProofObligation::assume("dr_max", "dr_max == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "dr_in_range",
        "dr_val >= dr_min && dr_val <= dr_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "deposition rate 120 nm/min in range [1,1000]");
}

#[test]
fn bias_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["bv_val", "bv_min", "bv_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Bias voltage in V DC: value 150, valid range 0 to 1000
    ctx.push_obligation(ProofObligation::assume("bv_val", "bv_val == 150"));
    ctx.push_obligation(ProofObligation::assume("bv_min", "bv_min == 0"));
    ctx.push_obligation(ProofObligation::assume("bv_max", "bv_max == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "bv_in_range",
        "bv_val >= bv_min && bv_val <= bv_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bias voltage 150 V DC in range [0,1000]");
}

#[test]
fn rotation_speed() {
    let mut ctx = VerificationContext::new();
    for v in &["rs_val", "rs_min", "rs_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Rotation speed in RPM: value 20, valid range 0 to 60
    ctx.push_obligation(ProofObligation::assume("rs_val", "rs_val == 20"));
    ctx.push_obligation(ProofObligation::assume("rs_min", "rs_min == 0"));
    ctx.push_obligation(ProofObligation::assume("rs_max", "rs_max == 60"));
    ctx.push_obligation(ProofObligation::assert(
        "rs_in_range",
        "rs_val >= rs_min && rs_val <= rs_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotation speed 20 RPM in range [0,60]");
}

#[test]
fn process_gas() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pg_type", u32_ty());
    ctx.declare_var_typed("valid_pg", i32_ty());
    // Process gas: 1=Ar, 2=N2, 3=O2
    ctx.push_obligation(ProofObligation::assume("pg_val", "pg_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "pg_def",
        "valid_pg == if pg_type == 1 || pg_type == 2 || pg_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("pg_chk", "valid_pg == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "process gas 1 (Ar) is valid sputtering process gas",
    );
}
