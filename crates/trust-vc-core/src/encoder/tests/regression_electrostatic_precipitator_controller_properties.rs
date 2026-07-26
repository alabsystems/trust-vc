// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn operating_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["kv", "kv_min", "kv_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Operating voltage in kV: value 45, valid range 20 to 80
    ctx.push_obligation(ProofObligation::assume("ov_val", "kv == 45"));
    ctx.push_obligation(ProofObligation::assume("ov_min", "kv_min == 20"));
    ctx.push_obligation(ProofObligation::assume("ov_max", "kv_max == 80"));
    ctx.push_obligation(ProofObligation::assert(
        "ov_in_range",
        "kv >= kv_min && kv <= kv_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating voltage 45 kV in range [20,80]");
}

#[test]
fn current_density() {
    let mut ctx = VerificationContext::new();
    for v in &["ma_per_m2", "cd_min", "cd_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Current density in mA/m²: value 120, valid range 1 to 500
    ctx.push_obligation(ProofObligation::assume("cd_val", "ma_per_m2 == 120"));
    ctx.push_obligation(ProofObligation::assume("cd_lo", "cd_min == 1"));
    ctx.push_obligation(ProofObligation::assume("cd_hi", "cd_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "cd_in_range",
        "ma_per_m2 >= cd_min && ma_per_m2 <= cd_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "current density 120 mA/m2 in range [1,500]");
}

#[test]
fn field_count() {
    let mut ctx = VerificationContext::new();
    for v in &["fields", "fc_min", "fc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Number of electrical fields: value 4, valid range 1 to 8
    ctx.push_obligation(ProofObligation::assume("fc_val", "fields == 4"));
    ctx.push_obligation(ProofObligation::assume("fc_min", "fc_min == 1"));
    ctx.push_obligation(ProofObligation::assume("fc_max", "fc_max == 8"));
    ctx.push_obligation(ProofObligation::assert(
        "fc_in_range",
        "fields >= fc_min && fields <= fc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "field count 4 in range [1,8]");
}

#[test]
fn rapping_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rap_type", u32_ty());
    ctx.declare_var_typed("valid_rap", i32_ty());
    // 1=mechanical, 2=electromagnetic, 3=acoustic
    ctx.push_obligation(ProofObligation::assume("rt_val", "rap_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "rt_def",
        "valid_rap == if rap_type == 1 || rap_type == 2 || rap_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("rt_chk", "valid_rap == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rapping type 2 (electromagnetic) is valid");
}

#[test]
fn electrode_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("elec_type", u32_ty());
    ctx.declare_var_typed("valid_elec", i32_ty());
    // 1=weighted wire, 2=rigid frame, 3=tubular
    ctx.push_obligation(ProofObligation::assume("et_val", "elec_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "et_def",
        "valid_elec == if elec_type == 1 || elec_type == 2 || elec_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("et_chk", "valid_elec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "electrode type 1 (weighted wire) is valid");
}

#[test]
fn power_supply() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("psu_type", u32_ty());
    ctx.declare_var_typed("valid_psu", i32_ty());
    // 1=conventional TR, 2=high-frequency SMPS, 3=pulsed energization
    ctx.push_obligation(ProofObligation::assume("ps_val", "psu_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ps_def",
        "valid_psu == if psu_type == 1 || psu_type == 2 || psu_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ps_chk", "valid_psu == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "power supply type 3 (pulsed energization) is valid",
    );
}

#[test]
fn collection_efficiency() {
    let mut ctx = VerificationContext::new();
    for v in &["eff_x100", "eff_min", "eff_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Collection efficiency x100 %: value 9950 (99.50%), valid range 9000 to 9999
    ctx.push_obligation(ProofObligation::assume("ce_val", "eff_x100 == 9950"));
    ctx.push_obligation(ProofObligation::assume("ce_min", "eff_min == 9000"));
    ctx.push_obligation(ProofObligation::assume("ce_max", "eff_max == 9999"));
    ctx.push_obligation(ProofObligation::assert(
        "ce_in_range",
        "eff_x100 >= eff_min && eff_x100 <= eff_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "collection efficiency 99.50% in range [90.00,99.99]",
    );
}

#[test]
fn spark_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["sparks_per_min", "sr_min", "sr_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Spark rate per minute: value 50, valid range 0 to 200
    ctx.push_obligation(ProofObligation::assume("sr_val", "sparks_per_min == 50"));
    ctx.push_obligation(ProofObligation::assume("sr_lo", "sr_min == 0"));
    ctx.push_obligation(ProofObligation::assume("sr_hi", "sr_max == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "sr_in_range",
        "sparks_per_min >= sr_min && sparks_per_min <= sr_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spark rate 50/min in range [0,200]");
}

#[test]
fn gas_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "gt_min", "gt_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Gas temperature offset +500: value 650 (150°C), valid range 400 to 900 (-100°C to 400°C)
    ctx.push_obligation(ProofObligation::assume("gt_val", "temp_offset == 650"));
    ctx.push_obligation(ProofObligation::assume("gt_lo", "gt_min == 400"));
    ctx.push_obligation(ProofObligation::assume("gt_hi", "gt_max == 900"));
    ctx.push_obligation(ProofObligation::assume(
        "gt_def",
        "temp_ok == if temp_offset >= gt_min && temp_offset <= gt_max { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("gt_chk", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gas temperature 150C (offset 650) in range [-100,400]",
    );
}

#[test]
fn opacity_monitor() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("installed", i32_ty());
    // Opacity monitor: boolean flag, 1=installed, 0=not installed
    ctx.push_obligation(ProofObligation::assume("om_val", "installed == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "om_chk",
        "installed == 0 || installed == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "opacity monitor flag 1 (installed) is valid boolean",
    );
}
