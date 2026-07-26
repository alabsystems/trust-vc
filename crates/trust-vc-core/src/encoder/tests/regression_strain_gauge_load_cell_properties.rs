// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn rated_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["kg", "kg_min", "kg_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Rated capacity in kg: value 5000, valid range 1 to 500000
    ctx.push_obligation(ProofObligation::assume("rc_val", "kg == 5000"));
    ctx.push_obligation(ProofObligation::assume("rc_min", "kg_min == 1"));
    ctx.push_obligation(ProofObligation::assume("rc_max", "kg_max == 500000"));
    ctx.push_obligation(ProofObligation::assert(
        "rc_in_range",
        "kg >= kg_min && kg <= kg_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rated capacity 5000 kg in range [1,500000]");
}

#[test]
fn sensitivity() {
    let mut ctx = VerificationContext::new();
    for v in &["mv_per_v_x1000", "sens_min", "sens_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Sensitivity in mV/V x1000: value 2000 (2.000 mV/V), valid range 500 to 4000
    ctx.push_obligation(ProofObligation::assume("sn_val", "mv_per_v_x1000 == 2000"));
    ctx.push_obligation(ProofObligation::assume("sn_min", "sens_min == 500"));
    ctx.push_obligation(ProofObligation::assume("sn_max", "sens_max == 4000"));
    ctx.push_obligation(ProofObligation::assert(
        "sn_in_range",
        "mv_per_v_x1000 >= sens_min && mv_per_v_x1000 <= sens_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sensitivity 2.000 mV/V in range [0.500,4.000]");
}

#[test]
fn accuracy_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_class", u32_ty());
    ctx.declare_var_typed("valid_class", i32_ty());
    // OIML R60 accuracy classes: 1=C3, 2=C4, 3=C5, 4=C6
    ctx.push_obligation(ProofObligation::assume("ac_val", "acc_class == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ac_def",
        "valid_class == if acc_class == 1 || acc_class == 2 || acc_class == 3 || acc_class == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ac_chk", "valid_class == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy class 2 (C4 per OIML R60) is valid");
}

#[test]
fn excitation_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["exc_mv", "exc_min", "exc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Excitation voltage in mV: value 10000 (10V), valid range 5000 to 15000
    ctx.push_obligation(ProofObligation::assume("ev_val", "exc_mv == 10000"));
    ctx.push_obligation(ProofObligation::assume("ev_min", "exc_min == 5000"));
    ctx.push_obligation(ProofObligation::assume("ev_max", "exc_max == 15000"));
    ctx.push_obligation(ProofObligation::assert(
        "ev_in_range",
        "exc_mv >= exc_min && exc_mv <= exc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "excitation voltage 10V in range [5V,15V]");
}

#[test]
fn bridge_resistance() {
    let mut ctx = VerificationContext::new();
    for v in &["ohms", "ohms_min", "ohms_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Bridge resistance in ohms: value 350 (typical), valid range 100 to 1000
    ctx.push_obligation(ProofObligation::assume("br_val", "ohms == 350"));
    ctx.push_obligation(ProofObligation::assume("br_min", "ohms_min == 100"));
    ctx.push_obligation(ProofObligation::assume("br_max", "ohms_max == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "br_in_range",
        "ohms >= ohms_min && ohms <= ohms_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bridge resistance 350 ohms in range [100,1000]");
}

#[test]
fn load_cell_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lc_type", u32_ty());
    ctx.declare_var_typed("valid_type", i32_ty());
    // 1=single point, 2=S-type, 3=compression, 4=shear beam, 5=canister
    ctx.push_obligation(ProofObligation::assume("lt_val", "lc_type == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "lt_def",
        "valid_type == if lc_type == 1 || lc_type == 2 || lc_type == 3 || lc_type == 4 || lc_type == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("lt_chk", "valid_type == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "load cell type 4 (shear beam) is valid");
}

#[test]
fn ip_rating() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ip_val", u32_ty());
    ctx.declare_var_typed("valid_ip", i32_ty());
    // IP ratings: 65=IP65, 67=IP67, 68=IP68 (non-sequential)
    ctx.push_obligation(ProofObligation::assume("ip_set", "ip_val == 67"));
    ctx.push_obligation(ProofObligation::assume(
        "ip_def",
        "valid_ip == if ip_val == 65 || ip_val == 67 || ip_val == 68 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ip_chk", "valid_ip == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IP67 is valid load cell protection rating");
}

#[test]
fn creep() {
    let mut ctx = VerificationContext::new();
    for v in &["creep_x1000", "creep_min", "creep_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Creep in % rated output x1000: value 20 (0.020%), valid range 1 to 500
    ctx.push_obligation(ProofObligation::assume("cr_val", "creep_x1000 == 20"));
    ctx.push_obligation(ProofObligation::assume("cr_min", "creep_min == 1"));
    ctx.push_obligation(ProofObligation::assume("cr_max", "creep_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "cr_in_range",
        "creep_x1000 >= creep_min && creep_x1000 <= creep_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "creep 0.020% rated output in range [0.001,0.500]");
}

#[test]
fn combined_error() {
    let mut ctx = VerificationContext::new();
    for v in &["err_x1000", "err_min", "err_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Combined error in % rated output x1000: value 200 (0.200%), valid range 10 to 5000
    ctx.push_obligation(ProofObligation::assume("ce_val", "err_x1000 == 200"));
    ctx.push_obligation(ProofObligation::assume("ce_min", "err_min == 10"));
    ctx.push_obligation(ProofObligation::assume("ce_max", "err_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "ce_in_range",
        "err_x1000 >= err_min && err_x1000 <= err_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "combined error 0.200% in range [0.010,5.000]");
}

#[test]
fn operating_temp() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Operating temperature -30 to 70°C, offset +500: 470 to 570
    ctx.push_obligation(ProofObligation::assume("ot_val", "temp_offset == 520")); // 20°C + 500
    ctx.push_obligation(ProofObligation::assume("ot_min", "min_temp_offset == 470")); // -30°C + 500
    ctx.push_obligation(ProofObligation::assume("ot_max", "max_temp_offset == 570")); // 70°C + 500
    ctx.push_obligation(ProofObligation::assume(
        "ot_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ot_chk", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "load cell 20°C in [-30,70] operating range");
}
