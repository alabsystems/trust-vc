// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn protection_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("prot_type", u32_ty());
    ctx.declare_var_typed("valid_type", i32_ty());
    // 1=impressed current (ICCP), 2=sacrificial anode (SACP)
    ctx.push_obligation(ProofObligation::assume("pt_val", "prot_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "pt_valid_def",
        "valid_type == if prot_type == 1 || prot_type == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("pt_check", "valid_type == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "protection type 1 (ICCP) is valid");
}

#[test]
fn output_current() {
    let mut ctx = VerificationContext::new();
    for v in &["current_ma", "current_min", "current_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Output current in mA: value 5000 (5A), valid range 1 to 100000 (100A)
    ctx.push_obligation(ProofObligation::assume("oc_val", "current_ma == 5000"));
    ctx.push_obligation(ProofObligation::assume("oc_min", "current_min == 1"));
    ctx.push_obligation(ProofObligation::assume("oc_max", "current_max == 100000"));
    ctx.push_obligation(ProofObligation::assert(
        "oc_in_range",
        "current_ma >= current_min && current_ma <= current_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "output current 5000 mA (5A) in range [1,100000] (up to 100A)",
    );
}

#[test]
fn reference_potential() {
    let mut ctx = VerificationContext::new();
    for v in &["potential_mv", "pot_min", "pot_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Offset +2000 mV: -850 mV Cu/CuSO4 → 1150, range 500 (-1500 mV) to 2500 (+500 mV)
    ctx.push_obligation(ProofObligation::assume("rp_val", "potential_mv == 1150"));
    ctx.push_obligation(ProofObligation::assume("rp_min", "pot_min == 500"));
    ctx.push_obligation(ProofObligation::assume("rp_max", "pot_max == 2500"));
    ctx.push_obligation(ProofObligation::assert(
        "rp_in_range",
        "potential_mv >= pot_min && potential_mv <= pot_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "reference potential 1150 (-850 mV Cu/CuSO4) in range [500,2500]",
    );
}

#[test]
fn anode_count() {
    let mut ctx = VerificationContext::new();
    for v in &["anodes", "anode_min", "anode_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Number of anodes: value 12, valid range 1 to 100
    ctx.push_obligation(ProofObligation::assume("ac_val", "anodes == 12"));
    ctx.push_obligation(ProofObligation::assume("ac_min", "anode_min == 1"));
    ctx.push_obligation(ProofObligation::assume("ac_max", "anode_max == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "ac_in_range",
        "anodes >= anode_min && anodes <= anode_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "anode count 12 in range [1,100]");
}

#[test]
fn channel_count() {
    let mut ctx = VerificationContext::new();
    for v in &["channels", "chan_min", "chan_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Number of monitoring channels: value 8, valid range 1 to 32
    ctx.push_obligation(ProofObligation::assume("cc_val", "channels == 8"));
    ctx.push_obligation(ProofObligation::assume("cc_min", "chan_min == 1"));
    ctx.push_obligation(ProofObligation::assume("cc_max", "chan_max == 32"));
    ctx.push_obligation(ProofObligation::assert(
        "cc_in_range",
        "channels >= chan_min && channels <= chan_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "channel count 8 in range [1,32]");
}

#[test]
fn reference_cell() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ref_cell", u32_ty());
    ctx.declare_var_typed("valid_cell", i32_ty());
    // 1=Cu/CuSO4, 2=Ag/AgCl, 3=Zn, 4=SCE
    ctx.push_obligation(ProofObligation::assume("rc_val", "ref_cell == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "rc_valid_def",
        "valid_cell == if ref_cell == 1 || ref_cell == 2 || ref_cell == 3 || ref_cell == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("rc_check", "valid_cell == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reference cell 1 (Cu/CuSO4) is valid");
}

#[test]
fn output_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["voltage_mv", "volt_min", "volt_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Output voltage in mV DC: value 12000 (12V), valid range 1000 (1V) to 50000 (50V)
    ctx.push_obligation(ProofObligation::assume("ov_val", "voltage_mv == 12000"));
    ctx.push_obligation(ProofObligation::assume("ov_min", "volt_min == 1000"));
    ctx.push_obligation(ProofObligation::assume("ov_max", "volt_max == 50000"));
    ctx.push_obligation(ProofObligation::assert(
        "ov_in_range",
        "voltage_mv >= volt_min && voltage_mv <= volt_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "output voltage 12000 mV (12V) in range [1000,50000] (1-50V)",
    );
}

#[test]
fn operating_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("op_mode", u32_ty());
    ctx.declare_var_typed("valid_mode", i32_ty());
    // 1=constant potential, 2=constant current, 3=pulsed, 4=GPS-synchronized
    ctx.push_obligation(ProofObligation::assume("om_val", "op_mode == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "om_valid_def",
        "valid_mode == if op_mode == 1 || op_mode == 2 || op_mode == 3 || op_mode == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("om_check", "valid_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating mode 2 (constant current) is valid");
}

#[test]
fn data_logging() {
    let mut ctx = VerificationContext::new();
    for v in &["log_interval_s", "log_min", "log_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Data logging interval in seconds: value 300 (5 min), valid range 1 to 86400 (24h)
    ctx.push_obligation(ProofObligation::assume("dl_val", "log_interval_s == 300"));
    ctx.push_obligation(ProofObligation::assume("dl_min", "log_min == 1"));
    ctx.push_obligation(ProofObligation::assume("dl_max", "log_max == 86400"));
    ctx.push_obligation(ProofObligation::assert(
        "dl_in_range",
        "log_interval_s >= log_min && log_interval_s <= log_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "logging interval 300s (5 min) in range [1,86400] (1s to 24h)",
    );
}

#[test]
fn coating_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("coating", u32_ty());
    ctx.declare_var_typed("valid_coating", i32_ty());
    // 1=FBE (fusion bonded epoxy), 2=polyethylene, 3=coal tar enamel
    ctx.push_obligation(ProofObligation::assume("ct_val", "coating == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ct_valid_def",
        "valid_coating == if coating == 1 || coating == 2 || coating == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ct_check", "valid_coating == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "coating type 2 (polyethylene) is valid");
}
