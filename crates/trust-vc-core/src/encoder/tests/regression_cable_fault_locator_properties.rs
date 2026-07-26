// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn method() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fl_method", u32_ty());
    ctx.declare_var_typed("valid_fm", i32_ty());
    // Fault location methods: 1=TDR, 2=thumper/surge, 3=bridge, 4=acoustic
    ctx.push_obligation(ProofObligation::assume("fm_val", "fl_method == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "fm_def",
        "valid_fm == if fl_method == 1 || fl_method == 2 || fl_method == 3 || fl_method == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("fm_chk", "valid_fm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fault location method 1 (TDR) is valid technique");
}

#[test]
fn max_range() {
    let mut ctx = VerificationContext::new();
    for v in &["mr_val", "mr_min", "mr_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Maximum cable range in meters: value 10000, valid range 100 to 50000
    ctx.push_obligation(ProofObligation::assume("mr_set", "mr_val == 10000"));
    ctx.push_obligation(ProofObligation::assume("mr_lo", "mr_min == 100"));
    ctx.push_obligation(ProofObligation::assume("mr_hi", "mr_max == 50000"));
    ctx.push_obligation(ProofObligation::assert(
        "mr_in_range",
        "mr_val >= mr_min && mr_val <= mr_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max range 10000 m in range [100,50000]");
}

#[test]
fn resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["rs_val", "rs_min", "rs_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Resolution in tenths of a meter (0.1m = 1): value 1, valid range 1 to 100
    ctx.push_obligation(ProofObligation::assume("rs_set", "rs_val == 1"));
    ctx.push_obligation(ProofObligation::assume("rs_lo", "rs_min == 1"));
    ctx.push_obligation(ProofObligation::assume("rs_hi", "rs_max == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "rs_in_range",
        "rs_val >= rs_min && rs_val <= rs_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution 1 (0.1 m) in range [1,100]");
}

#[test]
fn pulse_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["pv_val", "pv_min", "pv_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Pulse voltage in V: value 25000 (thumper high-voltage), valid range 100 to 32000
    ctx.push_obligation(ProofObligation::assume("pv_set", "pv_val == 25000"));
    ctx.push_obligation(ProofObligation::assume("pv_lo", "pv_min == 100"));
    ctx.push_obligation(ProofObligation::assume("pv_hi", "pv_max == 32000"));
    ctx.push_obligation(ProofObligation::assert(
        "pv_in_range",
        "pv_val >= pv_min && pv_val <= pv_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pulse voltage 25000 V in range [100,32000]");
}

#[test]
fn impedance_range() {
    let mut ctx = VerificationContext::new();
    for v in &["ir_val", "ir_min", "ir_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Cable impedance in ohms: value 75, valid range 10 to 600
    ctx.push_obligation(ProofObligation::assume("ir_set", "ir_val == 75"));
    ctx.push_obligation(ProofObligation::assume("ir_lo", "ir_min == 10"));
    ctx.push_obligation(ProofObligation::assume("ir_hi", "ir_max == 600"));
    ctx.push_obligation(ProofObligation::assert(
        "ir_in_range",
        "ir_val >= ir_min && ir_val <= ir_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impedance 75 ohms in range [10,600]");
}

#[test]
fn cable_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ct_type", u32_ty());
    ctx.declare_var_typed("valid_ct", i32_ty());
    // Cable insulation types: 1=XLPE, 2=paper-insulated lead-covered, 3=EPR, 4=PVC
    ctx.push_obligation(ProofObligation::assume("ct_val", "ct_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ct_def",
        "valid_ct == if ct_type == 1 || ct_type == 2 || ct_type == 3 || ct_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ct_chk", "valid_ct == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cable type 1 (XLPE) is valid insulation type");
}

#[test]
fn velocity_factor() {
    let mut ctx = VerificationContext::new();
    for v in &["vf_val", "vf_min", "vf_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Velocity factor x100 (0.50 = 50): value 50, valid range 30 to 99
    ctx.push_obligation(ProofObligation::assume("vf_set", "vf_val == 50"));
    ctx.push_obligation(ProofObligation::assume("vf_lo", "vf_min == 30"));
    ctx.push_obligation(ProofObligation::assume("vf_hi", "vf_max == 99"));
    ctx.push_obligation(ProofObligation::assert(
        "vf_in_range",
        "vf_val >= vf_min && vf_val <= vf_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "velocity factor 50 (0.50c) in range [30,99]");
}

#[test]
fn output_energy() {
    let mut ctx = VerificationContext::new();
    for v in &["oe_val", "oe_min", "oe_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Surge generator output energy in joules: value 2000, valid range 1 to 4000
    ctx.push_obligation(ProofObligation::assume("oe_set", "oe_val == 2000"));
    ctx.push_obligation(ProofObligation::assume("oe_lo", "oe_min == 1"));
    ctx.push_obligation(ProofObligation::assume("oe_hi", "oe_max == 4000"));
    ctx.push_obligation(ProofObligation::assert(
        "oe_in_range",
        "oe_val >= oe_min && oe_val <= oe_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output energy 2000 J in range [1,4000]");
}

#[test]
fn fault_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ft_type", u32_ty());
    ctx.declare_var_typed("valid_ft", i32_ty());
    // Cable fault types: 1=open, 2=short, 3=high-resistance, 4=intermittent
    ctx.push_obligation(ProofObligation::assume("ft_val", "ft_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ft_def",
        "valid_ft == if ft_type == 1 || ft_type == 2 || ft_type == 3 || ft_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ft_chk", "valid_ft == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fault type 3 (high-resistance) is valid cable fault class",
    );
}

#[test]
fn data_storage() {
    let mut ctx = VerificationContext::new();
    for v in &["ds_val", "ds_min", "ds_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Data storage capacity in records: value 5000, valid range 1 to 10000
    ctx.push_obligation(ProofObligation::assume("ds_set", "ds_val == 5000"));
    ctx.push_obligation(ProofObligation::assume("ds_lo", "ds_min == 1"));
    ctx.push_obligation(ProofObligation::assume("ds_hi", "ds_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "ds_in_range",
        "ds_val >= ds_min && ds_val <= ds_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "data storage 5000 records in range [1,10000]");
}
