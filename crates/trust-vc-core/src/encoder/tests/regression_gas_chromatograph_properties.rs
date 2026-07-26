// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_oven_temp_max() {
    let mut ctx = VerificationContext::new();
    for v in &["oven_temp_c", "min_temp_c", "max_temp_c"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Column oven temperature range
    ctx.push_obligation(ProofObligation::assume("ot", "oven_temp_c == 450"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_c == 50"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_c == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if oven_temp_c >= min_temp_c && oven_temp_c <= max_temp_c { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GC: oven 450C in [50, 500] -> OK");
}

#[test]
fn test_ramp_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["ramp_x10", "min_ramp_x10", "max_ramp_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ramp_ok", i32_ty());
    // Heating ramp rate x10 (20.0 C/min = 200)
    ctx.push_obligation(ProofObligation::assume("rx", "ramp_x10 == 200"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_ramp_x10 == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_ramp_x10 == 1200"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "ramp_ok == if ramp_x10 >= min_ramp_x10 && ramp_x10 <= max_ramp_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ramp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GC: ramp 20.0 C/min (200x10) in [10, 1200] -> OK");
}

#[test]
fn test_detector_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det_type", u32_ty());
    ctx.declare_var_typed("valid_det", i32_ty());
    // Detector types: 1=FID, 2=TCD, 3=ECD, 4=MS
    ctx.push_obligation(ProofObligation::assume("dt", "det_type == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_det == if det_type == 1 || det_type == 2 || det_type == 3 || det_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_det == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GC: MS is valid detector type (4-way)");
}

#[test]
fn test_carrier_gas() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("carrier", u32_ty());
    ctx.declare_var_typed("valid_carrier", i32_ty());
    // Carrier gas: 1=helium, 2=nitrogen, 3=hydrogen
    ctx.push_obligation(ProofObligation::assume("cg", "carrier == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_carrier == if carrier == 1 || carrier == 2 || carrier == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_carrier == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GC: helium is valid carrier gas (3-way)");
}

#[test]
fn test_column_length() {
    let mut ctx = VerificationContext::new();
    for v in &["col_length_m", "min_length_m", "max_length_m"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("length_ok", i32_ty());
    // Capillary column length in meters
    ctx.push_obligation(ProofObligation::assume("cl", "col_length_m == 30"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_length_m == 5"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_length_m == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "length_ok == if col_length_m >= min_length_m && col_length_m <= max_length_m { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "length_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GC: column 30m in [5, 100] -> OK");
}

#[test]
fn test_column_id() {
    let mut ctx = VerificationContext::new();
    for v in &["col_id_um", "min_id_um", "max_id_um"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("id_ok", i32_ty());
    // Column internal diameter in micrometers
    ctx.push_obligation(ProofObligation::assume("ci", "col_id_um == 250"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_id_um == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_id_um == 530"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "id_ok == if col_id_um >= min_id_um && col_id_um <= max_id_um { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "id_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GC: column ID 250um in [100, 530] -> OK");
}

#[test]
fn test_injection_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inj_mode", u32_ty());
    ctx.declare_var_typed("valid_mode", i32_ty());
    // Injection modes: 1=split, 2=splitless, 3=on-column
    ctx.push_obligation(ProofObligation::assume("im", "inj_mode == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mode == if inj_mode == 1 || inj_mode == 2 || inj_mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GC: splitless is valid injection mode (3-way)");
}

#[test]
fn test_sample_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["inj_vol_ul", "min_vol_ul", "max_vol_ul"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vol_ok", i32_ty());
    // Injection volume in microliters
    ctx.push_obligation(ProofObligation::assume("iv", "inj_vol_ul == 1"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_vol_ul == 0"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_vol_ul == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vol_ok == if inj_vol_ul >= min_vol_ul && inj_vol_ul <= max_vol_ul { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vol_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GC: injection 1uL in [0, 10] -> OK");
}

#[test]
fn test_run_time() {
    let mut ctx = VerificationContext::new();
    for v in &["run_time_s", "min_run_s", "max_run_s"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("time_ok", i32_ty());
    // Analysis duration in seconds
    ctx.push_obligation(ProofObligation::assume("rt", "run_time_s == 1800"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_run_s == 60"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_run_s == 7200"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "time_ok == if run_time_s >= min_run_s && run_time_s <= max_run_s { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "time_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GC: run 1800s in [60, 7200] -> OK");
}

#[test]
fn test_autosampler() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("autosampler_enabled", i32_ty());
    ctx.declare_var_typed("autosampler_active", i32_ty());
    // Autosampler as boolean flag (i32: 1=enabled, 0=disabled)
    ctx.push_obligation(ProofObligation::assume("ae", "autosampler_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "aa_def",
        "autosampler_active == if autosampler_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "autosampler_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GC: autosampler enabled -> active (boolean flag)");
}
