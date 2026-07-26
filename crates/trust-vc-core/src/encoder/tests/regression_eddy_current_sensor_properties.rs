// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn measurement_range() {
    // Full-scale measurement range in micrometers
    let mut ctx = VerificationContext::new();
    for v in &["range_um", "min_range", "max_range"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("range_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ru", "range_um == 2000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_range == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_range == 50000"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "range_ok == if range_um >= min_range && range_um <= max_range { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "range_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "eddy current: 2000um range within 100-50000um");
}

#[test]
fn resolution() {
    // Displacement resolution in nanometers
    let mut ctx = VerificationContext::new();
    for v in &["res_nm", "max_res"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("res_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rn", "res_nm == 50"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_res == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "res_ok == if res_nm <= max_res { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "res_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "eddy current: 50nm resolution within 1000nm max");
}

#[test]
fn linearity() {
    // Linearity x100 (percent of full scale); 20 = 0.20%, max 100 = 1.00%
    let mut ctx = VerificationContext::new();
    for v in &["lin_x100", "max_lin"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("lin_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lx", "lin_x100 == 20"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_lin == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "lin_ok == if lin_x100 <= max_lin { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "lin_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "eddy current: 0.20% linearity within 1.00% max");
}

#[test]
fn bandwidth() {
    // Frequency bandwidth in kHz
    let mut ctx = VerificationContext::new();
    for v in &["bw_khz", "min_bw", "max_bw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bw_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bk", "bw_khz == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_bw == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_bw == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bw_ok == if bw_khz >= min_bw && bw_khz <= max_bw { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "bw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "eddy current: 10kHz bandwidth within 1-100kHz");
}

#[test]
fn probe_diameter() {
    // Probe tip diameter in mm: valid sizes are 4, 5, 8, 12, 22
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter_mm", u32_ty());
    ctx.declare_var_typed("valid_diameter", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dm", "diameter_mm == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_diameter == if diameter_mm == 4 || diameter_mm == 5 || diameter_mm == 8 || diameter_mm == 12 || diameter_mm == 22 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "valid_diameter == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "eddy current: 8mm is a valid probe diameter");
}

#[test]
fn target_material() {
    // Target material: 1=steel, 2=aluminum, 3=copper, 4=titanium
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", u32_ty());
    ctx.declare_var_typed("valid_material", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mt", "material == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_material == if material == 1 || material == 2 || material == 3 || material == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "valid_material == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "eddy current: aluminum (2) is a valid target material",
    );
}

#[test]
fn operating_temperature() {
    // Temperature offset by +500 to keep unsigned: -40C=460, 200C=700, 20C=520
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp", "max_temp"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 520"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp == 460"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp == 700"));
    ctx.push_obligation(ProofObligation::assume(
        "tk_def",
        "temp_ok == if temp_offset >= min_temp && temp_offset <= max_temp { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "eddy current: 20C (offset 520) within -40C to 200C range",
    );
}

#[test]
fn output_signal() {
    // Output signal type: 1=voltage (0-10V), 2=current (4-20mA), 3=digital (RS485), 4=EtherCAT
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("signal_type", u32_ty());
    ctx.declare_var_typed("valid_signal", i32_ty());
    ctx.push_obligation(ProofObligation::assume("st", "signal_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_signal == if signal_type == 1 || signal_type == 2 || signal_type == 3 || signal_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "valid_signal == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "eddy current: RS485 (3) is a valid output signal type",
    );
}

#[test]
fn supply_voltage() {
    // Supply voltage in millivolts: 24V = 24000mV, range 18000-30000mV
    let mut ctx = VerificationContext::new();
    for v in &["supply_mv", "min_supply", "max_supply"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("supply_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sm", "supply_mv == 24000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_supply == 18000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_supply == 30000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "supply_ok == if supply_mv >= min_supply && supply_mv <= max_supply { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "supply_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "eddy current: 24V (24000mV) within 18-30V supply range",
    );
}

#[test]
fn cable_length() {
    // Maximum cable length in meters
    let mut ctx = VerificationContext::new();
    for v in &["cable_m", "min_cable", "max_cable"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cable_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cm", "cable_m == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_cable == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_cable == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cable_ok == if cable_m >= min_cable && cable_m <= max_cable { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "cable_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "eddy current: 10m cable within 1-30m range");
}
