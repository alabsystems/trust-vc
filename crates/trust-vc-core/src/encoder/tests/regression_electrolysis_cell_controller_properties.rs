// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_cell_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["voltage_mv", "volt_min", "volt_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Cell voltage in mV: value 2000 (2.0V), valid range 1200 (1.2V) to 3000 (3.0V)
    ctx.push_obligation(ProofObligation::assume("cv_val", "voltage_mv == 2000"));
    ctx.push_obligation(ProofObligation::assume("cv_min", "volt_min == 1200"));
    ctx.push_obligation(ProofObligation::assume("cv_max", "volt_max == 3000"));
    ctx.push_obligation(ProofObligation::assert(
        "cv_in_range",
        "voltage_mv >= volt_min && voltage_mv <= volt_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cell voltage 2000 mV (2.0V) in range [1200,3000] (1.2-3.0V)",
    );
}

#[test]
fn test_current_density() {
    let mut ctx = VerificationContext::new();
    for v in &["density_ma_cm2", "dens_min", "dens_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Current density in mA/cm2: value 200, valid range 10 to 2000
    ctx.push_obligation(ProofObligation::assume("cd_val", "density_ma_cm2 == 200"));
    ctx.push_obligation(ProofObligation::assume("cd_min", "dens_min == 10"));
    ctx.push_obligation(ProofObligation::assume("cd_max", "dens_max == 2000"));
    ctx.push_obligation(ProofObligation::assert(
        "cd_in_range",
        "density_ma_cm2 >= dens_min && density_ma_cm2 <= dens_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "current density 200 mA/cm2 in range [10,2000]");
}

#[test]
fn test_cell_count() {
    let mut ctx = VerificationContext::new();
    for v in &["cells", "cell_min", "cell_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Number of cells in stack: value 100, valid range 1 to 500
    ctx.push_obligation(ProofObligation::assume("cc_val", "cells == 100"));
    ctx.push_obligation(ProofObligation::assume("cc_min", "cell_min == 1"));
    ctx.push_obligation(ProofObligation::assume("cc_max", "cell_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "cc_in_range",
        "cells >= cell_min && cells <= cell_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cell count 100 in range [1,500]");
}

#[test]
fn test_electrolyte_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("electrolyte", u32_ty());
    ctx.declare_var_typed("valid_electrolyte", i32_ty());
    // 1=KOH alkaline, 2=PEM, 3=solid oxide
    ctx.push_obligation(ProofObligation::assume("et_val", "electrolyte == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "et_valid_def",
        "valid_electrolyte == if electrolyte == 1 || electrolyte == 2 || electrolyte == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "et_check",
        "valid_electrolyte == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "electrolyte type 1 (KOH alkaline) is valid");
}

#[test]
fn test_gas_purity() {
    let mut ctx = VerificationContext::new();
    for v in &["purity_x100", "pur_min", "pur_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Gas purity as x100 %: value 9999 (99.99%), valid range 9900 (99.00%) to 9999 (99.99%)
    ctx.push_obligation(ProofObligation::assume("gp_val", "purity_x100 == 9999"));
    ctx.push_obligation(ProofObligation::assume("gp_min", "pur_min == 9900"));
    ctx.push_obligation(ProofObligation::assume("gp_max", "pur_max == 9999"));
    ctx.push_obligation(ProofObligation::assert(
        "gp_in_range",
        "purity_x100 >= pur_min && purity_x100 <= pur_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gas purity 9999 (99.99%) in range [9900,9999] (99.00%-99.99%)",
    );
}

#[test]
fn test_operating_temp_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "temp_min", "temp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Operating temp offset +500 (deg C): value 580 (80C), valid range 520 (20C) to 1300 (800C for SOEC)
    ctx.push_obligation(ProofObligation::assume("ot_val", "temp_offset == 580"));
    ctx.push_obligation(ProofObligation::assume("ot_min", "temp_min == 520"));
    ctx.push_obligation(ProofObligation::assume("ot_max", "temp_max == 1300"));
    ctx.push_obligation(ProofObligation::assert(
        "ot_in_range",
        "temp_offset >= temp_min && temp_offset <= temp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp offset 580 (80C) in range [520,1300] (20C-800C for SOEC)",
    );
}

#[test]
fn test_electrode_material() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", u32_ty());
    ctx.declare_var_typed("valid_material", i32_ty());
    // 1=nickel, 2=platinum, 3=iridium, 4=mixed-metal oxide
    ctx.push_obligation(ProofObligation::assume("em_val", "material == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "em_valid_def",
        "valid_material == if material == 1 || material == 2 || material == 3 || material == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("em_check", "valid_material == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "electrode material 3 (iridium) is valid");
}

#[test]
fn test_water_flow_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["flow_lh", "flow_min", "flow_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Water flow rate in L/h: value 100, valid range 1 to 10000
    ctx.push_obligation(ProofObligation::assume("wf_val", "flow_lh == 100"));
    ctx.push_obligation(ProofObligation::assume("wf_min", "flow_min == 1"));
    ctx.push_obligation(ProofObligation::assume("wf_max", "flow_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "wf_in_range",
        "flow_lh >= flow_min && flow_lh <= flow_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "water flow rate 100 L/h in range [1,10000]");
}

#[test]
fn test_pressure() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure_kpa", "press_min", "press_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Operating pressure in kPa: value 3000, valid range 100 to 10000
    ctx.push_obligation(ProofObligation::assume("op_val", "pressure_kpa == 3000"));
    ctx.push_obligation(ProofObligation::assume("op_min", "press_min == 100"));
    ctx.push_obligation(ProofObligation::assume("op_max", "press_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "op_in_range",
        "pressure_kpa >= press_min && pressure_kpa <= press_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating pressure 3000 kPa in range [100,10000]");
}

#[test]
fn test_gas_leak_detect() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("leak_detected", i32_ty());
    ctx.declare_var_typed("shutdown", i32_ty());
    // Boolean flag: 0=no leak, 1=leak detected
    ctx.push_obligation(ProofObligation::assume("ld_val", "leak_detected == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "sd_def",
        "shutdown == if leak_detected == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("sd_check", "shutdown == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gas leak detected triggers shutdown");
}
