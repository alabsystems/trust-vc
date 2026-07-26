// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn collector_emitter_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vce_v", "max_vce_v"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vce_ok", i32_ty());
    // Maximum collector-emitter voltage
    ctx.push_obligation(ProofObligation::assume("vv", "vce_v == 1200"));
    ctx.push_obligation(ProofObligation::assume("mv", "max_vce_v == 1700"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vce_ok == if vce_v <= max_vce_v { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vce_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IGBT: 1200V VCE ≤ 1700V max → OK");
}

#[test]
fn saturation_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vce_sat_mv", "max_vce_sat_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sat_ok", i32_ty());
    // VCE(sat) in millivolts
    ctx.push_obligation(ProofObligation::assume("vm", "vce_sat_mv == 1700")); // 1.7V
    ctx.push_obligation(ProofObligation::assume("mv", "max_vce_sat_mv == 2500")); // 2.5V
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sat_ok == if vce_sat_mv <= max_vce_sat_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sat_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IGBT: 1.7V VCE(sat) ≤ 2.5V max → OK");
}

#[test]
fn collector_current() {
    let mut ctx = VerificationContext::new();
    for v in &["ic_a", "max_ic_a"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ic_ok", i32_ty());
    // Continuous collector current at 25°C
    ctx.push_obligation(ProofObligation::assume("ia", "ic_a == 200"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_ic_a == 600"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "ic_ok == if ic_a <= max_ic_a { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ic_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IGBT: 200A IC ≤ 600A max → OK");
}

#[test]
fn turn_off_energy() {
    let mut ctx = VerificationContext::new();
    for v in &["eoff_mj", "max_eoff_mj"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("eoff_ok", i32_ty());
    // Turn-off switching energy in millijoules
    ctx.push_obligation(ProofObligation::assume("em", "eoff_mj == 50"));
    ctx.push_obligation(ProofObligation::assume("me", "max_eoff_mj == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "eoff_ok == if eoff_mj <= max_eoff_mj { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "eoff_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IGBT: 50mJ turn-off energy ≤ 200mJ max → OK");
}

#[test]
fn gate_emitter_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vge_v", "min_vge_v", "max_vge_v"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vge_ok", i32_ty());
    // Gate drive voltage range
    ctx.push_obligation(ProofObligation::assume("vv", "vge_v == 15"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_vge_v == 13"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_vge_v == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vge_ok == if vge_v >= min_vge_v && vge_v <= max_vge_v { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vge_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IGBT: 15V VGE in [13, 20] → OK");
}

#[test]
fn thermal_impedance() {
    let mut ctx = VerificationContext::new();
    for v in &["rth_jc_x100", "max_rth_jc_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rth_ok", i32_ty());
    // Junction-to-case thermal impedance (°C/W ×100)
    ctx.push_obligation(ProofObligation::assume("rx", "rth_jc_x100 == 15")); // 0.15 °C/W
    ctx.push_obligation(ProofObligation::assume("mr", "max_rth_jc_x100 == 50")); // 0.50 °C/W
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rth_ok == if rth_jc_x100 <= max_rth_jc_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rth_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IGBT: 0.15°C/W Rth(j-c) ≤ 0.50 max → OK");
}

#[test]
fn module_configuration() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("config", u32_ty());
    ctx.declare_var_typed("valid_config", i32_ty());
    // Module types: 1=single, 2=dual, 3=six-pack, 4=chopper, 5=H-bridge
    ctx.push_obligation(ProofObligation::assume("c", "config == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_config == if config == 1 || config == 2 || config == 3 || config == 4 || config == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_config == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IGBT: dual module is valid configuration");
}

#[test]
fn short_circuit_rating() {
    let mut ctx = VerificationContext::new();
    for v in &["sc_time_us", "min_sc_time_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sc_ok", i32_ty());
    // Short-circuit withstand time in microseconds
    ctx.push_obligation(ProofObligation::assume("su", "sc_time_us == 10"));
    ctx.push_obligation(ProofObligation::assume("ms", "min_sc_time_us == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sc_ok == if sc_time_us >= min_sc_time_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IGBT: 10μs SC withstand ≥ 5μs min → OK");
}

#[test]
fn diode_recovery() {
    let mut ctx = VerificationContext::new();
    for v in &["erec_mj", "max_erec_mj"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("erec_ok", i32_ty());
    // Diode reverse recovery energy
    ctx.push_obligation(ProofObligation::assume("em", "erec_mj == 30"));
    ctx.push_obligation(ProofObligation::assume("me", "max_erec_mj == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "erec_ok == if erec_mj <= max_erec_mj { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "erec_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IGBT: 30mJ diode recovery ≤ 100mJ max → OK");
}

#[test]
fn junction_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["tj_c", "max_tj_c"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("tj_ok", i32_ty());
    // Maximum junction operating temperature
    ctx.push_obligation(ProofObligation::assume("tc", "tj_c == 150"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_tj_c == 175"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "tj_ok == if tj_c <= max_tj_c { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "tj_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IGBT: 150°C junction ≤ 175°C max → OK");
}
