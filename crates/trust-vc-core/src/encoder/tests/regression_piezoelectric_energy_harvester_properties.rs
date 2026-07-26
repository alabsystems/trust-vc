// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn output_power() {
    let mut ctx = VerificationContext::new();
    for v in &["power_uw", "min_power_uw", "max_power_uw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("power_ok", i32_ty());
    // Output power in microwatts (1 uW to 100000 uW = 100 mW)
    ctx.push_obligation(ProofObligation::assume("pw", "power_uw == 250"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_power_uw == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_power_uw == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "power_ok == if power_uw >= min_power_uw && power_uw <= max_power_uw { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "power_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "piezo harvester: 250 uW output in [1, 100000] range",
    );
}

#[test]
fn resonant_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_hz", "min_freq_hz", "max_freq_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Resonant frequency in Hz
    ctx.push_obligation(ProofObligation::assume("fh", "freq_hz == 120"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_hz == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_hz == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_hz >= min_freq_hz && freq_hz <= max_freq_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "piezo harvester: 120 Hz resonant frequency in [1, 1000] range",
    );
}

#[test]
fn piezo_material() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", u32_ty());
    ctx.declare_var_typed("valid_material", i32_ty());
    // Piezoelectric material: 1=PZT, 2=PVDF, 3=AlN, 4=BaTiO3
    ctx.push_obligation(ProofObligation::assume("mt", "material == 1")); // PZT
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_material == if material == 1 || material == 2 || material == 3 || material == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_material == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "piezo harvester: PZT is valid piezoelectric material",
    );
}

#[test]
fn harvester_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("valid_mode", i32_ty());
    // Harvester mode: 1=d31 bending, 2=d33 compression, 3=d15 shear
    ctx.push_obligation(ProofObligation::assume("hm", "mode == 2")); // d33 compression
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mode == if mode == 1 || mode == 2 || mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "piezo harvester: d33 compression is valid harvester mode",
    );
}

#[test]
fn output_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["voltage_mv", "min_voltage_mv", "max_voltage_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("voltage_ok", i32_ty());
    // Open-circuit voltage in millivolts (100 mV to 50000 mV = 50 V)
    ctx.push_obligation(ProofObligation::assume("vm", "voltage_mv == 3200"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_voltage_mv == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_voltage_mv == 50000"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "voltage_ok == if voltage_mv >= min_voltage_mv && voltage_mv <= max_voltage_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "voltage_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "piezo harvester: 3200 mV open-circuit in [100, 50000] range",
    );
}

#[test]
fn capacitance() {
    let mut ctx = VerificationContext::new();
    for v in &["cap_nf", "min_cap_nf", "max_cap_nf"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cap_ok", i32_ty());
    // Capacitance in nanofarads
    ctx.push_obligation(ProofObligation::assume("cn", "cap_nf == 33"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_cap_nf == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_cap_nf == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cap_ok == if cap_nf >= min_cap_nf && cap_nf <= max_cap_nf { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cap_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "piezo harvester: 33 nF capacitance in [1, 10000] range",
    );
}

#[test]
fn operating_temp() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Temperature offset +500 (-40C to 125C mapped to 460-625)
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 525")); // 25C
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 460")); // -40C
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 625")); // 125C
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "piezo harvester: 25C (offset 525) in [-40C, 125C] range",
    );
}

#[test]
fn acceleration() {
    let mut ctx = VerificationContext::new();
    for v in &["accel_x100", "min_accel_x100", "max_accel_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("accel_ok", i32_ty());
    // Acceleration in hundredths of g (0.50g = 50, 20.00g = 2000)
    ctx.push_obligation(ProofObligation::assume("ax", "accel_x100 == 100")); // 1.00g
    ctx.push_obligation(ProofObligation::assume("mn", "min_accel_x100 == 1")); // 0.01g
    ctx.push_obligation(ProofObligation::assume("mx", "max_accel_x100 == 2000")); // 20.00g
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "accel_ok == if accel_x100 >= min_accel_x100 && accel_x100 <= max_accel_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "accel_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "piezo harvester: 1.00g acceleration in [0.01, 20.00] range",
    );
}

#[test]
fn bandwidth() {
    let mut ctx = VerificationContext::new();
    for v in &["bw_hz", "min_bw_hz", "max_bw_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bw_ok", i32_ty());
    // 3dB bandwidth in Hz
    ctx.push_obligation(ProofObligation::assume("bh", "bw_hz == 15"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_bw_hz == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_bw_hz == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bw_ok == if bw_hz >= min_bw_hz && bw_hz <= max_bw_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "piezo harvester: 15 Hz 3dB bandwidth in [1, 200] range",
    );
}

#[test]
fn rectifier_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rectifier", u32_ty());
    ctx.declare_var_typed("valid_rectifier", i32_ty());
    // Rectifier type: 1=full-bridge, 2=voltage doubler, 3=active, 4=synchronous
    ctx.push_obligation(ProofObligation::assume("rt", "rectifier == 3")); // active
    ctx.push_obligation(ProofObligation::assume(
        "vr_def",
        "valid_rectifier == if rectifier == 1 || rectifier == 2 || rectifier == 3 || rectifier == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_rectifier == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "piezo harvester: active is valid rectifier type");
}
