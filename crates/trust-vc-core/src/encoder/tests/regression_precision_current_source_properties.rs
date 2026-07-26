// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn output_current_ua() {
    let mut ctx = VerificationContext::new();
    for v in &["current", "current_min", "current_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Output current in microamps: value 100000 (100 mA), valid range 1 to 1000000
    ctx.push_obligation(ProofObligation::assume("oc_val", "current == 100000"));
    ctx.push_obligation(ProofObligation::assume("oc_lo", "current_min == 1"));
    ctx.push_obligation(ProofObligation::assume("oc_hi", "current_max == 1000000"));
    ctx.push_obligation(ProofObligation::assert(
        "oc_in_range",
        "current >= current_min && current <= current_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "output current 100000 uA (100 mA) in range [1,1000000]",
    );
}

#[test]
fn accuracy_x100_ppm() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x100", "acc_min", "acc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Accuracy as x100 ppm (e.g., 5.00 ppm = 500), valid range 10 to 5000
    ctx.push_obligation(ProofObligation::assume("ac_val", "accuracy_x100 == 500"));
    ctx.push_obligation(ProofObligation::assume("ac_lo", "acc_min == 10"));
    ctx.push_obligation(ProofObligation::assume("ac_hi", "acc_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "ac_in_range",
        "accuracy_x100 >= acc_min && accuracy_x100 <= acc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy 500 (5.00 ppm) in range [10,5000]");
}

#[test]
fn compliance_voltage_mv() {
    let mut ctx = VerificationContext::new();
    for v in &["compliance", "comp_min", "comp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Compliance voltage in millivolts: value 10000 (10V), valid range 100 to 50000
    ctx.push_obligation(ProofObligation::assume("cv_val", "compliance == 10000"));
    ctx.push_obligation(ProofObligation::assume("cv_lo", "comp_min == 100"));
    ctx.push_obligation(ProofObligation::assume("cv_hi", "comp_max == 50000"));
    ctx.push_obligation(ProofObligation::assert(
        "cv_in_range",
        "compliance >= comp_min && compliance <= comp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "compliance voltage 10000 mV (10V) in range [100,50000]",
    );
}

#[test]
fn output_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("valid_mode", i32_ty());
    // Output mode: 1=unipolar, 2=bipolar, 3=pulsed
    ctx.push_obligation(ProofObligation::assume("om_val", "mode == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "om_def",
        "valid_mode == if mode == 1 || mode == 2 || mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("om_chk", "valid_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output mode 2 (bipolar) is valid mode");
}

#[test]
fn stability_x1000_ppm_per_c() {
    let mut ctx = VerificationContext::new();
    for v in &["stability_x1000", "stab_min", "stab_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Stability as x1000 ppm/C (e.g., 0.500 ppm/C = 500), valid range 1 to 5000
    ctx.push_obligation(ProofObligation::assume("st_val", "stability_x1000 == 500"));
    ctx.push_obligation(ProofObligation::assume("st_lo", "stab_min == 1"));
    ctx.push_obligation(ProofObligation::assume("st_hi", "stab_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "st_in_range",
        "stability_x1000 >= stab_min && stability_x1000 <= stab_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stability 500 (0.500 ppm/C) in range [1,5000]");
}

#[test]
fn resolution_bits() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bits", u32_ty());
    ctx.declare_var_typed("valid_bits", i32_ty());
    // Resolution in bits: valid values are 16, 18, 20, or 24
    ctx.push_obligation(ProofObligation::assume("rb_val", "bits == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "rb_def",
        "valid_bits == if bits == 16 || bits == 18 || bits == 20 || bits == 24 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("rb_chk", "valid_bits == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution 20 bits is valid bit depth");
}

#[test]
fn interface_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("iface", u32_ty());
    ctx.declare_var_typed("valid_iface", i32_ty());
    // Interface type: 1=GPIB, 2=USB, 3=RS-232, 4=Ethernet
    ctx.push_obligation(ProofObligation::assume("it_val", "iface == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "it_def",
        "valid_iface == if iface == 1 || iface == 2 || iface == 3 || iface == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("it_chk", "valid_iface == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "interface 3 (RS-232) is valid interface");
}

#[test]
fn settling_time_us() {
    let mut ctx = VerificationContext::new();
    for v in &["settling", "settle_min", "settle_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Settling time in microseconds: value 100, valid range 1 to 10000
    ctx.push_obligation(ProofObligation::assume("se_val", "settling == 100"));
    ctx.push_obligation(ProofObligation::assume("se_lo", "settle_min == 1"));
    ctx.push_obligation(ProofObligation::assume("se_hi", "settle_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "se_in_range",
        "settling >= settle_min && settling <= settle_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "settling time 100 us in range [1,10000]");
}

#[test]
fn operating_temperature_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["temp", "temp_min", "temp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Operating temperature with +500 offset (e.g., 23C = 523), valid range 460 (-40C) to 570 (70C)
    ctx.push_obligation(ProofObligation::assume("ot_val", "temp == 523"));
    ctx.push_obligation(ProofObligation::assume("ot_lo", "temp_min == 460"));
    ctx.push_obligation(ProofObligation::assume("ot_hi", "temp_max == 570"));
    ctx.push_obligation(ProofObligation::assert(
        "ot_in_range",
        "temp >= temp_min && temp <= temp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp 523 (23C offset+500) in range [460,570]",
    );
}

#[test]
fn guard_output_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.declare_var_typed("guard_active", i32_ty());
    // Guard output: boolean flag encoded as i32 (0=no, 1=yes)
    ctx.push_obligation(ProofObligation::assume("gf_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "gf_def",
        "guard_active == if flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("gf_chk", "guard_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "guard output flag 1 (enabled) asserts active");
}
