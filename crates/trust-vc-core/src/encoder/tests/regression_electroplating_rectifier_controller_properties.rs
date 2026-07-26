// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn output_current() {
    let mut ctx = VerificationContext::new();
    for v in &["current_a", "cur_min", "cur_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Output current in amps: value 2500, valid range 1 to 50000
    ctx.push_obligation(ProofObligation::assume("oc_val", "current_a == 2500"));
    ctx.push_obligation(ProofObligation::assume("oc_min", "cur_min == 1"));
    ctx.push_obligation(ProofObligation::assume("oc_max", "cur_max == 50000"));
    ctx.push_obligation(ProofObligation::assert(
        "oc_in_range",
        "current_a >= cur_min && current_a <= cur_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output current 2500 A in range [1,50000]");
}

#[test]
fn output_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["voltage_mv", "volt_min", "volt_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Output voltage in mV: value 12000 (12V), valid range 1000 (1V) to 24000 (24V)
    ctx.push_obligation(ProofObligation::assume("ov_val", "voltage_mv == 12000"));
    ctx.push_obligation(ProofObligation::assume("ov_min", "volt_min == 1000"));
    ctx.push_obligation(ProofObligation::assume("ov_max", "volt_max == 24000"));
    ctx.push_obligation(ProofObligation::assert(
        "ov_in_range",
        "voltage_mv >= volt_min && voltage_mv <= volt_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "output voltage 12000 mV (12V) in range [1000,24000] (1-24V)",
    );
}

#[test]
fn plating_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("plating", u32_ty());
    ctx.declare_var_typed("valid_plating", i32_ty());
    // 1=DC, 2=pulse, 3=periodic reverse, 4=pulse reverse
    ctx.push_obligation(ProofObligation::assume("pt_val", "plating == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "pt_valid_def",
        "valid_plating == if plating == 1 || plating == 2 || plating == 3 || plating == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("pt_check", "valid_plating == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "plating type 2 (pulse) is valid");
}

#[test]
fn ripple_percentage() {
    let mut ctx = VerificationContext::new();
    for v in &["ripple_x100", "rip_min", "rip_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Ripple as x100 %: value 150 (1.50%), valid range 1 (0.01%) to 500 (5.00%)
    ctx.push_obligation(ProofObligation::assume("rp_val", "ripple_x100 == 150"));
    ctx.push_obligation(ProofObligation::assume("rp_min", "rip_min == 1"));
    ctx.push_obligation(ProofObligation::assume("rp_max", "rip_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "rp_in_range",
        "ripple_x100 >= rip_min && ripple_x100 <= rip_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ripple 150 (1.50%) in range [1,500] (0.01%-5.00%)");
}

#[test]
fn pulse_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_hz", "freq_min", "freq_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Pulse frequency in Hz: value 1000, valid range 1 to 10000
    ctx.push_obligation(ProofObligation::assume("pf_val", "freq_hz == 1000"));
    ctx.push_obligation(ProofObligation::assume("pf_min", "freq_min == 1"));
    ctx.push_obligation(ProofObligation::assume("pf_max", "freq_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "pf_in_range",
        "freq_hz >= freq_min && freq_hz <= freq_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pulse frequency 1000 Hz in range [1,10000]");
}

#[test]
fn bath_temperature_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "temp_min", "temp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Bath temperature offset +500 (deg C): value 550 (50C), valid range 480 (-20C) to 600 (100C)
    ctx.push_obligation(ProofObligation::assume("bt_val", "temp_offset == 550"));
    ctx.push_obligation(ProofObligation::assume("bt_min", "temp_min == 480"));
    ctx.push_obligation(ProofObligation::assume("bt_max", "temp_max == 600"));
    ctx.push_obligation(ProofObligation::assert(
        "bt_in_range",
        "temp_offset >= temp_min && temp_offset <= temp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bath temp offset 550 (50C) in range [480,600] (-20C to 100C)",
    );
}

#[test]
fn current_density() {
    let mut ctx = VerificationContext::new();
    for v in &["density_x10", "dens_min", "dens_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Current density as x10 A/dm2: value 50 (5.0 A/dm2), valid range 1 (0.1) to 500 (50.0)
    ctx.push_obligation(ProofObligation::assume("cd_val", "density_x10 == 50"));
    ctx.push_obligation(ProofObligation::assume("cd_min", "dens_min == 1"));
    ctx.push_obligation(ProofObligation::assume("cd_max", "dens_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "cd_in_range",
        "density_x10 >= dens_min && density_x10 <= dens_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "current density 50 (5.0 A/dm2) in range [1,500] (0.1-50.0)",
    );
}

#[test]
fn anode_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("anode", u32_ty());
    ctx.declare_var_typed("valid_anode", i32_ty());
    // 1=soluble, 2=insoluble, 3=dimensionally stable
    ctx.push_obligation(ProofObligation::assume("at_val", "anode == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "at_valid_def",
        "valid_anode == if anode == 1 || anode == 2 || anode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("at_check", "valid_anode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "anode type 3 (dimensionally stable) is valid");
}

#[test]
fn efficiency() {
    let mut ctx = VerificationContext::new();
    for v in &["eff_x10", "eff_min", "eff_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Efficiency as x10 %: value 950 (95.0%), valid range 500 (50.0%) to 1000 (100.0%)
    ctx.push_obligation(ProofObligation::assume("ef_val", "eff_x10 == 950"));
    ctx.push_obligation(ProofObligation::assume("ef_min", "eff_min == 500"));
    ctx.push_obligation(ProofObligation::assume("ef_max", "eff_max == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "ef_in_range",
        "eff_x10 >= eff_min && eff_x10 <= eff_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "efficiency 950 (95.0%) in range [500,1000] (50.0%-100.0%)",
    );
}

#[test]
fn amp_hour_meter() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meter_enabled", i32_ty());
    ctx.declare_var_typed("logging", i32_ty());
    // Boolean flag: 0=disabled, 1=enabled
    ctx.push_obligation(ProofObligation::assume("ah_val", "meter_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "log_def",
        "logging == if meter_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("log_check", "logging == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "amp-hour meter enabled triggers logging");
}
