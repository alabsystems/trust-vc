// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn input_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vin_mv", "vin_min", "vin_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Input voltage in mV: value 12000 (12V), valid range 3000 to 60000 (3V to 60V)
    ctx.push_obligation(ProofObligation::assume("iv_val", "vin_mv == 12000"));
    ctx.push_obligation(ProofObligation::assume("iv_min", "vin_min == 3000"));
    ctx.push_obligation(ProofObligation::assume("iv_max", "vin_max == 60000"));
    ctx.push_obligation(ProofObligation::assert(
        "iv_in_range",
        "vin_mv >= vin_min && vin_mv <= vin_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "input voltage 12000 mV in range [3000,60000]");
}

#[test]
fn output_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vout_mv", "vout_min", "vout_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Output voltage in mV: value 3300 (3.3V), valid range 500 to 24000 (0.5V to 24V)
    ctx.push_obligation(ProofObligation::assume("ov_val", "vout_mv == 3300"));
    ctx.push_obligation(ProofObligation::assume("ov_min", "vout_min == 500"));
    ctx.push_obligation(ProofObligation::assume("ov_max", "vout_max == 24000"));
    ctx.push_obligation(ProofObligation::assert(
        "ov_in_range",
        "vout_mv >= vout_min && vout_mv <= vout_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output voltage 3300 mV in range [500,24000]");
}

#[test]
fn output_current() {
    let mut ctx = VerificationContext::new();
    for v in &["iout_ma", "iout_min", "iout_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Output current in mA: value 10000 (10A), valid range 100 to 100000 (100mA to 100A)
    ctx.push_obligation(ProofObligation::assume("oc_val", "iout_ma == 10000"));
    ctx.push_obligation(ProofObligation::assume("oc_min", "iout_min == 100"));
    ctx.push_obligation(ProofObligation::assume("oc_max", "iout_max == 100000"));
    ctx.push_obligation(ProofObligation::assert(
        "oc_in_range",
        "iout_ma >= iout_min && iout_ma <= iout_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output current 10000 mA in range [100,100000]");
}

#[test]
fn switching_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["fsw_khz", "fsw_min", "fsw_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Switching frequency in kHz: value 500, valid range 100 to 4000
    ctx.push_obligation(ProofObligation::assume("sf_val", "fsw_khz == 500"));
    ctx.push_obligation(ProofObligation::assume("sf_min", "fsw_min == 100"));
    ctx.push_obligation(ProofObligation::assume("sf_max", "fsw_max == 4000"));
    ctx.push_obligation(ProofObligation::assert(
        "sf_in_range",
        "fsw_khz >= fsw_min && fsw_khz <= fsw_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "switching frequency 500 kHz in range [100,4000]");
}

#[test]
fn efficiency() {
    let mut ctx = VerificationContext::new();
    for v in &["eff_x10", "eff_min", "eff_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Efficiency x10 percent: value 950 (95.0%), valid range 850 to 999 (85.0% to 99.9%)
    ctx.push_obligation(ProofObligation::assume("ef_val", "eff_x10 == 950"));
    ctx.push_obligation(ProofObligation::assume("ef_min", "eff_min == 850"));
    ctx.push_obligation(ProofObligation::assume("ef_max", "eff_max == 999"));
    ctx.push_obligation(ProofObligation::assert(
        "ef_in_range",
        "eff_x10 >= eff_min && eff_x10 <= eff_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "efficiency 950 (95.0%) in range [850,999]");
}

#[test]
fn inductor_value() {
    let mut ctx = VerificationContext::new();
    for v in &["ind_nh", "ind_min", "ind_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Inductor value in nH: value 4700 (4.7uH), valid range 100 to 100000 (100nH to 100uH)
    ctx.push_obligation(ProofObligation::assume("il_val", "ind_nh == 4700"));
    ctx.push_obligation(ProofObligation::assume("il_min", "ind_min == 100"));
    ctx.push_obligation(ProofObligation::assume("il_max", "ind_max == 100000"));
    ctx.push_obligation(ProofObligation::assert(
        "il_in_range",
        "ind_nh >= ind_min && ind_nh <= ind_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inductor value 4700 nH in range [100,100000]");
}

#[test]
fn output_ripple() {
    let mut ctx = VerificationContext::new();
    for v in &["rpl_mv", "rpl_min", "rpl_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Output ripple in mV peak-to-peak: value 30, valid range 1 to 500
    ctx.push_obligation(ProofObligation::assume("or_val", "rpl_mv == 30"));
    ctx.push_obligation(ProofObligation::assume("or_min", "rpl_min == 1"));
    ctx.push_obligation(ProofObligation::assume("or_max", "rpl_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "or_in_range",
        "rpl_mv >= rpl_min && rpl_mv <= rpl_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output ripple 30 mV pp in range [1,500]");
}

#[test]
fn load_transient_response() {
    let mut ctx = VerificationContext::new();
    for v in &["ltr_us", "ltr_min", "ltr_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Load transient response in us: value 50, valid range 1 to 500
    ctx.push_obligation(ProofObligation::assume("lt_val", "ltr_us == 50"));
    ctx.push_obligation(ProofObligation::assume("lt_min", "ltr_min == 1"));
    ctx.push_obligation(ProofObligation::assume("lt_max", "ltr_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "lt_in_range",
        "ltr_us >= ltr_min && ltr_us <= ltr_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "load transient response 50 us in range [1,500]");
}

#[test]
fn control_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ctrl_mode", u32_ty());
    ctx.declare_var_typed("valid_ctrl", i32_ty());
    // Control modes: 1=voltage mode, 2=current mode peak, 3=current mode average, 4=COT constant on-time
    ctx.push_obligation(ProofObligation::assume("cm_val", "ctrl_mode == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "cm_def",
        "valid_ctrl == if ctrl_mode == 1 || ctrl_mode == 2 || ctrl_mode == 3 || ctrl_mode == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cm_chk", "valid_ctrl == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "control mode 2 (current mode peak) is valid buck converter control type",
    );
}

#[test]
fn phase_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ph_cnt", u32_ty());
    ctx.declare_var_typed("valid_ph", i32_ty());
    // Phase counts: 1=single phase, 2=dual phase, 4=quad phase (non-sequential)
    ctx.push_obligation(ProofObligation::assume("pc_val", "ph_cnt == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "pc_def",
        "valid_ph == if ph_cnt == 1 || ph_cnt == 2 || ph_cnt == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("pc_chk", "valid_ph == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "phase count 2 (dual phase) is valid buck converter phase configuration",
    );
}
