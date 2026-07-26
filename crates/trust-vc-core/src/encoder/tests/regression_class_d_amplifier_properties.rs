// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn output_power() {
    let mut ctx = VerificationContext::new();
    for v in &["power_mw", "max_power_mw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pow_ok", i32_ty());
    // Output power per channel in mW
    ctx.push_obligation(ProofObligation::assume("pm", "power_mw == 20000")); // 20W
    ctx.push_obligation(ProofObligation::assume("mp", "max_power_mw == 100000")); // 100W
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pow_ok == if power_mw <= max_power_mw { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pow_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Class-D: 20W output ≤ 100W max → OK");
}

#[test]
fn efficiency() {
    let mut ctx = VerificationContext::new();
    for v in &["eff_x10", "min_eff_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("eff_ok", i32_ty());
    // Efficiency % (×10 for 0.1%)
    ctx.push_obligation(ProofObligation::assume("ex", "eff_x10 == 920")); // 92.0%
    ctx.push_obligation(ProofObligation::assume("me", "min_eff_x10 == 850")); // 85.0%
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "eff_ok == if eff_x10 >= min_eff_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "eff_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Class-D: 92.0% efficiency ≥ 85.0% min → OK");
}

#[test]
fn thd_plus_noise() {
    let mut ctx = VerificationContext::new();
    for v in &["thdn_x1000", "max_thdn_x1000"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("thdn_ok", i32_ty());
    // THD+N as % (×1000 for 0.001%)
    ctx.push_obligation(ProofObligation::assume("tx", "thdn_x1000 == 50")); // 0.050%
    ctx.push_obligation(ProofObligation::assume("mt", "max_thdn_x1000 == 100")); // 0.100%
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "thdn_ok == if thdn_x1000 <= max_thdn_x1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "thdn_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Class-D: 0.050% THD+N ≤ 0.100% max → OK");
}

#[test]
fn switching_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["sw_khz", "min_sw_khz", "max_sw_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sw_ok", i32_ty());
    // PWM switching frequency in kHz
    ctx.push_obligation(ProofObligation::assume("sk", "sw_khz == 400"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_sw_khz == 200"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_sw_khz == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sw_ok == if sw_khz >= min_sw_khz && sw_khz <= max_sw_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Class-D: 400kHz switching in [200, 2000] → OK");
}

#[test]
fn channel_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.declare_var_typed("valid_ch", i32_ty());
    // Channel configurations
    ctx.push_obligation(ProofObligation::assume("c", "channels == 2")); // stereo
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_ch == if channels == 1 || channels == 2 || channels == 4 || channels == 6 || channels == 8 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_ch == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Class-D: stereo (2ch) is valid channel count");
}

#[test]
fn snr() {
    let mut ctx = VerificationContext::new();
    for v in &["snr_db", "min_snr_db"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("snr_ok", i32_ty());
    // Signal-to-noise ratio in dB (A-weighted)
    ctx.push_obligation(ProofObligation::assume("sd", "snr_db == 100"));
    ctx.push_obligation(ProofObligation::assume("ms", "min_snr_db == 90"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "snr_ok == if snr_db >= min_snr_db { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "snr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Class-D: 100dB SNR ≥ 90dB min → OK");
}

#[test]
fn supply_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["supply_mv", "min_supply_mv", "max_supply_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sup_ok", i32_ty());
    // Supply voltage in mV
    ctx.push_obligation(ProofObligation::assume("sm", "supply_mv == 24000")); // 24V
    ctx.push_obligation(ProofObligation::assume("mn", "min_supply_mv == 8000")); // 8V
    ctx.push_obligation(ProofObligation::assume("mx", "max_supply_mv == 36000")); // 36V
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sup_ok == if supply_mv >= min_supply_mv && supply_mv <= max_supply_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sup_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Class-D: 24V supply in [8, 36] → OK");
}

#[test]
fn modulation_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mod_type", u32_ty());
    ctx.declare_var_typed("valid_mod", i32_ty());
    // Modulation: 1=AD (analog PWM), 2=BD (filterless), 3=ternary, 4=sigma-delta
    ctx.push_obligation(ProofObligation::assume("mt", "mod_type == 2")); // BD (filterless)
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mod == if mod_type == 1 || mod_type == 2 || mod_type == 3 || mod_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_mod == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Class-D: BD modulation is valid type");
}

#[test]
fn load_impedance() {
    let mut ctx = VerificationContext::new();
    for v in &["load_ohm", "min_load_ohm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("load_ok", i32_ty());
    // Speaker load impedance in ohms
    ctx.push_obligation(ProofObligation::assume("lo", "load_ohm == 8"));
    ctx.push_obligation(ProofObligation::assume("ml", "min_load_ohm == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "load_ok == if load_ohm >= min_load_ohm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "load_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Class-D: 8Ω load ≥ 2Ω min → OK");
}

#[test]
fn psrr() {
    let mut ctx = VerificationContext::new();
    for v in &["psrr_db", "min_psrr_db"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("psrr_ok", i32_ty());
    // Power supply rejection ratio in dB
    ctx.push_obligation(ProofObligation::assume("pd", "psrr_db == 70"));
    ctx.push_obligation(ProofObligation::assume("mp", "min_psrr_db == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "psrr_ok == if psrr_db >= min_psrr_db { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "psrr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Class-D: 70dB PSRR ≥ 50dB min → OK");
}
