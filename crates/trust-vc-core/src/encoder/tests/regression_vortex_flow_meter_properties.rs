// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn flow_velocity() {
    let mut ctx = VerificationContext::new();
    for v in &["velocity_x10", "min_velocity_x10", "max_velocity_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vel_ok", i32_ty());
    // Flow velocity in m/s (×10 for 0.1 m/s)
    ctx.push_obligation(ProofObligation::assume("vx", "velocity_x10 == 50")); // 5.0 m/s
    ctx.push_obligation(ProofObligation::assume("mn", "min_velocity_x10 == 5")); // 0.5 m/s
    ctx.push_obligation(ProofObligation::assume("mx", "max_velocity_x10 == 800")); // 80.0 m/s
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vel_ok == if velocity_x10 >= min_velocity_x10 && velocity_x10 <= max_velocity_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vel_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Vortex: 5.0 m/s velocity in [0.5, 80.0] → OK");
}

#[test]
fn shedding_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_hz", "min_freq_hz", "max_freq_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Vortex shedding frequency
    ctx.push_obligation(ProofObligation::assume("fh", "freq_hz == 500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_hz == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_hz == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_hz >= min_freq_hz && freq_hz <= max_freq_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Vortex: 500Hz shedding in [10, 3000] → OK");
}

#[test]
fn pipe_diameter() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter_mm", u32_ty());
    ctx.declare_var_typed("valid_dia", i32_ty());
    // Standard pipe sizes: DN15-DN300
    ctx.push_obligation(ProofObligation::assume("dm", "diameter_mm == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_dia == if diameter_mm == 15 || diameter_mm == 25 || diameter_mm == 50 || diameter_mm == 80 || diameter_mm == 100 || diameter_mm == 150 || diameter_mm == 200 || diameter_mm == 300 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_dia == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Vortex: DN50 is valid pipe size");
}

#[test]
fn reynolds_number() {
    let mut ctx = VerificationContext::new();
    for v in &["reynolds", "min_reynolds"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("re_ok", i32_ty());
    // Minimum Reynolds number for valid measurement
    ctx.push_obligation(ProofObligation::assume("r", "reynolds == 20000"));
    ctx.push_obligation(ProofObligation::assume("mr", "min_reynolds == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "re_ok == if reynolds >= min_reynolds { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "re_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Vortex: Re 20000 ≥ 5000 min → OK");
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x10", "max_accuracy_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Accuracy as % of reading (×10 for 0.1%)
    ctx.push_obligation(ProofObligation::assume("ax", "accuracy_x10 == 10")); // 1.0%
    ctx.push_obligation(ProofObligation::assume("ma", "max_accuracy_x10 == 15")); // 1.5%
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_x10 <= max_accuracy_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Vortex: 1.0% accuracy ≤ 1.5% max → OK");
}

#[test]
fn process_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Process temperature: -40°C to +260°C (offset +500)
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 600")); // 100°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 460")); // -40°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 760")); // 260°C
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Vortex: 100°C in [-40, 260] → OK");
}

#[test]
fn pressure_rating() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure_bar", "max_pressure_bar"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("press_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pb", "pressure_bar == 40"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_pressure_bar == 250"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "press_ok == if pressure_bar <= max_pressure_bar { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "press_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Vortex: 40 bar ≤ 250 max → OK");
}

#[test]
fn turndown_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["turndown", "min_turndown"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("td_ok", i32_ty());
    // Flow turndown ratio
    ctx.push_obligation(ProofObligation::assume("t", "turndown == 30")); // 30:1
    ctx.push_obligation(ProofObligation::assume("mt", "min_turndown == 10")); // 10:1
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "td_ok == if turndown >= min_turndown { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "td_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Vortex: 30:1 turndown ≥ 10:1 min → OK");
}

#[test]
fn bluff_body_width() {
    let mut ctx = VerificationContext::new();
    for v in &["width_x10", "min_width_x10", "max_width_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("wb_ok", i32_ty());
    // Bluff body width as fraction of pipe diameter (×10 for 0.1, typical 0.25-0.35)
    ctx.push_obligation(ProofObligation::assume("wx", "width_x10 == 3")); // 0.3 of D
    ctx.push_obligation(ProofObligation::assume("mn", "min_width_x10 == 2")); // 0.2
    ctx.push_obligation(ProofObligation::assume("mx", "max_width_x10 == 4")); // 0.4
    ctx.push_obligation(ProofObligation::assume(
        "wo_def",
        "wb_ok == if width_x10 >= min_width_x10 && width_x10 <= max_width_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "wb_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Vortex: bluff body 0.3D in [0.2, 0.4] → OK");
}

#[test]
fn signal_to_noise() {
    let mut ctx = VerificationContext::new();
    for v in &["snr_db", "min_snr_db"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("snr_ok", i32_ty());
    // Signal-to-noise ratio in dB
    ctx.push_obligation(ProofObligation::assume("sd", "snr_db == 20"));
    ctx.push_obligation(ProofObligation::assume("ms", "min_snr_db == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "snr_ok == if snr_db >= min_snr_db { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "snr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Vortex: 20dB SNR ≥ 10dB min → OK");
}
