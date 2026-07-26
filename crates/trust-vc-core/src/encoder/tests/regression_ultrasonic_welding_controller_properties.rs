// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn frequency() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_hz", u32_ty());
    ctx.declare_var_typed("valid_freq", i32_ty());
    // Operating frequency in Hz (20kHz standard for plastic welding)
    ctx.push_obligation(ProofObligation::assume("fh", "freq_hz == 20000"));
    ctx.push_obligation(ProofObligation::assume(
        "vf_def",
        "valid_freq == if freq_hz == 15000 || freq_hz == 20000 || freq_hz == 30000 || freq_hz == 35000 || freq_hz == 40000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_freq == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Ultrasonic welding: 20kHz is valid operating frequency",
    );
}

#[test]
fn amplitude() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("amp_um", u32_ty());
    ctx.declare_var_typed("amp_ok", i32_ty());
    // Peak-to-peak amplitude in microns
    ctx.push_obligation(ProofObligation::assume("au", "amp_um == 80"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "amp_ok == if amp_um >= 20 && amp_um <= 150 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "amp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Ultrasonic welding: 80um amplitude in [20, 150] range",
    );
}

#[test]
fn weld_force() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("force_n", u32_ty());
    ctx.declare_var_typed("force_ok", i32_ty());
    // Weld force in Newtons
    ctx.push_obligation(ProofObligation::assume("fn_val", "force_n == 1500"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "force_ok == if force_n >= 100 && force_n <= 10000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "force_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Ultrasonic welding: 1500N force in [100, 10000] range",
    );
}

#[test]
fn weld_time() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time_ms", u32_ty());
    ctx.declare_var_typed("time_ok", i32_ty());
    // Weld duration in milliseconds
    ctx.push_obligation(ProofObligation::assume("tm", "time_ms == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "time_ok == if time_ms >= 50 && time_ms <= 5000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "time_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Ultrasonic welding: 500ms weld time in [50, 5000] range",
    );
}

#[test]
fn power_rating() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_w", u32_ty());
    ctx.declare_var_typed("power_ok", i32_ty());
    // Generator power in watts
    ctx.push_obligation(ProofObligation::assume("pw", "power_w == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "power_ok == if power_w >= 500 && power_w <= 6000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "power_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Ultrasonic welding: 3000W generator in [500, 6000] range",
    );
}

#[test]
fn weld_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("valid_mode", i32_ty());
    // Weld modes: 1=time, 2=energy, 3=distance, 4=absolute distance
    ctx.push_obligation(ProofObligation::assume("m", "mode == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mode == if mode == 1 || mode == 2 || mode == 3 || mode == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Ultrasonic welding: energy mode is valid weld mode",
    );
}

#[test]
fn horn_gain() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gain_x100", u32_ty());
    ctx.declare_var_typed("gain_ok", i32_ty());
    // Sonotrode gain ratio x100 (2.50:1 = 250), range 1.00-5.00:1
    ctx.push_obligation(ProofObligation::assume("gx", "gain_x100 == 250"));
    ctx.push_obligation(ProofObligation::assume(
        "go_def",
        "gain_ok == if gain_x100 >= 100 && gain_x100 <= 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "gain_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Ultrasonic welding: 2.50:1 horn gain in [1.00, 5.00] range",
    );
}

#[test]
fn trigger_force() {
    let mut ctx = VerificationContext::new();
    for v in &["trig_force_n", "max_trig_n"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("trig_ok", i32_ty());
    // Trigger/pretrigger force in Newtons
    ctx.push_obligation(ProofObligation::assume("tf", "trig_force_n == 200"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_trig_n == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "tro_def",
        "trig_ok == if trig_force_n <= max_trig_n { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "trig_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Ultrasonic welding: 200N trigger force <= 2000N max",
    );
}

#[test]
fn hold_time() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hold_ms", u32_ty());
    ctx.declare_var_typed("hold_ok", i32_ty());
    // Post-weld hold time in milliseconds
    ctx.push_obligation(ProofObligation::assume("hm", "hold_ms == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "hold_ok == if hold_ms <= 5000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "hold_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Ultrasonic welding: 300ms hold time in [0, 5000] range",
    );
}

#[test]
fn energy_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["energy_j", "max_energy_j"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("energy_ok", i32_ty());
    // Weld energy limit in joules
    ctx.push_obligation(ProofObligation::assume("ej", "energy_j == 500"));
    ctx.push_obligation(ProofObligation::assume("me", "max_energy_j == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "energy_ok == if energy_j <= max_energy_j { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "energy_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Ultrasonic welding: 500J energy <= 10000J max");
}
