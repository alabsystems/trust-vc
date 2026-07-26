// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_frequency_bounded() {
    // Test frequency range: 20 Hz to 2 MHz
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_hz", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("f", "freq_hz == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if freq_hz >= 20 && freq_hz <= 2000000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCR freq: 1000 Hz in [20, 2000000]");
}

#[test]
fn test_capacitance_range_scaled() {
    // Capacitance in units of 0.01 pF (x100 scaling)
    // 100 pF = 10000 scaled units; range 1..999999999 (0.01 pF to ~10 mF)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cap_x100pf", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("c", "cap_x100pf == 10000")); // 100.00 pF
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if cap_x100pf >= 1 && cap_x100pf <= 999999999 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCR capacitance: 10000 x0.01pF in range");
}

#[test]
fn test_inductance_range_scaled() {
    // Inductance in units of 0.01 uH (x100 scaling)
    // 470 uH = 47000 scaled units
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ind_x100uh", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("l", "ind_x100uh == 47000")); // 470.00 uH
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if ind_x100uh >= 1 && ind_x100uh <= 999999999 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCR inductance: 47000 x0.01uH in range");
}

#[test]
fn test_resistance_bounded() {
    // Resistance range: 1 ohm to 100 Mohm
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resistance_ohm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("r", "resistance_ohm == 4700"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if resistance_ohm >= 1 && resistance_ohm <= 100000000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCR resistance: 4700 ohm in [1, 100000000]");
}

#[test]
fn test_basic_accuracy_scaled() {
    // Accuracy in units of 0.001% (x1000 scaling)
    // 0.05% = 50 scaled units; must be positive and bounded
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x1000", "max_accuracy_x1000"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("meets_spec", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "accuracy_x1000 == 50")); // 0.050%
    ctx.push_obligation(ProofObligation::assume("ma", "max_accuracy_x1000 == 100")); // 0.100%
    ctx.push_obligation(ProofObligation::assume(
        "ms_def",
        "meets_spec == if accuracy_x1000 >= 1 && accuracy_x1000 <= max_accuracy_x1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "meets_spec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCR accuracy: 50 x0.001% <= 100 x0.001% spec");
}

#[test]
fn test_measurement_parameter_disjunction() {
    // Measurement parameter: 1=Cs-Rs, 2=Cp-Rp, 3=Ls-Rs
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_param", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mp", "meas_param == 2")); // Cp-Rp
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if meas_param == 1 || meas_param == 2 || meas_param == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCR param: 2 (Cp-Rp) in {1,2,3}");
}

#[test]
fn test_signal_voltage_scaled() {
    // Test signal voltage in units of 0.01 V (x100 scaling)
    // 1.00 V = 100 scaled units; range 5..200 (0.05V to 2.00V)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("signal_x100v", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sv", "signal_x100v == 100")); // 1.00 V
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if signal_x100v >= 5 && signal_x100v <= 200 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCR signal: 100 x0.01V in [5, 200]");
}

#[test]
fn test_trigger_mode_disjunction() {
    // Trigger mode: 1=internal, 2=external, 3=bus
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trigger_mode", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tm", "trigger_mode == 3")); // bus trigger
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if trigger_mode == 1 || trigger_mode == 2 || trigger_mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCR trigger: 3 (bus) in {1,2,3}");
}

#[test]
fn test_measurement_speed_bounded() {
    // Measurement speed: 1 to 200 measurements per second
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_mps", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("s", "speed_mps == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if speed_mps >= 1 && speed_mps <= 200 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCR speed: 50 meas/s in [1, 200]");
}

#[test]
fn test_kelvin_connection_flag() {
    // Kelvin (4-terminal) connection: boolean flag as i32 (1=enabled, 0=disabled)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("kelvin_enabled", i32_ty());
    ctx.declare_var_typed("four_terminal", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ke", "kelvin_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ft_def",
        "four_terminal == if kelvin_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "four_terminal == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCR Kelvin: flag=1 -> 4-terminal active");
}
