// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn rated_power() {
    let mut ctx = VerificationContext::new();
    for v in &["power_kw_x10", "max_power_kw_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pow_ok", i32_ty());
    // Rated power in kW (×10 for 0.1kW precision)
    ctx.push_obligation(ProofObligation::assume("pk", "power_kw_x10 == 75")); // 7.5kW
    ctx.push_obligation(ProofObligation::assume("mp", "max_power_kw_x10 == 5000")); // 500kW
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pow_ok == if power_kw_x10 <= max_power_kw_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pow_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VFD: 7.5kW ≤ 500kW max → OK");
}

#[test]
fn output_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_x10", "max_freq_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Output frequency in Hz (×10 for 0.1Hz)
    ctx.push_obligation(ProofObligation::assume("fx", "freq_x10 == 500")); // 50.0 Hz
    ctx.push_obligation(ProofObligation::assume("mf", "max_freq_x10 == 6000")); // 600.0 Hz
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_x10 <= max_freq_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VFD: 50.0Hz ≤ 600.0Hz max → OK");
}

#[test]
fn voltage_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_v", u32_ty());
    ctx.declare_var_typed("valid_voltage", i32_ty());
    // Standard supply voltage classes
    ctx.push_obligation(ProofObligation::assume("vv", "voltage_v == 400"));
    ctx.push_obligation(ProofObligation::assume(
        "vv_def",
        "valid_voltage == if voltage_v == 200 || voltage_v == 230 || voltage_v == 400 || voltage_v == 480 || voltage_v == 690 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_voltage == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VFD: 400V is valid voltage class");
}

#[test]
fn carrier_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["carrier_khz", "min_carrier_khz", "max_carrier_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("carrier_ok", i32_ty());
    // PWM carrier/switching frequency in kHz
    ctx.push_obligation(ProofObligation::assume("ck", "carrier_khz == 8"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_carrier_khz == 2"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_carrier_khz == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "carrier_ok == if carrier_khz >= min_carrier_khz && carrier_khz <= max_carrier_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "carrier_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VFD: 8kHz carrier in [2, 16] → OK");
}

#[test]
fn accel_time() {
    let mut ctx = VerificationContext::new();
    for v in &["accel_sec_x10", "min_accel_sec_x10", "max_accel_sec_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("accel_ok", i32_ty());
    // Acceleration time in seconds (×10 for 0.1s)
    ctx.push_obligation(ProofObligation::assume("ax", "accel_sec_x10 == 100")); // 10.0s
    ctx.push_obligation(ProofObligation::assume("mn", "min_accel_sec_x10 == 1")); // 0.1s
    ctx.push_obligation(ProofObligation::assume("mx", "max_accel_sec_x10 == 36000")); // 3600s
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "accel_ok == if accel_sec_x10 >= min_accel_sec_x10 && accel_sec_x10 <= max_accel_sec_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "accel_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VFD: 10.0s accel in [0.1, 3600] → OK");
}

#[test]
fn control_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("valid_mode", i32_ty());
    // Control modes: 1=V/f, 2=sensorless vector, 3=closed-loop vector, 4=torque control
    ctx.push_obligation(ProofObligation::assume("m", "mode == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mode == if mode == 1 || mode == 2 || mode == 3 || mode == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VFD: sensorless vector is valid control mode");
}

#[test]
fn overload_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["overload_pct", "min_overload_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ovl_ok", i32_ty());
    // Overload capacity as % of rated current (60s rating)
    ctx.push_obligation(ProofObligation::assume("op", "overload_pct == 150"));
    ctx.push_obligation(ProofObligation::assume("mo", "min_overload_pct == 110"));
    ctx.push_obligation(ProofObligation::assume(
        "oo_def",
        "ovl_ok == if overload_pct >= min_overload_pct { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ovl_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VFD: 150% overload ≥ 110% min → OK");
}

#[test]
fn dc_bus_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["bus_v", "max_bus_v"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bus_ok", i32_ty());
    // DC bus voltage (√2 × line voltage)
    ctx.push_obligation(ProofObligation::assume("bv", "bus_v == 565")); // √2 × 400
    ctx.push_obligation(ProofObligation::assume("mb", "max_bus_v == 800"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bus_ok == if bus_v <= max_bus_v { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bus_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VFD: 565V DC bus ≤ 800V max → OK");
}

#[test]
fn braking_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("brake", u32_ty());
    ctx.declare_var_typed("valid_brake", i32_ty());
    // Braking modes: 1=coast, 2=DC injection, 3=dynamic (resistor), 4=regenerative
    ctx.push_obligation(ProofObligation::assume("b", "brake == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vb_def",
        "valid_brake == if brake == 1 || brake == 2 || brake == 3 || brake == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_brake == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VFD: dynamic braking is valid mode");
}

#[test]
fn efficiency() {
    let mut ctx = VerificationContext::new();
    for v in &["efficiency_x10", "min_efficiency_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("eff_ok", i32_ty());
    // Drive efficiency as % (×10 for 0.1%)
    ctx.push_obligation(ProofObligation::assume("ex", "efficiency_x10 == 975")); // 97.5%
    ctx.push_obligation(ProofObligation::assume("me", "min_efficiency_x10 == 950")); // 95.0%
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "eff_ok == if efficiency_x10 >= min_efficiency_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "eff_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VFD: 97.5% efficiency ≥ 95.0% min → OK");
}
