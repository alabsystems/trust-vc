// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn rated_current() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current_ma", u32_ty());
    ctx.declare_var_typed("current_ok", i32_ty());
    // Continuous current in mA: 10A = 10000mA, valid range 0.5A-100A
    ctx.push_obligation(ProofObligation::assume("val", "current_ma == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "current_ok == if current_ma >= 500 && current_ma <= 100000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "current_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Servo drive: 10A (10000mA) rated current in [500, 100000]",
    );
}

#[test]
fn peak_current() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("peak_ma", u32_ty());
    ctx.declare_var_typed("peak_ok", i32_ty());
    // Peak current in mA: 30A = 30000mA, valid range 1A-300A
    ctx.push_obligation(ProofObligation::assume("val", "peak_ma == 30000"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "peak_ok == if peak_ma >= 1000 && peak_ma <= 300000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "peak_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Servo drive: 30A (30000mA) peak current in [1000, 300000]",
    );
}

#[test]
fn supply_voltage() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bus_voltage_v", u32_ty());
    ctx.declare_var_typed("voltage_ok", i32_ty());
    // DC bus voltage: 325V (230VAC rectified), valid range 24-800V
    ctx.push_obligation(ProofObligation::assume("val", "bus_voltage_v == 325"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "voltage_ok == if bus_voltage_v >= 24 && bus_voltage_v <= 800 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "voltage_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Servo drive: 325V DC bus (230VAC rectified) in [24, 800]",
    );
}

#[test]
fn control_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("valid_mode", i32_ty());
    // 1=position, 2=velocity, 3=torque, 4=position+velocity, 5=impedance
    ctx.push_obligation(ProofObligation::assume("val", "mode == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mode == if mode == 1 || mode == 2 || mode == 3 || mode == 4 || mode == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Servo drive: torque mode (3) is valid control mode",
    );
}

#[test]
fn feedback_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fb_type", u32_ty());
    ctx.declare_var_typed("valid_fb", i32_ty());
    // 1=incremental encoder, 2=absolute encoder, 3=resolver, 4=hall sensors, 5=sensorless (back-EMF)
    ctx.push_obligation(ProofObligation::assume("val", "fb_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vf_def",
        "valid_fb == if fb_type == 1 || fb_type == 2 || fb_type == 3 || fb_type == 4 || fb_type == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_fb == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Servo drive: absolute encoder (2) is valid feedback type",
    );
}

#[test]
fn pwm_frequency() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pwm_khz", u32_ty());
    ctx.declare_var_typed("pwm_ok", i32_ty());
    // Switching frequency in kHz: 16kHz, valid range 4-32kHz
    ctx.push_obligation(ProofObligation::assume("val", "pwm_khz == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "pwm_ok == if pwm_khz >= 4 && pwm_khz <= 32 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "pwm_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Servo drive: 16kHz PWM switching frequency in [4, 32]",
    );
}

#[test]
fn velocity_loop_bandwidth() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bandwidth_hz", u32_ty());
    ctx.declare_var_typed("bw_ok", i32_ty());
    // Velocity loop bandwidth in Hz: 500Hz, valid range 50-5000Hz
    ctx.push_obligation(ProofObligation::assume("val", "bandwidth_hz == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "bw_ok == if bandwidth_hz >= 50 && bandwidth_hz <= 5000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "bw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Servo drive: 500Hz velocity loop bandwidth in [50, 5000]",
    );
}

#[test]
fn encoder_resolution() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("counts_per_rev", u32_ty());
    ctx.declare_var_typed("resolution_ok", i32_ty());
    // Encoder counts per revolution: 131072 (17-bit), valid range 1024 (10-bit) to 8388608 (23-bit)
    ctx.push_obligation(ProofObligation::assume("val", "counts_per_rev == 131072"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "resolution_ok == if counts_per_rev >= 1024 && counts_per_rev <= 8388608 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "resolution_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Servo drive: 131072 counts/rev (17-bit) in [1024, 8388608]",
    );
}

#[test]
fn communication_interface() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm_if", u32_ty());
    ctx.declare_var_typed("valid_comm", i32_ty());
    // 1=EtherCAT, 2=PROFINET, 3=Ethernet/IP, 4=CANopen, 5=Modbus RTU, 6=MECHATROLINK
    ctx.push_obligation(ProofObligation::assume("val", "comm_if == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_comm == if comm_if == 1 || comm_if == 2 || comm_if == 3 || comm_if == 4 || comm_if == 5 || comm_if == 6 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_comm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Servo drive: EtherCAT (1) is valid communication interface",
    );
}

#[test]
fn overload_capacity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("overload_pct_x10", u32_ty());
    ctx.declare_var_typed("overload_ok", i32_ty());
    // Overload % of rated (×10): 3000 = 300.0%, valid range 1500-4000 (150-400%)
    ctx.push_obligation(ProofObligation::assume("val", "overload_pct_x10 == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "overload_ok == if overload_pct_x10 >= 1500 && overload_pct_x10 <= 4000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "overload_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Servo drive: 300% overload capacity in [150%, 400%]",
    );
}
