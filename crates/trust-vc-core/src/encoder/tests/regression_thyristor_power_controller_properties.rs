// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn rated_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["voltage_v", "max_voltage_v"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("volt_ok", i32_ty());
    // Rated AC voltage
    ctx.push_obligation(ProofObligation::assume("vv", "voltage_v == 480"));
    ctx.push_obligation(ProofObligation::assume("mv", "max_voltage_v == 690"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "volt_ok == if voltage_v <= max_voltage_v { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "volt_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thyristor: 480V ≤ 690V max → OK");
}

#[test]
fn rated_current() {
    let mut ctx = VerificationContext::new();
    for v in &["current_a", "max_current_a"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cur_ok", i32_ty());
    // Continuous RMS current
    ctx.push_obligation(ProofObligation::assume("ca", "current_a == 100"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_current_a == 1200"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cur_ok == if current_a <= max_current_a { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cur_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thyristor: 100A ≤ 1200A max → OK");
}

#[test]
fn firing_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("valid_mode", i32_ty());
    // Firing modes: 1=phase-angle, 2=zero-cross (burst), 3=single-cycle, 4=soft-start
    ctx.push_obligation(ProofObligation::assume("m", "mode == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mode == if mode == 1 || mode == 2 || mode == 3 || mode == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thyristor: phase-angle is valid firing mode");
}

#[test]
fn phase_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("phases", u32_ty());
    ctx.declare_var_typed("valid_phases", i32_ty());
    // Phase configurations
    ctx.push_obligation(ProofObligation::assume("p", "phases == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_phases == if phases == 1 || phases == 2 || phases == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_phases == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thyristor: 3-phase is valid configuration");
}

#[test]
fn firing_angle() {
    let mut ctx = VerificationContext::new();
    for v in &["angle_deg", "max_angle_deg"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("angle_ok", i32_ty());
    // Phase-angle firing range (0° to 180°)
    ctx.push_obligation(ProofObligation::assume("ad", "angle_deg == 90"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_angle_deg == 175"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "angle_ok == if angle_deg <= max_angle_deg { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "angle_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thyristor: 90° firing ≤ 175° max → OK");
}

#[test]
fn di_dt_rating() {
    let mut ctx = VerificationContext::new();
    for v in &["didt_a_us", "min_didt_a_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("didt_ok", i32_ty());
    // di/dt rating in A/μs (rate of current rise)
    ctx.push_obligation(ProofObligation::assume("du", "didt_a_us == 200"));
    ctx.push_obligation(ProofObligation::assume("md", "min_didt_a_us == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "didt_ok == if didt_a_us >= min_didt_a_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "didt_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thyristor: 200 A/μs di/dt ≥ 50 min → OK");
}

#[test]
fn snubber_capacitance() {
    let mut ctx = VerificationContext::new();
    for v in &["snub_nf", "min_snub_nf", "max_snub_nf"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("snub_ok", i32_ty());
    // RC snubber capacitance in nF
    ctx.push_obligation(ProofObligation::assume("sn", "snub_nf == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_snub_nf == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_snub_nf == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "snub_ok == if snub_nf >= min_snub_nf && snub_nf <= max_snub_nf { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "snub_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thyristor: 100nF snubber in [10, 1000] → OK");
}

#[test]
fn load_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("load", u32_ty());
    ctx.declare_var_typed("valid_load", i32_ty());
    // Load types: 1=resistive, 2=inductive, 3=capacitive, 4=transformer, 5=infrared heater
    ctx.push_obligation(ProofObligation::assume("l", "load == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vl_def",
        "valid_load == if load == 1 || load == 2 || load == 3 || load == 4 || load == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_load == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thyristor: resistive is valid load type");
}

#[test]
fn control_signal() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("signal", u32_ty());
    ctx.declare_var_typed("valid_signal", i32_ty());
    // Control input: 1=4-20mA, 2=0-10V, 3=0-5V, 4=potentiometer, 5=digital (Modbus)
    ctx.push_obligation(ProofObligation::assume("s", "signal == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_signal == if signal == 1 || signal == 2 || signal == 3 || signal == 4 || signal == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_signal == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thyristor: 4-20mA is valid control signal");
}

#[test]
fn heatsink_thermal() {
    let mut ctx = VerificationContext::new();
    for v in &["rth_x100", "max_rth_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rth_ok", i32_ty());
    // Heatsink thermal resistance °C/W (×100 for 0.01°C/W)
    ctx.push_obligation(ProofObligation::assume("rx", "rth_x100 == 15")); // 0.15°C/W
    ctx.push_obligation(ProofObligation::assume("mr", "max_rth_x100 == 50")); // 0.50°C/W
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rth_ok == if rth_x100 <= max_rth_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rth_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thyristor: 0.15°C/W thermal ≤ 0.50 max → OK");
}
