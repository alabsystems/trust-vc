// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Ion pump (sputter-ion pump) controller property verification.
// Integer-scaled physical quantities avoid floating point in the SMT encoding.

/// Pumping speed: scaled x10 L/s (5000 = 500.0 L/s). Range 1..=50000.
#[test]
fn test_ion_pump_pumping_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 1 && speed <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assume("speed_val", "speed == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 1 && speed <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pumping speed 500.0 L/s within range");
}

/// Operating voltage in kV. Range 1..=10.
#[test]
fn test_ion_pump_operating_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_kv", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range",
        "voltage_kv >= 1 && voltage_kv <= 10",
    ));
    ctx.push_obligation(ProofObligation::assume("voltage_val", "voltage_kv == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_bounded",
        "voltage_kv >= 1 && voltage_kv <= 10",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating voltage 5 kV within range");
}

/// Ultimate pressure: scaled x10000 mbar (1 = 0.0001 mbar). Range 1..=100.
#[test]
fn test_ion_pump_ultimate_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_range",
        "pressure >= 1 && pressure <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("pressure_val", "pressure == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_bounded",
        "pressure >= 1 && pressure <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ultimate pressure 0.0001 mbar within range");
}

/// Starting pressure: scaled x100 mbar (1 = 0.01 mbar). Range 1..=1000.
#[test]
fn test_ion_pump_starting_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("start_pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "start_range",
        "start_pressure >= 1 && start_pressure <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "start_val",
        "start_pressure == 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "start_bounded",
        "start_pressure >= 1 && start_pressure <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "starting pressure 1.00 mbar within range");
}

/// Magnetic field strength: scaled x10 Tesla (12 = 1.2 T). Range 5..=30.
#[test]
fn test_ion_pump_magnetic_field_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mag_field", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mag_range",
        "mag_field >= 5 && mag_field <= 30",
    ));
    ctx.push_obligation(ProofObligation::assume("mag_val", "mag_field == 12"));
    ctx.push_obligation(ProofObligation::assert(
        "mag_bounded",
        "mag_field >= 5 && mag_field <= 30",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "magnetic field 1.2 T within range");
}

/// Number of anode cells. Range 1..=200.
#[test]
fn test_ion_pump_cell_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cells", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cell_range",
        "cells >= 1 && cells <= 200",
    ));
    ctx.push_obligation(ProofObligation::assume("cell_val", "cells == 60"));
    ctx.push_obligation(ProofObligation::assert(
        "cell_bounded",
        "cells >= 1 && cells <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "60 anode cells within range");
}

/// Pump type enumeration: 1=diode, 2=triode, 3=starcell.
#[test]
fn test_ion_pump_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pump_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("type_val", "pump_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "type_valid",
        "pump_type == 1 || pump_type == 2 || pump_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "diode pump type is valid enumeration member");
}

/// Cathode material enumeration: 1=titanium, 2=tantalum, 3=titanium-tantalum.
#[test]
fn test_ion_pump_cathode_material_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cathode", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cathode_val", "cathode == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "cathode_valid",
        "cathode == 1 || cathode == 2 || cathode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "titanium cathode is valid material");
}

/// Magnet type enumeration: 1=permanent, 2=electromagnet, 3=hybrid.
#[test]
fn test_ion_pump_magnet_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("magnet", i32_ty());
    ctx.push_obligation(ProofObligation::assume("magnet_val", "magnet == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "magnet_valid",
        "magnet == 1 || magnet == 2 || magnet == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "permanent magnet is valid type");
}

/// Automatic restart: boolean flag (1=enabled, 0=disabled).
/// When enabled, restart logic evaluates to 1.
#[test]
fn test_ion_pump_auto_restart_enabled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_restart", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "restart_enabled",
        "auto_restart == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "restart_active",
        "if auto_restart == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto restart flag enabled yields active");
}
