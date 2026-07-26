// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Accelerator mass spectrometer (AMS) properties:
// Terminal voltage (MV), beam current, isotope ratio precision,
// sample throughput, background ratio, ion source type,
// accelerator type, detector type, charge state, sequential injection.

#[test]
fn test_ams_terminal_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["voltage", "clamped"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    // Terminal voltage in MV, valid range 1-15
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range",
        "voltage >= 1 && voltage <= 15",
    ));
    ctx.push_obligation(ProofObligation::assume("voltage_val", "voltage == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "clamped_def",
        "clamped == if voltage >= 1 && voltage <= 15 { voltage } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "clamped_in_range",
        "clamped >= 1 && clamped <= 15",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "terminal voltage 5 MV within valid 1-15 MV range");
}

#[test]
fn test_ams_beam_current_scaled() {
    let mut ctx = VerificationContext::new();
    for v in &["current_x10", "within_range"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    // Beam current in units of 0.1 uA (scaled x10), range 1-1000 (0.1-100.0 uA)
    ctx.push_obligation(ProofObligation::assume(
        "current_range",
        "current_x10 >= 1 && current_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("current_val", "current_x10 == 250"));
    ctx.push_obligation(ProofObligation::assume(
        "within_range_def",
        "within_range == if current_x10 >= 1 && current_x10 <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "within_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "beam current 25.0 uA (x10=250) in valid range");
}

#[test]
fn test_ams_isotope_ratio_precision() {
    let mut ctx = VerificationContext::new();
    for v in &["precision_x10000", "high_precision"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    // Isotope ratio precision scaled x10000 (%), range 1-1000 (0.0001%-0.1000%)
    ctx.push_obligation(ProofObligation::assume(
        "precision_range",
        "precision_x10000 >= 1 && precision_x10000 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "precision_val",
        "precision_x10000 == 50",
    ));
    // High precision if <= 100 (i.e., <= 0.01%)
    ctx.push_obligation(ProofObligation::assume(
        "high_precision_def",
        "high_precision == if precision_x10000 <= 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_high_precision",
        "high_precision == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "isotope ratio precision 0.0050% (x10000=50) is high precision",
    );
}

#[test]
fn test_ams_sample_throughput_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["throughput", "total_two_days"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    // Sample throughput in samples/day, range 10-500
    ctx.push_obligation(ProofObligation::assume(
        "throughput_range",
        "throughput >= 10 && throughput <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "throughput_val",
        "throughput == 120",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "total_def",
        "total_two_days == throughput + throughput",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "two_day_bound",
        "total_two_days >= 20 && total_two_days <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "120 samples/day -> 240 over two days within bounds",
    );
}

#[test]
fn test_ams_background_ratio_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["bg_offset", "effective_exponent"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    // Background ratio exponent: actual range -15 to -10, stored as offset+20 -> 5 to 10
    ctx.push_obligation(ProofObligation::assume(
        "bg_range",
        "bg_offset >= 5 && bg_offset <= 10",
    ));
    ctx.push_obligation(ProofObligation::assume("bg_val", "bg_offset == 7"));
    // Recover the actual exponent: offset - 20
    ctx.push_obligation(ProofObligation::assume(
        "effective_def",
        "effective_exponent == bg_offset - 20",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "exponent_range",
        "effective_exponent >= 0 - 15 && effective_exponent <= 0 - 10",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "background ratio offset 7 -> exponent -13 in [-15, -10]",
    );
}

#[test]
fn test_ams_ion_source_type_disjunction() {
    let mut ctx = VerificationContext::new();
    for v in &["ion_source", "is_valid_source"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    // Ion source type: 1=cesium-sputter, 2=gas-ion, 3=SNICS
    ctx.push_obligation(ProofObligation::assume(
        "source_constraint",
        "ion_source == 1 || ion_source == 2 || ion_source == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("source_val", "ion_source == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "valid_def",
        "is_valid_source == if ion_source == 1 || ion_source == 2 || ion_source == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "source_valid",
        "is_valid_source == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gas-ion source (2) is a valid AMS ion source type");
}

#[test]
fn test_ams_accelerator_type_disjunction() {
    let mut ctx = VerificationContext::new();
    for v in &["accel_type", "is_valid_accel"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    // Accelerator type: 1=tandem, 2=single-stage, 3=compact-tandem
    ctx.push_obligation(ProofObligation::assume(
        "accel_constraint",
        "accel_type == 1 || accel_type == 2 || accel_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("accel_val", "accel_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "valid_def",
        "is_valid_accel == if accel_type == 1 || accel_type == 2 || accel_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "accel_valid",
        "is_valid_accel == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tandem accelerator (1) is a valid AMS accelerator type",
    );
}

#[test]
fn test_ams_detector_type_disjunction() {
    let mut ctx = VerificationContext::new();
    for v in &["detector_type", "is_valid_detector"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    // Detector type: 1=gas-ionization, 2=silicon-surface-barrier, 3=time-of-flight
    ctx.push_obligation(ProofObligation::assume(
        "detector_constraint",
        "detector_type == 1 || detector_type == 2 || detector_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "detector_val",
        "detector_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "valid_def",
        "is_valid_detector == if detector_type == 1 || detector_type == 2 || detector_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "detector_valid",
        "is_valid_detector == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "time-of-flight detector (3) is a valid AMS detector type",
    );
}

#[test]
fn test_ams_charge_state_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["charge_state", "next_charge"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    // Charge state after stripping, valid range 1-6
    ctx.push_obligation(ProofObligation::assume(
        "charge_range",
        "charge_state >= 1 && charge_state <= 6",
    ));
    ctx.push_obligation(ProofObligation::assume("charge_val", "charge_state == 3"));
    // Selecting a higher charge state (clamped to max 6)
    ctx.push_obligation(ProofObligation::assume(
        "next_charge_def",
        "next_charge == if charge_state + 1 <= 6 { charge_state + 1 } else { 6 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "next_in_range",
        "next_charge >= 1 && next_charge <= 6",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "charge state 3 -> 4 stays within valid 1-6 range");
}

#[test]
fn test_ams_sequential_injection_flag() {
    let mut ctx = VerificationContext::new();
    for v in &["seq_injection", "measurement_mode"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    // Sequential injection: boolean flag (0=simultaneous, 1=sequential)
    ctx.push_obligation(ProofObligation::assume(
        "flag_constraint",
        "seq_injection == 0 || seq_injection == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "seq_injection == 1"));
    // Measurement mode: sequential injection uses time-multiplexing (mode=2),
    // simultaneous uses parallel detection (mode=1)
    ctx.push_obligation(ProofObligation::assume(
        "mode_def",
        "measurement_mode == if seq_injection == 1 { 2 } else { 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_time_mux",
        "measurement_mode == 2",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sequential injection flag enables time-multiplexed measurement mode",
    );
}
