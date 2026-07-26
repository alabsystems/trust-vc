// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// LIBS = Laser-Induced Breakdown Spectroscopy: rapid multi-element analysis
// of solids, liquids, and gases via laser ablation plasma emission.

#[test]
fn laser_pulse_energy_bounded() {
    // Laser pulse energy must be within 1-500 mJ for safe LIBS operation
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pulse_energy_mj", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "energy_range",
        "pulse_energy_mj >= 1 && pulse_energy_mj <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "energy_positive",
        "pulse_energy_mj >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "energy_upper",
        "pulse_energy_mj <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIBS laser pulse energy bounded to 1-500 mJ");
}

#[test]
fn repetition_rate_bounded() {
    // Laser repetition rate must be within 1-1000 Hz
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rep_rate_hz", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rate_range",
        "rep_rate_hz >= 1 && rep_rate_hz <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert("rate_positive", "rep_rate_hz >= 1"));
    ctx.push_obligation(ProofObligation::assert("rate_upper", "rep_rate_hz <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIBS repetition rate bounded to 1-1000 Hz");
}

#[test]
fn gate_delay_scaled_bounded() {
    // Gate delay x100 in range 1-100000 (representing 0.01-1000.00 us)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gate_delay_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "delay_range",
        "gate_delay_x100 >= 1 && gate_delay_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "delay_positive",
        "gate_delay_x100 >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "delay_upper",
        "gate_delay_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "LIBS gate delay x100 bounded to 1-100000 (0.01-1000.00 us)",
    );
}

#[test]
fn spectral_range_bounded() {
    // Spectral observation range bounded to 100-1000 nm
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spectral_range_nm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spectral_range",
        "spectral_range_nm >= 100 && spectral_range_nm <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "range_lower",
        "spectral_range_nm >= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "range_upper",
        "spectral_range_nm <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIBS spectral range bounded to 100-1000 nm");
}

#[test]
fn spectral_resolution_scaled_bounded() {
    // Spectral resolution x100 in range 1-5000 (representing 0.01-50.00 nm)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "resolution_range",
        "resolution_x100 >= 1 && resolution_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "resolution_positive",
        "resolution_x100 >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "resolution_upper",
        "resolution_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "LIBS spectral resolution x100 bounded to 1-5000 (0.01-50.00 nm)",
    );
}

#[test]
fn accumulations_bounded() {
    // Number of shot accumulations must be within 1-10000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accumulations", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "accum_range",
        "accumulations >= 1 && accumulations <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "accum_positive",
        "accumulations >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "accum_upper",
        "accumulations <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIBS accumulations bounded to 1-10000");
}

#[test]
fn laser_type_three_way_disjunction() {
    // Laser type: 1=Nd:YAG, 2=fiber, 3=excimer
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("laser_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_laser",
        "laser_type == 1 || laser_type == 2 || laser_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "laser_in_range",
        "laser_type >= 1 && laser_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "LIBS laser type is one of Nd:YAG(1), fiber(2), excimer(3)",
    );
}

#[test]
fn spectrometer_type_three_way_disjunction() {
    // Spectrometer type: 1=Echelle, 2=Czerny-Turner, 3=multi-channel
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spec_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_spec",
        "spec_type == 1 || spec_type == 2 || spec_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spec_in_range",
        "spec_type >= 1 && spec_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "LIBS spectrometer type is one of Echelle(1), Czerny-Turner(2), multi-channel(3)",
    );
}

#[test]
fn measurement_environment_three_way_disjunction() {
    // Measurement environment: 1=air, 2=argon, 3=vacuum
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("environment", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_env",
        "environment == 1 || environment == 2 || environment == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "env_in_range",
        "environment >= 1 && environment <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "LIBS environment is one of air(1), argon(2), vacuum(3)",
    );
}

#[test]
fn auto_focus_boolean_flag() {
    // Automatic focus adjustment: 0=off, 1=on (boolean flag)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_focus", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_flag",
        "auto_focus == 0 || auto_focus == 1",
    ));
    ctx.push_obligation(ProofObligation::assert("flag_lower", "auto_focus >= 0"));
    ctx.push_obligation(ProofObligation::assert("flag_upper", "auto_focus <= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIBS auto-focus flag is boolean (0 or 1)");
}
