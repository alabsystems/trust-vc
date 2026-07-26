// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Excimer (UV pulsed) laser controller properties.
// Gas type codes: 1=ArF, 2=KrF, 3=XeCl, 4=F2
// Wavelengths (nm): ArF=193, KrF=248, XeCl=308, F2=157
// Cooling codes: 1=air, 2=water, 3=chiller

#[test]
fn test_wavelength_four_way_non_sequential() {
    // Gas type -> wavelength (nm): 1=ArF->193, 2=KrF->248, 3=XeCl->308, 4=F2->157
    // Note: wavelengths are NOT sequential with gas type ordering
    let mut ctx = VerificationContext::new();
    for v in &["gas_type", "wavelength"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume(
        "gas_range",
        "gas_type >= 1 && gas_type <= 4",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "wavelength_def",
        "wavelength == if gas_type == 1 { 193 } else { if gas_type == 2 { 248 } else { if gas_type == 3 { 308 } else { 157 } } }",
    ));
    // All four wavelengths are valid excimer UV lines
    ctx.push_obligation(ProofObligation::assert(
        "valid_wavelength",
        "wavelength == 157 || wavelength == 193 || wavelength == 248 || wavelength == 308",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gas type maps to one of four valid excimer wavelengths",
    );
}

#[test]
fn test_pulse_energy_bounds() {
    // Pulse energy: value 500 mJ, min 10, max 2000
    let mut ctx = VerificationContext::new();
    for v in &["energy", "min_energy", "max_energy"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("energy_val", "energy == 500"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_energy == 10"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_energy == 2000"));
    ctx.push_obligation(ProofObligation::assert(
        "energy_in_range",
        "energy >= min_energy && energy <= max_energy",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pulse energy 500 mJ within [10, 2000]");
}

#[test]
fn test_repetition_rate_bounds() {
    // Pulse repetition frequency: value 200 Hz, min 1, max 6000
    let mut ctx = VerificationContext::new();
    for v in &["prf", "min_prf", "max_prf"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("prf_val", "prf == 200"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_prf == 1"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_prf == 6000"));
    ctx.push_obligation(ProofObligation::assert(
        "prf_in_range",
        "prf >= min_prf && prf <= max_prf",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "repetition rate 200 Hz within [1, 6000]");
}

#[test]
fn test_pulse_duration_bounds() {
    // Temporal pulse width: value 25 ns, min 5, max 100
    let mut ctx = VerificationContext::new();
    for v in &["duration", "min_dur", "max_dur"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("dur_val", "duration == 25"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_dur == 5"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_dur == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "duration_in_range",
        "duration >= min_dur && duration <= max_dur",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pulse duration 25 ns within [5, 100]");
}

#[test]
fn test_gas_mixture_four_way_disjunction() {
    // Gas mixture type must be one of: 1=ArF, 2=KrF, 3=XeCl, 4=F2
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas_mix", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gas_mix_range",
        "gas_mix >= 1 && gas_mix <= 4",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_gas",
        "gas_mix == 1 || gas_mix == 2 || gas_mix == 3 || gas_mix == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gas mixture is one of ArF/KrF/XeCl/F2");
}

#[test]
fn test_beam_size_width_scaled() {
    // Beam aperture width in x10 mm: value 60 (6.0mm), min 10, max 200
    let mut ctx = VerificationContext::new();
    for v in &["width_x10", "min_w", "max_w"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("width_val", "width_x10 == 60"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_w == 10"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_w == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "width_in_range",
        "width_x10 >= min_w && width_x10 <= max_w",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "beam width 60 (6.0mm) within [10, 200] x10mm");
}

#[test]
fn test_energy_stability_scaled() {
    // Pulse-to-pulse energy stability in x100 %: value 200 (2.00%), min 50, max 500
    let mut ctx = VerificationContext::new();
    for v in &["stability_x100", "min_stab", "max_stab"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("stab_val", "stability_x100 == 200"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_stab == 50"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_stab == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "stability_in_range",
        "stability_x100 >= min_stab && stability_x100 <= max_stab",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "energy stability 200 (2.00%) within [50, 500] x100%",
    );
}

#[test]
fn test_gas_lifetime_scaled() {
    // Gas lifetime in x1000 pulses: value 5000 (5M pulses), min 1000, max 20000
    let mut ctx = VerificationContext::new();
    for v in &["lifetime_x1k", "min_life", "max_life"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("life_val", "lifetime_x1k == 5000"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_life == 1000"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_life == 20000"));
    ctx.push_obligation(ProofObligation::assert(
        "lifetime_in_range",
        "lifetime_x1k >= min_life && lifetime_x1k <= max_life",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gas lifetime 5000 (5M pulses) within [1000, 20000] x1000",
    );
}

#[test]
fn test_cooling_type_three_way_disjunction() {
    // Cooling type must be one of: 1=air, 2=water, 3=chiller
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooling", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cooling_range",
        "cooling >= 1 && cooling <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_cooling",
        "cooling == 1 || cooling == 2 || cooling == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cooling type is one of air/water/chiller");
}

#[test]
fn test_interlock_active_boolean_flag() {
    // Interlock active as i32 boolean flag: 0=inactive, 1=active
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("interlock", i32_ty());
    ctx.declare_var_typed("laser_enabled", i32_ty());
    ctx.push_obligation(ProofObligation::assume("interlock_val", "interlock == 1"));
    // Laser can only fire when interlock is active
    ctx.push_obligation(ProofObligation::assume(
        "laser_def",
        "laser_enabled == if interlock == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("laser_on", "laser_enabled == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "interlock active enables laser firing");
}
