// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Precision lock-in amplifier property verification tests

use super::*;

#[test]
fn test_frequency_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_mhz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "freq_mhz >= 1 && freq_mhz <= 600",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "freq_mhz == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "freq_mhz >= 1 && freq_mhz <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frequency MHz bounded 1-600 at 200");
}

#[test]
fn test_sensitivity_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensitivity_x1000_nv", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "sensitivity_x1000_nv >= 1 && sensitivity_x1000_nv <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "sensitivity_x1000_nv == 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "sensitivity_x1000_nv >= 1 && sensitivity_x1000_nv <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sensitivity x1000 nV bounded 1-1000000 at 1000 (1.000 uV full scale)",
    );
}

#[test]
fn test_dynamic_reserve_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dynamic_reserve_db", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "dynamic_reserve_db >= 60 && dynamic_reserve_db <= 120",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "dynamic_reserve_db == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "dynamic_reserve_db >= 60 && dynamic_reserve_db <= 120",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dynamic reserve dB bounded 60-120 at 100");
}

#[test]
fn test_time_constant_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time_constant_x10_us", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "time_constant_x10_us >= 1 && time_constant_x10_us <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "time_constant_x10_us == 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "time_constant_x10_us >= 1 && time_constant_x10_us <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "time constant x10 us bounded 1-100000 at 10000 (1000.0 us)",
    );
}

#[test]
fn test_input_impedance_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("input_impedance_mohm", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "input_impedance_mohm >= 1 && input_impedance_mohm <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "input_impedance_mohm == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "input_impedance_mohm >= 1 && input_impedance_mohm <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "input impedance MOhm bounded 1-100 at 10");
}

#[test]
fn test_adc_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("adc_bits", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "adc_bits >= 16 && adc_bits <= 24",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "adc_bits == 18"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "adc_bits >= 16 && adc_bits <= 24",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADC resolution bits bounded 16-24 at 18");
}

#[test]
fn test_demodulator_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("demod_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "demod_type >= 1 && demod_type <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "demod_type == 1 || demod_type == 2 || demod_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "demodulator type disjunction: 1=analog, 2=digital, 3=dual-phase",
    );
}

#[test]
fn test_reference_source_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ref_source", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "ref_source >= 1 && ref_source <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "ref_source == 1 || ref_source == 2 || ref_source == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "reference source disjunction: 1=internal, 2=external, 3=dual",
    );
}

#[test]
fn test_input_coupling_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("input_coupling", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "input_coupling >= 1 && input_coupling <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "input_coupling == 1 || input_coupling == 2 || input_coupling == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "input coupling disjunction: 1=AC, 2=DC, 3=differential",
    );
}

#[test]
fn test_auto_phase_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "auto_phase",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto phase flag enabled implies output 1");
}
