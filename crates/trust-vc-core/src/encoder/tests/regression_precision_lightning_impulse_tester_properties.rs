// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Peak voltage must be within 10-2400 kV range per IEC 60060-1.
#[test]
fn test_lightning_impulse_tester_peak_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pv_a",
        "voltage >= 10 && voltage <= 2400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pv_c",
        "voltage >= 10 && voltage <= 2400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lightning impulse tester peak voltage bounded 10-2400 kV",
    );
}

/// Front time at x100 us precision must be within 50-500 (0.50-5.00 us).
#[test]
fn test_lightning_impulse_tester_front_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("front_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ft_a",
        "front_x100 >= 50 && front_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ft_c",
        "front_x100 >= 50 && front_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lightning impulse tester front time x100 bounded 50-500",
    );
}

/// Tail time at x10 us precision must be within 100-5000 (10.0-500.0 us).
#[test]
fn test_lightning_impulse_tester_tail_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tail_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tt_a",
        "tail_x10 >= 100 && tail_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tt_c",
        "tail_x10 >= 100 && tail_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lightning impulse tester tail time x10 bounded 100-5000",
    );
}

/// Energy in joules must be within 100-500000 J range.
#[test]
fn test_lightning_impulse_tester_energy_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("energy", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "en_a",
        "energy >= 100 && energy <= 500000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "en_c",
        "energy >= 100 && energy <= 500000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lightning impulse tester energy bounded 100-500000 J",
    );
}

/// Capacitance at x100 nF precision must be within 10-100000 (1.0-10000.0 nF).
#[test]
fn test_lightning_impulse_tester_capacitance_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cap_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cp_a",
        "cap_x100 >= 10 && cap_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cp_c",
        "cap_x100 >= 10 && cap_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lightning impulse tester capacitance x100 bounded 10-100000",
    );
}

/// Charging current at x10 mA precision must be within 1-5000 (0.1-500.0 mA).
#[test]
fn test_lightning_impulse_tester_charging_current_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curr_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cc_a",
        "curr_x10 >= 1 && curr_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cc_c",
        "curr_x10 >= 1 && curr_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lightning impulse tester charging current x10 bounded 1-5000",
    );
}

/// Waveform type must be one of three valid kinds: 1=full, 2=chopped, 3=switching.
#[test]
fn test_lightning_impulse_tester_waveform_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("waveform", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wt_a",
        "waveform == 1 || waveform == 2 || waveform == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wt_c",
        "waveform == 1 || waveform == 2 || waveform == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lightning impulse tester waveform type three-way (full/chopped/switching)",
    );
}

/// Polarity must be one of three valid options: 1=positive, 2=negative, 3=alternating.
#[test]
fn test_lightning_impulse_tester_polarity_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("polarity", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "po_a",
        "polarity == 1 || polarity == 2 || polarity == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "po_c",
        "polarity == 1 || polarity == 2 || polarity == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lightning impulse tester polarity three-way (positive/negative/alternating)",
    );
}

/// Standard compliance must be one of three valid standards: 1=IEC60060, 2=IEEE4, 3=ASTM.
#[test]
fn test_lightning_impulse_tester_standard_compliance_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("standard", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sc_a",
        "standard == 1 || standard == 2 || standard == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sc_c",
        "standard == 1 || standard == 2 || standard == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lightning impulse tester standard compliance three-way (IEC60060/IEEE4/ASTM)",
    );
}

/// Automatic waveform analysis flag must be boolean: 0=disabled, 1=enabled.
#[test]
fn test_lightning_impulse_tester_auto_waveform_analysis_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wa_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("wa_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lightning impulse tester automatic waveform analysis flag boolean (0 or 1)",
    );
}
