// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn min_particle_size_bounded() {
    // Particle size in nanometers must be in [50, 10000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("particle_size_nm", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "particle_size_nm >= 50 && particle_size_nm <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lower_bound",
        "particle_size_nm >= 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "upper_bound",
        "particle_size_nm <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "particle size bounded [50, 10000] nm");
}

#[test]
fn channel_count_bounded() {
    // Particle counters have between 2 and 32 size channels
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "channels >= 2 && channels <= 32",
    ));
    ctx.push_obligation(ProofObligation::assert("at_least_two", "channels >= 2"));
    ctx.push_obligation(ProofObligation::assert("at_most_32", "channels <= 32"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "channel count bounded [2, 32]");
}

#[test]
fn flow_rate_bounded() {
    // Flow rate scaled x100: 2.83 L/min -> 283, bounded [10, 5000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_rate_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "flow_rate_x100 >= 10 && flow_rate_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "flow_rate_x100 >= 10"));
    ctx.push_obligation(ProofObligation::assert("upper", "flow_rate_x100 <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate x100 bounded [10, 5000]");
}

#[test]
fn light_source_three_way_disjunction() {
    // Light source: 1=laser diode, 2=HeNe laser, 3=white light
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("light_source", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "light_source == 1 || light_source == 2 || light_source == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("at_least_1", "light_source >= 1"));
    ctx.push_obligation(ProofObligation::assert("at_most_3", "light_source <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "light source is one of {laser diode, HeNe, white light}",
    );
}

#[test]
fn concentration_limit_bounded() {
    // Maximum concentration in particles/ft^3, bounded [1000, 10000000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conc_limit", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "conc_limit >= 1000 && conc_limit <= 10000000",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "conc_limit >= 1000"));
    ctx.push_obligation(ProofObligation::assert("upper", "conc_limit <= 10000000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "concentration limit bounded [1000, 10000000] particles/ft^3",
    );
}

#[test]
fn sample_time_bounded() {
    // Sample time in seconds, bounded [1, 3600]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sample_time_s", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "sample_time_s >= 1 && sample_time_s <= 3600",
    ));
    ctx.push_obligation(ProofObligation::assert("at_least_1s", "sample_time_s >= 1"));
    ctx.push_obligation(ProofObligation::assert(
        "at_most_1h",
        "sample_time_s <= 3600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sample time bounded [1, 3600] seconds");
}

#[test]
fn size_channels_four_way_non_sequential() {
    // Standard size channel counts: 6, 8, 16, or 31 (non-sequential)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("size_channels", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "size_channels == 6 || size_channels == 8 || size_channels == 16 || size_channels == 31",
    ));
    ctx.push_obligation(ProofObligation::assert("at_least_6", "size_channels >= 6"));
    ctx.push_obligation(ProofObligation::assert("at_most_31", "size_channels <= 31"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "size channels in {6, 8, 16, 31}");
}

#[test]
fn communication_interface_four_way_disjunction() {
    // Communication: 1=USB, 2=Ethernet, 3=RS-485, 4=analog
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm_iface", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "comm_iface == 1 || comm_iface == 2 || comm_iface == 3 || comm_iface == 4",
    ));
    ctx.push_obligation(ProofObligation::assert("at_least_1", "comm_iface >= 1"));
    ctx.push_obligation(ProofObligation::assert("at_most_4", "comm_iface <= 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "comm interface in {USB, Ethernet, RS-485, analog}");
}

#[test]
fn operating_temp_offset_bounded() {
    // Operating temperature with +500 offset: -50C to 80C -> [450, 580]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "temp_offset >= 450 && temp_offset <= 580",
    ));
    // 20C nominal -> 520 with offset
    ctx.push_obligation(ProofObligation::assert("above_min", "temp_offset >= 450"));
    ctx.push_obligation(ProofObligation::assert("below_max", "temp_offset <= 580"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp offset+500 bounded [450, 580]");
}

#[test]
fn iso_21501_compliant_boolean_flag() {
    // ISO 21501 compliance as boolean flag: i32, 1=compliant, 0=not
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("iso_compliant", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag", "iso_compliant == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "valid_flag",
        "iso_compliant == 0 || iso_compliant == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_compliant",
        "iso_compliant == if iso_compliant == 1 { 1 } else { 0 }",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ISO 21501 compliant flag is boolean 1");
}
