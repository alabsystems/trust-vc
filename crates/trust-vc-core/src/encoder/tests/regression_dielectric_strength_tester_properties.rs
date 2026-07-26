// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("test_voltage", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "test_voltage >= 100 && test_voltage <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "test_voltage >= 100"));
    ctx.push_obligation(ProofObligation::assert("upper", "test_voltage <= 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dielectric: test voltage in [100, 50000] V");
}

#[test]
fn ramp_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ramp_rate", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "ramp_rate >= 1 && ramp_rate <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "ramp_rate >= 1"));
    ctx.push_obligation(ProofObligation::assert("upper", "ramp_rate <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dielectric: ramp rate in [1, 5000] V/s");
}

#[test]
fn test_mode_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("test_mode", u32_ty());
    // 1=AC, 2=DC, 3=IR (insulation resistance)
    ctx.push_obligation(ProofObligation::assume(
        "valid_mode",
        "test_mode == 1 || test_mode == 2 || test_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("at_least_one", "test_mode >= 1"));
    ctx.push_obligation(ProofObligation::assert("at_most_three", "test_mode <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dielectric: test mode is AC(1), DC(2), or IR(3)");
}

#[test]
fn frequency_bounded_for_ac_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("test_mode", u32_ty());
    ctx.declare_var_typed("frequency", u32_ty());
    // AC mode with valid frequency
    ctx.push_obligation(ProofObligation::assume("mode_ac", "test_mode == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "freq_range",
        "frequency >= 50 && frequency <= 400",
    ));
    ctx.push_obligation(ProofObligation::assert("freq_lower", "frequency >= 50"));
    ctx.push_obligation(ProofObligation::assert("freq_upper", "frequency <= 400"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dielectric: AC frequency in [50, 400] Hz");
}

#[test]
fn leakage_current_limit_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("leakage_limit_ua", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "leakage_limit_ua >= 1 && leakage_limit_ua <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "leakage_limit_ua >= 1"));
    ctx.push_obligation(ProofObligation::assert(
        "upper",
        "leakage_limit_ua <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "dielectric: leakage current limit in [1, 100000] uA",
    );
}

#[test]
fn dwell_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dwell_time_s", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "dwell_time_s >= 1 && dwell_time_s <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "dwell_time_s >= 1"));
    ctx.push_obligation(ProofObligation::assert("upper", "dwell_time_s <= 600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dielectric: dwell time in [1, 600] s");
}

#[test]
fn voltage_accuracy_bounded() {
    // Accuracy in tenths of percent: 1.0% → 10, range [5, 50] = [0.5%, 5.0%]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "accuracy_x10 >= 5 && accuracy_x10 <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "accuracy_x10 >= 5"));
    ctx.push_obligation(ProofObligation::assert("upper", "accuracy_x10 <= 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dielectric: voltage accuracy in [0.5%, 5.0%]");
}

#[test]
fn output_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "channels >= 1 && channels <= 16",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "channels >= 1"));
    ctx.push_obligation(ProofObligation::assert("upper", "channels <= 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dielectric: output channels in [1, 16]");
}

#[test]
fn safety_standard_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("safety_std", u32_ty());
    // 1=IEC 60950, 2=IEC 62368, 3=IEC 60601, 4=UL 1950
    ctx.push_obligation(ProofObligation::assume(
        "valid_std",
        "safety_std == 1 || safety_std == 2 || safety_std == 3 || safety_std == 4",
    ));
    ctx.push_obligation(ProofObligation::assert("at_least_one", "safety_std >= 1"));
    ctx.push_obligation(ProofObligation::assert("at_most_four", "safety_std <= 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "dielectric: safety standard is IEC 60950/62368/60601 or UL 1950",
    );
}

#[test]
fn ground_continuity_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ground_continuity", i32_ty());
    ctx.declare_var_typed("test_passed", i32_ty());
    // Ground continuity is a boolean flag: 0 or 1
    ctx.push_obligation(ProofObligation::assume(
        "flag_valid",
        "ground_continuity == 0 || ground_continuity == 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "gc_enabled",
        "ground_continuity == 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "pass_def",
        "test_passed == if ground_continuity == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("passed", "test_passed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "dielectric: ground continuity enabled -> test passed",
    );
}
