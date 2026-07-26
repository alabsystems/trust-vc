// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Test voltage in kV is bounded between 1 and 200.
#[test]
fn test_tan_delta_tester_voltage_kv_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tv_a",
        "voltage >= 1 && voltage <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tv_c",
        "voltage >= 1 && voltage <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tan delta tester voltage must be between 1 and 200 kV",
    );
}

/// Test frequency at x10 Hz is bounded between 1 and 10000.
#[test]
fn test_tan_delta_tester_frequency_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fq_a",
        "freq_x10 >= 1 && freq_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fq_c",
        "freq_x10 >= 1 && freq_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tan delta tester frequency x10 must be between 1 and 10000",
    );
}

/// Test tan delta at x10000 is bounded between 1 and 10000.
#[test]
fn test_tan_delta_tester_td_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("td_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "td_a",
        "td_x10000 >= 1 && td_x10000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "td_c",
        "td_x10000 >= 1 && td_x10000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tan delta tester dissipation factor x10000 must be between 1 and 10000",
    );
}

/// Test capacitance at x100 pF is bounded between 1 and 100000.
#[test]
fn test_tan_delta_tester_capacitance_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cap_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cp_a",
        "cap_x100 >= 1 && cap_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cp_c",
        "cap_x100 >= 1 && cap_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tan delta tester capacitance x100 pF must be between 1 and 100000",
    );
}

/// Test power factor at x10000 is bounded between 1 and 10000.
#[test]
fn test_tan_delta_tester_power_factor_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pf_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pf_a",
        "pf_x10000 >= 1 && pf_x10000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pf_c",
        "pf_x10000 >= 1 && pf_x10000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tan delta tester power factor x10000 must be between 1 and 10000",
    );
}

/// Test temperature at offset +100 degrees C is bounded between 80 and 250.
#[test]
fn test_tan_delta_tester_temperature_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tp_a",
        "temp_off >= 80 && temp_off <= 250",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tp_c",
        "temp_off >= 80 && temp_off <= 250",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tan delta tester temperature offset must be between 80 and 250",
    );
}

/// Test bridge type is one of three valid values.
#[test]
fn test_tan_delta_tester_bridge_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bridge", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bt_a",
        "bridge >= 1 && bridge <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bt_c",
        "bridge == 1 || bridge == 2 || bridge == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tan delta tester bridge type must be 1=Schering, 2=Wien, or 3=transformer-ratio-arm",
    );
}

/// Test specimen type is one of three valid values.
#[test]
fn test_tan_delta_tester_specimen_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("specimen", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sp_a",
        "specimen >= 1 && specimen <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sp_c",
        "specimen == 1 || specimen == 2 || specimen == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tan delta tester specimen type must be 1=bushing, 2=cable, or 3=transformer-winding",
    );
}

/// Test standard is one of three valid values.
#[test]
fn test_tan_delta_tester_test_standard_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("standard", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ts_a",
        "standard >= 1 && standard <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ts_c",
        "standard == 1 || standard == 2 || standard == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tan delta tester test standard must be 1=IEC60250, 2=ASTMD150, or 3=IEEE62",
    );
}

/// Test automatic temperature compensation flag is boolean.
#[test]
fn test_tan_delta_tester_auto_temp_comp_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tc_a", "flag >= 0 && flag <= 1"));
    ctx.push_obligation(ProofObligation::assert("tc_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tan delta tester auto temperature compensation flag must be 0=disabled or 1=enabled",
    );
}
