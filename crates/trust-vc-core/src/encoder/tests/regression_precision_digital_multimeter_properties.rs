// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_digit_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("digs_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "digs_range",
        "digs_x10 >= 35 && digs_x10 <= 85",
    ));
    ctx.push_obligation(ProofObligation::assume("digs_val", "digs_x10 == 65"));
    ctx.push_obligation(ProofObligation::assert("digit_count", "digs_x10 == 65"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "6.5 display digits (65 scaled x10) within 3.5-8.5 digit range",
    );
}

#[test]
fn test_dc_voltage_accuracy_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dcv_x10000", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dcv_range",
        "dcv_x10000 >= 1 && dcv_x10000 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("dcv_val", "dcv_x10000 == 30"));
    ctx.push_obligation(ProofObligation::assert(
        "dc_voltage_accuracy",
        "dcv_x10000 == 30",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "0.0030% DCV accuracy (30 scaled x10000) within 0.0001-0.0500% range",
    );
}

#[test]
fn test_dc_current_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dc_curr", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "curr_range",
        "dc_curr >= 1 && dc_curr <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("curr_val", "dc_curr == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "dc_current_range",
        "dc_curr == 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1000 mA max DC current within 1-10000 mA range");
}

#[test]
fn test_ac_bandwidth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bw", u64_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bw_range",
        "bw >= 1 && bw <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assume("bw_val", "bw == 300000"));
    ctx.push_obligation(ProofObligation::assert("ac_bandwidth", "bw == 300000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "300 kHz AC bandwidth (300000 Hz) within 1-1000000 Hz range",
    );
}

#[test]
fn test_resistance_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_max", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_range",
        "res_max >= 1 && res_max <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("res_val", "res_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "resistance_max",
        "res_max == 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "10000 MOhm max resistance within 1-100000 MOhm range",
    );
}

#[test]
fn test_input_impedance_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("imp", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "imp_range",
        "imp >= 1 && imp <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("imp_val", "imp == 10"));
    ctx.push_obligation(ProofObligation::assert("input_impedance", "imp == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "10 GOhm input impedance within 1-100 GOhm range");
}

#[test]
fn test_measurement_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u8_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_mode",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mode_bounded",
        "mode >= 1 && mode <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement mode (1=DCV, 2=ACV, 3=resistance) implies [1,3]",
    );
}

#[test]
fn test_trigger_source_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trig", u8_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_trig",
        "trig == 1 || trig == 2 || trig == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "trig_bounded",
        "trig >= 1 && trig <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "trigger source (1=internal, 2=external, 3=bus) implies [1,3]",
    );
}

#[test]
fn test_interface_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("iface", u8_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_iface",
        "iface == 1 || iface == 2 || iface == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "iface_bounded",
        "iface >= 1 && iface <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "interface type (1=GPIB, 2=USB, 3=LAN) implies [1,3]",
    );
}

#[test]
fn test_auto_range_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto", i32_ty());
    ctx.push_obligation(ProofObligation::assume("auto_set", "auto == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "flag_is_true",
        "if auto == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto-range flag set to 1 evaluates to true");
}
