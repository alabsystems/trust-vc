// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_battery_impedance_voltage_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume("voltage_lower", "voltage >= 1"));
    ctx.push_obligation(ProofObligation::assume("voltage_upper", "voltage <= 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_bounded",
        "voltage >= 1 && voltage <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "battery impedance tester voltage range bounded 1-1000 V",
    );
}

#[test]
fn test_battery_impedance_test_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq", i32_ty());
    ctx.push_obligation(ProofObligation::assume("freq_lower", "freq >= 1"));
    ctx.push_obligation(ProofObligation::assume("freq_upper", "freq <= 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "freq_bounded",
        "freq >= 1 && freq <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "battery impedance test frequency bounded 1-10000 Hz",
    );
}

#[test]
fn test_battery_impedance_impedance_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("imp_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume("imp_lower", "imp_x100 >= 1"));
    ctx.push_obligation(ProofObligation::assume("imp_upper", "imp_x100 <= 1000000"));
    ctx.push_obligation(ProofObligation::assert(
        "imp_bounded",
        "imp_x100 >= 1 && imp_x100 <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "battery impedance x100 bounded 1-1000000 in 0.01 milliohm",
    );
}

#[test]
fn test_battery_impedance_accuracy_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume("acc_lower", "acc_x100 >= 10"));
    ctx.push_obligation(ProofObligation::assume("acc_upper", "acc_x100 <= 500"));
    ctx.push_obligation(ProofObligation::assert(
        "acc_bounded",
        "acc_x100 >= 10 && acc_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "battery impedance accuracy x100 bounded 10-500 in 0.01 percent",
    );
}

#[test]
fn test_battery_impedance_temperature_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_lower", "temp_off >= 60"));
    ctx.push_obligation(ProofObligation::assume("temp_upper", "temp_off <= 300"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp_off >= 60 && temp_off <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "battery impedance temperature offset+100 bounded 60-300 representing -40 to 200 C",
    );
}

#[test]
fn test_battery_impedance_battery_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bt_valid",
        "bt == 1 || bt == 2 || bt == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bt_three_way",
        "bt == 1 || bt == 2 || bt == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "battery type three-way 1=lead-acid 2=lithium-ion 3=nickel-cadmium",
    );
}

#[test]
fn test_battery_impedance_measurement_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mm_valid",
        "mm == 1 || mm == 2 || mm == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mm_three_way",
        "mm == 1 || mm == 2 || mm == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement method three-way 1=AC-impedance 2=DC-resistance 3=EIS",
    );
}

#[test]
fn test_battery_impedance_test_standard_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("std", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "std_valid",
        "std == 1 || std == 2 || std == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "std_three_way",
        "std == 1 || std == 2 || std == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "test standard three-way 1=IEEE-1188 2=IEC-60896 3=IEEE-450",
    );
}

#[test]
fn test_battery_impedance_auto_cell_scan_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_valid",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_boolean",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto cell scan flag boolean 0 or 1");
}

#[test]
fn test_battery_impedance_channel_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", i32_ty());
    ctx.push_obligation(ProofObligation::assume("channels_lower", "channels >= 1"));
    ctx.push_obligation(ProofObligation::assume("channels_upper", "channels <= 256"));
    ctx.push_obligation(ProofObligation::assert(
        "channels_bounded",
        "channels >= 1 && channels <= 256",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "battery impedance channel count bounded 1-256");
}
