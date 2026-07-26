// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn channel_count_bounded() {
    // Gas detection panel: number of monitored channels [1, 64]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channel_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ch_range",
        "channel_count >= 1 && channel_count <= 64",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ch_above_min",
        "channel_count >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ch_below_max",
        "channel_count <= 64",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gas panel: channel count in [1, 64] bounded");
}

#[test]
fn alarm_levels_bounded() {
    // Alarm severity levels: [1, 4] (1=low, 2=high, 3=urgent, 4=emergency)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("alarm_level", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "al_range",
        "alarm_level >= 1 && alarm_level <= 4",
    ));
    ctx.push_obligation(ProofObligation::assert("al_above_min", "alarm_level >= 1"));
    ctx.push_obligation(ProofObligation::assert("al_below_max", "alarm_level <= 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gas panel: alarm levels in [1, 4] bounded");
}

#[test]
fn sensor_type_four_way_disjunction() {
    // Sensor types: 1=catalytic bead, 2=infrared, 3=electrochemical, 4=PID
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensor_type", u32_ty());
    ctx.declare_var_typed("valid_sensor", i32_ty());
    ctx.push_obligation(ProofObligation::assume("st", "sensor_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_sensor == if sensor_type == 1 || sensor_type == 2 || sensor_type == 3 || sensor_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_sensor == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Gas panel: electrochemical is valid sensor type (4-way)",
    );
}

#[test]
fn detection_range_ppm_bounded() {
    // Detection range in parts per million [1, 100000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range_ppm", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rp_range",
        "range_ppm >= 1 && range_ppm <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert("rp_above_min", "range_ppm >= 1"));
    ctx.push_obligation(ProofObligation::assert(
        "rp_below_max",
        "range_ppm <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Gas panel: detection range in [1, 100000] ppm bounded",
    );
}

#[test]
fn response_time_t90_bounded() {
    // T90 response time in seconds [1, 120]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("t90_sec", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "t90_range",
        "t90_sec >= 1 && t90_sec <= 120",
    ));
    ctx.push_obligation(ProofObligation::assert("t90_above_min", "t90_sec >= 1"));
    ctx.push_obligation(ProofObligation::assert("t90_below_max", "t90_sec <= 120"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Gas panel: T90 response time in [1, 120] s bounded",
    );
}

#[test]
fn relay_outputs_bounded() {
    // Number of relay outputs [1, 32]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("relay_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rc_range",
        "relay_count >= 1 && relay_count <= 32",
    ));
    ctx.push_obligation(ProofObligation::assert("rc_above_min", "relay_count >= 1"));
    ctx.push_obligation(ProofObligation::assert("rc_below_max", "relay_count <= 32"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gas panel: relay outputs in [1, 32] bounded");
}

#[test]
fn communication_protocol_four_way_disjunction() {
    // Communication: 1=4-20mA, 2=Modbus, 3=HART, 4=Ethernet
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm_proto", u32_ty());
    ctx.declare_var_typed("valid_comm", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cp", "comm_proto == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_comm == if comm_proto == 1 || comm_proto == 2 || comm_proto == 3 || comm_proto == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_comm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gas panel: Modbus is valid comm protocol (4-way)");
}

#[test]
fn sil_rating_three_way_disjunction() {
    // SIL rating: 1=SIL1, 2=SIL2, 3=SIL3
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sil_rating", u32_ty());
    ctx.declare_var_typed("valid_sil", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sr", "sil_rating == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_sil == if sil_rating == 1 || sil_rating == 2 || sil_rating == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_sil == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gas panel: SIL2 is valid SIL rating (3-way)");
}

#[test]
fn operating_temp_offset_bounded() {
    // Operating temperature: real range -250C to +300C, offset +500 → [250, 800]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("op_temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ot_range",
        "op_temp >= 250 && op_temp <= 800",
    ));
    ctx.push_obligation(ProofObligation::assert("ot_above_min", "op_temp >= 250"));
    ctx.push_obligation(ProofObligation::assert("ot_below_max", "op_temp <= 800"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Gas panel: operating temp offset [250, 800] (-250C to 300C + 500) bounded",
    );
}

#[test]
fn fault_relay_boolean_flag() {
    // Fault relay: boolean flag (i32: 1=active, 0=inactive)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fault_detected", i32_ty());
    ctx.declare_var_typed("fault_relay_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fd", "fault_detected == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "fr_def",
        "fault_relay_active == if fault_detected == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fault_relay_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Gas panel: fault detected -> fault relay active (boolean flag)",
    );
}
