// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Digital inclinometer (tilt/angle sensor) property verification.

#[test]
fn test_measurement_range_tenths_deg() {
    let mut ctx = VerificationContext::new();
    for v in &["range_td", "range_td_min", "range_td_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Measurement range in tenths of degree (x10): value 900 = 90.0 deg
    ctx.push_obligation(ProofObligation::assume("mr_val", "range_td == 900"));
    ctx.push_obligation(ProofObligation::assume("mr_lo", "range_td_min == 10"));
    ctx.push_obligation(ProofObligation::assume("mr_hi", "range_td_max == 3600"));
    ctx.push_obligation(ProofObligation::assert(
        "mr_in_range",
        "range_td >= range_td_min && range_td <= range_td_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inclinometer: range 900 (90.0 deg) in [10,3600]");
}

#[test]
fn test_resolution_thousandths_deg() {
    let mut ctx = VerificationContext::new();
    for v in &["res_md", "res_md_min", "res_md_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Resolution in thousandths of degree (x1000): value 1 = 0.001 deg
    ctx.push_obligation(ProofObligation::assume("rs_val", "res_md == 1"));
    ctx.push_obligation(ProofObligation::assume("rs_lo", "res_md_min == 1"));
    ctx.push_obligation(ProofObligation::assume("rs_hi", "res_md_max == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "rs_in_range",
        "res_md >= res_md_min && res_md <= res_md_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inclinometer: resolution 1 (0.001 deg) in [1,100]");
}

#[test]
fn test_accuracy_hundredths_deg() {
    let mut ctx = VerificationContext::new();
    for v in &["acc_hd", "acc_hd_min", "acc_hd_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Accuracy in hundredths of degree (x100): value 10 = 0.10 deg
    ctx.push_obligation(ProofObligation::assume("ac_val", "acc_hd == 10"));
    ctx.push_obligation(ProofObligation::assume("ac_lo", "acc_hd_min == 1"));
    ctx.push_obligation(ProofObligation::assume("ac_hi", "acc_hd_max == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "ac_in_range",
        "acc_hd >= acc_hd_min && acc_hd <= acc_hd_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inclinometer: accuracy 10 (0.10 deg) in [1,100]");
}

#[test]
fn test_axis_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("axes", u32_ty());
    ctx.declare_var_typed("valid_axes", i32_ty());
    // Axis count: 1=single, 2=dual, 3=triaxial
    ctx.push_obligation(ProofObligation::assume("ax_val", "axes == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ax_def",
        "valid_axes == if axes == 1 || axes == 2 || axes == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ax_check", "valid_axes == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "inclinometer: axis count 2 (dual) is valid (1, 2, or 3)",
    );
}

#[test]
fn test_sensor_technology() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tech", u32_ty());
    ctx.declare_var_typed("valid_tech", i32_ty());
    // Sensor technology: 1=MEMS, 2=electrolytic, 3=servo
    ctx.push_obligation(ProofObligation::assume("st_val", "tech == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "st_def",
        "valid_tech == if tech == 1 || tech == 2 || tech == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("st_check", "valid_tech == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "inclinometer: technology 1 (MEMS) is valid (1, 2, or 3)",
    );
}

#[test]
fn test_output_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output", u32_ty());
    ctx.declare_var_typed("valid_output", i32_ty());
    // Output type: 1=analog, 2=RS485, 3=CANbus, 4=SSI
    ctx.push_obligation(ProofObligation::assume("ot_val", "output == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ot_def",
        "valid_output == if output == 1 || output == 2 || output == 3 || output == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ot_check", "valid_output == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "inclinometer: output 3 (CANbus) is valid (1, 2, 3, or 4)",
    );
}

#[test]
fn test_bandwidth_hz() {
    let mut ctx = VerificationContext::new();
    for v in &["bw_hz", "bw_hz_min", "bw_hz_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Measurement bandwidth in Hz
    ctx.push_obligation(ProofObligation::assume("bw_val", "bw_hz == 100"));
    ctx.push_obligation(ProofObligation::assume("bw_lo", "bw_hz_min == 1"));
    ctx.push_obligation(ProofObligation::assume("bw_hi", "bw_hz_max == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "bw_in_range",
        "bw_hz >= bw_hz_min && bw_hz <= bw_hz_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inclinometer: bandwidth 100 Hz in [1,1000]");
}

#[test]
fn test_operating_temp_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Operating temperature: offset +500, actual 25 C -> 525, range -40 C (460) to 85 C (585)
    ctx.push_obligation(ProofObligation::assume("to_val", "temp_offset == 525"));
    ctx.push_obligation(ProofObligation::assume("to_lo", "min_temp_offset == 460"));
    ctx.push_obligation(ProofObligation::assume("to_hi", "max_temp_offset == 585"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("to_check", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "inclinometer: 25 C operating temp in [-40, 85] (offset +500) -> OK",
    );
}

#[test]
fn test_ip_rating() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ip_val", u32_ty());
    ctx.declare_var_typed("valid_ip", i32_ty());
    // IP rating: 3-way non-sequential (65, 67, 68)
    ctx.push_obligation(ProofObligation::assume("ip_v", "ip_val == 67"));
    ctx.push_obligation(ProofObligation::assume(
        "ip_def",
        "valid_ip == if ip_val == 65 || ip_val == 67 || ip_val == 68 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ip_chk", "valid_ip == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "inclinometer: IP rating 67 is valid (65, 67, or 68)",
    );
}

#[test]
fn test_zero_set_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("zero_set", i32_ty());
    // Boolean flag: 1=zero set (tare) enabled, 0=disabled
    ctx.push_obligation(ProofObligation::assume("zs_val", "zero_set == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "zs_check",
        "zero_set == 0 || zero_set == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inclinometer: zero set flag 1 is valid boolean");
}
