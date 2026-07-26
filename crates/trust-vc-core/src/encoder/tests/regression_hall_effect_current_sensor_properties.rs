// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn primary_current() {
    let mut ctx = VerificationContext::new();
    for v in &["current_ma", "cur_min", "cur_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Primary current in mA: value 50000 (50A), valid range 100 (100mA) to 2000000 (2000A)
    ctx.push_obligation(ProofObligation::assume("pc_val", "current_ma == 50000"));
    ctx.push_obligation(ProofObligation::assume("pc_min", "cur_min == 100"));
    ctx.push_obligation(ProofObligation::assume("pc_max", "cur_max == 2000000"));
    ctx.push_obligation(ProofObligation::assert(
        "pc_in_range",
        "current_ma >= cur_min && current_ma <= cur_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "primary current 50000 mA (50A) in range [100,2000000] (100mA to 2000A)",
    );
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_pct", "acc_min", "acc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Accuracy x100 % of reading: value 100 (1.00%), valid range 10 (0.10%) to 500 (5.00%)
    ctx.push_obligation(ProofObligation::assume("ac_val", "accuracy_pct == 100"));
    ctx.push_obligation(ProofObligation::assume("ac_min", "acc_min == 10"));
    ctx.push_obligation(ProofObligation::assume("ac_max", "acc_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "ac_in_range",
        "accuracy_pct >= acc_min && accuracy_pct <= acc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "accuracy 100 (1.00%) in range [10,500] (0.10% to 5.00%)",
    );
}

#[test]
fn sensor_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sens_type", u32_ty());
    ctx.declare_var_typed("valid_type", i32_ty());
    // 1=open-loop, 2=closed-loop, 3=fluxgate, 4=Rogowski
    ctx.push_obligation(ProofObligation::assume("st_val", "sens_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "st_valid_def",
        "valid_type == if sens_type == 1 || sens_type == 2 || sens_type == 3 || sens_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("st_check", "valid_type == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sensor type 2 (closed-loop) is valid");
}

#[test]
fn bandwidth() {
    let mut ctx = VerificationContext::new();
    for v in &["bandwidth_khz", "bw_min", "bw_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Bandwidth in kHz: value 200, valid range 1 to 1000
    ctx.push_obligation(ProofObligation::assume("bw_val", "bandwidth_khz == 200"));
    ctx.push_obligation(ProofObligation::assume("bw_min", "bw_min == 1"));
    ctx.push_obligation(ProofObligation::assume("bw_max", "bw_max == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "bw_in_range",
        "bandwidth_khz >= bw_min && bandwidth_khz <= bw_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bandwidth 200 kHz in range [1,1000]");
}

#[test]
fn output_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("out_type", u32_ty());
    ctx.declare_var_typed("valid_out", i32_ty());
    // 1=analog voltage, 2=analog current, 3=digital SPI, 4=PWM
    ctx.push_obligation(ProofObligation::assume("ot_val", "out_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ot_valid_def",
        "valid_out == if out_type == 1 || out_type == 2 || out_type == 3 || out_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ot_check", "valid_out == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output type 1 (analog voltage) is valid");
}

#[test]
fn supply_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["supply_mv", "sup_min", "sup_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Supply voltage in mV: value 5000 (5.0V), valid range 3000 (3.0V) to 15000 (15.0V)
    ctx.push_obligation(ProofObligation::assume("sv_val", "supply_mv == 5000"));
    ctx.push_obligation(ProofObligation::assume("sv_min", "sup_min == 3000"));
    ctx.push_obligation(ProofObligation::assume("sv_max", "sup_max == 15000"));
    ctx.push_obligation(ProofObligation::assert(
        "sv_in_range",
        "supply_mv >= sup_min && supply_mv <= sup_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "supply voltage 5000 mV (5.0V) in range [3000,15000] (3.0V to 15.0V)",
    );
}

#[test]
fn isolation_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["isolation_v", "iso_min", "iso_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Isolation voltage in Vrms: value 2500, valid range 1000 to 5000
    ctx.push_obligation(ProofObligation::assume("iv_val", "isolation_v == 2500"));
    ctx.push_obligation(ProofObligation::assume("iv_min", "iso_min == 1000"));
    ctx.push_obligation(ProofObligation::assume("iv_max", "iso_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "iv_in_range",
        "isolation_v >= iso_min && isolation_v <= iso_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "isolation voltage 2500 Vrms in range [1000,5000]");
}

#[test]
fn response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["resp_us", "resp_min", "resp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Response time in microseconds: value 3, valid range 1 to 100
    ctx.push_obligation(ProofObligation::assume("rt_val", "resp_us == 3"));
    ctx.push_obligation(ProofObligation::assume("rt_min", "resp_min == 1"));
    ctx.push_obligation(ProofObligation::assume("rt_max", "resp_max == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "rt_in_range",
        "resp_us >= resp_min && resp_us <= resp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "response time 3 us in range [1,100]");
}

#[test]
fn linearity() {
    let mut ctx = VerificationContext::new();
    for v in &["linearity_pct", "lin_min", "lin_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Linearity x100 %: value 50 (0.50%), valid range 1 (0.01%) to 200 (2.00%)
    ctx.push_obligation(ProofObligation::assume("ln_val", "linearity_pct == 50"));
    ctx.push_obligation(ProofObligation::assume("ln_min", "lin_min == 1"));
    ctx.push_obligation(ProofObligation::assume("ln_max", "lin_max == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "ln_in_range",
        "linearity_pct >= lin_min && linearity_pct <= lin_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "linearity 50 (0.50%) in range [1,200] (0.01% to 2.00%)",
    );
}

#[test]
fn operating_temp() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_off", "temp_min", "temp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Temperature offset +500: 25C → 525, valid range 460 (-40C) to 625 (125C)
    ctx.push_obligation(ProofObligation::assume("te_val", "temp_off == 525"));
    ctx.push_obligation(ProofObligation::assume("te_min", "temp_min == 460"));
    ctx.push_obligation(ProofObligation::assume("te_max", "temp_max == 625"));
    ctx.push_obligation(ProofObligation::assert(
        "te_in_range",
        "temp_off >= temp_min && temp_off <= temp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp 525 (25C) in range [460,625] (-40C to 125C)",
    );
}
