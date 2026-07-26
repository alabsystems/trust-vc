// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn device_count() {
    let mut ctx = VerificationContext::new();
    for v in &["dev_cnt", "dev_min", "dev_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // KNX devices per line: value 32, valid range 1 to 64 per ISO 14543-3
    ctx.push_obligation(ProofObligation::assume("dc_val", "dev_cnt == 32"));
    ctx.push_obligation(ProofObligation::assume("dc_min", "dev_min == 1"));
    ctx.push_obligation(ProofObligation::assume("dc_max", "dev_max == 64"));
    ctx.push_obligation(ProofObligation::assert(
        "dc_in_range",
        "dev_cnt >= dev_min && dev_cnt <= dev_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "KNX device count 32 in range [1,64] per line");
}

#[test]
fn data_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bps", u32_ty());
    // KNX TP1 twisted pair data rate: fixed 9600 bps
    ctx.push_obligation(ProofObligation::assume("dr_val", "bps == 9600"));
    ctx.push_obligation(ProofObligation::assert("dr_chk", "bps == 9600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "KNX TP1 data rate is 9600 bps");
}

#[test]
fn bus_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["v_mv", "v_min", "v_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // KNX bus voltage in millivolts DC: value 24000, valid range 21000 to 30000 (21V to 30V)
    ctx.push_obligation(ProofObligation::assume("bv_val", "v_mv == 24000"));
    ctx.push_obligation(ProofObligation::assume("bv_min", "v_min == 21000"));
    ctx.push_obligation(ProofObligation::assume("bv_max", "v_max == 30000"));
    ctx.push_obligation(ProofObligation::assert(
        "bv_in_range",
        "v_mv >= v_min && v_mv <= v_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "KNX bus voltage 24000 mV in range [21000,30000]");
}

#[test]
fn telegram_priority() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tg_pri", u32_ty());
    ctx.declare_var_typed("valid_pri", i32_ty());
    // KNX telegram priorities: 1=system, 2=alarm, 3=high, 4=low
    ctx.push_obligation(ProofObligation::assume("tp_val", "tg_pri == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "tp_def",
        "valid_pri == if tg_pri == 1 || tg_pri == 2 || tg_pri == 3 || tg_pri == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("tp_chk", "valid_pri == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "telegram priority 2 (alarm) is valid KNX priority level",
    );
}

#[test]
fn medium_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("med_type", u32_ty());
    ctx.declare_var_typed("valid_med", i32_ty());
    // KNX media: 1=TP (twisted pair), 2=PL (powerline), 3=RF, 4=IP
    ctx.push_obligation(ProofObligation::assume("mt_val", "med_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "mt_def",
        "valid_med == if med_type == 1 || med_type == 2 || med_type == 3 || med_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("mt_chk", "valid_med == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "medium type 1 (TP/twisted pair) is valid KNX medium",
    );
}

#[test]
fn group_address() {
    let mut ctx = VerificationContext::new();
    for v in &["grp_addr", "ga_min", "ga_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // KNX group address (3-level: main/middle/sub): value 2050, valid range 1 to 65535
    ctx.push_obligation(ProofObligation::assume("ga_val", "grp_addr == 2050"));
    ctx.push_obligation(ProofObligation::assume("ga_min", "ga_min == 1"));
    ctx.push_obligation(ProofObligation::assume("ga_max", "ga_max == 65535"));
    ctx.push_obligation(ProofObligation::assert(
        "ga_in_range",
        "grp_addr >= ga_min && grp_addr <= ga_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "KNX group address 2050 in range [1,65535]");
}

#[test]
fn physical_address() {
    let mut ctx = VerificationContext::new();
    for v in &["phy_addr", "pa_min", "pa_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // KNX physical address (area.line.device): value 4610, valid range 1 to 65535
    ctx.push_obligation(ProofObligation::assume("pa_val", "phy_addr == 4610"));
    ctx.push_obligation(ProofObligation::assume("pa_min", "pa_min == 1"));
    ctx.push_obligation(ProofObligation::assume("pa_max", "pa_max == 65535"));
    ctx.push_obligation(ProofObligation::assert(
        "pa_in_range",
        "phy_addr >= pa_min && phy_addr <= pa_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "KNX physical address 4610 in range [1,65535]");
}

#[test]
fn line_count() {
    let mut ctx = VerificationContext::new();
    for v in &["ln_cnt", "ln_min", "ln_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // KNX lines per area: value 8, valid range 1 to 15
    ctx.push_obligation(ProofObligation::assume("lc_val", "ln_cnt == 8"));
    ctx.push_obligation(ProofObligation::assume("lc_min", "ln_min == 1"));
    ctx.push_obligation(ProofObligation::assume("lc_max", "ln_max == 15"));
    ctx.push_obligation(ProofObligation::assert(
        "lc_in_range",
        "ln_cnt >= ln_min && ln_cnt <= ln_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "KNX line count 8 in range [1,15] per area");
}

#[test]
fn area_count() {
    let mut ctx = VerificationContext::new();
    for v in &["ar_cnt", "ar_min", "ar_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // KNX areas: value 10, valid range 1 to 15
    ctx.push_obligation(ProofObligation::assume("ac_val", "ar_cnt == 10"));
    ctx.push_obligation(ProofObligation::assume("ac_min", "ar_min == 1"));
    ctx.push_obligation(ProofObligation::assume("ac_max", "ar_max == 15"));
    ctx.push_obligation(ProofObligation::assert(
        "ac_in_range",
        "ar_cnt >= ar_min && ar_cnt <= ar_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "KNX area count 10 in range [1,15]");
}

#[test]
fn programming_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("prog_mode", i32_ty());
    ctx.declare_var_typed("valid_pm", i32_ty());
    // KNX programming mode: 0=normal operation, 1=in programming
    ctx.push_obligation(ProofObligation::assume("pm_val", "prog_mode == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "pm_def",
        "valid_pm == if prog_mode == 0 || prog_mode == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("pm_chk", "valid_pm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "programming mode 0 (normal) is valid KNX device state",
    );
}
