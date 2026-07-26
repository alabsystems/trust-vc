// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn device_count() {
    let mut ctx = VerificationContext::new();
    for v in &["devices", "dev_min", "dev_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // DALI bus device count: value 32, valid range 1 to 64 per IEC 62386
    ctx.push_obligation(ProofObligation::assume("dc_val", "devices == 32"));
    ctx.push_obligation(ProofObligation::assume("dc_min", "dev_min == 1"));
    ctx.push_obligation(ProofObligation::assume("dc_max", "dev_max == 64"));
    ctx.push_obligation(ProofObligation::assert(
        "dc_rng",
        "devices >= dev_min && devices <= dev_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DALI bus device count 32 in range [1,64]");
}

#[test]
fn group_count() {
    let mut ctx = VerificationContext::new();
    for v in &["groups", "gr_min", "gr_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // DALI group count: value 8, valid range 1 to 16
    ctx.push_obligation(ProofObligation::assume("gc_val", "groups == 8"));
    ctx.push_obligation(ProofObligation::assume("gc_min", "gr_min == 1"));
    ctx.push_obligation(ProofObligation::assume("gc_max", "gr_max == 16"));
    ctx.push_obligation(ProofObligation::assert(
        "gc_rng",
        "groups >= gr_min && groups <= gr_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DALI group count 8 in range [1,16]");
}

#[test]
fn scene_count() {
    let mut ctx = VerificationContext::new();
    for v in &["scenes", "sc_min", "sc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // DALI scene count: value 12, valid range 1 to 16
    ctx.push_obligation(ProofObligation::assume("sc_val", "scenes == 12"));
    ctx.push_obligation(ProofObligation::assume("sc_min", "sc_min == 1"));
    ctx.push_obligation(ProofObligation::assume("sc_max", "sc_max == 16"));
    ctx.push_obligation(ProofObligation::assert(
        "sc_rng",
        "scenes >= sc_min && scenes <= sc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DALI scene count 12 in range [1,16]");
}

#[test]
fn data_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bps", u32_ty());
    // DALI data rate: single-value 1200 bps per IEC 62386
    ctx.push_obligation(ProofObligation::assume("dr_val", "bps == 1200"));
    ctx.push_obligation(ProofObligation::assert("dr_chk", "bps == 1200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DALI data rate fixed at 1200 bps");
}

#[test]
fn forward_frame() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("frame_type", u32_ty());
    ctx.declare_var_typed("valid_frame", i32_ty());
    // Forward frame types: 1=16-bit standard, 2=24-bit DALI-2, 3=25-bit device type
    ctx.push_obligation(ProofObligation::assume("ff_val", "frame_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ff_def",
        "valid_frame == if frame_type == 1 || frame_type == 2 || frame_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ff_chk", "valid_frame == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "frame type 2 (24-bit DALI-2) is valid forward frame",
    );
}

#[test]
fn dimming_level() {
    let mut ctx = VerificationContext::new();
    for v in &["level", "lv_min", "lv_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // DALI dimming level: logarithmic 0-254, value 180, bounded 0 to 254
    ctx.push_obligation(ProofObligation::assume("dl_val", "level == 180"));
    ctx.push_obligation(ProofObligation::assume("dl_min", "lv_min == 0"));
    ctx.push_obligation(ProofObligation::assume("dl_max", "lv_max == 254"));
    ctx.push_obligation(ProofObligation::assert(
        "dl_rng",
        "level >= lv_min && level <= lv_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DALI dimming level 180 in range [0,254]");
}

#[test]
fn fade_time() {
    let mut ctx = VerificationContext::new();
    for v in &["fade_ms", "ft_min", "ft_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // DALI fade time in tenths of seconds: 0.7s=7, 90.5s=905, bounded 0 to 905
    ctx.push_obligation(ProofObligation::assume("ft_val", "fade_ms == 7"));
    ctx.push_obligation(ProofObligation::assume("ft_min", "ft_min == 0"));
    ctx.push_obligation(ProofObligation::assume("ft_max", "ft_max == 905"));
    ctx.push_obligation(ProofObligation::assert(
        "ft_rng",
        "fade_ms >= ft_min && fade_ms <= ft_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DALI fade time 7 (0.7s) in range [0,905]");
}

#[test]
fn bus_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["mv_dc", "bv_min", "bv_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // DALI bus voltage in millivolts DC: value 16000, bounded 11500 to 22500
    ctx.push_obligation(ProofObligation::assume("bv_val", "mv_dc == 16000"));
    ctx.push_obligation(ProofObligation::assume("bv_min", "bv_min == 11500"));
    ctx.push_obligation(ProofObligation::assume("bv_max", "bv_max == 22500"));
    ctx.push_obligation(ProofObligation::assert(
        "bv_rng",
        "mv_dc >= bv_min && mv_dc <= bv_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DALI bus voltage 16000 mV in range [11500,22500]");
}

#[test]
fn color_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("col_type", u32_ty());
    ctx.declare_var_typed("valid_col", i32_ty());
    // Color types: 1=Tc (tunable white), 2=RGBWAF, 3=xy coordinates, 4=primary N
    ctx.push_obligation(ProofObligation::assume("ct_val", "col_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ct_def",
        "valid_col == if col_type == 1 || col_type == 2 || col_type == 3 || col_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ct_chk", "valid_col == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "color type 3 (xy coordinates) is valid DALI color type",
    );
}

#[test]
fn power_supply() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bus_powered", i32_ty());
    ctx.declare_var_typed("pwr_ok", i32_ty());
    // Power supply flag: 1=bus powered, 0=external
    ctx.push_obligation(ProofObligation::assume("ps_val", "bus_powered == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ps_def",
        "pwr_ok == if bus_powered == 0 || bus_powered == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ps_chk", "pwr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power supply 1 (bus powered) is valid DALI flag");
}
