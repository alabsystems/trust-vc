// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// SAG mill diameter in millimeters — bounded within [3000, 15000].
#[test]
fn test_mill_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter", u32_ty());
    ctx.push_obligation(ProofObligation::assume("diameter_val", "diameter == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "diameter_lower",
        "diameter >= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "diameter_upper",
        "diameter <= 15000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mill diameter 10000 mm within [3000, 15000]");
}

/// Motor drive power in kW — bounded within [1000, 30000].
#[test]
fn test_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power", u32_ty());
    ctx.push_obligation(ProofObligation::assume("power_val", "power == 15000"));
    ctx.push_obligation(ProofObligation::assert("power_lower", "power >= 1000"));
    ctx.push_obligation(ProofObligation::assert("power_upper", "power <= 30000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power 15000 kW within [1000, 30000]");
}

/// Critical speed as percentage x10 — 750 represents 75.0%, bounded [600, 850].
#[test]
fn test_critical_speed_percentage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_pct", u32_ty());
    ctx.push_obligation(ProofObligation::assume("speed_val", "speed_pct == 750"));
    ctx.push_obligation(ProofObligation::assert("speed_lower", "speed_pct >= 600"));
    ctx.push_obligation(ProofObligation::assert("speed_upper", "speed_pct <= 850"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "critical speed 75.0% (750) within [600, 850]");
}

/// Mill type as 3-way disjunction: 1=SAG, 2=AG, 3=ball.
#[test]
fn test_mill_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mill_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mill_type_valid",
        "mill_type == 1 || mill_type == 2 || mill_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("mill_type_lower", "mill_type >= 1"));
    ctx.push_obligation(ProofObligation::assert("mill_type_upper", "mill_type <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mill type disjunction {1=SAG, 2=AG, 3=ball} implies [1, 3]",
    );
}

/// Drive type as 3-way disjunction: 1=gearless, 2=single-pinion, 3=dual-pinion.
#[test]
fn test_drive_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "drive_type_valid",
        "drive_type == 1 || drive_type == 2 || drive_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "drive_type_lower",
        "drive_type >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "drive_type_upper",
        "drive_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drive type disjunction {1=gearless, 2=single-pinion, 3=dual-pinion} implies [1, 3]",
    );
}

/// Liner type as 4-way disjunction: 1=steel, 2=rubber, 3=composite, 4=ceramic.
#[test]
fn test_liner_type_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("liner_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "liner_type_valid",
        "liner_type == 1 || liner_type == 2 || liner_type == 3 || liner_type == 4",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "liner_type_lower",
        "liner_type >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "liner_type_upper",
        "liner_type <= 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "liner type disjunction {1=steel, 2=rubber, 3=composite, 4=ceramic} implies [1, 4]",
    );
}

/// Charge volume as percentage x10 — 300 represents 30.0%, bounded [200, 400].
#[test]
fn test_charge_volume_percentage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("charge_vol", u32_ty());
    ctx.push_obligation(ProofObligation::assume("charge_val", "charge_vol == 300"));
    ctx.push_obligation(ProofObligation::assert("charge_lower", "charge_vol >= 200"));
    ctx.push_obligation(ProofObligation::assert("charge_upper", "charge_vol <= 400"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "charge volume 30.0% (300) within [200, 400]");
}

/// Feed rate in tonnes per hour — bounded within [100, 10000].
#[test]
fn test_feed_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed_rate", u32_ty());
    ctx.push_obligation(ProofObligation::assume("feed_val", "feed_rate == 2000"));
    ctx.push_obligation(ProofObligation::assert("feed_lower", "feed_rate >= 100"));
    ctx.push_obligation(ProofObligation::assert("feed_upper", "feed_rate <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed rate 2000 t/h within [100, 10000]");
}

/// Bearing type as 3-way disjunction: 1=hydrostatic, 2=hydrodynamic, 3=roller.
#[test]
fn test_bearing_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bearing_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bearing_type_valid",
        "bearing_type == 1 || bearing_type == 2 || bearing_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bearing_type_lower",
        "bearing_type >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bearing_type_upper",
        "bearing_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bearing type disjunction {1=hydrostatic, 2=hydrodynamic, 3=roller} implies [1, 3]",
    );
}

/// Lubrication monitoring as boolean flag — i32 flag where 1=enabled, 0=disabled.
#[test]
fn test_lubrication_monitoring_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lube_monitor", i32_ty());
    ctx.declare_var_typed("alarm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lube_flag",
        "lube_monitor == 0 || lube_monitor == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("lube_enabled", "lube_monitor == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "alarm_def",
        "alarm == if lube_monitor == 1 { 0 } else { 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "no_alarm_when_monitored",
        "alarm == 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "lubrication monitoring enabled suppresses alarm");
}
