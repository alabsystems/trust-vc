// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Test 1: Flow rate in x10 L/min (0.1 L/min resolution).
/// 350 represents 35.0 L/min, must be in range [1, 10000] (0.1-1000.0 L/min).
#[test]
fn test_flow_rate_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_rate_x10", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fr", "flow_rate_x10 == 350")); // 35.0 L/min
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if flow_rate_x10 >= 1 && flow_rate_x10 <= 10000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mag drive pump: flow 35.0 L/min (x10=350) in [0.1, 1000.0]",
    );
}

/// Test 2: Head in meters, bounded [5, 100].
#[test]
fn test_head_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("head_m", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("h", "head_m == 45"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if head_m >= 5 && head_m <= 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mag drive pump: head 45m in [5, 100]");
}

/// Test 3: Motor power in kW, bounded [1, 150].
#[test]
fn test_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_kw", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pk", "power_kw == 37"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if power_kw >= 1 && power_kw <= 150 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mag drive pump: motor 37 kW in [1, 150]");
}

/// Test 4: Max temperature offset +500 (deg C) -- bounded [540, 700].
/// 540 represents 40 C, 700 represents 200 C. Value 650 (150 C).
#[test]
fn test_max_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume("tv", "temp_offset == 650")); // 150 C
    ctx.push_obligation(ProofObligation::assert("temp_min", "temp_offset >= 540"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "temp_offset <= 700"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mag drive pump: temp 150 C (offset 650) in [540, 700]",
    );
}

/// Test 5: Max pressure in bar, bounded [10, 40].
#[test]
fn test_max_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_bar", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pb", "pressure_bar == 25"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if pressure_bar >= 10 && pressure_bar <= 40 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mag drive pump: pressure 25 bar in [10, 40]");
}

/// Test 6: Containment shell material -- 3-way disjunction (1=PTFE, 2=hastelloy, 3=ceramic).
#[test]
fn test_containment_shell_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shell_material", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sm", "shell_material == 2")); // hastelloy
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "shell_material == 1 || shell_material == 2 || shell_material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mag drive pump: shell 2 (hastelloy) in {PTFE, hastelloy, ceramic}",
    );
}

/// Test 7: Impeller type -- 3-way disjunction (1=closed, 2=semi-open, 3=open).
#[test]
fn test_impeller_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("impeller_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("it", "impeller_type == 1")); // closed
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "impeller_type == 1 || impeller_type == 2 || impeller_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mag drive pump: impeller 1 (closed) in {closed, semi-open, open}",
    );
}

/// Test 8: Bearing material -- 3-way disjunction (1=SiC, 2=carbon, 3=PTFE).
#[test]
fn test_bearing_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bearing_material", u32_ty());
    ctx.push_obligation(ProofObligation::assume("bm", "bearing_material == 1")); // SiC
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "bearing_material == 1 || bearing_material == 2 || bearing_material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mag drive pump: bearing 1 (SiC) in {SiC, carbon, PTFE}",
    );
}

/// Test 9: Efficiency in x10 % (0.1% resolution).
/// 725 represents 72.5%, must be in range [300, 950] (30.0%-95.0%).
#[test]
fn test_efficiency_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("efficiency_x10", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("eff", "efficiency_x10 == 725")); // 72.5%
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if efficiency_x10 >= 300 && efficiency_x10 <= 950 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mag drive pump: efficiency 72.5% (x10=725) in [300, 950]",
    );
}

/// Test 10: Dry-run protection -- boolean flag (i32, 1=enabled, 0=disabled).
/// When enabled and flow drops to zero, pump shuts down.
#[test]
fn test_dry_run_protection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_rate_x10", u32_ty());
    ctx.declare_var_typed("dry_run_protection", i32_ty());
    ctx.declare_var_typed("shutdown", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fr", "flow_rate_x10 == 0")); // no flow
    ctx.push_obligation(ProofObligation::assume("drp", "dry_run_protection == 1")); // enabled
    ctx.push_obligation(ProofObligation::assume(
        "sd_def",
        "shutdown == if dry_run_protection == 1 { if flow_rate_x10 == 0 { 1 } else { 0 } } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "shutdown == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mag drive pump: dry-run protection enabled, zero flow -> shutdown",
    );
}
