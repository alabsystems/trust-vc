// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_centrifugal_compressor_impeller_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["imp_dia", "imp_min", "imp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Impeller diameter in mm: value 600, valid range 200 to 1500
    ctx.push_obligation(ProofObligation::assume("id_val", "imp_dia == 600"));
    ctx.push_obligation(ProofObligation::assume("id_min", "imp_min == 200"));
    ctx.push_obligation(ProofObligation::assume("id_max", "imp_max == 1500"));
    ctx.push_obligation(ProofObligation::assert(
        "id_in_range",
        "imp_dia >= imp_min && imp_dia <= imp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impeller diameter 600 mm within [200, 1500]");
}

#[test]
fn test_centrifugal_compressor_shaft_speed_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["shaft_rpm", "rpm_min", "rpm_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Shaft speed in RPM: value 15000, valid range 3000 to 60000
    ctx.push_obligation(ProofObligation::assume("ss_val", "shaft_rpm == 15000"));
    ctx.push_obligation(ProofObligation::assume("ss_min", "rpm_min == 3000"));
    ctx.push_obligation(ProofObligation::assume("ss_max", "rpm_max == 60000"));
    ctx.push_obligation(ProofObligation::assert(
        "ss_in_range",
        "shaft_rpm >= rpm_min && shaft_rpm <= rpm_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shaft speed 15000 RPM within [3000, 60000]");
}

#[test]
fn test_centrifugal_compressor_discharge_pressure_scaled() {
    let mut ctx = VerificationContext::new();
    for v in &["dp_val", "dp_min", "dp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Discharge pressure x10 kPa (350.0 kPa = 3500): value 3500, valid range 500 to 50000
    ctx.push_obligation(ProofObligation::assume("dp_val", "dp_val == 3500"));
    ctx.push_obligation(ProofObligation::assume("dp_min", "dp_min == 500"));
    ctx.push_obligation(ProofObligation::assume("dp_max", "dp_max == 50000"));
    ctx.push_obligation(ProofObligation::assert(
        "dp_in_range",
        "dp_val >= dp_min && dp_val <= dp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge pressure 3500 (350.0 kPa) within [500, 50000]",
    );
}

#[test]
fn test_centrifugal_compressor_flow_rate_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["flow_rate", "flow_min", "flow_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Flow rate in m3/h: value 8000, valid range 100 to 50000
    ctx.push_obligation(ProofObligation::assume("fr_val", "flow_rate == 8000"));
    ctx.push_obligation(ProofObligation::assume("fr_min", "flow_min == 100"));
    ctx.push_obligation(ProofObligation::assume("fr_max", "flow_max == 50000"));
    ctx.push_obligation(ProofObligation::assert(
        "fr_in_range",
        "flow_rate >= flow_min && flow_rate <= flow_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate 8000 m3/h within [100, 50000]");
}

#[test]
fn test_centrifugal_compressor_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["motor_kw", "kw_min", "kw_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Motor power in kW: value 2000, valid range 50 to 10000
    ctx.push_obligation(ProofObligation::assume("mp_val", "motor_kw == 2000"));
    ctx.push_obligation(ProofObligation::assume("mp_min", "kw_min == 50"));
    ctx.push_obligation(ProofObligation::assume("mp_max", "kw_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "mp_in_range",
        "motor_kw >= kw_min && motor_kw <= kw_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power 2000 kW within [50, 10000]");
}

#[test]
fn test_centrifugal_compressor_bearing_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bearing_type", u32_ty());
    // Bearing types: 1=tilting pad, 2=magnetic, 3=sleeve
    ctx.push_obligation(ProofObligation::assume("bt_val", "bearing_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_bearing",
        "bearing_type == 1 || bearing_type == 2 || bearing_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bearing type 2 (magnetic) is valid (3-way disjunction)",
    );
}

#[test]
fn test_centrifugal_compressor_seal_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal_type", u32_ty());
    // Seal types: 1=dry gas, 2=labyrinth, 3=carbon ring
    ctx.push_obligation(ProofObligation::assume("st_val", "seal_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_seal",
        "seal_type == 1 || seal_type == 2 || seal_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "seal type 1 (dry gas) is valid (3-way disjunction)",
    );
}

#[test]
fn test_centrifugal_compressor_surge_margin_scaled() {
    let mut ctx = VerificationContext::new();
    for v in &["surge_margin", "sm_min", "sm_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Surge margin x10 % (10.0% = 100): value 100, valid range 50 to 300
    ctx.push_obligation(ProofObligation::assume("sm_val", "surge_margin == 100"));
    ctx.push_obligation(ProofObligation::assume("sm_min", "sm_min == 50"));
    ctx.push_obligation(ProofObligation::assume("sm_max", "sm_max == 300"));
    ctx.push_obligation(ProofObligation::assert(
        "sm_in_range",
        "surge_margin >= sm_min && surge_margin <= sm_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "surge margin 100 (10.0%) within [50, 300]");
}

#[test]
fn test_centrifugal_compressor_stage_count_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["stage_count", "sc_min", "sc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Stage count: value 4, valid range 1 to 8
    ctx.push_obligation(ProofObligation::assume("sc_val", "stage_count == 4"));
    ctx.push_obligation(ProofObligation::assume("sc_min", "sc_min == 1"));
    ctx.push_obligation(ProofObligation::assume("sc_max", "sc_max == 8"));
    ctx.push_obligation(ProofObligation::assert(
        "sc_in_range",
        "stage_count >= sc_min && stage_count <= sc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stage count 4 within [1, 8]");
}

#[test]
fn test_centrifugal_compressor_anti_surge_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("anti_surge", i32_ty());
    ctx.declare_var_typed("valid_as", i32_ty());
    // Anti-surge control: 1=enabled, 0=disabled (boolean flag)
    ctx.push_obligation(ProofObligation::assume("as_val", "anti_surge == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "as_def",
        "valid_as == if anti_surge == 1 || anti_surge == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("as_chk", "valid_as == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "anti-surge control flag is boolean (enabled)");
}
