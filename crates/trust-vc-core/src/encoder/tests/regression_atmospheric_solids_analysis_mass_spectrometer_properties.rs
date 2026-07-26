// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_asap_discharge_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("discharge_v", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dv_a",
        "discharge_v >= 500 && discharge_v <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dv_c",
        "discharge_v >= 500 && discharge_v <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge voltage in [500, 5000] V");
}

#[test]
fn test_asap_vaporization_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vap_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vt_a",
        "vap_temp >= 50 && vap_temp <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vt_c",
        "vap_temp >= 50 && vap_temp <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vaporization temperature in [50, 600] C");
}

#[test]
fn test_asap_nitrogen_flow_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n2_flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "nf_a",
        "n2_flow_x10 >= 5 && n2_flow_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "nf_c",
        "n2_flow_x10 >= 5 && n2_flow_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nitrogen flow x10 in [5, 100] representing 0.5-10.0 L/min",
    );
}

#[test]
fn test_asap_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mz_max", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mr_a",
        "mz_max >= 10 && mz_max <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mr_c",
        "mz_max >= 10 && mz_max <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass range in [10, 2000] m/z");
}

#[test]
fn test_asap_corona_current_ua_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("corona_ua", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cc_a",
        "corona_ua >= 1 && corona_ua <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cc_c",
        "corona_ua >= 1 && corona_ua <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "corona current in [1, 100] uA");
}

#[test]
fn test_asap_sample_mass_mg_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sample_mg", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sm_a",
        "sample_mg >= 1 && sample_mg <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sm_c",
        "sample_mg >= 1 && sample_mg <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sample mass in [1, 1000] mg");
}

#[test]
fn test_asap_sample_form_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sample_form", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sf_a",
        "sample_form == 1 || sample_form == 2 || sample_form == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sf_c",
        "sample_form == 1 || sample_form == 2 || sample_form == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sample form: solid powder, film/coating, or biological tissue",
    );
}

#[test]
fn test_asap_ionization_mode_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ion_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "im_a",
        "ion_mode == 1 || ion_mode == 2 || ion_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "im_c",
        "ion_mode == 1 || ion_mode == 2 || ion_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ionization: corona discharge, glow discharge, or plasma",
    );
}

#[test]
fn test_asap_probe_material_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("probe_mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pm_a",
        "probe_mat == 1 || probe_mat == 2 || probe_mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pm_c",
        "probe_mat == 1 || probe_mat == 2 || probe_mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "probe: glass capillary, metal rod, or mesh screen");
}

#[test]
fn test_asap_direct_insertion_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("direct_ins", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "di_a",
        "direct_ins == 0 || direct_ins == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "di_c",
        "direct_ins == 0 || direct_ins == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "direct insertion flag is boolean");
}
