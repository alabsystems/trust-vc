// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_naa_spec_neutron_flux_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("neutron_flux", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flux_range",
        "neutron_flux >= 1 && neutron_flux <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flux_valid",
        "neutron_flux >= 1 && neutron_flux <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "neutron flux bounded 1-100000 x10^8 n/cm2/s");
}

#[test]
fn test_naa_spec_irradiation_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("irradiation_time", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "irrad_range",
        "irradiation_time >= 1 && irradiation_time <= 86400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "irrad_valid",
        "irradiation_time >= 1 && irradiation_time <= 86400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "irradiation time bounded 1-86400 seconds");
}

#[test]
fn test_naa_spec_decay_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("decay_time", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "decay_range",
        "decay_time >= 1 && decay_time <= 604800",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "decay_valid",
        "decay_time >= 1 && decay_time <= 604800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "decay/cooling time bounded 1-604800 seconds");
}

#[test]
fn test_naa_spec_counting_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("counting_time", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "count_range",
        "counting_time >= 1 && counting_time <= 36000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "count_valid",
        "counting_time >= 1 && counting_time <= 36000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gamma counting time bounded 1-36000 seconds");
}

#[test]
fn test_naa_spec_energy_resolution_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("energy_resolution_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "eres_range",
        "energy_resolution_x10 >= 10 && energy_resolution_x10 <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "eres_valid",
        "energy_resolution_x10 >= 10 && energy_resolution_x10 <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector energy resolution x10 bounded 10-50 (1.0-5.0 keV at 1332 keV)",
    );
}

#[test]
fn test_naa_spec_detector_efficiency_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector_efficiency_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "deff_range",
        "detector_efficiency_x10 >= 10 && detector_efficiency_x10 <= 1500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "deff_valid",
        "detector_efficiency_x10 >= 10 && detector_efficiency_x10 <= 1500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "relative detector efficiency x10 bounded 10-1500 (1.0-150.0%)",
    );
}

#[test]
fn test_naa_spec_neutron_source_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("neutron_source", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "src_range",
        "neutron_source >= 1 && neutron_source <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "src_valid",
        "neutron_source >= 1 && neutron_source <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "neutron source three-way: 1=reactor, 2=californium-252, 3=accelerator",
    );
}

#[test]
fn test_naa_spec_detector_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "det_range",
        "detector_type >= 1 && detector_type <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "det_valid",
        "detector_type >= 1 && detector_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector type three-way: 1=HPGe, 2=NaI-Tl, 3=Si-Li",
    );
}

#[test]
fn test_naa_spec_analysis_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("analysis_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mode_range",
        "analysis_mode >= 1 && analysis_mode <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mode_valid",
        "analysis_mode >= 1 && analysis_mode <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "analysis mode three-way: 1=INAA, 2=RNAA, 3=PGNAA");
}

#[test]
fn test_naa_spec_auto_peak_search_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_peak_search", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "aps_range",
        "auto_peak_search >= 0 && auto_peak_search <= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "aps_valid",
        "auto_peak_search >= 0 && auto_peak_search <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto peak search flag boolean: 0=disabled, 1=enabled",
    );
}
