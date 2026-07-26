// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_ion_chrom_flow_rate_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_x100 >= 1 && flow_x100 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow_x100 >= 1 && flow_x100 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate x100 mL/min bounded [1, 1000]");
}

#[test]
fn test_ion_chrom_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press >= 1 && press <= 6000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "press_bounded",
        "press >= 1 && press <= 6000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure bounded [1, 6000] psi");
}

#[test]
fn test_ion_chrom_conductivity_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cond", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cond_range",
        "cond >= 1 && cond <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cond_bounded",
        "cond >= 1 && cond <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "conductivity bounded [1, 10000] uS/cm");
}

#[test]
fn test_ion_chrom_injection_volume_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inj_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "inj_range",
        "inj_x10 >= 1 && inj_x10 <= 2500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "inj_bounded",
        "inj_x10 >= 1 && inj_x10 <= 2500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "injection volume x10 uL bounded [1, 2500]");
}

#[test]
fn test_ion_chrom_column_temp_offset500_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp >= 520 && temp <= 580",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp >= 520 && temp <= 580",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "column temp offset+500 bounded [520, 580]");
}

#[test]
fn test_ion_chrom_detection_limit_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lod_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lod_range",
        "lod_x1000 >= 1 && lod_x1000 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lod_bounded",
        "lod_x1000 >= 1 && lod_x1000 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detection limit x1000 ppb bounded [1, 1000]");
}

#[test]
fn test_ion_chrom_suppression_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sup", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sup_range",
        "sup == 1 || sup == 2 || sup == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sup_valid",
        "sup == 1 || sup == 2 || sup == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "suppression type is chemical, electrolytic, or membrane",
    );
}

#[test]
fn test_ion_chrom_detector_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "det_range",
        "det == 1 || det == 2 || det == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "det_valid",
        "det == 1 || det == 2 || det == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector type is conductivity, UV, or amperometric",
    );
}

#[test]
fn test_ion_chrom_eluent_generation_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("elu", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "elu_range",
        "elu == 1 || elu == 2 || elu == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "elu_valid",
        "elu == 1 || elu == 2 || elu == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "eluent generation is manual, electrolytic, or carbonate",
    );
}

#[test]
fn test_ion_chrom_autosampler_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_s", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_range",
        "auto_s == 0 || auto_s == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_valid",
        "auto_s == 0 || auto_s == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "autosampler flag is boolean 0 or 1");
}
