// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Regression tests: Fourier transform ion cyclotron resonance mass spectrometer (FT-ICR MS) properties

use super::*;

// Test 1: Mass range — bounded between 50 and 100000 Da
#[test]
fn test_ft_icr_mass_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mass_range",
        "mass >= 50 && mass <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mass_range_valid",
        "mass >= 50 && mass <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FT-ICR mass range must be bounded between 50 and 100000 Da",
    );
}

// Test 2: Mass resolution — bounded between 100000 and 10000000 m/Δm
#[test]
fn test_ft_icr_mass_resolution() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "resolution_range",
        "resolution >= 100000 && resolution <= 10000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "resolution_valid",
        "resolution >= 100000 && resolution <= 10000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FT-ICR mass resolution must be bounded between 100000 and 10000000",
    );
}

// Test 3: Magnetic field strength scaled by 10 (e.g. 70 represents 7.0 Tesla)
#[test]
fn test_ft_icr_magnetic_field_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("field_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "field_range",
        "field_x10 > 0 && field_x10 < 300",
    ));
    ctx.push_obligation(ProofObligation::assert("field_positive", "field_x10 > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FT-ICR magnetic field scaled x10 must be positive within range",
    );
}

// Test 4: Mass accuracy scaled by 10000 (e.g. 5000 represents 0.5 ppm)
#[test]
fn test_ft_icr_mass_accuracy_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "accuracy_range",
        "acc_x10000 > 0 && acc_x10000 < 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "accuracy_positive",
        "acc_x10000 > 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FT-ICR mass accuracy scaled x10000 must be positive within range",
    );
}

// Test 5: Transient length scaled by 100 (e.g. 100000 represents 1000.00 ms)
#[test]
fn test_ft_icr_transient_length_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trans_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "transient_range",
        "trans_x100 > 0 && trans_x100 < 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "transient_positive",
        "trans_x100 > 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FT-ICR transient length scaled x100 must be positive within range",
    );
}

// Test 6: Number of data points — bounded between 1000 and 100000000
#[test]
fn test_ft_icr_data_points() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("points", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "points_range",
        "points >= 1000 && points <= 100000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "points_valid",
        "points >= 1000 && points <= 100000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FT-ICR data points must be bounded between 1000 and 100000000",
    );
}

// Test 7: Ion source disjunction — 1=ESI, 2=MALDI, 3=APCI
#[test]
fn test_ft_icr_ion_source_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "source_valid",
        "source == 1 || source == 2 || source == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "source_in_range",
        "source >= 1 && source <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FT-ICR ion source must be one of ESI(1), MALDI(2), APCI(3)",
    );
}

// Test 8: Fragmentation method disjunction — 1=CID, 2=ECD, 3=IRMPD
#[test]
fn test_ft_icr_fragmentation_method_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("frag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "frag_valid",
        "frag == 1 || frag == 2 || frag == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "frag_in_range",
        "frag >= 1 && frag <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FT-ICR fragmentation must be one of CID(1), ECD(2), IRMPD(3)",
    );
}

// Test 9: Cell geometry disjunction — 1=cubic, 2=cylindrical, 3=open-ended
#[test]
fn test_ft_icr_cell_geometry_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cell", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cell_valid",
        "cell == 1 || cell == 2 || cell == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cell_in_range",
        "cell >= 1 && cell <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FT-ICR cell geometry must be one of cubic(1), cylindrical(2), open-ended(3)",
    );
}

// Test 10: Automatic mass calibration flag — boolean encoded as i32 (0 or 1)
#[test]
fn test_ft_icr_auto_calibration_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_cal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cal_flag",
        "auto_cal == 0 || auto_cal == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cal_bounded",
        "auto_cal >= 0 && auto_cal <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FT-ICR automatic calibration flag must be 0 or 1");
}
