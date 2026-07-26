// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Synchrotron XRF spectrometer (SR-XRF) property verification.
// Encodes key parameters of a synchrotron radiation X-ray fluorescence spectrometer
// used for ultra-trace elemental mapping with nanometer-scale resolution.

/// Test 1: Beam energy bounded (1-100 keV).
#[test]
fn test_synchrotron_xrf_beam_energy_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("energy", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "energy_range",
        "energy >= 1 && energy <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "energy_bounded",
        "energy >= 1 && energy <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "beam energy must be between 1 and 100 keV");
}

/// Test 2: Beam size x100 bounded (range 1-100000 representing 0.01-1000.00 um).
#[test]
fn test_synchrotron_xrf_beam_size_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("beam_size_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "beam_size_range",
        "beam_size_x100 >= 1 && beam_size_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "beam_size_bounded",
        "beam_size_x100 >= 1 && beam_size_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "beam size x100 must be between 1 and 100000 (0.01-1000.00 um)",
    );
}

/// Test 3: Photon flux bounded (1-1000000000 photons/s).
#[test]
fn test_synchrotron_xrf_photon_flux_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("photon_flux", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flux_range",
        "photon_flux >= 1 && photon_flux <= 1000000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flux_bounded",
        "photon_flux >= 1 && photon_flux <= 1000000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "photon flux must be between 1 and 1000000000 photons/s",
    );
}

/// Test 4: Energy resolution x10 bounded (range 1-2000 representing 0.1-200.0 eV).
#[test]
fn test_synchrotron_xrf_energy_resolution_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "resolution_range",
        "resolution_x10 >= 1 && resolution_x10 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "resolution_bounded",
        "resolution_x10 >= 1 && resolution_x10 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "energy resolution x10 must be between 1 and 2000 (0.1-200.0 eV)",
    );
}

/// Test 5: Scan speed bounded (1-10000 pixels/s).
#[test]
fn test_synchrotron_xrf_scan_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scan_speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "scan_speed >= 1 && scan_speed <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "scan_speed >= 1 && scan_speed <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scan speed must be between 1 and 10000 pixels/s");
}

/// Test 6: Number of detector elements bounded (1-384).
#[test]
fn test_synchrotron_xrf_detector_elements_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det_elements", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "elements_range",
        "det_elements >= 1 && det_elements <= 384",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "elements_bounded",
        "det_elements >= 1 && det_elements <= 384",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detector elements must be between 1 and 384");
}

/// Test 7: Beamline optics 3-way disjunction (1=KB-mirror, 2=zone-plate, 3=CRL).
#[test]
fn test_synchrotron_xrf_beamline_optics_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("optics", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "optics_domain",
        "optics == 1 || optics == 2 || optics == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_optics",
        "optics == 1 || optics == 2 || optics == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "beamline optics must be KB-mirror(1), zone-plate(2), or CRL(3)",
    );
}

/// Test 8: Scanning method 3-way disjunction (1=step-scan, 2=fly-scan, 3=confocal).
#[test]
fn test_synchrotron_xrf_scanning_method_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scan_method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "method_domain",
        "scan_method == 1 || scan_method == 2 || scan_method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_method",
        "scan_method == 1 || scan_method == 2 || scan_method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "scanning method must be step-scan(1), fly-scan(2), or confocal(3)",
    );
}

/// Test 9: Detector geometry 3-way disjunction (1=single-element, 2=multi-element, 3=Maia-array).
#[test]
fn test_synchrotron_xrf_detector_geometry_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det_geometry", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "geometry_domain",
        "det_geometry == 1 || det_geometry == 2 || det_geometry == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_geometry",
        "det_geometry == 1 || det_geometry == 2 || det_geometry == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector geometry must be single-element(1), multi-element(2), or Maia-array(3)",
    );
}

/// Test 10: Automatic beam alignment boolean flag (== 0 || == 1).
#[test]
fn test_synchrotron_xrf_auto_alignment_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_align", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "align_domain",
        "auto_align == 0 || auto_align == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_align",
        "auto_align == 0 || auto_align == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic beam alignment flag must be 0 (off) or 1 (on)",
    );
}
