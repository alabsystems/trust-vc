// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn detector_resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["pixel_count", "min_pixels", "max_pixels"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("res_ok", i32_ty());
    // 320×240 = 76800 pixels (precomputed), range 4800 (80×60) to 1310720 (1280×1024)
    ctx.push_obligation(ProofObligation::assume("pc", "pixel_count == 76800"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_pixels == 4800"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_pixels == 1310720"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "res_ok == if pixel_count >= min_pixels && pixel_count <= max_pixels { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "res_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Thermal Camera: 76800 pixels (320x240) in [4800, 1310720] -> OK",
    );
}

#[test]
fn temperature_range_high() {
    let mut ctx = VerificationContext::new();
    for v in &["max_temp_offset", "min_offset", "max_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Max measurable temp offset +500: 2000°C → 2500, range 100°C (600) to 3000°C (3500)
    ctx.push_obligation(ProofObligation::assume("mt", "max_temp_offset == 2500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_offset == 600"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_offset == 3500"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if max_temp_offset >= min_offset && max_temp_offset <= max_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Thermal Camera: 2000C max temp in [100C, 3000C] -> OK",
    );
}

#[test]
fn thermal_sensitivity() {
    let mut ctx = VerificationContext::new();
    for v in &["netd_mk", "max_netd_mk"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("netd_ok", i32_ty());
    // NETD (Noise Equivalent Temperature Difference) in millikelvin
    ctx.push_obligation(ProofObligation::assume("nm", "netd_mk == 50"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_netd_mk == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "no_def",
        "netd_ok == if netd_mk <= max_netd_mk { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "netd_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thermal Camera: 50mK NETD <= 200mK max -> OK");
}

#[test]
fn detector_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det_type", u32_ty());
    ctx.declare_var_typed("valid_det", i32_ty());
    // Detector types: 1=microbolometer, 2=InSb, 3=MCT (HgCdTe), 4=QWIP
    ctx.push_obligation(ProofObligation::assume("dt", "det_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_det == if det_type == 1 || det_type == 2 || det_type == 3 || det_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_det == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Thermal Camera: microbolometer is valid detector type",
    );
}

#[test]
fn spectral_band() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("band", u32_ty());
    ctx.declare_var_typed("valid_band", i32_ty());
    // Spectral bands: 1=SWIR (1-3um), 2=MWIR (3-5um), 3=LWIR (8-14um)
    ctx.push_obligation(ProofObligation::assume("b", "band == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vb_def",
        "valid_band == if band == 1 || band == 2 || band == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_band == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Thermal Camera: LWIR (8-14um) is valid spectral band",
    );
}

#[test]
fn frame_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["fps", "min_fps", "max_fps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fps_ok", i32_ty());
    // Frame rate in frames per second
    ctx.push_obligation(ProofObligation::assume("f", "fps == 30"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_fps == 9"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_fps == 240"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "fps_ok == if fps >= min_fps && fps <= max_fps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fps_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thermal Camera: 30fps in [9, 240] -> OK");
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x10", "max_accuracy_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Temperature accuracy in degrees C (x10 for 0.1C resolution): 2.0C = 20, max 5.0C = 50
    ctx.push_obligation(ProofObligation::assume("ax", "accuracy_x10 == 20"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_accuracy_x10 == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_x10 <= max_accuracy_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thermal Camera: 2.0C accuracy <= 5.0C max -> OK");
}

#[test]
fn field_of_view() {
    let mut ctx = VerificationContext::new();
    for v in &["fov_x10", "min_fov_x10", "max_fov_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fov_ok", i32_ty());
    // Horizontal FOV in degrees (x10 for 0.1 degree): 25.0 deg = 250, range 4.0 (40) to 90.0 (900)
    ctx.push_obligation(ProofObligation::assume("fx", "fov_x10 == 250"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_fov_x10 == 40"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_fov_x10 == 900"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "fov_ok == if fov_x10 >= min_fov_x10 && fov_x10 <= max_fov_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fov_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thermal Camera: 25.0 deg FOV in [4.0, 90.0] -> OK");
}

#[test]
fn emissivity_range() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "emissivity_x100",
        "min_emissivity_x100",
        "max_emissivity_x100",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("emis_ok", i32_ty());
    // Emissivity setting (x100): 0.95 = 95, range 0.01 (1) to 1.00 (100)
    ctx.push_obligation(ProofObligation::assume("ex", "emissivity_x100 == 95"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_emissivity_x100 == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_emissivity_x100 == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "emis_ok == if emissivity_x100 >= min_emissivity_x100 && emissivity_x100 <= max_emissivity_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "emis_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Thermal Camera: 0.95 emissivity in [0.01, 1.00] -> OK",
    );
}

#[test]
fn image_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["refresh_hz", "min_hz", "max_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Thermal image refresh rate in Hz
    ctx.push_obligation(ProofObligation::assume("rh", "refresh_hz == 50"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_hz == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_hz == 60"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if refresh_hz >= min_hz && refresh_hz <= max_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thermal Camera: 50Hz refresh in [1, 60] -> OK");
}
