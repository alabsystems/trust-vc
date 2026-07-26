// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_drum_dryer_drum_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dia", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dia_range",
        "dia >= 600 && dia <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dia_bounded",
        "dia >= 600 && dia <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drum diameter should be bounded to 600-3000mm");
}

#[test]
fn test_drum_dryer_drum_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("len", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "len_range",
        "len >= 500 && len <= 4000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "len_bounded",
        "len >= 500 && len <= 4000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drum length should be bounded to 500-4000mm");
}

#[test]
fn test_drum_dryer_rotation_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rpm_range",
        "rpm_x10 >= 5 && rpm_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_bounded",
        "rpm_x10 >= 5 && rpm_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rotation speed x10 should be bounded to 5-200 (0.5-20.0 RPM)",
    );
}

#[test]
fn test_drum_dryer_steam_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press_x10 >= 10 && press_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "press_bounded",
        "press_x10 >= 10 && press_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "steam pressure x10 should be bounded to 10-100 (1.0-10.0 bar)",
    );
}

#[test]
fn test_drum_dryer_surface_temp_offset500_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp >= 550 && temp <= 700",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp >= 550 && temp <= 700",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "surface temp offset+500 should be bounded to 550-700 (50-200C)",
    );
}

#[test]
fn test_drum_dryer_film_thickness_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("film_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "film_range",
        "film_x100 >= 5 && film_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "film_bounded",
        "film_x100 >= 5 && film_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "film thickness x100 should be bounded to 5-500 (0.05-5.00mm)",
    );
}

#[test]
fn test_drum_dryer_feed_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "feed_valid",
        "feed == 1 || feed == 2 || feed == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "feed_bounded",
        "feed == 1 || feed == 2 || feed == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed method should be 1=dip, 2=splash, or 3=spray");
}

#[test]
fn test_drum_dryer_drum_config_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cfg", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cfg_valid",
        "cfg == 1 || cfg == 2 || cfg == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cfg_bounded",
        "cfg == 1 || cfg == 2 || cfg == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drum config should be 1=single, 2=double, or 3=twin",
    );
}

#[test]
fn test_drum_dryer_scraper_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scr", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "scr_valid",
        "scr == 1 || scr == 2 || scr == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "scr_bounded",
        "scr == 1 || scr == 2 || scr == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "scraper type should be 1=blade, 2=roller, or 3=wire",
    );
}

#[test]
fn test_drum_dryer_enclosed_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("enc", i32_ty());
    ctx.push_obligation(ProofObligation::assume("enc_valid", "enc == 0 || enc == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "enc_bounded",
        "enc == 0 || enc == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "enclosed flag should be 0 or 1");
}
