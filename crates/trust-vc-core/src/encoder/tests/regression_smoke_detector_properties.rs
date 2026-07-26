// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn obscuration_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "obscuration_x100",
        "min_threshold_x100",
        "max_threshold_x100",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("obs_ok", i32_ty());
    // Smoke obscuration in %/ft (×100 for 0.01% precision)
    ctx.push_obligation(ProofObligation::assume("ox", "obscuration_x100 == 250")); // 2.50%/ft
    ctx.push_obligation(ProofObligation::assume("mn", "min_threshold_x100 == 50")); // 0.50%
    ctx.push_obligation(ProofObligation::assume("mx", "max_threshold_x100 == 400")); // 4.00%
    ctx.push_obligation(ProofObligation::assume(
        "oo_def",
        "obs_ok == if obscuration_x100 >= min_threshold_x100 && obscuration_x100 <= max_threshold_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "obs_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Smoke: 2.50%/ft obscuration in [0.50, 4.00] → OK");
}

#[test]
fn alarm_response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["response_sec", "max_response_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("resp_ok", i32_ty());
    // Alarm response time in seconds (UL 217 requirement)
    ctx.push_obligation(ProofObligation::assume("rs", "response_sec == 25"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_response_sec == 60"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "resp_ok == if response_sec <= max_response_sec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "resp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Smoke: 25s response ≤ 60s max → OK");
}

#[test]
fn detector_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det_type", u32_ty());
    ctx.declare_var_typed("valid_type", i32_ty());
    // Detector types: 1=photoelectric, 2=ionization, 3=dual-sensor, 4=aspirating
    ctx.push_obligation(ProofObligation::assume("dt", "det_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_type == if det_type == 1 || det_type == 2 || det_type == 3 || det_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_type == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Smoke: dual-sensor is valid detector type");
}

#[test]
fn battery_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["batt_mv", "min_batt_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("batt_ok", i32_ty());
    // Battery voltage threshold for low-battery warning
    ctx.push_obligation(ProofObligation::assume("bm", "batt_mv == 2800")); // 2.8V
    ctx.push_obligation(ProofObligation::assume("mb", "min_batt_mv == 2400")); // 2.4V
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "batt_ok == if batt_mv >= min_batt_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "batt_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Smoke: 2.8V battery ≥ 2.4V min → OK");
}

#[test]
fn alarm_sound_level() {
    let mut ctx = VerificationContext::new();
    for v in &["sound_db", "min_sound_db"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sound_ok", i32_ty());
    // Alarm sound level at 10ft (UL 217: ≥85 dBA)
    ctx.push_obligation(ProofObligation::assume("sd", "sound_db == 90"));
    ctx.push_obligation(ProofObligation::assume("ms", "min_sound_db == 85"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sound_ok == if sound_db >= min_sound_db { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sound_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Smoke: 90 dBA alarm ≥ 85 min → OK");
}

#[test]
fn chamber_sensitivity() {
    let mut ctx = VerificationContext::new();
    for v in &["sens_x100", "min_sens_x100", "max_sens_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sens_ok", i32_ty());
    // Smoke chamber sensitivity in %/ft (×100)
    ctx.push_obligation(ProofObligation::assume("sx", "sens_x100 == 150")); // 1.50%/ft
    ctx.push_obligation(ProofObligation::assume("mn", "min_sens_x100 == 50")); // 0.50%
    ctx.push_obligation(ProofObligation::assume("mx", "max_sens_x100 == 300")); // 3.00%
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sens_ok == if sens_x100 >= min_sens_x100 && sens_x100 <= max_sens_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sens_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Smoke: 1.50%/ft sensitivity in [0.50, 3.00] → OK");
}

#[test]
fn test_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["test_hours", "max_test_hours"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("test_ok", i32_ty());
    // Self-test interval in hours
    ctx.push_obligation(ProofObligation::assume("th", "test_hours == 24"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_test_hours == 168")); // weekly
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "test_ok == if test_hours <= max_test_hours { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "test_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Smoke: 24h self-test interval ≤ 168h max → OK");
}

#[test]
fn interconnect_count() {
    let mut ctx = VerificationContext::new();
    for v in &["detectors", "max_detectors"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("det_ok", i32_ty());
    // Interconnected detector count (NFPA 72)
    ctx.push_obligation(ProofObligation::assume("d", "detectors == 18"));
    ctx.push_obligation(ProofObligation::assume("md", "max_detectors == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "det_ok == if detectors <= max_detectors { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "det_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Smoke: 18 interconnected ≤ 30 max → OK");
}

#[test]
fn led_flash_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["flash_sec", "min_flash_sec", "max_flash_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("flash_ok", i32_ty());
    // Status LED flash interval in seconds
    ctx.push_obligation(ProofObligation::assume("fs", "flash_sec == 40"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_flash_sec == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_flash_sec == 60"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "flash_ok == if flash_sec >= min_flash_sec && flash_sec <= max_flash_sec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "flash_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Smoke: 40s LED flash in [10, 60] → OK");
}

#[test]
fn drift_compensation() {
    let mut ctx = VerificationContext::new();
    for v in &["drift_pct_x10", "max_drift_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("drift_ok", i32_ty());
    // Chamber contamination drift compensation (×10 for 0.1%)
    ctx.push_obligation(ProofObligation::assume("dx", "drift_pct_x10 == 30")); // 3.0%
    ctx.push_obligation(ProofObligation::assume("md", "max_drift_x10 == 100")); // 10.0%
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "drift_ok == if drift_pct_x10 <= max_drift_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "drift_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Smoke: 3.0% drift ≤ 10.0% max → OK");
}
