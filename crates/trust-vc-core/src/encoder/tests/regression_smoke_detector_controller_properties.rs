// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_device_count() {
    let mut ctx = VerificationContext::new();
    for v in &["addr_points", "min_points", "max_points"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("points_ok", i32_ty());
    // Addressable points on fire alarm controller
    ctx.push_obligation(ProofObligation::assume("ap", "addr_points == 128"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_points == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_points == 512"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "points_ok == if addr_points >= min_points && addr_points <= max_points { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "points_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FACP: 128 addressable points in [1, 512] -> OK");
}

#[test]
fn test_loop_count() {
    let mut ctx = VerificationContext::new();
    for v in &["sgl_loops", "min_loops", "max_loops"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("loops_ok", i32_ty());
    // Signalling line circuits (SLCs)
    ctx.push_obligation(ProofObligation::assume("sl", "sgl_loops == 4"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_loops == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_loops == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "loops_ok == if sgl_loops >= min_loops && sgl_loops <= max_loops { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "loops_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FACP: 4 signalling loops in [1, 16] -> OK");
}

#[test]
fn test_detector_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det_type", u32_ty());
    ctx.declare_var_typed("valid_type", i32_ty());
    // Detector types: 1=photoelectric, 2=ionization, 3=heat, 4=multi-criteria
    ctx.push_obligation(ProofObligation::assume("dt", "det_type == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_type == if det_type == 1 || det_type == 2 || det_type == 3 || det_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_type == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FACP: multi-criteria is valid detector type (4-way)",
    );
}

#[test]
fn test_alarm_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("alarm_class", u32_ty());
    ctx.declare_var_typed("valid_class", i32_ty());
    // Alarm classes: 1=pre-alarm, 2=alarm, 3=fire
    ctx.push_obligation(ProofObligation::assume("ac", "alarm_class == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_class == if alarm_class == 1 || alarm_class == 2 || alarm_class == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_class == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FACP: alarm is valid alarm class (3-way)");
}

#[test]
fn test_sensitivity() {
    let mut ctx = VerificationContext::new();
    for v in &["sens_x100", "min_sens_x100", "max_sens_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sens_ok", i32_ty());
    // Sensitivity in %/ft obscuration (x100 for 0.01% precision)
    ctx.push_obligation(ProofObligation::assume("sx", "sens_x100 == 150")); // 1.50%/ft
    ctx.push_obligation(ProofObligation::assume("mn", "min_sens_x100 == 50")); // 0.50%/ft
    ctx.push_obligation(ProofObligation::assume("mx", "max_sens_x100 == 400")); // 4.00%/ft
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sens_ok == if sens_x100 >= min_sens_x100 && sens_x100 <= max_sens_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sens_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FACP: 1.50%/ft sensitivity in [0.50, 4.00] -> OK");
}

#[test]
fn test_loop_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["supply_mv", "min_supply_mv", "max_supply_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("supply_ok", i32_ty());
    // Loop supply voltage in millivolts
    ctx.push_obligation(ProofObligation::assume("sv", "supply_mv == 24000")); // 24V
    ctx.push_obligation(ProofObligation::assume("mn", "min_supply_mv == 15000")); // 15V
    ctx.push_obligation(ProofObligation::assume("mx", "max_supply_mv == 30000")); // 30V
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "supply_ok == if supply_mv >= min_supply_mv && supply_mv <= max_supply_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "supply_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FACP: 24V loop supply in [15V, 30V] -> OK");
}

#[test]
fn test_protocol_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("protocol", u32_ty());
    ctx.declare_var_typed("valid_proto", i32_ty());
    // Protocol types: 1=analog addressable, 2=conventional, 3=wireless
    ctx.push_obligation(ProofObligation::assume("pt", "protocol == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_proto == if protocol == 1 || protocol == 2 || protocol == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_proto == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FACP: analog addressable is valid protocol (3-way)",
    );
}

#[test]
fn test_zone_count() {
    let mut ctx = VerificationContext::new();
    for v in &["fire_zones", "min_zones", "max_zones"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("zones_ok", i32_ty());
    // Fire zones on addressable panel
    ctx.push_obligation(ProofObligation::assume("fz", "fire_zones == 16"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_zones == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_zones == 128"));
    ctx.push_obligation(ProofObligation::assume(
        "zo_def",
        "zones_ok == if fire_zones >= min_zones && fire_zones <= max_zones { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "zones_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FACP: 16 fire zones in [1, 128] -> OK");
}

#[test]
fn test_response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["detect_sec", "min_detect_sec", "max_detect_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("detect_ok", i32_ty());
    // Detection response latency in seconds
    ctx.push_obligation(ProofObligation::assume("ds", "detect_sec == 30"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_detect_sec == 5"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_detect_sec == 120"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "detect_ok == if detect_sec >= min_detect_sec && detect_sec <= max_detect_sec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "detect_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FACP: 30s detection latency in [5, 120] -> OK");
}

#[test]
fn test_sounder_output() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sounder_enabled", i32_ty());
    ctx.declare_var_typed("sounder_active", i32_ty());
    // Sounder output as boolean flag (i32: 1=enabled, 0=disabled)
    ctx.push_obligation(ProofObligation::assume("se", "sounder_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "sa_def",
        "sounder_active == if sounder_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sounder_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FACP: sounder enabled -> active (boolean flag)");
}
