// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn sentence_length() {
    let mut ctx = VerificationContext::new();
    for v in &["length", "max_length"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("len_ok", i32_ty());
    // NMEA 0183: maximum 82 characters per sentence (including $ and CRLF)
    ctx.push_obligation(ProofObligation::assume("l", "length == 60"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_length == 82"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "len_ok == if length <= max_length { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "len_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMEA0183: 60 chars ≤ 82 max → length OK");
}

#[test]
fn talker_id() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("talker", u32_ty());
    ctx.declare_var_typed("valid_talker", i32_ty());
    // Common talker IDs encoded: 1=GP(GPS), 2=GL(GLONASS), 3=GA(Galileo), 4=GN(combined), 5=II(instruments)
    ctx.push_obligation(ProofObligation::assume("t", "talker == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_talker == if talker == 1 || talker == 2 || talker == 3 || talker == 4 || talker == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_talker == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMEA0183: talker=1 (GP/GPS) → valid");
}

#[test]
fn checksum_range() {
    let mut ctx = VerificationContext::new();
    for v in &["checksum", "max_checksum"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cs_ok", i32_ty());
    // XOR checksum: 8-bit value (0-255)
    ctx.push_obligation(ProofObligation::assume("c", "checksum == 74"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_checksum == 255"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cs_ok == if checksum <= max_checksum { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cs_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMEA0183: checksum 74 ≤ 255 → valid 8-bit");
}

#[test]
fn update_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["rate_hz", "min_rate_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rate_ok", i32_ty());
    // GPS fix update rate: 1-10Hz typical
    ctx.push_obligation(ProofObligation::assume("rh", "rate_hz == 5"));
    ctx.push_obligation(ProofObligation::assume("mr", "min_rate_hz == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rate_ok == if rate_hz >= min_rate_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMEA0183: 5Hz update ≥ 1Hz min → rate OK");
}

#[test]
fn latitude_range() {
    let mut ctx = VerificationContext::new();
    for v in &["lat_x10000", "max_lat_x10000"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("lat_ok", i32_ty());
    // Latitude: 0-90° (×10000 for 0.0001° = ~11m resolution)
    ctx.push_obligation(ProofObligation::assume("lx", "lat_x10000 == 374178")); // 37.4178°N
    ctx.push_obligation(ProofObligation::assume("ml", "max_lat_x10000 == 900000")); // 90.0000°
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "lat_ok == if lat_x10000 <= max_lat_x10000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "lat_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMEA0183: 37.4178° ≤ 90° → latitude OK");
}

#[test]
fn speed_knots() {
    let mut ctx = VerificationContext::new();
    for v in &["speed_x10", "max_speed_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("spd_ok", i32_ty());
    // Speed over ground in knots (×10 for 0.1kn resolution)
    ctx.push_obligation(ProofObligation::assume("sx", "speed_x10 == 85")); // 8.5 knots
    ctx.push_obligation(ProofObligation::assume("ms", "max_speed_x10 == 500")); // 50.0 knots
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "spd_ok == if speed_x10 <= max_speed_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "spd_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMEA0183: 8.5kn ≤ 50.0kn max → speed OK");
}

#[test]
fn heading_field() {
    let mut ctx = VerificationContext::new();
    for v in &["heading_x10", "max_heading_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("hdg_ok", i32_ty());
    // True heading: 0-359.9° (×10 for 0.1° resolution)
    ctx.push_obligation(ProofObligation::assume("hx", "heading_x10 == 2700")); // 270.0°
    ctx.push_obligation(ProofObligation::assume("mh", "max_heading_x10 == 3599")); // 359.9°
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "hdg_ok == if heading_x10 <= max_heading_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "hdg_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMEA0183: 270.0° ≤ 359.9° → heading OK");
}

#[test]
fn depth_value() {
    let mut ctx = VerificationContext::new();
    for v in &["depth_x10", "max_depth_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("depth_ok", i32_ty());
    // Depth below transducer in meters (×10 for 0.1m)
    ctx.push_obligation(ProofObligation::assume("dx", "depth_x10 == 152")); // 15.2m
    ctx.push_obligation(ProofObligation::assume("md", "max_depth_x10 == 10000")); // 1000.0m
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "depth_ok == if depth_x10 <= max_depth_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "depth_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMEA0183: 15.2m depth ≤ 1000.0m max → OK");
}

#[test]
fn satellite_count() {
    let mut ctx = VerificationContext::new();
    for v in &["sats", "min_sats"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sats_ok", i32_ty());
    // Satellites in view for fix: minimum 4 for 3D fix
    ctx.push_obligation(ProofObligation::assume("s", "sats == 8"));
    ctx.push_obligation(ProofObligation::assume("ms", "min_sats == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sats_ok == if sats >= min_sats { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sats_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMEA0183: 8 satellites ≥ 4 min (3D fix) → OK");
}

#[test]
fn sentence_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stype", u32_ty());
    ctx.declare_var_typed("valid_type", i32_ty());
    // Common sentence types: 1=GGA, 2=RMC, 3=GSA, 4=GSV, 5=VTG, 6=DBT
    ctx.push_obligation(ProofObligation::assume("st", "stype == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_type == if stype == 1 || stype == 2 || stype == 3 || stype == 4 || stype == 5 || stype == 6 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_type == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMEA0183: stype=2 (RMC) → valid sentence type");
}
