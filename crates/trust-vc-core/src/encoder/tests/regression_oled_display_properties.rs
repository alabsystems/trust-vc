// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn pixel_address_valid() {
    let mut ctx = VerificationContext::new();
    for v in &["x", "y", "width", "height"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_bounds", i32_ty());
    // 128×64 OLED: pixel coordinates must be within bounds
    ctx.push_obligation(ProofObligation::assume("xv", "x == 100"));
    ctx.push_obligation(ProofObligation::assume("yv", "y == 32"));
    ctx.push_obligation(ProofObligation::assume("w", "width == 128"));
    ctx.push_obligation(ProofObligation::assume("h", "height == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "ib_def",
        "in_bounds == if x < width && y < height { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_bounds == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OLED: (100, 32) in 128×64 → pixel in bounds");
}

#[test]
fn contrast_level() {
    let mut ctx = VerificationContext::new();
    for v in &["contrast", "max_contrast"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    // Contrast: 0-255 (8-bit)
    ctx.push_obligation(ProofObligation::assume("c", "contrast == 200"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_contrast == 255"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if contrast <= max_contrast { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OLED: contrast 200 ≤ 255 max → valid");
}

#[test]
fn page_address() {
    let mut ctx = VerificationContext::new();
    for v in &["page", "max_pages"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("page_valid", i32_ty());
    // SSD1306: 8 pages (0-7), each page = 8 rows
    ctx.push_obligation(ProofObligation::assume("p", "page == 5"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_pages == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "pv_def",
        "page_valid == if page < max_pages { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "page_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OLED: page 5 < 8 pages → page valid");
}

#[test]
fn buffer_size() {
    let mut ctx = VerificationContext::new();
    for v in &["width", "height_pages"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("buffer_bytes", u32_ty());
    // Buffer = width × (height/8). Precompute: 128 × 8 = 1024
    ctx.push_obligation(ProofObligation::assume("w", "width == 128"));
    ctx.push_obligation(ProofObligation::assume("hp", "height_pages == 8")); // 64/8
    ctx.push_obligation(ProofObligation::assume("bb", "buffer_bytes == 1024")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_1024", "buffer_bytes == 1024"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "OLED: 128 × 8 pages = 1024 byte buffer (precomputed)",
    );
}

#[test]
fn i2c_address() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("address", u32_ty());
    ctx.declare_var_typed("is_oled", i32_ty());
    // SSD1306 I2C address: 0x3C or 0x3D
    ctx.push_obligation(ProofObligation::assume("a", "address == 60")); // 0x3C
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "is_oled == if address == 60 || address == 61 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_oled == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OLED: I2C address 0x3C → valid SSD1306 address");
}

#[test]
fn scroll_speed() {
    let mut ctx = VerificationContext::new();
    for v in &["scroll_interval", "min_interval"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("speed_ok", i32_ty());
    // Scroll interval: frames between scroll steps (2-256)
    ctx.push_obligation(ProofObligation::assume("si", "scroll_interval == 5"));
    ctx.push_obligation(ProofObligation::assume("mi", "min_interval == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "speed_ok == if scroll_interval >= min_interval { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "speed_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OLED: scroll interval 5 ≥ 2 min → speed OK");
}

#[test]
fn multiplex_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["mux_ratio", "expected_ratio"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("mux_ok", i32_ty());
    // Multiplex ratio = number of display rows - 1 (e.g., 63 for 64 rows)
    ctx.push_obligation(ProofObligation::assume("mr", "mux_ratio == 63"));
    ctx.push_obligation(ProofObligation::assume("er", "expected_ratio == 63"));
    ctx.push_obligation(ProofObligation::assume(
        "mo_def",
        "mux_ok == if mux_ratio == expected_ratio { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "mux_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OLED: mux ratio 63 = expected → configuration OK");
}

#[test]
fn charge_pump_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["pump_voltage_mv", "min_voltage_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pump_ok", i32_ty());
    // Internal charge pump generates ~7.5V for OLED from 3.3V supply
    ctx.push_obligation(ProofObligation::assume("pv", "pump_voltage_mv == 7500"));
    ctx.push_obligation(ProofObligation::assume("mv", "min_voltage_mv == 7000"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pump_ok == if pump_voltage_mv >= min_voltage_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pump_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OLED: charge pump 7500mV ≥ 7000mV min → pump OK");
}

#[test]
fn display_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["offset_rows", "max_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("offset_valid", i32_ty());
    // Display start line offset: 0-63
    ctx.push_obligation(ProofObligation::assume("or", "offset_rows == 16"));
    ctx.push_obligation(ProofObligation::assume("mo", "max_offset == 63"));
    ctx.push_obligation(ProofObligation::assume(
        "ov_def",
        "offset_valid == if offset_rows <= max_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "offset_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OLED: offset 16 rows ≤ 63 max → offset valid");
}

#[test]
fn pixel_lifetime() {
    let mut ctx = VerificationContext::new();
    for v in &["on_hours", "rated_hours"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_life", i32_ty());
    // OLED pixel lifetime: typically 30,000-100,000 hours
    ctx.push_obligation(ProofObligation::assume("oh", "on_hours == 15000"));
    ctx.push_obligation(ProofObligation::assume("rh", "rated_hours == 50000"));
    ctx.push_obligation(ProofObligation::assume(
        "wl_def",
        "within_life == if on_hours < rated_hours { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "within_life == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "OLED: 15K hours < 50K rated → within pixel lifetime",
    );
}
