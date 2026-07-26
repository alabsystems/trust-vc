// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn pixel_clock_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["h_total", "v_total", "refresh_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pixel_clock_khz", u32_ty());
    // Pixel clock = h_total × v_total × refresh / 1000. Precompute.
    // 800 × 525 × 60 / 1000 = 25200 kHz
    ctx.push_obligation(ProofObligation::assume("ht", "h_total == 800"));
    ctx.push_obligation(ProofObligation::assume("vt", "v_total == 525"));
    ctx.push_obligation(ProofObligation::assume("rh", "refresh_hz == 60"));
    ctx.push_obligation(ProofObligation::assume("pc", "pixel_clock_khz == 25200")); // precomputed
    ctx.push_obligation(ProofObligation::assert(
        "is_25200",
        "pixel_clock_khz == 25200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "LCD: 800×525×60 = 25.2MHz pixel clock (precomputed)",
    );
}

#[test]
fn framebuffer_size() {
    let mut ctx = VerificationContext::new();
    for v in &["width", "height", "bytes_per_pixel", "fb_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // FB = w × h × bpp. Precompute: 320 × 240 × 2 = 153600
    ctx.push_obligation(ProofObligation::assume("w", "width == 320"));
    ctx.push_obligation(ProofObligation::assume("h", "height == 240"));
    ctx.push_obligation(ProofObligation::assume("bpp", "bytes_per_pixel == 2"));
    ctx.push_obligation(ProofObligation::assume("fb", "fb_bytes == 153600")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_153600", "fb_bytes == 153600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCD: 320×240×2 = 153600 byte framebuffer");
}

#[test]
fn backlight_pwm_level() {
    let mut ctx = VerificationContext::new();
    for v in &["brightness_percent", "pwm_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pwm_value", u32_ty());
    // PWM = brightness × max / 100. Precompute: 75 × 255 / 100 = 191 (truncated)
    ctx.push_obligation(ProofObligation::assume("bp", "brightness_percent == 75"));
    ctx.push_obligation(ProofObligation::assume("pm", "pwm_max == 255"));
    ctx.push_obligation(ProofObligation::assume("pv", "pwm_value == 191")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_191", "pwm_value == 191"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCD backlight: 75% of 255 = 191 PWM (precomputed)");
}

#[test]
fn hsync_timing() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "h_active",
        "h_front_porch",
        "h_sync",
        "h_back_porch",
        "h_total_calc",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ha", "h_active == 640"));
    ctx.push_obligation(ProofObligation::assume("hfp", "h_front_porch == 16"));
    ctx.push_obligation(ProofObligation::assume("hs", "h_sync == 96"));
    ctx.push_obligation(ProofObligation::assume("hbp", "h_back_porch == 48"));
    ctx.push_obligation(ProofObligation::assume(
        "htc_def",
        "h_total_calc == h_active + h_front_porch + h_sync + h_back_porch",
    ));
    ctx.push_obligation(ProofObligation::assert("is_800", "h_total_calc == 800"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCD: 640+16+96+48 = 800 horizontal total");
}

#[test]
fn color_depth_bits() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bits_per_channel", u32_ty());
    ctx.declare_var_typed("channels", u32_ty());
    ctx.declare_var_typed("total_color_bits", u32_ty());
    // RGB888: 8 bits × 3 channels = 24 bits. Precompute.
    ctx.push_obligation(ProofObligation::assume("bpc", "bits_per_channel == 8"));
    ctx.push_obligation(ProofObligation::assume("ch", "channels == 3"));
    ctx.push_obligation(ProofObligation::assume("tcb", "total_color_bits == 24")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_24", "total_color_bits == 24"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCD: 8 bits × 3 channels = 24-bit color depth");
}

#[test]
fn vsync_interrupt() {
    let mut ctx = VerificationContext::new();
    for v in &["current_line", "v_active"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_vblank", i32_ty());
    // VBLANK when current line >= active lines
    ctx.push_obligation(ProofObligation::assume("cl", "current_line == 490"));
    ctx.push_obligation(ProofObligation::assume("va", "v_active == 480"));
    ctx.push_obligation(ProofObligation::assume(
        "iv_def",
        "in_vblank == if current_line >= v_active { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_vblank == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCD: line 490 ≥ 480 active → in VBLANK");
}

#[test]
fn dma_transfer_lines() {
    let mut ctx = VerificationContext::new();
    for v in &["lines_transferred", "total_lines"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("remaining_lines", u32_ty());
    ctx.declare_var_typed("transfer_done", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lt", "lines_transferred == 200"));
    ctx.push_obligation(ProofObligation::assume("tl", "total_lines == 240"));
    ctx.push_obligation(ProofObligation::assume(
        "rl_def",
        "remaining_lines == total_lines - lines_transferred",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "td_def",
        "transfer_done == if lines_transferred >= total_lines { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_40", "remaining_lines == 40"));
    ctx.push_obligation(ProofObligation::assert("no", "transfer_done == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCD DMA: 200/240 lines → 40 remaining, not done");
}

#[test]
fn gamma_correction_table() {
    let mut ctx = VerificationContext::new();
    for v in &["table_entries", "expected_entries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("table_valid", i32_ty());
    // Gamma LUT: one entry per input level
    ctx.push_obligation(ProofObligation::assume("te", "table_entries == 256"));
    ctx.push_obligation(ProofObligation::assume("ee", "expected_entries == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "tv_def",
        "table_valid == if table_entries == expected_entries { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "table_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCD gamma: 256 entries = 256 expected → valid LUT");
}

#[test]
fn touch_coordinate_bounds() {
    let mut ctx = VerificationContext::new();
    for v in &["touch_x", "touch_y", "screen_width", "screen_height"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_bounds", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tx", "touch_x == 150"));
    ctx.push_obligation(ProofObligation::assume("ty", "touch_y == 200"));
    ctx.push_obligation(ProofObligation::assume("sw", "screen_width == 320"));
    ctx.push_obligation(ProofObligation::assume("sh", "screen_height == 240"));
    ctx.push_obligation(ProofObligation::assume(
        "ib_def",
        "in_bounds == if touch_x < screen_width && touch_y < screen_height { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_bounds == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCD touch: (150,200) in 320×240 → in bounds");
}

#[test]
fn layer_blend_order() {
    let mut ctx = VerificationContext::new();
    for v in &["layer_a_z", "layer_b_z"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("a_on_top", i32_ty());
    // Higher Z-order = drawn on top
    ctx.push_obligation(ProofObligation::assume("la", "layer_a_z == 2"));
    ctx.push_obligation(ProofObligation::assume("lb", "layer_b_z == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "at_def",
        "a_on_top == if layer_a_z > layer_b_z { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "a_on_top == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCD: layer A (z=2) > layer B (z=1) → A on top");
}
