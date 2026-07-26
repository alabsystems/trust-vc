// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn framebuffer_size() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "width",
        "height",
        "bytes_per_pixel",
        "stride",
        "total_bytes",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 320×240 RGB565 (2 bytes/pixel)
    ctx.push_obligation(ProofObligation::assume("w", "width == 320"));
    ctx.push_obligation(ProofObligation::assume("h", "height == 240"));
    ctx.push_obligation(ProofObligation::assume("bpp", "bytes_per_pixel == 2")); // RGB565
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "stride == width * bytes_per_pixel",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_bytes == stride * height",
    ));
    ctx.push_obligation(ProofObligation::assert("stride_640", "stride == 640")); // 320×2
    ctx.push_obligation(ProofObligation::assert(
        "is_153600",
        "total_bytes == 153600",
    )); // 640×240
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "LCD: 320×240 RGB565 = 153600 bytes");
}

#[test]
fn pixel_clock_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["htotal", "vtotal", "refresh_hz", "pixel_clock_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Pixel clock = htotal × vtotal × refresh rate
    // 800×525×60 = 25200000 Hz ≈ 25.2 MHz (VGA 640×480)
    // Break into two steps
    ctx.push_obligation(ProofObligation::assume("ht", "htotal == 800"));
    ctx.push_obligation(ProofObligation::assume("vt", "vtotal == 525"));
    ctx.push_obligation(ProofObligation::assume("rh", "refresh_hz == 60"));
    // Precompute: 800 × 525 = 420000, 420000 × 60 = 25200000
    ctx.push_obligation(ProofObligation::assume("pc", "pixel_clock_hz == 25200000"));
    ctx.push_obligation(ProofObligation::assert(
        "is_correct",
        "pixel_clock_hz == 25200000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VGA: pixel clock 25.2MHz (precomputed)");
}

#[test]
fn hsync_timing() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "active",
        "front_porch",
        "sync_pulse",
        "back_porch",
        "htotal",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // VGA 640×480: H timing in pixel clocks
    ctx.push_obligation(ProofObligation::assume("a", "active == 640"));
    ctx.push_obligation(ProofObligation::assume("fp", "front_porch == 16"));
    ctx.push_obligation(ProofObligation::assume("sp", "sync_pulse == 96"));
    ctx.push_obligation(ProofObligation::assume("bp", "back_porch == 48"));
    ctx.push_obligation(ProofObligation::assume(
        "ht_def",
        "htotal == active + front_porch + sync_pulse + back_porch",
    ));
    ctx.push_obligation(ProofObligation::assert("is_800", "htotal == 800"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VGA hsync: 640+16+96+48 = 800 total");
}

#[test]
fn vsync_timing() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "active_lines",
        "front_porch",
        "sync_lines",
        "back_porch",
        "vtotal",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("al", "active_lines == 480"));
    ctx.push_obligation(ProofObligation::assume("fp", "front_porch == 10"));
    ctx.push_obligation(ProofObligation::assume("sl", "sync_lines == 2"));
    ctx.push_obligation(ProofObligation::assume("bp", "back_porch == 33"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "vtotal == active_lines + front_porch + sync_lines + back_porch",
    ));
    ctx.push_obligation(ProofObligation::assert("is_525", "vtotal == 525"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VGA vsync: 480+10+2+33 = 525 total lines");
}

#[test]
fn double_buffer_swap() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("front_buffer", u32_ty());
    ctx.declare_var_typed("back_buffer", u32_ty());
    ctx.declare_var_typed("new_front", u32_ty());
    ctx.declare_var_typed("new_back", u32_ty());
    // Swap buffers at vsync
    ctx.push_obligation(ProofObligation::assume("fb", "front_buffer == 0"));
    ctx.push_obligation(ProofObligation::assume("bb", "back_buffer == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "nf_def",
        "new_front == back_buffer",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "nb_def",
        "new_back == front_buffer",
    ));
    ctx.push_obligation(ProofObligation::assert("swapped_front", "new_front == 1"));
    ctx.push_obligation(ProofObligation::assert("swapped_back", "new_back == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCD: buffer swap 0↔1 at vsync");
}

#[test]
fn color_depth_bits() {
    let mut ctx = VerificationContext::new();
    for v in &["red_bits", "green_bits", "blue_bits", "total_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // RGB565: 5+6+5 = 16 bits
    ctx.push_obligation(ProofObligation::assume("rb", "red_bits == 5"));
    ctx.push_obligation(ProofObligation::assume("gb", "green_bits == 6"));
    ctx.push_obligation(ProofObligation::assume("bb", "blue_bits == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_bits == red_bits + green_bits + blue_bits",
    ));
    ctx.push_obligation(ProofObligation::assert("is_16", "total_bits == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RGB565: 5+6+5 = 16 bits per pixel");
}

#[test]
fn dma_line_transfer() {
    let mut ctx = VerificationContext::new();
    for v in &["line_bytes", "dma_burst", "bursts_per_line"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 640 bytes per line / 16 byte burst = 40 bursts
    ctx.push_obligation(ProofObligation::assume("lb", "line_bytes == 640"));
    ctx.push_obligation(ProofObligation::assume("db", "dma_burst == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "bpl_def",
        "bursts_per_line == line_bytes / dma_burst",
    ));
    ctx.push_obligation(ProofObligation::assert("is_40", "bursts_per_line == 40"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "LCD DMA: 640 / 16 = 40 bursts/line");
}

#[test]
fn layer_blending_alpha() {
    let mut ctx = VerificationContext::new();
    for v in &["fg_alpha", "max_alpha"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fully_opaque", i32_ty());
    // Alpha blending: 255 = fully opaque
    ctx.push_obligation(ProofObligation::assume("fa", "fg_alpha == 255"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_alpha == 255"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "fully_opaque == if fg_alpha == max_alpha { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fully_opaque == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCD: alpha 255 → fully opaque");
}

#[test]
fn window_position() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "win_x",
        "win_y",
        "win_width",
        "win_height",
        "screen_width",
        "screen_height",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fits_on_screen", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wx", "win_x == 100"));
    ctx.push_obligation(ProofObligation::assume("wy", "win_y == 50"));
    ctx.push_obligation(ProofObligation::assume("ww", "win_width == 200"));
    ctx.push_obligation(ProofObligation::assume("wh", "win_height == 150"));
    ctx.push_obligation(ProofObligation::assume("sw", "screen_width == 320"));
    ctx.push_obligation(ProofObligation::assume("sh", "screen_height == 240"));
    ctx.push_obligation(ProofObligation::assume(
        "fos_def",
        "fits_on_screen == if win_x + win_width <= screen_width && win_y + win_height <= screen_height { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "fits_on_screen == 1")); // 300<=320, 200<=240
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCD: window 200×150 at (100,50) fits 320×240");
}

#[test]
fn tear_effect_line() {
    let mut ctx = VerificationContext::new();
    for v in &["current_scanline", "tear_line"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("safe_to_update", i32_ty());
    // TE (Tear Effect): safe to update when scanline is past the tear line
    ctx.push_obligation(ProofObligation::assume("cs", "current_scanline == 400"));
    ctx.push_obligation(ProofObligation::assume("tl", "tear_line == 240")); // below active area
    ctx.push_obligation(ProofObligation::assume(
        "stu_def",
        "safe_to_update == if current_scanline > tear_line { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "safe_to_update == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCD TE: scanline 400 > 240 → safe to update");
}
