// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn clock_polarity_idle_state() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cpol", u32_ty()); // 0=idle low, 1=idle high
    ctx.declare_var_typed("idle_level", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cp", "cpol == 0"));
    ctx.push_obligation(ProofObligation::assume("il_def", "idle_level == cpol"));
    ctx.push_obligation(ProofObligation::assert("low", "idle_level == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI: CPOL=0 → idle low");
}

#[test]
fn transfer_size_bits() {
    let mut ctx = VerificationContext::new();
    for v in &["frame_bits", "num_frames", "total_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("fb", "frame_bits == 8"));
    ctx.push_obligation(ProofObligation::assume("nf", "num_frames == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_bits == frame_bits * num_frames",
    ));
    ctx.push_obligation(ProofObligation::assert("is_32", "total_bits == 32"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "SPI: 8×4=32 bits");
}

#[test]
fn clock_divider() {
    let mut ctx = VerificationContext::new();
    for v in &["sys_clock_hz", "divider", "spi_clock_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sc", "sys_clock_hz == 48000000")); // 48MHz
    ctx.push_obligation(ProofObligation::assume("d", "divider == 48"));
    ctx.push_obligation(ProofObligation::assume(
        "sck_def",
        "spi_clock_hz == sys_clock_hz / divider",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_1mhz",
        "spi_clock_hz == 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "SPI clock: 48MHz/48=1MHz");
}

#[test]
fn chip_select_active_low() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cs_pin", u32_ty());
    ctx.declare_var_typed("device_selected", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cs", "cs_pin == 0")); // active low
    ctx.push_obligation(ProofObligation::assume(
        "ds_def",
        "device_selected == if cs_pin == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("selected", "device_selected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI: CS=0 (active low) → selected");
}

#[test]
fn multi_slave_addressing() {
    let mut ctx = VerificationContext::new();
    for v in &["num_slaves", "selected_slave"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_selection", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ns", "num_slaves == 4"));
    ctx.push_obligation(ProofObligation::assume("ss", "selected_slave == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_selection == if selected_slave < num_slaves { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_selection == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI: slave 2 < 4 → valid");
}

#[test]
fn full_duplex_throughput() {
    let mut ctx = VerificationContext::new();
    for v in &["clock_hz", "bits_per_frame", "frames_per_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ch", "clock_hz == 1000000")); // 1MHz
    ctx.push_obligation(ProofObligation::assume("bpf", "bits_per_frame == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "fps_def",
        "frames_per_sec == clock_hz / bits_per_frame",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_125k",
        "frames_per_sec == 125000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "SPI throughput: 1MHz/8=125000 frames/s");
}

#[test]
fn fifo_depth_check() {
    let mut ctx = VerificationContext::new();
    for v in &["tx_fifo_level", "tx_fifo_depth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("tx_full", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tfl", "tx_fifo_level == 16"));
    ctx.push_obligation(ProofObligation::assume("tfd", "tx_fifo_depth == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "tf_def",
        "tx_full == if tx_fifo_level >= tx_fifo_depth { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("full", "tx_full == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI TX FIFO: 16/16 → full");
}

#[test]
fn dma_trigger_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["rx_fifo_level", "dma_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dma_request", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rfl", "rx_fifo_level == 8"));
    ctx.push_obligation(ProofObligation::assume("dt", "dma_threshold == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "dr_def",
        "dma_request == if rx_fifo_level >= dma_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dma_request == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI DMA: RX level 8 >= threshold 4");
}

#[test]
fn mode_fault_detection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("configured_as_master", u32_ty());
    ctx.declare_var_typed("ss_input_low", u32_ty());
    ctx.declare_var_typed("mode_fault", i32_ty());
    // Mode fault: configured as master but SS driven low by another master
    ctx.push_obligation(ProofObligation::assume("cam", "configured_as_master == 1"));
    ctx.push_obligation(ProofObligation::assume("ssl", "ss_input_low == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "mf_def",
        "mode_fault == if configured_as_master == 1 && ss_input_low == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("fault", "mode_fault == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI mode fault: master + SS low → fault");
}

#[test]
fn transfer_complete_count() {
    let mut ctx = VerificationContext::new();
    for v in &["requested_frames", "transferred_frames", "remaining"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("rf", "requested_frames == 100"));
    ctx.push_obligation(ProofObligation::assume("tf", "transferred_frames == 75"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "remaining == requested_frames - transferred_frames",
    ));
    ctx.push_obligation(ProofObligation::assert("is_25", "remaining == 25"));
    ctx.push_obligation(ProofObligation::assert(
        "progress",
        "transferred_frames > 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI: 100-75=25 frames remaining");
}
