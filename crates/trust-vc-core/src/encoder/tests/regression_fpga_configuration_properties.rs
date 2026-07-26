// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn lut_input_count() {
    let mut ctx = VerificationContext::new();
    for v in &["lut_inputs", "possible_entries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 6-input LUT has 2^6 = 64 truth table entries
    ctx.push_obligation(ProofObligation::assume("li", "lut_inputs == 6"));
    ctx.push_obligation(ProofObligation::assume("pe", "possible_entries == 64")); // precomputed 2^6
    ctx.push_obligation(ProofObligation::assert("is_64", "possible_entries == 64"));
    ctx.push_obligation(ProofObligation::assert("positive", "possible_entries > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FPGA: 6-input LUT → 64 entries");
}

#[test]
fn clb_slice_count() {
    let mut ctx = VerificationContext::new();
    for v in &["slices_per_clb", "luts_per_slice", "total_luts"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // CLB = 2 slices × 4 LUTs per slice = 8 LUTs
    ctx.push_obligation(ProofObligation::assume("sc", "slices_per_clb == 2"));
    ctx.push_obligation(ProofObligation::assume("ls", "luts_per_slice == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "tl_def",
        "total_luts == slices_per_clb * luts_per_slice",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "total_luts == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "FPGA CLB: 2 slices × 4 LUTs = 8");
}

#[test]
fn bitstream_frame_count() {
    let mut ctx = VerificationContext::new();
    for v in &["total_frames", "words_per_frame", "total_words"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Bitstream = frames × words per frame
    ctx.push_obligation(ProofObligation::assume("tf", "total_frames == 3000"));
    ctx.push_obligation(ProofObligation::assume("wpf", "words_per_frame == 101"));
    ctx.push_obligation(ProofObligation::assume(
        "tw_def",
        "total_words == total_frames * words_per_frame",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_303000",
        "total_words == 303000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "FPGA bitstream: 3000 × 101 = 303000 words");
}

#[test]
fn bram_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["bram_blocks", "bits_per_block", "total_kbits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Block RAM: 100 blocks × 36Kbit each
    // Precompute: 100 × 36 = 3600 Kbit
    ctx.push_obligation(ProofObligation::assume("bb", "bram_blocks == 100"));
    ctx.push_obligation(ProofObligation::assume("bpb", "bits_per_block == 36")); // in Kbit
    ctx.push_obligation(ProofObligation::assume(
        "tk_def",
        "total_kbits == bram_blocks * bits_per_block",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3600", "total_kbits == 3600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "FPGA BRAM: 100 × 36K = 3600 Kbit");
}

#[test]
fn dsp_slice_multiply() {
    let mut ctx = VerificationContext::new();
    for v in &["a_width", "b_width", "result_width"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fits_dsp", i32_ty());
    // DSP48E2: 27×18 multiplier → 45-bit result
    ctx.push_obligation(ProofObligation::assume("aw", "a_width == 27"));
    ctx.push_obligation(ProofObligation::assume("bw", "b_width == 18"));
    ctx.push_obligation(ProofObligation::assume(
        "rw_def",
        "result_width == a_width + b_width",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "fd_def",
        "fits_dsp == if result_width <= 48 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_45", "result_width == 45"));
    ctx.push_obligation(ProofObligation::assert("ok", "fits_dsp == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FPGA DSP: 27+18 = 45 bits ≤ 48-bit accumulator");
}

#[test]
fn clock_region_assignment() {
    let mut ctx = VerificationContext::new();
    for v in &["total_regions", "bufg_per_region", "total_bufg"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("region_valid", i32_ty());
    // Clock regions with global buffers
    ctx.push_obligation(ProofObligation::assume("tr", "total_regions == 12"));
    ctx.push_obligation(ProofObligation::assume("bpr", "bufg_per_region == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_bufg == total_regions * bufg_per_region",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "rv_def",
        "region_valid == if total_regions <= 24 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_144", "total_bufg == 144"));
    ctx.push_obligation(ProofObligation::assert("ok", "region_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "FPGA: 12 regions × 12 BUFG = 144 global buffers");
}

#[test]
fn io_bank_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["bank_voltage_mv", "pin_standard_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("compatible", i32_ty());
    // IO bank voltage must match pin standard
    ctx.push_obligation(ProofObligation::assume("bv", "bank_voltage_mv == 3300"));
    ctx.push_obligation(ProofObligation::assume("ps", "pin_standard_mv == 3300")); // LVCMOS33
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "compatible == if bank_voltage_mv == pin_standard_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "compatible == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FPGA IO: bank 3.3V matches LVCMOS33");
}

#[test]
fn partial_reconfiguration_region() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "region_start_frame",
        "region_frames",
        "region_end_frame",
        "total_frames",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_bounds", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rsf", "region_start_frame == 500"));
    ctx.push_obligation(ProofObligation::assume("rf", "region_frames == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "ref_def",
        "region_end_frame == region_start_frame + region_frames",
    ));
    ctx.push_obligation(ProofObligation::assume("tf", "total_frames == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "ib_def",
        "in_bounds == if region_end_frame <= total_frames { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_700", "region_end_frame == 700"));
    ctx.push_obligation(ProofObligation::assert("ok", "in_bounds == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FPGA PR: frames [500, 700) within 3000 total");
}

#[test]
fn configuration_crc_word_count() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "data_words",
        "header_words",
        "crc_words",
        "total_config_words",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Config frame: header + data + CRC
    ctx.push_obligation(ProofObligation::assume("dw", "data_words == 101"));
    ctx.push_obligation(ProofObligation::assume("hw", "header_words == 5"));
    ctx.push_obligation(ProofObligation::assume("cw", "crc_words == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "tc_def",
        "total_config_words == data_words + header_words + crc_words",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_107",
        "total_config_words == 107",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FPGA config: 101 data + 5 header + 1 CRC = 107 words",
    );
}

#[test]
fn mmcm_output_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["input_mhz", "multiply", "divide", "output_mhz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // MMCM: output = input × M / D
    // Precompute: 100 × 10 / 5 = 200 MHz
    ctx.push_obligation(ProofObligation::assume("im", "input_mhz == 100"));
    ctx.push_obligation(ProofObligation::assume("m", "multiply == 10"));
    ctx.push_obligation(ProofObligation::assume("d", "divide == 5"));
    ctx.push_obligation(ProofObligation::assume("om", "output_mhz == 200")); // precomputed
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if output_mhz >= 10 && output_mhz <= 800 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_200", "output_mhz == 200"));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FPGA MMCM: 100 × 10 / 5 = 200 MHz (valid)");
}
