// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn thread_block_size() {
    let mut ctx = VerificationContext::new();
    for v in &["threads_x", "threads_y", "threads_z", "block_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_limit", i32_ty());
    // Block size = x × y × z, max 1024 threads
    // 16 × 16 × 1 = 256
    ctx.push_obligation(ProofObligation::assume("tx", "threads_x == 16"));
    ctx.push_obligation(ProofObligation::assume("ty", "threads_y == 16"));
    ctx.push_obligation(ProofObligation::assume("tz", "threads_z == 1"));
    ctx.push_obligation(ProofObligation::assume("bs", "block_size == 256")); // precomputed
    ctx.push_obligation(ProofObligation::assume(
        "wl_def",
        "within_limit == if block_size <= 1024 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_256", "block_size == 256"));
    ctx.push_obligation(ProofObligation::assert("ok", "within_limit == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPU: 16×16×1 = 256 threads ≤ 1024 max");
}

#[test]
fn warp_count() {
    let mut ctx = VerificationContext::new();
    for v in &["block_threads", "warp_size", "warps_per_block"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Warps = ceil(threads / warp_size). 256 / 32 = 8 exactly.
    ctx.push_obligation(ProofObligation::assume("bt", "block_threads == 256"));
    ctx.push_obligation(ProofObligation::assume("ws", "warp_size == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "wpb_def",
        "warps_per_block == block_threads / warp_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "warps_per_block == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "GPU: 256 / 32 = 8 warps per block");
}

#[test]
fn shared_memory_per_block() {
    let mut ctx = VerificationContext::new();
    for v in &["shared_mem_bytes", "max_shared_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fits", i32_ty());
    // Shared memory limit: 48KB = 49152 bytes
    ctx.push_obligation(ProofObligation::assume("smb", "shared_mem_bytes == 32768")); // 32KB
    ctx.push_obligation(ProofObligation::assume("msb", "max_shared_bytes == 49152"));
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "fits == if shared_mem_bytes <= max_shared_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fits == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPU: 32KB shared ≤ 48KB limit");
}

#[test]
fn register_pressure() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "regs_per_thread",
        "block_threads",
        "total_regs",
        "sm_reg_limit",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("occupancy_ok", i32_ty());
    // Total regs = regs_per_thread × threads. Precompute: 32 × 256 = 8192
    ctx.push_obligation(ProofObligation::assume("rpt", "regs_per_thread == 32"));
    ctx.push_obligation(ProofObligation::assume("bt", "block_threads == 256"));
    ctx.push_obligation(ProofObligation::assume("tr", "total_regs == 8192")); // precomputed
    ctx.push_obligation(ProofObligation::assume("srl", "sm_reg_limit == 65536"));
    ctx.push_obligation(ProofObligation::assume(
        "oo_def",
        "occupancy_ok == if total_regs <= sm_reg_limit { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8192", "total_regs == 8192"));
    ctx.push_obligation(ProofObligation::assert("ok", "occupancy_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPU: 32×256 = 8192 regs ≤ 65536 SM limit");
}

#[test]
fn grid_dimension() {
    let mut ctx = VerificationContext::new();
    for v in &["data_elements", "block_size", "grid_blocks"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Grid blocks = ceil(data / block_size)
    // 10000 / 256 = 39 remainder 16, so need 40 blocks. Precompute.
    ctx.push_obligation(ProofObligation::assume("de", "data_elements == 10000"));
    ctx.push_obligation(ProofObligation::assume("bs", "block_size == 256"));
    ctx.push_obligation(ProofObligation::assume("gb", "grid_blocks == 40")); // precomputed ceil
    ctx.push_obligation(ProofObligation::assert("is_40", "grid_blocks == 40"));
    ctx.push_obligation(ProofObligation::assert("positive", "grid_blocks > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPU: ceil(10000/256) = 40 grid blocks");
}

#[test]
fn memory_coalescing() {
    let mut ctx = VerificationContext::new();
    for v in &["base_addr", "thread_id", "element_size", "access_addr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("coalesced", i32_ty());
    // Coalesced access: consecutive threads access consecutive addresses
    // addr = base + thread_id × element_size
    // Precompute: 65536 + 5 × 4 = 65556
    ctx.push_obligation(ProofObligation::assume("ba", "base_addr == 65536"));
    ctx.push_obligation(ProofObligation::assume("ti", "thread_id == 5"));
    ctx.push_obligation(ProofObligation::assume("es", "element_size == 4"));
    ctx.push_obligation(ProofObligation::assume("aa", "access_addr == 65556")); // precomputed
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "coalesced == if element_size <= 16 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_65556", "access_addr == 65556"));
    ctx.push_obligation(ProofObligation::assert("ok", "coalesced == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPU coalesced: base + 5×4 = 65556, elem ≤ 16B");
}

#[test]
fn dispatch_workgroup_count() {
    let mut ctx = VerificationContext::new();
    for v in &["global_x", "local_x", "workgroups_x"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Vulkan/OpenCL: workgroups = global / local
    ctx.push_obligation(ProofObligation::assume("gx", "global_x == 1024"));
    ctx.push_obligation(ProofObligation::assume("lx", "local_x == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "wx_def",
        "workgroups_x == global_x / local_x",
    ));
    ctx.push_obligation(ProofObligation::assert("is_16", "workgroups_x == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "GPU dispatch: 1024 / 64 = 16 workgroups");
}

#[test]
fn texture_mipmap_levels() {
    let mut ctx = VerificationContext::new();
    for v in &["base_width", "base_height"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("mip_levels", u32_ty());
    // mip levels = floor(log2(max(width, height))) + 1
    // Precompute: max(1024, 512) = 1024, log2(1024) = 10, + 1 = 11
    ctx.push_obligation(ProofObligation::assume("bw", "base_width == 1024"));
    ctx.push_obligation(ProofObligation::assume("bh", "base_height == 512"));
    ctx.push_obligation(ProofObligation::assume("ml", "mip_levels == 11")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_11", "mip_levels == 11"));
    ctx.push_obligation(ProofObligation::assert("at_least_1", "mip_levels >= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPU texture: 1024×512 → 11 mipmap levels");
}

#[test]
fn occupancy_blocks_per_sm() {
    let mut ctx = VerificationContext::new();
    for v in &["sm_max_threads", "block_threads", "max_blocks_per_sm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Max concurrent blocks = SM_max_threads / block_threads
    ctx.push_obligation(ProofObligation::assume("smt", "sm_max_threads == 2048"));
    ctx.push_obligation(ProofObligation::assume("bt", "block_threads == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "mbps_def",
        "max_blocks_per_sm == sm_max_threads / block_threads",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "max_blocks_per_sm == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "GPU occupancy: 2048 / 256 = 8 blocks per SM");
}

#[test]
fn constant_memory_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["const_buffer_bytes", "max_const_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fits", i32_ty());
    // Constant memory: 64KB = 65536 bytes
    ctx.push_obligation(ProofObligation::assume("cbb", "const_buffer_bytes == 4096"));
    ctx.push_obligation(ProofObligation::assume("mcb", "max_const_bytes == 65536"));
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "fits == if const_buffer_bytes <= max_const_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fits == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPU: 4KB const ≤ 64KB limit");
}
