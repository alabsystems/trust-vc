// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn image_header_magic() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("header_magic", u32_ty());
    ctx.declare_var_typed("expected_magic", u32_ty());
    ctx.declare_var_typed("valid_header", i32_ty());
    ctx.push_obligation(ProofObligation::assume("hm", "header_magic == 305419896")); // 0x12345678
    ctx.push_obligation(ProofObligation::assume("em", "expected_magic == 305419896"));
    ctx.push_obligation(ProofObligation::assume(
        "vh_def",
        "valid_header == if header_magic == expected_magic { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_header == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "boot: magic 0x12345678 matches → valid header");
}

#[test]
fn image_size_bounds() {
    let mut ctx = VerificationContext::new();
    for v in &["image_size", "min_size", "max_flash_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("size_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("is", "image_size == 65536")); // 64KB
    ctx.push_obligation(ProofObligation::assume("mn", "min_size == 1024")); // at least 1KB
    ctx.push_obligation(ProofObligation::assume("mf", "max_flash_size == 524288")); // 512KB
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "size_ok == if image_size >= min_size && image_size <= max_flash_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "size_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "boot: 64KB in [1KB, 512KB] → size valid");
}

#[test]
fn vector_table_stack_pointer() {
    let mut ctx = VerificationContext::new();
    for v in &["initial_sp", "ram_start", "ram_end"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sp_valid", i32_ty());
    // Initial SP must point within RAM
    ctx.push_obligation(ProofObligation::assume("isp", "initial_sp == 537001984")); // 0x20020000 (RAM top)
    ctx.push_obligation(ProofObligation::assume("rs", "ram_start == 536870912")); // 0x20000000
    ctx.push_obligation(ProofObligation::assume("re", "ram_end == 537001984")); // 0x20020000
    ctx.push_obligation(ProofObligation::assume(
        "sv_def",
        "sp_valid == if initial_sp >= ram_start && initial_sp <= ram_end { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "sp_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "boot: SP 0x20020000 in RAM range → valid");
}

#[test]
fn version_comparison() {
    let mut ctx = VerificationContext::new();
    for v in &["current_major", "current_minor", "new_major", "new_minor"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_upgrade", i32_ty());
    // Only allow firmware upgrade (not downgrade)
    ctx.push_obligation(ProofObligation::assume("cm", "current_major == 2"));
    ctx.push_obligation(ProofObligation::assume("cn", "current_minor == 3"));
    ctx.push_obligation(ProofObligation::assume("nm", "new_major == 2"));
    ctx.push_obligation(ProofObligation::assume("nn", "new_minor == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "iu_def",
        "is_upgrade == if new_major > current_major || (new_major == current_major && new_minor > current_minor) { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_upgrade == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "boot: v2.5 > v2.3 → upgrade allowed");
}

#[test]
fn slot_selection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("slot_a_valid", u32_ty());
    ctx.declare_var_typed("slot_b_valid", u32_ty());
    ctx.declare_var_typed("slot_a_version", u32_ty());
    ctx.declare_var_typed("slot_b_version", u32_ty());
    ctx.declare_var_typed("boot_slot", u32_ty());
    // Dual-slot: boot newest valid slot. Slot 0=A, 1=B
    ctx.push_obligation(ProofObligation::assume("sav", "slot_a_valid == 1"));
    ctx.push_obligation(ProofObligation::assume("sbv", "slot_b_valid == 1"));
    ctx.push_obligation(ProofObligation::assume("saver", "slot_a_version == 3"));
    ctx.push_obligation(ProofObligation::assume("sbver", "slot_b_version == 5")); // newer
    ctx.push_obligation(ProofObligation::assume(
        "bs_def",
        "boot_slot == if slot_b_valid == 1 && slot_b_version > slot_a_version { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_b", "boot_slot == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "boot: slot B (v5) > slot A (v3) → boot B");
}

#[test]
fn crc_integrity_check() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("computed_crc", u32_ty());
    ctx.declare_var_typed("stored_crc", u32_ty());
    ctx.declare_var_typed("integrity_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cc", "computed_crc == 3735928559")); // 0xDEADBEEF
    ctx.push_obligation(ProofObligation::assume("sc", "stored_crc == 3735928559"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "integrity_ok == if computed_crc == stored_crc { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "integrity_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "boot CRC: computed == stored → integrity OK");
}

#[test]
fn secure_boot_chain() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rom_verified", u32_ty());
    ctx.declare_var_typed("bootloader_verified", u32_ty());
    ctx.declare_var_typed("app_verified", u32_ty());
    ctx.declare_var_typed("chain_valid", i32_ty());
    // All stages must be verified for secure boot
    ctx.push_obligation(ProofObligation::assume("rv", "rom_verified == 1"));
    ctx.push_obligation(ProofObligation::assume("bv", "bootloader_verified == 1"));
    ctx.push_obligation(ProofObligation::assume("av", "app_verified == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "cv_def",
        "chain_valid == if rom_verified == 1 && bootloader_verified == 1 && app_verified == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "chain_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "secure boot: all 3 stages verified → chain valid");
}

#[test]
fn watchdog_feed_before_jump() {
    let mut ctx = VerificationContext::new();
    for v in &["watchdog_counter", "feed_value", "new_counter"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Feed watchdog before jumping to application (prevents reset during boot)
    ctx.push_obligation(ProofObligation::assume("wc", "watchdog_counter == 100")); // nearly expired
    ctx.push_obligation(ProofObligation::assume("fv", "feed_value == 10000")); // full reload
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "new_counter == feed_value",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10000", "new_counter == 10000"));
    ctx.push_obligation(ProofObligation::assert("safe", "new_counter > 1000")); // enough time to start app
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "boot: watchdog fed to 10000 before app jump");
}

#[test]
fn flash_bank_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["slot_base", "flash_base", "offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Calculate slot offset from flash base for writing
    ctx.push_obligation(ProofObligation::assume("sb", "slot_base == 134479872")); // 0x08040000
    ctx.push_obligation(ProofObligation::assume("fb", "flash_base == 134217728")); // 0x08000000
    ctx.push_obligation(ProofObligation::assume(
        "o_def",
        "offset == slot_base - flash_base",
    ));
    ctx.push_obligation(ProofObligation::assert("is_262144", "offset == 262144")); // 256KB
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "boot: 0x08040000 - 0x08000000 = 256KB offset");
}

#[test]
fn rollback_protection() {
    let mut ctx = VerificationContext::new();
    for v in &["monotonic_counter", "image_counter"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rollback_allowed", i32_ty());
    // Rollback protection: image counter must be >= monotonic counter
    ctx.push_obligation(ProofObligation::assume("mc", "monotonic_counter == 42"));
    ctx.push_obligation(ProofObligation::assume("ic", "image_counter == 43")); // newer
    ctx.push_obligation(ProofObligation::assume(
        "ra_def",
        "rollback_allowed == if image_counter >= monotonic_counter { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "rollback_allowed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "boot: counter 43 >= 42 → no rollback");
}
