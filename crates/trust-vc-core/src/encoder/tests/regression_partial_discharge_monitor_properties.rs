// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn detection_method() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det_method", u32_ty());
    ctx.declare_var_typed("valid_det", i32_ty());
    // PD detection methods: 1=electrical (coupling capacitor), 2=UHF, 3=acoustic, 4=TEV
    ctx.push_obligation(ProofObligation::assume("dm_val", "det_method == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "dm_def",
        "valid_det == if det_method == 1 || det_method == 2 || det_method == 3 || det_method == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("dm_chk", "valid_det == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detection method 1 (electrical/coupling capacitor) is valid IEC 60270 type",
    );
}

#[test]
fn sensitivity() {
    let mut ctx = VerificationContext::new();
    for v in &["pc_val", "pc_min", "pc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // PD sensitivity in picocoulombs: value 500, valid range 1 to 50000
    ctx.push_obligation(ProofObligation::assume("sn_val", "pc_val == 500"));
    ctx.push_obligation(ProofObligation::assume("sn_min", "pc_min == 1"));
    ctx.push_obligation(ProofObligation::assume("sn_max", "pc_max == 50000"));
    ctx.push_obligation(ProofObligation::assert(
        "sn_in_range",
        "pc_val >= pc_min && pc_val <= pc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PD sensitivity 500 pC in range [1,50000]");
}

#[test]
fn bandwidth() {
    let mut ctx = VerificationContext::new();
    for v in &["bw_khz", "bw_min", "bw_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Measurement bandwidth in kHz: value 300000, valid range 100 to 3000000 (100 kHz to 3 GHz for UHF)
    ctx.push_obligation(ProofObligation::assume("bw_val", "bw_khz == 300000"));
    ctx.push_obligation(ProofObligation::assume("bw_min", "bw_min == 100"));
    ctx.push_obligation(ProofObligation::assume("bw_max", "bw_max == 3000000"));
    ctx.push_obligation(ProofObligation::assert(
        "bw_in_range",
        "bw_khz >= bw_min && bw_khz <= bw_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PD bandwidth 300000 kHz in range [100,3000000]");
}

#[test]
fn noise_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["nt_pc", "nt_min", "nt_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Noise rejection threshold in pC: value 50, valid range 1 to 1000
    ctx.push_obligation(ProofObligation::assume("nt_val", "nt_pc == 50"));
    ctx.push_obligation(ProofObligation::assume("nt_min", "nt_min == 1"));
    ctx.push_obligation(ProofObligation::assume("nt_max", "nt_max == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "nt_in_range",
        "nt_pc >= nt_min && nt_pc <= nt_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "noise threshold 50 pC in range [1,1000]");
}

#[test]
fn channel_count() {
    let mut ctx = VerificationContext::new();
    for v in &["ch_cnt", "ch_min", "ch_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // PD measurement channels: value 6, valid range 1 to 12
    ctx.push_obligation(ProofObligation::assume("cc_val", "ch_cnt == 6"));
    ctx.push_obligation(ProofObligation::assume("cc_min", "ch_min == 1"));
    ctx.push_obligation(ProofObligation::assume("cc_max", "ch_max == 12"));
    ctx.push_obligation(ProofObligation::assert(
        "cc_in_range",
        "ch_cnt >= ch_min && ch_cnt <= ch_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PD channel count 6 in range [1,12]");
}

#[test]
fn voltage_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("v_class", u32_ty());
    ctx.declare_var_typed("valid_vc", i32_ty());
    // HV voltage classes in kV: 11, 33, 66, 132 (non-sequential)
    ctx.push_obligation(ProofObligation::assume("vc_val", "v_class == 33"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_vc == if v_class == 11 || v_class == 33 || v_class == 66 || v_class == 132 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("vc_chk", "valid_vc == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "voltage class 33 kV is valid HV insulation class");
}

#[test]
fn sample_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["sr_mhz", "sr_min", "sr_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // PD digitizer sample rate in MHz: value 250, valid range 1 to 5000
    ctx.push_obligation(ProofObligation::assume("sr_val", "sr_mhz == 250"));
    ctx.push_obligation(ProofObligation::assume("sr_min", "sr_min == 1"));
    ctx.push_obligation(ProofObligation::assume("sr_max", "sr_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "sr_in_range",
        "sr_mhz >= sr_min && sr_mhz <= sr_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PD sample rate 250 MHz in range [1,5000]");
}

#[test]
fn prpd_resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["pr_deg", "pr_min", "pr_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Phase-resolved PD resolution in degrees: value 3, valid range 1 to 360
    ctx.push_obligation(ProofObligation::assume("pr_val", "pr_deg == 3"));
    ctx.push_obligation(ProofObligation::assume("pr_min", "pr_min == 1"));
    ctx.push_obligation(ProofObligation::assume("pr_max", "pr_max == 360"));
    ctx.push_obligation(ProofObligation::assert(
        "pr_in_range",
        "pr_deg >= pr_min && pr_deg <= pr_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PRPD resolution 3 degrees in range [1,360]");
}

#[test]
fn communication() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm_type", u32_ty());
    ctx.declare_var_typed("valid_comm", i32_ty());
    // Communication protocols: 1=IEC 61850, 2=Modbus, 3=Ethernet, 4=fiber optic
    ctx.push_obligation(ProofObligation::assume("co_val", "comm_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "valid_comm == if comm_type == 1 || comm_type == 2 || comm_type == 3 || comm_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("co_chk", "valid_comm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "communication 1 (IEC 61850) is valid PD monitor protocol",
    );
}

#[test]
fn alarm_level() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("alarm_lvl", u32_ty());
    ctx.declare_var_typed("valid_alarm", i32_ty());
    // PD alarm levels: 1=normal, 2=attention, 3=critical
    ctx.push_obligation(ProofObligation::assume("al_val", "alarm_lvl == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "al_def",
        "valid_alarm == if alarm_lvl == 1 || alarm_lvl == 2 || alarm_lvl == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("al_chk", "valid_alarm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "alarm level 2 (attention) is valid PD alarm state");
}
