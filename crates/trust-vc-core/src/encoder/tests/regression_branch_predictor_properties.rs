// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn two_bit_counter_saturating_increment() {
    let mut ctx = VerificationContext::new();
    for v in &["old_counter", "new_counter", "max_val"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("oc", "old_counter == 2"));
    ctx.push_obligation(ProofObligation::assume("mv", "max_val == 3")); // 2-bit: 0-3
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "new_counter == if old_counter < max_val { old_counter + 1 } else { max_val }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "new_counter == 3"));
    ctx.push_obligation(ProofObligation::assert("bounded", "new_counter <= max_val"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "2-bit counter: 2 → 3 (saturating)");
}

#[test]
fn two_bit_counter_saturating_decrement() {
    let mut ctx = VerificationContext::new();
    for v in &["old_counter", "new_counter"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("oc", "old_counter == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "new_counter == if old_counter > 0 { old_counter - 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_0", "new_counter == 0"));
    ctx.push_obligation(ProofObligation::assert("non_neg", "new_counter >= 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "2-bit counter: 1 → 0 (saturating)");
}

#[test]
fn prediction_from_counter_msb() {
    // Counter >= 2 → predict taken, < 2 → predict not taken
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("counter", u32_ty());
    ctx.declare_var_typed("predict_taken", i32_ty());
    ctx.push_obligation(ProofObligation::assume("c", "counter == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "pt_def",
        "predict_taken == if counter >= 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("taken", "predict_taken == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "predict: counter=3 >= 2 → taken");
}

#[test]
fn btb_hit_provides_target() {
    let mut ctx = VerificationContext::new();
    for v in &["pc", "btb_tag", "btb_target", "predicted_target"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("p", "pc == 4096"));
    ctx.push_obligation(ProofObligation::assume("bt", "btb_tag == 4096")); // hit
    ctx.push_obligation(ProofObligation::assume("btar", "btb_target == 8192"));
    ctx.push_obligation(ProofObligation::assume(
        "pt_def",
        "predicted_target == if pc == btb_tag { btb_target } else { pc + 4 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_8192",
        "predicted_target == 8192",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BTB hit: PC=4096, target=8192");
}

#[test]
fn btb_miss_falls_through() {
    let mut ctx = VerificationContext::new();
    for v in &["pc", "btb_tag", "btb_target", "predicted_target"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("p", "pc == 4096"));
    ctx.push_obligation(ProofObligation::assume("bt", "btb_tag == 5000")); // miss
    ctx.push_obligation(ProofObligation::assume("btar", "btb_target == 8192"));
    ctx.push_obligation(ProofObligation::assume(
        "pt_def",
        "predicted_target == if pc == btb_tag { btb_target } else { pc + 4 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_4100",
        "predicted_target == 4100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BTB miss: PC=4096, fall through to 4100");
}

#[test]
fn gshare_index_computation() {
    // GShare: index = PC XOR global_history
    let mut ctx = VerificationContext::new();
    for v in &["pc_low_bits", "global_history", "table_index", "table_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pl", "pc_low_bits == 10"));
    ctx.push_obligation(ProofObligation::assume("gh", "global_history == 6"));
    ctx.push_obligation(ProofObligation::assume(
        "ti_def",
        "table_index == pc_low_bits ^ global_history",
    ));
    ctx.push_obligation(ProofObligation::assume("ts", "table_size == 16"));
    // 10 XOR 6 = 12
    ctx.push_obligation(ProofObligation::assert("is_12", "table_index == 12"));
    ctx.push_obligation(ProofObligation::assert(
        "within",
        "table_index < table_size",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "GShare: 10 XOR 6 = 12, within table[16]");
}

#[test]
fn global_history_shift() {
    let mut ctx = VerificationContext::new();
    for v in &["old_history", "outcome", "new_history", "history_mask"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Shift left by 1, insert new outcome bit
    ctx.push_obligation(ProofObligation::assume("oh", "old_history == 5")); // binary: 0101
    ctx.push_obligation(ProofObligation::assume("o", "outcome == 1")); // taken
    ctx.push_obligation(ProofObligation::assume("hm", "history_mask == 15")); // 4-bit history
    ctx.push_obligation(ProofObligation::assume(
        "nh_def",
        "new_history == ((old_history << 1) | outcome) & history_mask",
    ));
    // (5 << 1) | 1 = 11, 11 & 15 = 11
    ctx.push_obligation(ProofObligation::assert("is_11", "new_history == 11"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "history: (0101 << 1) | 1 = 1011");
}

#[test]
fn misprediction_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["total_branches", "mispredictions", "rate_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tb", "total_branches == 10000"));
    ctx.push_obligation(ProofObligation::assume("mp", "mispredictions == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "rp_def",
        "rate_pct == mispredictions * 100 / total_branches",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "rate_pct == 3")); // 3%
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "misprediction: 300/10000 = 3%");
}

#[test]
fn return_address_stack_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["calls", "returns", "ras_depth", "max_depth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("overflow", i32_ty());
    ctx.push_obligation(ProofObligation::assume("c", "calls == 12"));
    ctx.push_obligation(ProofObligation::assume("r", "returns == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "rd_def",
        "ras_depth == calls - returns",
    ));
    ctx.push_obligation(ProofObligation::assume("md", "max_depth == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "of_def",
        "overflow == if ras_depth > max_depth { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "ras_depth == 4"));
    ctx.push_obligation(ProofObligation::assert("no_overflow", "overflow == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RAS: 12-8=4 depth < max 16");
}

#[test]
fn tournament_predictor_selection() {
    // Tournament: meta-predictor selects between local and global predictors
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("local_prediction", u32_ty());
    ctx.declare_var_typed("global_prediction", u32_ty());
    ctx.declare_var_typed("meta_counter", u32_ty());
    ctx.declare_var_typed("final_prediction", u32_ty());
    ctx.push_obligation(ProofObligation::assume("lp", "local_prediction == 1")); // taken
    ctx.push_obligation(ProofObligation::assume("gp", "global_prediction == 0")); // not taken
    ctx.push_obligation(ProofObligation::assume("mc", "meta_counter == 3")); // >= 2 → prefer global
    ctx.push_obligation(ProofObligation::assume(
        "fp_def",
        "final_prediction == if meta_counter >= 2 { global_prediction } else { local_prediction }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_0", "final_prediction == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tournament: meta=3 → use global prediction (0)");
}
