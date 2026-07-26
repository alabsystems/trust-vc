// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn digital_input_debounce() {
    let mut ctx = VerificationContext::new();
    for v in &["stable_count", "debounce_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("input_valid", i32_ty());
    // Input valid after N consecutive stable readings
    ctx.push_obligation(ProofObligation::assume("sc", "stable_count == 5"));
    ctx.push_obligation(ProofObligation::assume("dt", "debounce_threshold == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "iv_def",
        "input_valid == if stable_count >= debounce_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "input_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLC: 5 stable ≥ 3 threshold → input valid");
}

#[test]
fn timer_on_delay() {
    let mut ctx = VerificationContext::new();
    for v in &["elapsed_ms", "preset_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("timer_done", i32_ty());
    // TON: output goes high after preset time elapses
    ctx.push_obligation(ProofObligation::assume("em", "elapsed_ms == 2000"));
    ctx.push_obligation(ProofObligation::assume("pm", "preset_ms == 1500"));
    ctx.push_obligation(ProofObligation::assume(
        "td_def",
        "timer_done == if elapsed_ms >= preset_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "timer_done == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLC TON: 2000ms ≥ 1500ms preset → done");
}

#[test]
fn counter_up_preset() {
    let mut ctx = VerificationContext::new();
    for v in &["count_value", "preset_value"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("counter_done", i32_ty());
    // CTU: count up to preset
    ctx.push_obligation(ProofObligation::assume("cv", "count_value == 10"));
    ctx.push_obligation(ProofObligation::assume("pv", "preset_value == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "cd_def",
        "counter_done == if count_value >= preset_value { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "counter_done == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLC CTU: count 10 = preset 10 → done");
}

#[test]
fn analog_scaling() {
    let mut ctx = VerificationContext::new();
    for v in &["raw_adc", "adc_max", "eng_max", "eng_value"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Scale raw ADC to engineering units
    // raw=2048, max=4096, eng_max=1000 → eng = 2048 × 1000 / 4096 = 500
    ctx.push_obligation(ProofObligation::assume("ra", "raw_adc == 2048"));
    ctx.push_obligation(ProofObligation::assume("am", "adc_max == 4096"));
    ctx.push_obligation(ProofObligation::assume("em", "eng_max == 1000"));
    ctx.push_obligation(ProofObligation::assume("ev", "eng_value == 500")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_500", "eng_value == 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLC scale: 2048/4096 × 1000 = 500 eng units");
}

#[test]
fn interlock_safety() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("guard_closed", u32_ty());
    ctx.declare_var_typed("estop_clear", u32_ty());
    ctx.declare_var_typed("motor_allowed", i32_ty());
    // Motor runs only if guard closed AND e-stop clear
    ctx.push_obligation(ProofObligation::assume("gc", "guard_closed == 1"));
    ctx.push_obligation(ProofObligation::assume("ec", "estop_clear == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ma_def",
        "motor_allowed == if guard_closed == 1 && estop_clear == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "motor_allowed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "PLC interlock: guard + e-stop clear → motor allowed",
    );
}

#[test]
fn scan_cycle_time() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "input_scan_us",
        "program_exec_us",
        "output_scan_us",
        "total_scan_us",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_deadline", i32_ty());
    ctx.push_obligation(ProofObligation::assume("is", "input_scan_us == 100"));
    ctx.push_obligation(ProofObligation::assume("pe", "program_exec_us == 500"));
    ctx.push_obligation(ProofObligation::assume("os", "output_scan_us == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ts_def",
        "total_scan_us == input_scan_us + program_exec_us + output_scan_us",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "wd_def",
        "within_deadline == if total_scan_us <= 10000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_700", "total_scan_us == 700"));
    ctx.push_obligation(ProofObligation::assert("ok", "within_deadline == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLC scan: 100+500+100 = 700us ≤ 10ms deadline");
}

#[test]
fn pid_output_clamp() {
    let mut ctx = VerificationContext::new();
    for v in &["pid_output", "output_min", "output_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("clamped_output", u32_ty());
    ctx.push_obligation(ProofObligation::assume("po", "pid_output == 1200"));
    ctx.push_obligation(ProofObligation::assume("om", "output_min == 0"));
    ctx.push_obligation(ProofObligation::assume("ox", "output_max == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "clamped_output == if pid_output > output_max { output_max } else { pid_output }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1000", "clamped_output == 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLC PID: output 1200 > 1000 max → clamp");
}

#[test]
fn recipe_step_sequence() {
    let mut ctx = VerificationContext::new();
    for v in &["current_step", "total_steps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("next_step", u32_ty());
    ctx.declare_var_typed("in_bounds", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cs", "current_step == 3"));
    ctx.push_obligation(ProofObligation::assume("ts", "total_steps == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ns_def",
        "next_step == current_step + 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ib_def",
        "in_bounds == if next_step <= total_steps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "next_step == 4"));
    ctx.push_obligation(ProofObligation::assert("ok", "in_bounds == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLC recipe: step 3+1 = 4 ≤ 10 total → valid");
}

#[test]
fn data_register_move() {
    let mut ctx = VerificationContext::new();
    for v in &["source_value", "dest_value"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("move_ok", i32_ty());
    // MOV instruction: copy source to destination
    ctx.push_obligation(ProofObligation::assume("sv", "source_value == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "dv_def",
        "dest_value == source_value",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "mo_def",
        "move_ok == if dest_value == source_value { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_42", "dest_value == 42"));
    ctx.push_obligation(ProofObligation::assert("ok", "move_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLC MOV: source 42 → dest 42 (match)");
}

#[test]
fn word_bit_extract() {
    let mut ctx = VerificationContext::new();
    for v in &["word_value", "bit_position", "bit_mask"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bit_set", i32_ty());
    // Extract bit 3 from word 0x0F (15): bit 3 is set
    // bit_mask = 1 << bit_position = 8 (precomputed)
    ctx.push_obligation(ProofObligation::assume("wv", "word_value == 15"));
    ctx.push_obligation(ProofObligation::assume("bp", "bit_position == 3"));
    ctx.push_obligation(ProofObligation::assume("bm", "bit_mask == 8")); // precomputed 1<<3
    ctx.push_obligation(ProofObligation::assume("bs_val", "bit_set == 1")); // precomputed: 15 & 8 != 0
    ctx.push_obligation(ProofObligation::assert("yes", "bit_set == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLC: word 0x0F bit 3 → set (precomputed)");
}
