// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_flow_range_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["flow_lpm", "min_flow", "max_flow"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // Flow rate 500 L/min within [1, 50000]
    ctx.push_obligation(ProofObligation::assume("fl", "flow_lpm == 500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_flow == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_flow == 50000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if flow_lpm >= min_flow && flow_lpm <= max_flow { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Ultrasonic flow: 500 L/min in [1, 50000] range");
}

#[test]
fn test_accuracy_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x100", "min_accuracy", "max_accuracy"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // Accuracy 0.50% (×100 = 50) within [10, 500] i.e. 0.10% to 5.00%
    ctx.push_obligation(ProofObligation::assume("ac", "accuracy_x100 == 50"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_accuracy == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_accuracy == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if accuracy_x100 >= min_accuracy && accuracy_x100 <= max_accuracy { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Ultrasonic flow: accuracy 0.50% in [0.10%, 5.00%]");
}

#[test]
fn test_measurement_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // 1=transit-time, 2=Doppler, 3=hybrid
    ctx.push_obligation(ProofObligation::assume("mt", "meas_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if meas_type == 1 || meas_type == 2 || meas_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Ultrasonic flow: transit-time is valid measurement type (1|2|3)",
    );
}

#[test]
fn test_pipe_size_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["pipe_mm", "min_pipe", "max_pipe"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // Pipe 100mm within [15, 3000]
    ctx.push_obligation(ProofObligation::assume("ps", "pipe_mm == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_pipe == 15"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_pipe == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if pipe_mm >= min_pipe && pipe_mm <= max_pipe { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Ultrasonic flow: 100mm pipe in [15, 3000] range");
}

#[test]
fn test_path_count_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("path_count", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // 1=single-path, 2=dual-path, 3=multi-path, 4=clamp-on
    ctx.push_obligation(ProofObligation::assume("pc", "path_count == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if path_count == 1 || path_count == 2 || path_count == 3 || path_count == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Ultrasonic flow: dual-path is valid path count (1|2|3|4)",
    );
}

#[test]
fn test_fluid_temp_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp", "max_temp"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // 25C + 500 offset = 525. Range: 260 (-240C) to 1000 (500C)
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 525"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp == 260"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if temp_offset >= min_temp && temp_offset <= max_temp { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Ultrasonic flow: 25C (offset 525) in [260, 1000] temp range",
    );
}

#[test]
fn test_output_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // 1=4-20mA, 2=pulse, 3=frequency, 4=digital
    ctx.push_obligation(ProofObligation::assume("ot", "output_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if output_type == 1 || output_type == 2 || output_type == 3 || output_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Ultrasonic flow: frequency is valid output type (1|2|3|4)",
    );
}

#[test]
fn test_reynolds_number_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["reynolds", "min_re", "max_re"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // Reynolds 4000 within [2000, 100000] (turbulent flow regime)
    ctx.push_obligation(ProofObligation::assume("re", "reynolds == 4000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_re == 2000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_re == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if reynolds >= min_re && reynolds <= max_re { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Ultrasonic flow: Re 4000 in [2000, 100000] turbulent range",
    );
}

#[test]
fn test_transducer_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_khz", "min_freq", "max_freq"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // Transducer 1000 kHz within [100, 4000]
    ctx.push_obligation(ProofObligation::assume("fk", "freq_khz == 1000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq == 4000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if freq_khz >= min_freq && freq_khz <= max_freq { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Ultrasonic flow: 1000 kHz transducer in [100, 4000] range",
    );
}

#[test]
fn test_bidirectional_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bidirectional", i32_ty());
    ctx.declare_var_typed("can_measure_reverse", i32_ty());
    // Boolean flag: 1=bidirectional enabled
    ctx.push_obligation(ProofObligation::assume("bd", "bidirectional == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "cmr_def",
        "can_measure_reverse == if bidirectional == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_measure_reverse == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Ultrasonic flow: bidirectional=1 enables reverse measurement",
    );
}
