// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn simulation_step() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("step_us", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sv", "step_us == 1000")); // 1ms
    ctx.push_obligation(ProofObligation::assume("lb", "step_us >= 1"));
    ctx.push_obligation(ProofObligation::assume("ub", "step_us <= 1000000"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "step_us >= 1 && step_us <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digital twin: 1000 us step in [1, 1000000]");
}

#[test]
fn model_fidelity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fidelity", u32_ty());
    ctx.declare_var_typed("valid_fidelity", i32_ty());
    // 1=physics-based, 2=data-driven, 3=hybrid, 4=reduced-order
    ctx.push_obligation(ProofObligation::assume("fv", "fidelity == 3")); // hybrid
    ctx.push_obligation(ProofObligation::assume(
        "vf_def",
        "valid_fidelity == if fidelity == 1 || fidelity == 2 || fidelity == 3 || fidelity == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_fidelity == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digital twin: hybrid (3) is valid fidelity mode");
}

#[test]
fn state_variables() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_vars", u32_ty());
    ctx.push_obligation(ProofObligation::assume("nv", "num_vars == 50"));
    ctx.push_obligation(ProofObligation::assume("lb", "num_vars >= 1"));
    ctx.push_obligation(ProofObligation::assume("ub", "num_vars <= 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "num_vars >= 1 && num_vars <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digital twin: 50 state variables in [1, 10000]");
}

#[test]
fn sync_interval() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sync_ms", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sm", "sync_ms == 100"));
    ctx.push_obligation(ProofObligation::assume("lb", "sync_ms >= 10"));
    ctx.push_obligation(ProofObligation::assume("ub", "sync_ms <= 60000"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "sync_ms >= 10 && sync_ms <= 60000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digital twin: 100ms sync interval in [10, 60000]");
}

#[test]
fn prediction_horizon() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("horizon_s", u32_ty());
    ctx.push_obligation(ProofObligation::assume("hs", "horizon_s == 300")); // 5 min
    ctx.push_obligation(ProofObligation::assume("lb", "horizon_s >= 1"));
    ctx.push_obligation(ProofObligation::assume("ub", "horizon_s <= 86400"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "horizon_s >= 1 && horizon_s <= 86400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "digital twin: 300s prediction horizon in [1, 86400]",
    );
}

#[test]
fn sensor_inputs() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_sensors", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ns", "num_sensors == 20"));
    ctx.push_obligation(ProofObligation::assume("lb", "num_sensors >= 1"));
    ctx.push_obligation(ProofObligation::assume("ub", "num_sensors <= 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "num_sensors >= 1 && num_sensors <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digital twin: 20 sensor inputs in [1, 1000]");
}

#[test]
fn update_latency() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("latency_ms", u32_ty());
    ctx.declare_var_typed("latency_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lm", "latency_ms == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "latency_ok == if latency_ms <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "latency_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digital twin: 50ms latency <= 1000ms max");
}

#[test]
fn accuracy_target() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x10", u32_ty());
    ctx.declare_var_typed("accurate_ok", i32_ty());
    // 950 = 95.0%, minimum 900 = 90.0%
    ctx.push_obligation(ProofObligation::assume("ax", "accuracy_x10 == 950"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "accurate_ok == if accuracy_x10 >= 900 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "accurate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digital twin: 95.0% accuracy >= 90.0% minimum");
}

#[test]
fn deployment_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("valid_mode", i32_ty());
    // 1=edge, 2=cloud, 3=hybrid
    ctx.push_obligation(ProofObligation::assume("mv", "mode == 2")); // cloud
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mode == if mode == 1 || mode == 2 || mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digital twin: cloud (2) is valid deployment mode");
}

#[test]
fn anomaly_threshold() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("threshold_x100", u32_ty());
    ctx.declare_var_typed("thresh_ok", i32_ty());
    // 500 = 5.00%, range 100-2000 (1.00-20.00%)
    ctx.push_obligation(ProofObligation::assume("tx", "threshold_x100 == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "thresh_ok == if threshold_x100 >= 100 && threshold_x100 <= 2000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "thresh_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "digital twin: 5.00% anomaly threshold in [1.00%, 20.00%]",
    );
}
