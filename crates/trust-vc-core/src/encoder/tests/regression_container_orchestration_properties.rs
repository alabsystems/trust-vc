// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn pod_replica_count() {
    let mut ctx = VerificationContext::new();
    for v in &["desired_replicas", "running_replicas", "pending_replicas"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("needs_scaling", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dr", "desired_replicas == 5"));
    ctx.push_obligation(ProofObligation::assume("rr", "running_replicas == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "pr_def",
        "pending_replicas == desired_replicas - running_replicas",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ns_def",
        "needs_scaling == if running_replicas < desired_replicas { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2", "pending_replicas == 2"));
    ctx.push_obligation(ProofObligation::assert("yes", "needs_scaling == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "k8s: 3 running < 5 desired → scale up 2");
}

#[test]
fn resource_request_fit() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "node_cpu_milli",
        "used_cpu_milli",
        "request_cpu_milli",
        "available_cpu_milli",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fits", i32_ty());
    ctx.push_obligation(ProofObligation::assume("nc", "node_cpu_milli == 4000")); // 4 cores
    ctx.push_obligation(ProofObligation::assume("uc", "used_cpu_milli == 2500"));
    ctx.push_obligation(ProofObligation::assume(
        "ac_def",
        "available_cpu_milli == node_cpu_milli - used_cpu_milli",
    ));
    ctx.push_obligation(ProofObligation::assume("rc", "request_cpu_milli == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "fits == if request_cpu_milli <= available_cpu_milli { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_1500",
        "available_cpu_milli == 1500",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "fits == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "k8s: 500m request ≤ 1500m available → fits");
}

#[test]
fn memory_limit_enforcement() {
    let mut ctx = VerificationContext::new();
    for v in &["container_mem_mb", "limit_mb"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("oom_kill", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cm", "container_mem_mb == 600"));
    ctx.push_obligation(ProofObligation::assume("lm", "limit_mb == 512"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "oom_kill == if container_mem_mb > limit_mb { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "oom_kill == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "k8s: 600MB > 512MB limit → OOM kill");
}

#[test]
fn rolling_update_progress() {
    let mut ctx = VerificationContext::new();
    for v in &["total_replicas", "updated_replicas", "max_unavailable"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("available_replicas", u32_ty());
    ctx.declare_var_typed("meets_availability", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tr", "total_replicas == 10"));
    ctx.push_obligation(ProofObligation::assume("ur", "updated_replicas == 3"));
    ctx.push_obligation(ProofObligation::assume("mu", "max_unavailable == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ar_def",
        "available_replicas == total_replicas - max_unavailable",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ma_def",
        "meets_availability == if available_replicas >= total_replicas - max_unavailable { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "available_replicas == 8"));
    ctx.push_obligation(ProofObligation::assert("ok", "meets_availability == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "k8s rolling: 10 - 2 unavailable = 8 available");
}

#[test]
fn service_endpoint_count() {
    let mut ctx = VerificationContext::new();
    for v in &["ready_pods", "not_ready_pods", "total_endpoints"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("rp", "ready_pods == 4"));
    ctx.push_obligation(ProofObligation::assume("nrp", "not_ready_pods == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "te_def",
        "total_endpoints == ready_pods",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "total_endpoints == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "k8s service: 4 ready pods → 4 endpoints");
}

#[test]
fn hpa_target_replicas() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "current_cpu_percent",
        "target_cpu_percent",
        "current_replicas",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("target_replicas", u32_ty());
    // HPA: target = ceil(current_replicas × current_util / target_util)
    // Precompute: ceil(3 × 80 / 50) = ceil(4.8) = 5
    ctx.push_obligation(ProofObligation::assume("ccp", "current_cpu_percent == 80"));
    ctx.push_obligation(ProofObligation::assume("tcp", "target_cpu_percent == 50"));
    ctx.push_obligation(ProofObligation::assume("cr", "current_replicas == 3"));
    ctx.push_obligation(ProofObligation::assume("trp", "target_replicas == 5")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_5", "target_replicas == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "scaled_up",
        "target_replicas > current_replicas",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "k8s HPA: 80%/50% × 3 = 5 target replicas");
}

#[test]
fn namespace_resource_quota() {
    let mut ctx = VerificationContext::new();
    for v in &["used_pods", "new_pods", "total_pods", "quota_pods"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_quota", i32_ty());
    ctx.push_obligation(ProofObligation::assume("up", "used_pods == 8"));
    ctx.push_obligation(ProofObligation::assume("np", "new_pods == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "tp_def",
        "total_pods == used_pods + new_pods",
    ));
    ctx.push_obligation(ProofObligation::assume("qp", "quota_pods == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "wq_def",
        "within_quota == if total_pods <= quota_pods { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10", "total_pods == 10"));
    ctx.push_obligation(ProofObligation::assert("ok", "within_quota == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "k8s quota: 8 + 2 = 10 pods ≤ 20 limit");
}

#[test]
fn node_taint_toleration() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("node_taint", u32_ty());
    ctx.declare_var_typed("pod_toleration", u32_ty());
    ctx.declare_var_typed("can_schedule", i32_ty());
    // Pod scheduled only if it tolerates node's taint
    ctx.push_obligation(ProofObligation::assume("nt", "node_taint == 1")); // NoSchedule
    ctx.push_obligation(ProofObligation::assume("pt", "pod_toleration == 1")); // matches
    ctx.push_obligation(ProofObligation::assume(
        "cs_def",
        "can_schedule == if node_taint == pod_toleration { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_schedule == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "k8s: pod toleration matches node taint → schedule");
}

#[test]
fn liveness_probe_failure() {
    let mut ctx = VerificationContext::new();
    for v in &["consecutive_failures", "failure_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("restart_container", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cf", "consecutive_failures == 4"));
    ctx.push_obligation(ProofObligation::assume("ft", "failure_threshold == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "rc_def",
        "restart_container == if consecutive_failures >= failure_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "restart_container == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "k8s probe: 4 failures ≥ 3 threshold → restart");
}

#[test]
fn persistent_volume_claim() {
    let mut ctx = VerificationContext::new();
    for v in &["pvc_request_gb", "pv_capacity_gb"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("satisfies", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pr", "pvc_request_gb == 50"));
    ctx.push_obligation(ProofObligation::assume("pc", "pv_capacity_gb == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "satisfies == if pv_capacity_gb >= pvc_request_gb { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "satisfies == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "k8s PVC: 100GB PV ≥ 50GB request → bound");
}
