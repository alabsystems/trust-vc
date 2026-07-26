// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn longest_prefix_match() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "route_a_prefix_len",
        "route_b_prefix_len",
        "selected_prefix_len",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ra", "route_a_prefix_len == 16"));
    ctx.push_obligation(ProofObligation::assume("rb", "route_b_prefix_len == 24"));
    ctx.push_obligation(ProofObligation::assume(
        "sel_def",
        "selected_prefix_len == if route_b_prefix_len > route_a_prefix_len { route_b_prefix_len } else { route_a_prefix_len }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_24",
        "selected_prefix_len == 24",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "longest prefix: /24 > /16 → select /24");
}

#[test]
fn route_metric_selection() {
    let mut ctx = VerificationContext::new();
    for v in &["metric_a", "metric_b", "selected_metric"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ma", "metric_a == 100")); // OSPF cost
    ctx.push_obligation(ProofObligation::assume("mb", "metric_b == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "sm_def",
        "selected_metric == if metric_b < metric_a { metric_b } else { metric_a }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_50", "selected_metric == 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "lower metric: 50 < 100 → select 50");
}

#[test]
fn hop_count_increment() {
    let mut ctx = VerificationContext::new();
    for v in &["incoming_hops", "outgoing_hops"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ih", "incoming_hops == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "oh_def",
        "outgoing_hops == incoming_hops + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "outgoing_hops == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "hop count: 3 + 1 = 4");
}

#[test]
fn ttl_decrement_at_hop() {
    let mut ctx = VerificationContext::new();
    for v in &["ttl_in", "ttl_out"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("should_forward", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ti", "ttl_in == 64"));
    ctx.push_obligation(ProofObligation::assume("to_def", "ttl_out == ttl_in - 1"));
    ctx.push_obligation(ProofObligation::assume(
        "sf_def",
        "should_forward == if ttl_out > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("forward", "should_forward == 1"));
    ctx.push_obligation(ProofObligation::assert("is_63", "ttl_out == 63"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TTL: 64 → 63, still > 0 → forward");
}

#[test]
fn route_aggregation() {
    // Two /25 routes aggregate to one /24
    let mut ctx = VerificationContext::new();
    for v in &[
        "route_count_before",
        "route_count_after",
        "aggregated_prefix",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("rcb", "route_count_before == 2"));
    ctx.push_obligation(ProofObligation::assume("rca_def", "route_count_after == 1"));
    ctx.push_obligation(ProofObligation::assume("ap", "aggregated_prefix == 24")); // /25 + /25 → /24
    ctx.push_obligation(ProofObligation::assert(
        "fewer",
        "route_count_after < route_count_before",
    ));
    ctx.push_obligation(ProofObligation::assert("wider", "aggregated_prefix < 25"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "aggregate: 2×/25 → 1×/24");
}

#[test]
fn ecmp_load_distribution() {
    // Equal-cost multi-path: traffic split across N paths
    let mut ctx = VerificationContext::new();
    for v in &["total_traffic", "num_paths", "per_path"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tt", "total_traffic == 1000"));
    ctx.push_obligation(ProofObligation::assume("np", "num_paths == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "pp_def",
        "per_path == total_traffic / num_paths",
    ));
    ctx.push_obligation(ProofObligation::assert("is_250", "per_path == 250"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "ECMP: 1000 / 4 = 250 per path");
}

#[test]
fn administrative_distance_preference() {
    let mut ctx = VerificationContext::new();
    for v in &["ospf_ad", "bgp_ad", "static_ad", "preferred_ad"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("oa", "ospf_ad == 110"));
    ctx.push_obligation(ProofObligation::assume("ba", "bgp_ad == 20"));
    ctx.push_obligation(ProofObligation::assume("sa", "static_ad == 1"));
    // Prefer lowest AD
    ctx.push_obligation(ProofObligation::assume(
        "pa_def",
        "preferred_ad == if static_ad < bgp_ad && static_ad < ospf_ad { static_ad } else { bgp_ad }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_static", "preferred_ad == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AD preference: static(1) < BGP(20) < OSPF(110)");
}

#[test]
fn route_table_entry_count() {
    let mut ctx = VerificationContext::new();
    for v in &["entries_before", "added", "removed", "entries_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("eb", "entries_before == 500"));
    ctx.push_obligation(ProofObligation::assume("a", "added == 10"));
    ctx.push_obligation(ProofObligation::assume("r", "removed == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ea_def",
        "entries_after == entries_before + added - removed",
    ));
    ctx.push_obligation(ProofObligation::assert("is_507", "entries_after == 507"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "routes: 500 + 10 - 3 = 507");
}

#[test]
fn default_route_fallback() {
    let mut ctx = VerificationContext::new();
    for v in &["specific_routes", "default_prefix"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("use_default", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sr", "specific_routes == 0")); // no match
    ctx.push_obligation(ProofObligation::assume("dp", "default_prefix == 0")); // /0
    ctx.push_obligation(ProofObligation::assume(
        "ud_def",
        "use_default == if specific_routes == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("fallback", "use_default == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "no specific routes → use default");
}

#[test]
fn convergence_timer() {
    let mut ctx = VerificationContext::new();
    for v in &["hold_down", "elapsed", "remaining"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("converged", i32_ty());
    ctx.push_obligation(ProofObligation::assume("hd", "hold_down == 180")); // seconds
    ctx.push_obligation(ProofObligation::assume("e", "elapsed == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "converged == if elapsed >= hold_down { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("done", "converged == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "200s >= 180s hold-down → converged");
}
