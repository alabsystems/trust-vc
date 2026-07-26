// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn spray_distance_bounded() {
    // Spray distance in mm, bounded [50, 500]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("distance", u32_ty());
    ctx.declare_var_typed("dist_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("d", "distance == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dist_ok == if distance >= 50 && distance <= 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dist_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thermal spray: 300mm distance in [50, 500] range");
}

#[test]
fn particle_velocity_bounded() {
    // Particle velocity in m/s, bounded [100, 2000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("velocity", u32_ty());
    ctx.declare_var_typed("vel_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("v", "velocity == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vel_ok == if velocity >= 100 && velocity <= 2000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vel_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Thermal spray: 500 m/s velocity in [100, 2000] range",
    );
}

#[test]
fn coating_thickness_scaled_bounded() {
    // Coating thickness scaled x10 um: 300.0um -> 3000, bounded [50, 50000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("thick_x10", u32_ty());
    ctx.declare_var_typed("thick_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tx", "thick_x10 == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "thick_ok == if thick_x10 >= 50 && thick_x10 <= 50000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "thick_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Thermal spray: 300.0um thickness (x10) in [50, 50000] range",
    );
}

#[test]
fn spray_process_four_way_disjunction() {
    // 1=plasma, 2=HVOF, 3=flame, 4=cold spray
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("process", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_process",
        "process == 1 || process == 2 || process == 3 || process == 4",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "process >= 1 && process <= 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Thermal spray: process {1=plasma,2=HVOF,3=flame,4=cold} implies [1,4] bounds",
    );
}

#[test]
fn feed_type_three_way_disjunction() {
    // 1=powder, 2=wire, 3=rod
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_feed",
        "feed_type == 1 || feed_type == 2 || feed_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "feed_type >= 1 && feed_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Thermal spray: feed type {1=powder,2=wire,3=rod} implies [1,3] bounds",
    );
}

#[test]
fn gas_flow_bounded() {
    // Gas flow rate in L/min, bounded [10, 200]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas_flow", u32_ty());
    ctx.declare_var_typed("flow_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("gf", "gas_flow == 80"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "flow_ok == if gas_flow >= 10 && gas_flow <= 200 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "flow_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Thermal spray: 80 L/min gas flow in [10, 200] range",
    );
}

#[test]
fn traverse_speed_bounded() {
    // Traverse speed in mm/s, bounded [50, 2000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", u32_ty());
    ctx.declare_var_typed("speed_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("s", "speed == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "speed_ok == if speed >= 50 && speed <= 2000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "speed_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Thermal spray: 500 mm/s traverse speed in [50, 2000] range",
    );
}

#[test]
fn substrate_temp_bounded() {
    // Substrate temperature in deg C, bounded [50, 500] (all positive, no offset)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sub_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "sub_temp >= 50 && sub_temp <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "sub_temp >= 50"));
    ctx.push_obligation(ProofObligation::assert("upper", "sub_temp <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Thermal spray: substrate temp (deg C) in [50, 500] implies bounds",
    );
}

#[test]
fn powder_feed_rate_scaled_bounded() {
    // Powder feed rate scaled x10 g/min: 50.0 g/min -> 500, bounded [10, 2000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed_x10", u32_ty());
    ctx.declare_var_typed("feed_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fx", "feed_x10 == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "fdo_def",
        "feed_ok == if feed_x10 >= 10 && feed_x10 <= 2000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "feed_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Thermal spray: 50.0 g/min feed rate (x10) in [10, 2000] range",
    );
}

#[test]
fn robot_controlled_boolean_flag() {
    // Boolean flag encoded as i32: 0=manual, 1=robot controlled
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.declare_var_typed("robot_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_is_bool",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("f", "flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ra_def",
        "robot_active == if flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "robot_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Thermal spray: robot controlled flag propagates correctly",
    );
}
