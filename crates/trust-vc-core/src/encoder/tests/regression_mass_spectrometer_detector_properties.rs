// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn mass_range() {
    let mut ctx = VerificationContext::new();
    for v in &["mz_ratio", "min_mz", "max_mz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("mz_ok", i32_ty());
    // Max mass-to-charge ratio (m/z) in amu/e
    ctx.push_obligation(ProofObligation::assume("mr", "mz_ratio == 2000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_mz == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_mz == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "mo_def",
        "mz_ok == if mz_ratio >= min_mz && mz_ratio <= max_mz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "mz_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MS: m/z 2000 in [100, 100000] range -> OK");
}

#[test]
fn resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["mass_res", "min_res", "max_res"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("res_ok", i32_ty());
    // Mass resolution in amu (unit mass = 1 amu)
    ctx.push_obligation(ProofObligation::assume("mr", "mass_res == 1000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_res == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_res == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "res_ok == if mass_res >= min_res && mass_res <= max_res { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "res_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MS: resolution 1000 in [1, 100000] -> OK");
}

#[test]
fn analyzer_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("analyzer", u32_ty());
    ctx.declare_var_typed("valid_analyzer", i32_ty());
    // 1=quadrupole, 2=time-of-flight, 3=ion trap, 4=magnetic sector, 5=orbitrap
    ctx.push_obligation(ProofObligation::assume("at", "analyzer == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "va_def",
        "valid_analyzer == if analyzer == 1 || analyzer == 2 || analyzer == 3 || analyzer == 4 || analyzer == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_analyzer == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MS: quadrupole is valid analyzer type");
}

#[test]
fn ionization_method() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ionization", u32_ty());
    ctx.declare_var_typed("valid_ionization", i32_ty());
    // 1=electron impact (EI), 2=chemical ionization (CI), 3=electrospray (ESI), 4=MALDI
    ctx.push_obligation(ProofObligation::assume("im", "ionization == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vi_def",
        "valid_ionization == if ionization == 1 || ionization == 2 || ionization == 3 || ionization == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_ionization == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MS: electron impact is valid ionization method");
}

#[test]
fn scan_speed() {
    let mut ctx = VerificationContext::new();
    for v in &["scans_per_sec", "min_scan", "max_scan"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("scan_ok", i32_ty());
    // Scans per second
    ctx.push_obligation(ProofObligation::assume("ss", "scans_per_sec == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_scan == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_scan == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "scan_ok == if scans_per_sec >= min_scan && scans_per_sec <= max_scan { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "scan_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MS: 10 scans/sec in [1, 10000] -> OK");
}

#[test]
fn sensitivity() {
    let mut ctx = VerificationContext::new();
    for v in &["detect_limit_ppb", "max_detect_ppb"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sens_ok", i32_ty());
    // Detection limit in parts per billion
    ctx.push_obligation(ProofObligation::assume("dl", "detect_limit_ppb == 1"));
    ctx.push_obligation(ProofObligation::assume("md", "max_detect_ppb == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sens_ok == if detect_limit_ppb <= max_detect_ppb { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sens_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MS: 1 ppb detection limit <= 100 ppb max -> OK");
}

#[test]
fn dynamic_range() {
    let mut ctx = VerificationContext::new();
    for v in &["range_x10", "min_range_x10", "max_range_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("range_ok", i32_ty());
    // Orders of magnitude x10: 60 = 6.0 decades, range 30-100 (3.0-10.0)
    ctx.push_obligation(ProofObligation::assume("rx", "range_x10 == 60"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_range_x10 == 30"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_range_x10 == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "range_ok == if range_x10 >= min_range_x10 && range_x10 <= max_range_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "range_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "MS: 6.0 decades dynamic range in [3.0, 10.0] -> OK",
    );
}

#[test]
fn vacuum_level() {
    let mut ctx = VerificationContext::new();
    for v in &["vacuum_mpa", "max_vacuum_mpa"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vacuum_ok", i32_ty());
    // Vacuum pressure in millipascal
    ctx.push_obligation(ProofObligation::assume("vm", "vacuum_mpa == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_vacuum_mpa == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vacuum_ok == if vacuum_mpa <= max_vacuum_mpa { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vacuum_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MS: 1 mPa vacuum <= 100 mPa max -> OK");
}

#[test]
fn detector_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", u32_ty());
    ctx.declare_var_typed("valid_detector", i32_ty());
    // 1=electron multiplier, 2=Faraday cup, 3=microchannel plate, 4=photomultiplier
    ctx.push_obligation(ProofObligation::assume("dt", "detector == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_detector == if detector == 1 || detector == 2 || detector == 3 || detector == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_detector == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MS: electron multiplier is valid detector type");
}

#[test]
fn mass_accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_ppm", "max_accuracy_ppm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Mass accuracy in parts per million
    ctx.push_obligation(ProofObligation::assume("ap", "accuracy_ppm == 5"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_accuracy_ppm == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_ppm <= max_accuracy_ppm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MS: 5 ppm mass accuracy <= 50 ppm max -> OK");
}
