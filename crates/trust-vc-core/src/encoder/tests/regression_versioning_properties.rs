// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn semver_major_bump() {
    let mut ctx = VerificationContext::new();
    for v in &["major", "minor", "patch", "new_major"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("maj", "major == 2"));
    ctx.push_obligation(ProofObligation::assume("min", "minor == 3"));
    ctx.push_obligation(ProofObligation::assume("p", "patch == 1"));
    ctx.push_obligation(ProofObligation::assume("nm_def", "new_major == major + 1"));
    ctx.push_obligation(ProofObligation::assert("is_3", "new_major == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "semver major bump: 2.3.1 → 3.x.x");
}

#[test]
fn semver_minor_resets_patch() {
    let mut ctx = VerificationContext::new();
    for v in &["minor", "patch", "new_minor", "new_patch"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("min", "minor == 5"));
    ctx.push_obligation(ProofObligation::assume("p", "patch == 3"));
    ctx.push_obligation(ProofObligation::assume("nm_def", "new_minor == minor + 1"));
    ctx.push_obligation(ProofObligation::assume("np_def", "new_patch == 0"));
    ctx.push_obligation(ProofObligation::assert("minor_up", "new_minor == 6"));
    ctx.push_obligation(ProofObligation::assert("patch_reset", "new_patch == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "minor bump: x.5.3 → x.6.0");
}

#[test]
fn version_ordering() {
    // 1.2.3 < 1.3.0 (minor wins over patch)
    let mut ctx = VerificationContext::new();
    for v in &[
        "a_major", "a_minor", "a_patch", "b_major", "b_minor", "b_patch",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("a_less_than_b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("am", "a_major == 1"));
    ctx.push_obligation(ProofObligation::assume("ami", "a_minor == 2"));
    ctx.push_obligation(ProofObligation::assume("ap", "a_patch == 3"));
    ctx.push_obligation(ProofObligation::assume("bm", "b_major == 1"));
    ctx.push_obligation(ProofObligation::assume("bmi", "b_minor == 3"));
    ctx.push_obligation(ProofObligation::assume("bp", "b_patch == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "lt_def",
        "a_less_than_b == if a_major < b_major { 1 } else { if a_major == b_major && a_minor < b_minor { 1 } else { if a_major == b_major && a_minor == b_minor && a_patch < b_patch { 1 } else { 0 } } }",
    ));
    ctx.push_obligation(ProofObligation::assert("ordered", "a_less_than_b == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1.2.3 < 1.3.0");
}

#[test]
fn compatibility_same_major() {
    let mut ctx = VerificationContext::new();
    for v in &["lib_major", "app_major"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("compatible", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lm", "lib_major == 2"));
    ctx.push_obligation(ProofObligation::assume("am", "app_major == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "compatible == if lib_major == app_major { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("compat", "compatible == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "same major version → compatible");
}

#[test]
fn monotonic_version_sequence() {
    let mut ctx = VerificationContext::new();
    for v in &["v1", "v2", "v3"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v1_val", "v1 == 100"));
    ctx.push_obligation(ProofObligation::assume("v2_def", "v2 == v1 + 1"));
    ctx.push_obligation(ProofObligation::assume("v3_def", "v3 == v2 + 1"));
    ctx.push_obligation(ProofObligation::assert("mono", "v1 < v2 && v2 < v3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "versions: 100 < 101 < 102");
}

#[test]
fn prerelease_less_than_release() {
    // 1.0.0-alpha < 1.0.0 (prerelease has lower precedence)
    let mut ctx = VerificationContext::new();
    for v in &["release_val", "prerelease_val"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("rv", "release_val == 100")); // 1.0.0 encoded
    ctx.push_obligation(ProofObligation::assume("pv", "prerelease_val == 99")); // 1.0.0-alpha < 1.0.0
    ctx.push_obligation(ProofObligation::assert(
        "less",
        "prerelease_val < release_val",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "prerelease 99 < release 100");
}

#[test]
fn revision_count_from_tag() {
    let mut ctx = VerificationContext::new();
    for v in &["tag_rev", "commits_since", "current_rev"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tr", "tag_rev == 1000"));
    ctx.push_obligation(ProofObligation::assume("cs", "commits_since == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "cr_def",
        "current_rev == tag_rev + commits_since",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1015", "current_rev == 1015"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "revision: tag 1000 + 15 commits = 1015");
}

#[test]
fn api_version_header() {
    let mut ctx = VerificationContext::new();
    for v in &["requested_version", "min_supported", "max_supported"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("supported", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rv", "requested_version == 3"));
    ctx.push_obligation(ProofObligation::assume("ms", "min_supported == 2"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_supported == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "supported == if requested_version >= min_supported && requested_version <= max_supported { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_supported", "supported == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "API v3 in supported range [2, 5]");
}

#[test]
fn deprecation_window() {
    let mut ctx = VerificationContext::new();
    for v in &["deprecated_at", "removal_at", "current_version"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("still_available", i32_ty());
    ctx.push_obligation(ProofObligation::assume("da", "deprecated_at == 3"));
    ctx.push_obligation(ProofObligation::assume("ra", "removal_at == 5"));
    ctx.push_obligation(ProofObligation::assume("cv", "current_version == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "sa_def",
        "still_available == if current_version < removal_at { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("available", "still_available == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "v4 < removal at v5 → still available");
}

#[test]
fn feature_flag_version_gate() {
    let mut ctx = VerificationContext::new();
    for v in &["app_version", "feature_min_version"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("feature_enabled", i32_ty());
    ctx.push_obligation(ProofObligation::assume("av", "app_version == 10"));
    ctx.push_obligation(ProofObligation::assume("fmv", "feature_min_version == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "fe_def",
        "feature_enabled == if app_version >= feature_min_version { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("enabled", "feature_enabled == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "app v10 >= feature min v8 → enabled");
}
