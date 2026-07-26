// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VC-level cache regression tests.
//!
//! Tests the cache infrastructure from #2646:
//! - second identical verification hits cache (no solver work)
//! - changed obligations miss cache
//! - corrupt / truncated / wrong-schema / wrong-fingerprint entries fail open
//! - cache disable flag works
//! - non-verified results are not stored
//! - empty cache directory returns None
//! - variable type change invalidates cache
//! - concurrent store safety (no corruption)
//! - large context round-trips correctly

use crate::encoder::tests::{expect_counterexample, expect_verified};
use crate::encoder::types::VerifyResult;
use crate::encoder::verification::cache::{
    cache_hit_count, cache_miss_count, clear_test_build_source_identity, clear_test_cache_dir,
    reset_cache_counts, reset_test_cache_disable, set_test_build_source_identity,
    set_test_cache_dir, VC_CACHE_DISABLE, VC_CACHE_SCHEMA_VERSION,
};
use crate::encoder::verification::test_hooks::{
    reset_setup_from_prepared_count, setup_from_prepared_count,
};
use crate::encoder::AYEncoder;
use crate::ir::{ConformanceMethodBody, TraitDecl, TraitImplDecl, TraitMethodDecl, TrustVcType};
use crate::prepared_context::prepare_context;
use crate::vc::{DemandInlineConfig, ProofObligation, SolverMode, VerificationContext};

struct CacheTestEnvGuard {
    dir: std::path::PathBuf,
}

impl CacheTestEnvGuard {
    fn install(name: &str) -> Self {
        let dir = std::env::temp_dir().join(name);
        let _ = std::fs::remove_dir_all(&dir);
        set_test_cache_dir(dir.clone());
        Self { dir }
    }
}

impl Drop for CacheTestEnvGuard {
    fn drop(&mut self) {
        VC_CACHE_DISABLE.with(|flag| flag.set(true));
        clear_test_build_source_identity();
        clear_test_cache_dir();
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

fn make_simple_context() -> VerificationContext {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assert("self_eq", "x == x"));
    ctx
}

fn fingerprint_hex_for_context(ctx: &VerificationContext) -> String {
    let prepared = prepare_context(ctx).expect("prepare_context");
    let payload = crate::encoder::verification::cache::fingerprint_payload_for_test(&prepared);
    payload.fingerprint_hex_for_test()
}

/// Build a context whose assertion verifies only when demand-inline retry is
/// enabled. The unrelated trigger keeps the ordinary broadcast path inert.
fn make_demand_inline_only_context(config: DemandInlineConfig) -> VerificationContext {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.declare_helper_function_typed(
        "cache_helper",
        TrustVcType::Int { width: 32 },
        vec![("x".to_string(), TrustVcType::Int { width: 32 })],
    );
    ctx.declare_helper_function_typed(
        "cache_seed",
        TrustVcType::Int { width: 32 },
        vec![("x".to_string(), TrustVcType::Int { width: 32 })],
    );
    ctx.push_obligation(
        ProofObligation::broadcast_assume("__body_axiom_cache_helper", "cache_helper(x) == x + x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["cache_seed(x)".to_string()]]),
    );
    ctx.push_obligation(
        ProofObligation::assert("check_cache_helper", "cache_helper(3) == 6")
            .with_solver_mode(SolverMode::NonlinearArith),
    );
    ctx.set_demand_inline_config(config);
    ctx
}

/// A Verified recovered via demand inlining must not be replayed after the
/// caller disables that retry lane.
#[test]
fn test_demand_inline_policy_change_invalidates_cache() {
    let _cache_dir = CacheTestEnvGuard::install("trust_vc_cache_test_demand_inline_policy");
    reset_test_cache_disable();
    reset_cache_counts();

    let enabled = make_demand_inline_only_context(DemandInlineConfig::new());
    let prime = AYEncoder::verify(&enabled);
    expect_verified(&prime, "enabled demand-inline should prime Verified");
    assert_eq!(cache_miss_count(), 1, "prime run should miss");

    let disabled = make_demand_inline_only_context(DemandInlineConfig::new().with_enabled(false));
    reset_cache_counts();
    let result = AYEncoder::verify(&disabled);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "disabled demand-inline must not receive the stronger policy's cached verdict: {result:?}",
    );
    assert_eq!(cache_hit_count(), 0, "retry-policy change must not hit");
    assert_eq!(cache_miss_count(), 1, "retry-policy change must miss");
}

#[test]
fn test_all_retry_policy_fields_change_fingerprint() {
    let base = make_simple_context();
    let base_fp = fingerprint_hex_for_context(&base);

    let mut disabled = make_simple_context();
    disabled.set_demand_inline_enabled(false);
    assert_ne!(base_fp, fingerprint_hex_for_context(&disabled));

    let mut deeper = make_simple_context();
    deeper.set_demand_inline_depth(2);
    assert_ne!(base_fp, fingerprint_hex_for_context(&deeper));

    let mut wider = make_simple_context();
    wider.set_demand_inline_max_callees(5);
    assert_ne!(base_fp, fingerprint_hex_for_context(&wider));

    let mut skip_cascade = make_simple_context();
    skip_cascade.set_skip_retry_cascade(true);
    assert_ne!(base_fp, fingerprint_hex_for_context(&skip_cascade));
}

#[test]
fn test_loop_entry_scope_and_bounded_len_change_fingerprint() {
    let mut unbounded = VerificationContext::new();
    unbounded.declare_var_typed(
        "items",
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
    );

    let mut bounded = VerificationContext::new();
    bounded.declare_var_typed_bounded(
        "items",
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
        true,
    );
    assert_ne!(
        fingerprint_hex_for_context(&unbounded),
        fingerprint_hex_for_context(&bounded),
        "exec-collection length provenance changes solver assumptions and must change the key"
    );

    let plain = make_simple_context();
    let mut entry_scoped = make_simple_context();
    entry_scoped.set_loop_entry_scope(
        "loop_invariant",
        vec![ProofObligation::assume("entry_x", "x == 0")],
    );
    assert_ne!(
        fingerprint_hex_for_context(&plain),
        fingerprint_hex_for_context(&entry_scoped),
        "loop base-case entry assumptions must participate in the cache key"
    );
}

/// A persistent `Verified` is authority only for the exact verifier source
/// revision that produced it. Package version `1.0.0` remains stable across
/// development commits, so the full build revision must independently key the
/// entry. An unavailable identity must bypass both lookup and storage.
#[test]
fn test_build_source_identity_changes_key_and_unavailable_bypasses_cache() {
    const REV_A: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    const REV_B: &str = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";

    let _cache_dir = CacheTestEnvGuard::install("trust_vc_cache_test_build_source_identity");
    reset_test_cache_disable();
    reset_cache_counts();

    let ctx = make_simple_context();
    set_test_build_source_identity(Some(REV_A));
    let rev_a_fingerprint = fingerprint_hex_for_context(&ctx);
    let prime = AYEncoder::verify(&ctx);
    expect_verified(&prime, "revision A should prime its own cache entry");
    assert_eq!(cache_hit_count(), 0);
    assert_eq!(cache_miss_count(), 1);

    set_test_build_source_identity(Some(REV_B));
    let rev_b_fingerprint = fingerprint_hex_for_context(&ctx);
    assert_ne!(
        rev_a_fingerprint, rev_b_fingerprint,
        "source revision must participate in the VC cache fingerprint"
    );
    reset_cache_counts();
    reset_setup_from_prepared_count();
    let changed_revision = AYEncoder::verify(&ctx);
    expect_verified(
        &changed_revision,
        "revision B should re-solve instead of replaying revision A",
    );
    assert_eq!(cache_hit_count(), 0, "revision change must not cache-hit");
    assert_eq!(cache_miss_count(), 1, "revision change must cache-miss");
    assert!(
        setup_from_prepared_count() >= 1,
        "revision change must reach a fresh solver setup"
    );

    // Returning to A demonstrates that both identities have distinct entries,
    // rather than the revision merely disabling a usable cache key.
    set_test_build_source_identity(Some(REV_A));
    reset_cache_counts();
    reset_setup_from_prepared_count();
    let rev_a_again = AYEncoder::verify(&ctx);
    expect_verified(&rev_a_again, "revision A should recover only its own entry");
    assert_eq!(cache_hit_count(), 1);
    assert_eq!(cache_miss_count(), 0);
    assert_eq!(setup_from_prepared_count(), 0);

    // Missing and mutable-placeholder identities carry no authority. Two
    // identical runs must both solve and neither may create or consume an entry.
    for unavailable in [None, Some("unknown")] {
        set_test_build_source_identity(unavailable);
        reset_cache_counts();
        reset_setup_from_prepared_count();
        for _ in 0..2 {
            let result = AYEncoder::verify(&ctx);
            expect_verified(&result, "unidentified build should still verify fresh");
        }
        assert_eq!(cache_hit_count(), 0, "unidentified build must never hit");
        assert_eq!(
            cache_miss_count(),
            2,
            "each bypass must reach a fresh solve"
        );
        assert!(
            setup_from_prepared_count() >= 2,
            "unidentified build must not skip solver setup"
        );
    }
}

/// Second identical verification should hit cache and NOT bump
/// `setup_from_prepared_count`.
#[test]
fn test_second_identical_verification_hits_cache() {
    // Use a unique cache directory for this test to avoid interference.
    let _cache_dir = CacheTestEnvGuard::install("trust_vc_cache_test_hit");
    reset_test_cache_disable();
    reset_cache_counts();
    reset_setup_from_prepared_count();

    let ctx = make_simple_context();

    // First verification: cache miss, solver runs.
    let result1 = AYEncoder::verify(&ctx);
    expect_verified(
        &result1,
        "test_second_identical_verification_hits_cache (first)",
    );
    let setup_after_first = setup_from_prepared_count();
    assert!(
        setup_after_first >= 1,
        "first verification should run solver setup, got {}",
        setup_after_first
    );
    assert_eq!(cache_miss_count(), 1, "first run should be a cache miss");

    // Second verification: cache hit, no solver.
    reset_setup_from_prepared_count();
    let result2 = AYEncoder::verify(&ctx);
    expect_verified(
        &result2,
        "test_second_identical_verification_hits_cache (second)",
    );
    assert_eq!(
        setup_from_prepared_count(),
        0,
        "second run should hit cache without solver setup"
    );
    assert_eq!(cache_hit_count(), 1, "second run should be a cache hit");
}

/// Changed obligation payload should miss cache.
#[test]
fn test_changed_obligation_misses_cache() {
    let _cache_dir = CacheTestEnvGuard::install("trust_vc_cache_test_miss");
    reset_test_cache_disable();
    reset_cache_counts();

    let ctx1 = make_simple_context();
    let result1 = AYEncoder::verify(&ctx1);
    expect_verified(&result1, "test_changed_obligation_misses_cache (first)");
    assert_eq!(cache_miss_count(), 1);

    // Change the assertion condition.
    let mut ctx2 = VerificationContext::new();
    ctx2.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx2.push_obligation(ProofObligation::assert("self_ge", "x >= x"));

    reset_cache_counts();
    let result2 = AYEncoder::verify(&ctx2);
    expect_verified(&result2, "test_changed_obligation_misses_cache (second)");
    assert_eq!(
        cache_miss_count(),
        1,
        "changed obligation should be a cache miss"
    );
    assert_eq!(
        cache_hit_count(),
        0,
        "changed obligation should NOT hit cache"
    );
}

/// Corrupt cache entries should fail open and verify normally.
#[test]
fn test_corrupt_cache_entry_fails_open() {
    let cache_dir = CacheTestEnvGuard::install("trust_vc_cache_test_corrupt");
    std::fs::create_dir_all(&cache_dir.dir).expect("create test cache dir");
    reset_test_cache_disable();
    reset_cache_counts();

    let ctx = make_simple_context();

    // Compute the fingerprint to know what filename the cache would use.
    // We write garbage to that path.
    let hash_hex = fingerprint_hex_for_context(&ctx);
    let entry_path = cache_dir.dir.join(format!("{hash_hex}.json"));
    std::fs::write(&entry_path, "THIS IS NOT VALID JSON").expect("write corrupt entry");

    reset_setup_from_prepared_count();
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test_corrupt_cache_entry_fails_open");
    assert!(
        setup_from_prepared_count() >= 1,
        "corrupt cache should fall through to solver"
    );
    assert_eq!(
        cache_hit_count(),
        0,
        "corrupt entry should not count as hit"
    );
}

/// Wrong schema version in cache entry should fail open (miss, not error).
#[test]
fn test_wrong_schema_version_fails_open() {
    let cache_dir = CacheTestEnvGuard::install("trust_vc_cache_test_wrong_schema");
    std::fs::create_dir_all(&cache_dir.dir).expect("create test cache dir");
    reset_test_cache_disable();
    reset_cache_counts();

    let ctx = make_simple_context();
    let hash_hex = fingerprint_hex_for_context(&ctx);
    let entry_path = cache_dir.dir.join(format!("{hash_hex}.json"));

    // Write a structurally valid entry but with a future schema version.
    let content = format!(
        "{{\n  \"schema_version\": 99,\n  \"fingerprint\": {:?},\n  \"display_name\": null,\n  \"primary_location\": null,\n  \"result\": \"verified\"\n}}",
        hash_hex,
    );
    std::fs::write(&entry_path, content).expect("write wrong-schema entry");

    reset_setup_from_prepared_count();
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test_wrong_schema_version_fails_open");
    assert!(
        setup_from_prepared_count() >= 1,
        "wrong schema version should fall through to solver"
    );
    assert_eq!(
        cache_hit_count(),
        0,
        "wrong schema version should not count as hit"
    );
}

/// Cache entry with mismatched fingerprint should fail open.
#[test]
fn test_fingerprint_mismatch_fails_open() {
    let cache_dir = CacheTestEnvGuard::install("trust_vc_cache_test_fp_mismatch");
    std::fs::create_dir_all(&cache_dir.dir).expect("create test cache dir");
    reset_test_cache_disable();
    reset_cache_counts();

    let ctx = make_simple_context();
    let hash_hex = fingerprint_hex_for_context(&ctx);
    let entry_path = cache_dir.dir.join(format!("{hash_hex}.json"));

    // Write a valid entry but with a different fingerprint inside the JSON.
    let bogus_fp = "0".repeat(64);
    let content = format!(
        "{{\n  \"schema_version\": {VC_CACHE_SCHEMA_VERSION},\n  \"fingerprint\": {:?},\n  \"display_name\": null,\n  \"primary_location\": null,\n  \"result\": \"verified\"\n}}",
        bogus_fp,
    );
    std::fs::write(&entry_path, content).expect("write fp-mismatch entry");

    reset_setup_from_prepared_count();
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test_fingerprint_mismatch_fails_open");
    assert!(
        setup_from_prepared_count() >= 1,
        "fingerprint mismatch should fall through to solver"
    );
    assert_eq!(
        cache_hit_count(),
        0,
        "fingerprint mismatch should not count as hit"
    );
}

/// store_cache should only persist Verified results; non-Verified results
/// must not produce cache entries.
#[test]
fn test_store_cache_skips_non_verified_results() {
    use crate::encoder::verification::cache::{lookup_cache, store_cache};
    use crate::encoder::UnknownCategory;

    let _cache_dir = CacheTestEnvGuard::install("trust_vc_cache_test_skip_non_verified");
    reset_test_cache_disable();
    reset_cache_counts();

    let vc = make_simple_context();
    let prepared = prepare_context(&vc).expect("prepare_context");

    let non_verified_results = [
        VerifyResult::Counterexample {
            obligation_name: "test".to_string(),
            model: None,
            bindings: vec![],
        },
        VerifyResult::Unknown {
            reason: "timeout".to_string(),
            category: UnknownCategory::Timeout,
        },
        VerifyResult::Error {
            message: "encoding error".to_string(),
        },
    ];

    for result in &non_verified_results {
        store_cache(&prepared, result);
    }

    // Lookup should miss — nothing was stored.
    reset_cache_counts();
    let cached = lookup_cache(&prepared);
    assert!(
        cached.is_none(),
        "non-verified results should not produce cache entries"
    );
    assert_eq!(
        cache_hit_count(),
        0,
        "no hits expected when only non-verified results were stored"
    );
}

/// Truncated JSON (valid prefix but incomplete) should fail open.
#[test]
fn test_truncated_json_fails_open() {
    let cache_dir = CacheTestEnvGuard::install("trust_vc_cache_test_truncated");
    std::fs::create_dir_all(&cache_dir.dir).expect("create test cache dir");
    reset_test_cache_disable();
    reset_cache_counts();

    let ctx = make_simple_context();
    let hash_hex = fingerprint_hex_for_context(&ctx);
    let entry_path = cache_dir.dir.join(format!("{hash_hex}.json"));

    // Write a truncated entry — valid start but cut off mid-field.
    let content = format!(
        "{{\n  \"schema_version\": {VC_CACHE_SCHEMA_VERSION},\n  \"fingerprint\": \"{hash_hex}"
    );
    std::fs::write(&entry_path, content).expect("write truncated entry");

    reset_setup_from_prepared_count();
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test_truncated_json_fails_open");
    assert!(
        setup_from_prepared_count() >= 1,
        "truncated JSON should fall through to solver"
    );
    assert_eq!(
        cache_hit_count(),
        0,
        "truncated entry should not count as hit"
    );
}

/// A truncated entry that already contains every authority-bearing field must
/// still miss. The old prefix parser accepted this complete-looking fragment
/// even though the JSON object was never closed.
#[test]
fn test_truncated_after_verified_result_fails_open() {
    let cache_dir =
        CacheTestEnvGuard::install("trust_vc_cache_test_truncated_after_verified_result");
    std::fs::create_dir_all(&cache_dir.dir).expect("create test cache dir");
    reset_test_cache_disable();
    reset_cache_counts();

    let ctx = make_simple_context();
    let hash_hex = fingerprint_hex_for_context(&ctx);
    let entry_path = cache_dir.dir.join(format!("{hash_hex}.json"));
    let content = format!(
        "{{\n  \"schema_version\": {VC_CACHE_SCHEMA_VERSION},\n  \"fingerprint\": \"{hash_hex}\",\n  \"result\": \"verified\"\n"
    );
    std::fs::write(&entry_path, content).expect("write complete-looking truncated entry");

    reset_setup_from_prepared_count();
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test_truncated_after_verified_result_fails_open");
    assert!(
        setup_from_prepared_count() >= 1,
        "unclosed cache JSON must fall through to the solver"
    );
    assert_eq!(cache_hit_count(), 0, "unclosed cache JSON must not hit");
    assert_eq!(cache_miss_count(), 1, "unclosed cache JSON must miss");
}

/// Duplicate authority fields are malformed rather than first-key-wins. This
/// prevents a concatenated or partially overwritten entry from being reused.
#[test]
fn test_duplicate_result_field_fails_open() {
    let cache_dir = CacheTestEnvGuard::install("trust_vc_cache_test_duplicate_result");
    std::fs::create_dir_all(&cache_dir.dir).expect("create test cache dir");
    reset_test_cache_disable();
    reset_cache_counts();

    let ctx = make_simple_context();
    let hash_hex = fingerprint_hex_for_context(&ctx);
    let entry_path = cache_dir.dir.join(format!("{hash_hex}.json"));
    let content = format!(
        "{{\n  \"schema_version\": {VC_CACHE_SCHEMA_VERSION},\n  \"fingerprint\": \"{hash_hex}\",\n  \"display_name\": null,\n  \"primary_location\": null,\n  \"result\": \"verified\",\n  \"result\": \"counterexample\"\n}}"
    );
    std::fs::write(&entry_path, content).expect("write duplicate-field entry");

    reset_setup_from_prepared_count();
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test_duplicate_result_field_fails_open");
    assert!(
        setup_from_prepared_count() >= 1,
        "duplicate cache fields must fall through to the solver"
    );
    assert_eq!(cache_hit_count(), 0, "duplicate cache fields must not hit");
    assert_eq!(cache_miss_count(), 1, "duplicate cache fields must miss");
}

/// Every line must match the canonical serializer exactly. The previous
/// prefix/suffix shape check accepted several of these malformed entries and
/// then extracted their leading `verified` scalar, bypassing a fresh solve.
#[test]
fn test_noncanonical_or_trailing_cache_material_fails_open() {
    let cache_dir = CacheTestEnvGuard::install("trust_vc_cache_test_noncanonical_material");
    std::fs::create_dir_all(&cache_dir.dir).expect("create test cache dir");
    reset_test_cache_disable();

    let ctx = make_simple_context();
    let hash_hex = fingerprint_hex_for_context(&ctx);
    let entry_path = cache_dir.dir.join(format!("{hash_hex}.json"));
    let malformed = [
        format!(
            "{{\n  \"schema_version\": {VC_CACHE_SCHEMA_VERSION}garbage,\n  \"fingerprint\": \"{hash_hex}\",\n  \"display_name\": null,\n  \"primary_location\": null,\n  \"result\": \"verified\"\n}}"
        ),
        format!(
            "{{\n  \"schema_version\": {VC_CACHE_SCHEMA_VERSION},\n  \"fingerprint\": \"{hash_hex}\" trailing,\n  \"display_name\": null,\n  \"primary_location\": null,\n  \"result\": \"verified\"\n}}"
        ),
        format!(
            "{{\n  \"schema_version\": {VC_CACHE_SCHEMA_VERSION},\n  \"fingerprint\": \"{hash_hex}\",\n  \"display_name\": null, \"extra\": true,\n  \"primary_location\": null,\n  \"result\": \"verified\"\n}}"
        ),
        format!(
            "{{\n  \"schema_version\": {VC_CACHE_SCHEMA_VERSION},\n  \"fingerprint\": \"{hash_hex}\",\n  \"display_name\": null,\n  \"primary_location\": null trailing,\n  \"result\": \"verified\"\n}}"
        ),
        format!(
            "{{\n  \"schema_version\": {VC_CACHE_SCHEMA_VERSION},\n  \"fingerprint\": \"{hash_hex}\",\n  \"display_name\": null,\n  \"primary_location\": null,\n  \"result\": \"verified\" trailing\n}}"
        ),
        format!(
            "{{\n  \"schema_version\": {VC_CACHE_SCHEMA_VERSION},\n  \"fingerprint\": \"{hash_hex}\",\n  \"display_name\": null,\n  \"primary_location\": null,\n  \"result\": \"verified\",\n  \"unknown\": true\n}}"
        ),
        format!(
            "{{\n  \"schema_version\": {VC_CACHE_SCHEMA_VERSION},\n  \"fingerprint\": \"{hash_hex}\",\n  \"primary_location\": null,\n  \"display_name\": null,\n  \"result\": \"verified\"\n}}"
        ),
    ];

    for (index, content) in malformed.into_iter().enumerate() {
        std::fs::write(&entry_path, content)
            .unwrap_or_else(|error| panic!("write malformed entry {index}: {error}"));
        reset_cache_counts();
        reset_setup_from_prepared_count();
        let result = AYEncoder::verify(&ctx);
        expect_verified(
            &result,
            &format!("malformed entry {index} should fall through to a fresh solve"),
        );
        assert_eq!(
            cache_hit_count(),
            0,
            "malformed entry {index} must not authorize a cache hit"
        );
        assert_eq!(cache_miss_count(), 1, "malformed entry {index} must miss");
        assert!(
            setup_from_prepared_count() >= 1,
            "malformed entry {index} must reach solver setup"
        );
    }
}

/// Lookup on an empty (but existing) cache directory returns None gracefully.
#[test]
fn test_lookup_empty_cache_directory_returns_none() {
    use crate::encoder::verification::cache::lookup_cache;

    let cache_dir = CacheTestEnvGuard::install("trust_vc_cache_test_empty_dir");
    std::fs::create_dir_all(&cache_dir.dir).expect("create empty cache dir");
    reset_test_cache_disable();
    reset_cache_counts();

    let vc = make_simple_context();
    let prepared = prepare_context(&vc).expect("prepare_context");

    let cached = lookup_cache(&prepared);
    assert!(
        cached.is_none(),
        "lookup on empty cache directory should return None"
    );
    assert_eq!(
        cache_hit_count(),
        0,
        "empty directory should produce zero hits"
    );
}

/// Changing the variable type (same assertion text) should invalidate cache.
/// This proves the fingerprint includes type information, not just strings.
#[test]
fn test_variable_type_change_invalidates_cache() {
    let _cache_dir = CacheTestEnvGuard::install("trust_vc_cache_test_type_change");
    reset_test_cache_disable();
    reset_cache_counts();

    // First: verify with i32.
    let mut ctx_i32 = VerificationContext::new();
    ctx_i32.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx_i32.push_obligation(ProofObligation::assert("self_eq", "x == x"));
    let result1 = AYEncoder::verify(&ctx_i32);
    expect_verified(
        &result1,
        "test_variable_type_change_invalidates_cache (i32)",
    );
    assert_eq!(cache_miss_count(), 1);

    // Second: same assertion text but with i64 type.
    let mut ctx_i64 = VerificationContext::new();
    ctx_i64.declare_var_typed("x", TrustVcType::Int { width: 64 });
    ctx_i64.push_obligation(ProofObligation::assert("self_eq", "x == x"));

    reset_cache_counts();
    let result2 = AYEncoder::verify(&ctx_i64);
    expect_verified(
        &result2,
        "test_variable_type_change_invalidates_cache (i64)",
    );
    assert_eq!(
        cache_miss_count(),
        1,
        "different variable type should be a cache miss"
    );
    assert_eq!(
        cache_hit_count(),
        0,
        "type change should NOT hit the i32 cache entry"
    );
}

/// Concurrent stores to the same cache key should not corrupt the entry.
/// Both threads write the same verified result; a subsequent lookup must
/// either hit or miss cleanly (no partial/corrupt reads).
#[test]
fn test_concurrent_store_does_not_corrupt() {
    use crate::encoder::verification::cache::{lookup_cache, store_cache};

    let cache_dir = CacheTestEnvGuard::install("trust_vc_cache_test_concurrent");
    std::fs::create_dir_all(&cache_dir.dir).expect("create test cache dir");
    reset_test_cache_disable();

    let vc = make_simple_context();
    let prepared = prepare_context(&vc).expect("prepare_context");
    let verified = VerifyResult::Verified;

    // Spawn multiple threads that all store the same entry.
    let barrier = std::sync::Arc::new(std::sync::Barrier::new(4));
    let handles: Vec<_> = (0..4)
        .map(|_| {
            let prepared_clone = prepared.clone();
            let verified_clone = verified.clone();
            let barrier_clone = barrier.clone();
            // Each thread needs the thread-local cache dir set.
            let dir = cache_dir.dir.clone();
            std::thread::spawn(move || {
                set_test_cache_dir(dir);
                reset_test_cache_disable();
                barrier_clone.wait();
                store_cache(&prepared_clone, &verified_clone);
            })
        })
        .collect();

    for h in handles {
        h.join().expect("thread panicked");
    }

    // After concurrent writes, lookup should succeed cleanly.
    reset_cache_counts();
    let cached = lookup_cache(&prepared);
    assert!(
        cached.is_some(),
        "cache entry should be readable after concurrent stores"
    );
    assert_eq!(
        cache_hit_count(),
        1,
        "post-concurrent-store lookup should count as a hit"
    );
}

/// A context with many variables and obligations should round-trip through
/// the cache correctly (large fingerprint payload).
#[test]
fn test_large_context_round_trips_through_cache() {
    let _cache_dir = CacheTestEnvGuard::install("trust_vc_cache_test_large");
    reset_test_cache_disable();
    reset_cache_counts();

    let mut ctx = VerificationContext::new();
    // Declare 50 variables of varying types.
    for i in 0..50 {
        let width = if i % 2 == 0 { 32 } else { 64 };
        ctx.declare_var_typed(&format!("v{i}"), TrustVcType::Int { width });
    }
    // Add 20 self-equality assertions.
    for i in 0..20 {
        ctx.push_obligation(ProofObligation::assert(
            format!("eq_{i}"),
            format!("v{i} == v{i}"),
        ));
    }

    // First verification: cache miss.
    let result1 = AYEncoder::verify(&ctx);
    expect_verified(
        &result1,
        "test_large_context_round_trips_through_cache (first)",
    );
    assert_eq!(cache_miss_count(), 1, "first run should be a miss");

    // Second verification: cache hit.
    reset_cache_counts();
    reset_setup_from_prepared_count();
    let result2 = AYEncoder::verify(&ctx);
    expect_verified(
        &result2,
        "test_large_context_round_trips_through_cache (second)",
    );
    assert_eq!(
        setup_from_prepared_count(),
        0,
        "large context second run should hit cache without solver"
    );
    assert_eq!(cache_hit_count(), 1, "large context should cache-hit");
}

/// VC_CACHE_DISABLE thread-local flag should bypass cache entirely.
#[test]
fn test_cache_disable_flag() {
    let _cache_dir = CacheTestEnvGuard::install("trust_vc_cache_test_disable");
    reset_cache_counts();

    // Disable cache via thread-local.
    VC_CACHE_DISABLE.with(|flag| flag.set(true));

    let ctx = make_simple_context();
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test_cache_disable_flag (first)");

    // Second run should NOT hit cache because it's disabled.
    reset_setup_from_prepared_count();
    let result2 = AYEncoder::verify(&ctx);
    expect_verified(&result2, "test_cache_disable_flag (second)");
    assert!(
        setup_from_prepared_count() >= 1,
        "with cache disabled, second run should still run solver"
    );
}

#[test]
fn test_cache_file_uses_sha256_hex_filename_and_minimal_entry() {
    let cache_dir = CacheTestEnvGuard::install("trust_vc_cache_test_sha256_file");
    reset_test_cache_disable();
    reset_cache_counts();

    let ctx = make_simple_context();
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "test_cache_file_uses_sha256_hex_filename_and_minimal_entry",
    );

    let hash_hex = fingerprint_hex_for_context(&ctx);
    assert_eq!(hash_hex.len(), 64, "SHA-256 hex digest should be 64 chars");
    assert!(
        hash_hex
            .chars()
            .all(|ch| matches!(ch, '0'..='9' | 'a'..='f')),
        "cache fingerprint should be lowercase hex: {hash_hex}"
    );

    let entry_path = cache_dir.dir.join(format!("{hash_hex}.json"));
    assert!(
        entry_path.exists(),
        "cache entry should be written at {entry_path:?}"
    );

    let content = std::fs::read_to_string(&entry_path).expect("read cache entry");
    assert!(
        content.contains(&format!("\"fingerprint\": \"{hash_hex}\"")),
        "cache entry should store the SHA-256 fingerprint"
    );
    assert!(
        !content.contains("\"canonical_text\""),
        "cache entry should not persist canonical text"
    );
    assert!(
        !content.contains("\"canonical_text_len\""),
        "cache entry should not persist canonical text length"
    );
    assert!(
        !content.contains("\"canonical_text_hash\""),
        "cache entry should not persist canonical text hash"
    );
}

// =====================================================================
// Trait-impl method-body fingerprinting (round-6 cache-key soundness).
//
// The persistent VC cache fingerprint formerly omitted the trait-impl method
// BODY, so a non-conforming impl body could hit a stale `Verified` entry
// computed for a structurally-identical CONFORMING body — skipping the
// conformance pass entirely and returning a false-`Verified`. These tests pin:
//   (1) a body change is a cache MISS and the non-conforming body
//       Counterexamples (no stale false-`Verified`);
//   (2) an IDENTICAL conforming body still HITS (no over-rejection / no
//       spurious miss);
//   (3) the conformance-exempt set is part of the key.
// =====================================================================

/// Build a `VerificationContext` exercising the captured-body conformance path:
/// trait `Valued { fn get_value(&self) -> bool ensures(result) }`, impl for
/// bool binding `concrete_fn`, with `concrete_fn`'s body captured as
/// `body_text`. Everything except `body_text` is identical across calls, so two
/// contexts differing only in the body must (post-fix) fingerprint differently.
fn make_trait_impl_body_context(concrete_fn: &str, body_text: &str) -> VerificationContext {
    let mut ctx = VerificationContext::new();
    ctx.register_trait_decl(TraitDecl {
        name: "CacheValued".to_string(),
        methods: vec![TraitMethodDecl {
            name: "get_value".to_string(),
            params: vec![],
            return_type: TrustVcType::Bool,
            requires: vec![],
            ensures: vec!["result".to_string()],
            has_default: false,
            default_body: None,
            default_ensures: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });
    ctx.register_trait_impl(TraitImplDecl {
        trait_name: "CacheValued".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![("get_value".to_string(), concrete_fn.to_string())],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });
    // Declare the impl-method signature so it lowers, but rely on the captured
    // body (no body axiom) for the conformance binding.
    ctx.declare_helper_function_typed(
        concrete_fn,
        TrustVcType::Bool,
        vec![("self".to_string(), TrustVcType::Bool)],
    );
    ctx.register_trait_impl_method_body(
        concrete_fn.to_string(),
        ConformanceMethodBody::new(body_text, 0),
    );
    ctx.push_obligation(ProofObligation::assert("user_goal", "true"));
    ctx
}

/// CORE SOUNDNESS TEST. Priming the cache with a CONFORMING impl body (`true`)
/// must NOT serve that `Verified` to a NON-conforming body (`false`) that is
/// byte-identical except for the captured body: the differing body yields a cache
/// MISS, and the bad body is REFUTED with a Counterexample — never a stale
/// false-`Verified`.
///
/// ATTRIBUTION: the impl body's verdict now lives on the IMPL's own conformance
/// obligation, not on a sibling function's verdict, so that is where the
/// refutation is asserted (the conformance path is not cached at all, so it
/// cannot serve a stale verdict; the fingerprint guard below still pins that the
/// body text distinguishes the two contexts). Both halves of the original
/// soundness content are preserved: no stale HIT, and the violating body is
/// caught.
#[test]
fn test_trait_impl_body_change_invalidates_cache() {
    let _cache_dir = CacheTestEnvGuard::install("trust_vc_cache_test_trait_body_change");
    reset_test_cache_disable();
    reset_cache_counts();

    // Prime: conforming body `true` verifies and is stored.
    let conforming = make_trait_impl_body_context("CacheBoolImpl__m", "true");
    let prime = AYEncoder::verify(&conforming);
    expect_verified(&prime, "conforming trait-impl body should verify (prime)");
    expect_verified(
        &crate::encoder::tests::context_conformance_verdict(&conforming),
        "conforming trait-impl body should discharge its conformance obligation (prime)",
    );
    assert_eq!(cache_miss_count(), 1, "prime run should be a cache miss");

    // Same struct, trait, impl binding, obligations — ONLY the body differs.
    let nonconforming = make_trait_impl_body_context("CacheBoolImpl__m", "false");

    reset_cache_counts();
    let _ = AYEncoder::verify(&nonconforming);
    assert_eq!(
        cache_hit_count(),
        0,
        "differing impl body must MISS, not hit a stale Verified entry"
    );
    assert_eq!(
        cache_miss_count(),
        1,
        "differing impl body should register as a cache miss"
    );

    // The non-conforming body is refuted where it is now attributed — on the
    // IMPL's own conformance obligation. A `Verified` here would be the cardinal
    // false-verify this test exists to prevent.
    expect_counterexample(
        &crate::encoder::tests::context_conformance_verdict(&nonconforming),
        "a non-conforming impl body must be REFUTED, never served a stale Verified",
    );
}

/// NO OVER-REJECTION. An IDENTICAL conforming impl body must still cache-hit on
/// the second verification — the body-inclusion fix must not introduce spurious
/// misses for genuinely-unchanged conforming code.
#[test]
fn test_identical_trait_impl_body_still_hits_cache() {
    let _cache_dir = CacheTestEnvGuard::install("trust_vc_cache_test_trait_body_identical");
    reset_test_cache_disable();
    reset_cache_counts();
    reset_setup_from_prepared_count();

    let ctx = make_trait_impl_body_context("CacheBoolImpl__same", "true");

    let first = AYEncoder::verify(&ctx);
    expect_verified(&first, "conforming body should verify (first)");
    assert_eq!(cache_miss_count(), 1, "first run should be a cache miss");

    reset_setup_from_prepared_count();
    let ctx2 = make_trait_impl_body_context("CacheBoolImpl__same", "true");
    let second = AYEncoder::verify(&ctx2);
    expect_verified(
        &second,
        "identical conforming body should still verify (second)",
    );
    assert_eq!(
        setup_from_prepared_count(),
        0,
        "identical conforming body should hit cache without solver setup"
    );
    assert_eq!(
        cache_hit_count(),
        1,
        "identical conforming body must still cache-hit"
    );
}

/// The captured impl body must be part of the fingerprint: two contexts that
/// differ ONLY in the body text must produce DIFFERENT fingerprints.
#[test]
fn test_trait_impl_body_changes_fingerprint() {
    let _cache_dir = CacheTestEnvGuard::install("trust_vc_cache_test_trait_body_fp");
    reset_test_cache_disable();

    let conforming = make_trait_impl_body_context("CacheBoolImpl__fp", "true");
    let nonconforming = make_trait_impl_body_context("CacheBoolImpl__fp", "false");

    let fp_a = fingerprint_hex_for_context(&conforming);
    let fp_b = fingerprint_hex_for_context(&nonconforming);
    assert_ne!(
        fp_a, fp_b,
        "trait-impl body text must change the cache fingerprint"
    );
}

/// The conformance-exempt method set must be part of the fingerprint: two
/// contexts differing ONLY in whether a method is conformance-exempt must
/// fingerprint differently (whether conformance runs is decisive).
#[test]
fn test_conformance_exempt_set_changes_fingerprint() {
    let _cache_dir = CacheTestEnvGuard::install("trust_vc_cache_test_exempt_fp");
    reset_test_cache_disable();

    let base = make_trait_impl_body_context("CacheBoolImpl__ex", "true");
    let mut exempt = make_trait_impl_body_context("CacheBoolImpl__ex", "true");
    exempt.register_conformance_exempt_method("CacheBoolImpl__ex".to_string());

    let fp_base = fingerprint_hex_for_context(&base);
    let fp_exempt = fingerprint_hex_for_context(&exempt);
    assert_ne!(
        fp_base, fp_exempt,
        "conformance-exempt status must change the cache fingerprint"
    );
}

/// Every trait record component consumed by generic/default conformance must
/// participate in the cache key. These mutations operate on an already
/// prepared context so each field is isolated from preparation-time coupling.
#[test]
fn test_trait_generic_and_default_metadata_change_fingerprint() {
    let base = prepare_context(&make_trait_impl_body_context(
        "CacheBoolImpl__metadata",
        "true",
    ))
    .expect("trait metadata context should prepare");
    let base_fp = crate::encoder::verification::cache::fingerprint_payload_for_test(&base)
        .fingerprint_hex_for_test();

    let mut trait_generics = base.clone();
    trait_generics
        .trait_decls
        .first_mut()
        .expect("trait declaration")
        .generics = vec!["T".to_string()];
    assert_ne!(
        base_fp,
        crate::encoder::verification::cache::fingerprint_payload_for_test(&trait_generics)
            .fingerprint_hex_for_test(),
        "trait generic parameters must change the cache fingerprint"
    );

    let mut impl_args = base.clone();
    impl_args
        .trait_impl_decls
        .first_mut()
        .expect("trait impl declaration")
        .trait_type_args = vec![TrustVcType::Bool];
    assert_ne!(
        base_fp,
        crate::encoder::verification::cache::fingerprint_payload_for_test(&impl_args)
            .fingerprint_hex_for_test(),
        "impl trait arguments must change the cache fingerprint"
    );

    let mut default_ensures = base.clone();
    default_ensures
        .trait_decls
        .first_mut()
        .expect("trait declaration")
        .methods
        .first_mut()
        .expect("trait method declaration")
        .default_ensures = vec!["result".to_string()];
    assert_ne!(
        base_fp,
        crate::encoder::verification::cache::fingerprint_payload_for_test(&default_ensures)
            .fingerprint_hex_for_test(),
        "default-body ensures must change the cache fingerprint"
    );
}

#[test]
fn test_cache_hit_does_not_require_persisted_canonical_text() {
    let cache_dir = CacheTestEnvGuard::install("trust_vc_cache_test_no_canonical_text");
    std::fs::create_dir_all(&cache_dir.dir).expect("create test cache dir");
    reset_test_cache_disable();

    let ctx = make_simple_context();
    let hash_hex = fingerprint_hex_for_context(&ctx);
    let entry_path = cache_dir.dir.join(format!("{hash_hex}.json"));
    let content = format!(
        "{{\n  \"schema_version\": {VC_CACHE_SCHEMA_VERSION},\n  \"fingerprint\": {:?},\n  \"display_name\": null,\n  \"primary_location\": null,\n  \"result\": \"verified\"\n}}",
        hash_hex,
    );
    std::fs::write(&entry_path, content).expect("write cache entry without canonical text");

    reset_cache_counts();
    reset_setup_from_prepared_count();
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "test_cache_hit_does_not_require_persisted_canonical_text",
    );
    assert_eq!(
        setup_from_prepared_count(),
        0,
        "cache hit should skip solver setup even without canonical text"
    );
    assert_eq!(
        cache_hit_count(),
        1,
        "minimal cache entry should count as hit"
    );
    assert_eq!(
        cache_miss_count(),
        0,
        "minimal cache entry should avoid a miss"
    );
}
