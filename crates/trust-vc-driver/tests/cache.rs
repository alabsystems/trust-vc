// Certified cross-crate proof cache tests — replay a checkable certificate
// instead of re-proving (capability #3).
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Run with: targo --unverified test -p trust-vc-driver --features cache
//
// These tests demonstrate trust-vc's edge over Verus: because a `Verified`
// result carries an ay UNSAT proof that `trust-vc-kernel` re-checks, the *same*
// obligation can be served from a content-addressed cache by REPLAYING the
// kernel-checked certificate — no re-proving. Verus's black-box Z3 verdicts
// carry no such artifact, so a recurring obligation must always be re-sent.
#![cfg(feature = "cache")]

use trust_vc_core::ir::{CompareOp, TrustVcType};
use trust_vc_driver::cache::{verify_with_cache, CacheStatus, CertifiedCache};
use trust_vc_driver::lower::{add, cmp, lit, mul, uint, var, Binding, DriverFn, Outcome};

fn u32t() -> TrustVcType {
    uint(32)
}

/// `fn add_bounds(x,y) requires x<100, y<100 { x+y } ensures result<200`.
/// A real, kernel-checkable obligation: x+y < 100+100 = 200.
fn add_bounds() -> DriverFn {
    DriverFn {
        name: "add_bounds".into(),
        params: vec![Binding::new("x", u32t()), Binding::new("y", u32t())],
        result: Binding::new("result", u32t()),
        requires: vec![
            cmp(CompareOp::Lt, var("x", u32t()), lit(100, u32t())),
            cmp(CompareOp::Lt, var("y", u32t()), lit(100, u32t())),
        ],
        body_value: Some(add(var("x", u32t()), var("y", u32t()), u32t())),
        ensures: vec![cmp(CompareOp::Lt, var("result", u32t()), lit(200, u32t()))],
    }
}

/// A structurally DIFFERENT verified obligation:
/// `fn double_bounds(x) requires x<100 { x*2 } ensures result<200`.
fn double_bounds() -> DriverFn {
    DriverFn {
        name: "double_bounds".into(),
        params: vec![Binding::new("x", u32t())],
        result: Binding::new("result", u32t()),
        requires: vec![cmp(CompareOp::Lt, var("x", u32t()), lit(100, u32t()))],
        body_value: Some(mul(var("x", u32t()), lit(2, u32t()), u32t())),
        ensures: vec![cmp(CompareOp::Lt, var("result", u32t()), lit(200, u32t()))],
    }
}

/// (1) Verify the same function twice. The first call is a `Miss` that runs the
/// solver and stores a kernel-checked certificate; the second is a `Hit` that
/// replays that exact certificate WITHOUT re-running the solver.
#[test]
fn second_verification_is_a_cache_hit_replaying_the_certificate() {
    let f = add_bounds();
    let mut cache = CertifiedCache::new();
    assert_eq!(cache.len(), 0);

    // First time: Miss, real proof, kernel-checked certificate produced.
    let (first, status) = verify_with_cache(&f, &mut cache);
    assert_eq!(status, CacheStatus::Miss);
    assert_eq!(first.outcome, Outcome::Verified);
    let first_cert = first
        .certificate
        .expect("a verified result must carry a proof certificate");
    assert!(
        first_cert.kernel_verified,
        "trust-vc-kernel must independently re-check the ay UNSAT proof"
    );
    assert!(
        !first_cert.alethe.is_empty(),
        "the certificate must carry Alethe proof text"
    );
    assert_eq!(
        cache.len(),
        1,
        "the certificate must be cached after a Miss"
    );

    // Second time: Hit. The certificate is REPLAYED, not re-proved. The cache
    // does not grow, and the replayed certificate preserves kernel_verified and
    // the exact Alethe proof text of the cached artifact.
    let (second, status) = verify_with_cache(&f, &mut cache);
    assert_eq!(
        status,
        CacheStatus::Hit,
        "the second call must be a cache Hit"
    );
    assert_eq!(second.outcome, Outcome::Verified);
    assert_eq!(cache.len(), 1, "a Hit must not add a new cache entry");

    let second_cert = second
        .certificate
        .expect("a Hit must replay the cached certificate");
    assert!(
        second_cert.kernel_verified,
        "the replayed certificate must preserve the kernel_verified flag"
    );
    assert_eq!(
        second_cert.alethe, first_cert.alethe,
        "the replayed certificate must be the same checkable artifact"
    );
    assert_eq!(second_cert.trust_count, first_cert.trust_count);
    assert_eq!(second_cert.hole_count, first_cert.hole_count);
}

/// (2) A structurally different function is a fresh `Miss`: the cache grows to 2
/// rather than colliding with the first entry.
#[test]
fn structurally_different_function_is_a_fresh_miss() {
    let mut cache = CertifiedCache::new();

    let (a, status) = verify_with_cache(&add_bounds(), &mut cache);
    assert_eq!(status, CacheStatus::Miss);
    assert_eq!(a.outcome, Outcome::Verified);
    assert_eq!(cache.len(), 1);

    let (b, status) = verify_with_cache(&double_bounds(), &mut cache);
    assert_eq!(
        status,
        CacheStatus::Miss,
        "a structurally different contract must not collide with the cached one"
    );
    assert_eq!(b.outcome, Outcome::Verified);
    assert_eq!(
        cache.len(),
        2,
        "the second distinct contract grows the cache"
    );

    // And re-verifying the first one is still a Hit served from the same cache.
    let (a2, status) = verify_with_cache(&add_bounds(), &mut cache);
    assert_eq!(status, CacheStatus::Hit);
    assert_eq!(a2.outcome, Outcome::Verified);
    assert_eq!(cache.len(), 2);
}
