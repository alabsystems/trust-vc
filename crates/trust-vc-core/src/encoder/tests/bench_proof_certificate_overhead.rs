// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Proof certificate overhead benchmark (#2745).
//!
//! Measures verification time with and without proof certificate generation
//! to quantify the overhead of `set_produce_proofs(true)` + artifact
//! extraction + kernel checking.
//!
//! Since `proof-certificates` is a compile-time feature flag, the benchmark
//! records absolute timings for a suite of representative workloads. Running
//! `cargo test -p trust-vc-core` (without the feature) and then
//! `cargo test -p trust-vc-core --features proof-certificates` produces
//! comparable wall-clock data.
//!
//! When `proof-certificates` is enabled, the benchmark also records:
//! - Alethe proof text size (bytes)
//! - Resolution / theory / trust step counts
//! - Kernel verification result
//!
//! Gated behind `expensive-tests` to avoid slowing CI on every commit.

use std::time::Instant;

use super::*;
use crate::ir::TrustVcType;
use crate::vc::VerificationContext;
use crate::verification_report::VerificationReportOptions;

/// Number of warmup + measurement iterations per workload.
const WARMUP_ITERS: usize = 1;
const MEASURE_ITERS: usize = 5;

// ---------------------------------------------------------------------------
// Workload builders
// ---------------------------------------------------------------------------

/// Simple: one assumption, one assertion on a single i32 variable.
fn build_simple_workload() -> VerificationContext {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("positive", "x > 0"));
    ctx.push_obligation(ProofObligation::assert("nonneg", "x >= 0"));
    ctx
}

/// Medium: two variables with chained assumptions and multiple assertions.
fn build_medium_workload() -> VerificationContext {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.declare_var_typed("y", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("x_bound", "x > 0 && x < 100"));
    ctx.push_obligation(ProofObligation::assume("y_bound", "y > x && y < 200"));
    ctx.push_obligation(ProofObligation::assert("x_nonneg", "x >= 0"));
    ctx.push_obligation(ProofObligation::assert("y_positive", "y > 0"));
    ctx.push_obligation(ProofObligation::assert("order", "y > x"));
    ctx
}

/// Multi-assertion: N independent assertions sharing a common assumption set.
/// Exercises incremental solving overhead (push/pop per assertion).
/// Each assertion `x >= i` is provable from `x >= N` (assumed).
fn build_multi_assertion_workload(n: usize) -> VerificationContext {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("x_lower", &format!("x >= {n}")));
    ctx.push_obligation(ProofObligation::assume("x_upper", "x < 1000"));
    for i in 0..n {
        ctx.push_obligation(ProofObligation::assert(
            &format!("a_{i}"),
            &format!("x >= {i}"),
        ));
    }
    ctx
}

/// Bitvector: uses u16 width to exercise the BV theory path with
/// bounds that avoid vacuous truth detection.
fn build_bv_workload() -> VerificationContext {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", TrustVcType::Int { width: 16 });
    ctx.declare_var_typed("b", TrustVcType::Int { width: 16 });
    ctx.push_obligation(ProofObligation::assume("a_bound", "a > 0 && a < 100"));
    ctx.push_obligation(ProofObligation::assume("b_bound", "b > 0 && b < 100"));
    ctx.push_obligation(ProofObligation::assert("a_pos", "a >= 1"));
    ctx.push_obligation(ProofObligation::assert("b_pos", "b >= 1"));
    ctx
}

// ---------------------------------------------------------------------------
// Timing harness
// ---------------------------------------------------------------------------

struct BenchResult {
    workload_name: &'static str,
    median_us: u128,
    min_us: u128,
    max_us: u128,
    #[cfg(feature = "proof-certificates")]
    certificate_bytes: Option<usize>,
    #[cfg(feature = "proof-certificates")]
    resolution_count: Option<u32>,
    #[cfg(feature = "proof-certificates")]
    theory_count: Option<u32>,
    #[cfg(feature = "proof-certificates")]
    trust_count: Option<u32>,
    #[cfg(feature = "proof-certificates")]
    kernel_verified: Option<bool>,
    #[cfg(feature = "proof-certificates")]
    strict_verified: Option<bool>,
}

fn bench_workload(name: &'static str, ctx: &VerificationContext) -> BenchResult {
    // Disable VC cache so each iteration actually runs the solver. Serialized
    // behind the process-wide env lock and restored when this workload returns
    // (the cache guard drops before the lock releases).
    let _env_lock = crate::env::lock_env();
    let _vc_cache = crate::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");

    // Warmup
    for _ in 0..WARMUP_ITERS {
        let _ = ctx.verify_with_report(VerificationReportOptions::new());
    }

    let mut timings = Vec::with_capacity(MEASURE_ITERS);

    // Last report kept for certificate inspection.
    let mut last_report = None;

    for _ in 0..MEASURE_ITERS {
        let start = Instant::now();
        let report = ctx.verify_with_report(VerificationReportOptions::new());
        let elapsed_us = start.elapsed().as_micros();
        timings.push(elapsed_us);

        // Verify that each run actually succeeds.
        super::result_oracles::expect_verified(report.result(), name);

        last_report = Some(report);
    }

    timings.sort_unstable();
    let median_us = timings[timings.len() / 2];
    let min_us = timings[0];
    let max_us = timings[timings.len() - 1];

    #[cfg(feature = "proof-certificates")]
    let (
        certificate_bytes,
        resolution_count,
        theory_count,
        trust_count,
        kernel_verified,
        strict_verified,
    ) = {
        if let Some(ref report) = last_report {
            if let Some(proof) = report.proof() {
                (
                    Some(proof.alethe().len()),
                    Some(proof.resolution_count()),
                    Some(proof.theory_count()),
                    Some(proof.trust_count()),
                    Some(proof.kernel_verified()),
                    Some(proof.strict_verified()),
                )
            } else {
                (None, None, None, None, None, None)
            }
        } else {
            (None, None, None, None, None, None)
        }
    };

    // Suppress unused variable warning when proof-certificates is off.
    let _ = &last_report;

    BenchResult {
        workload_name: name,
        median_us,
        min_us,
        max_us,
        #[cfg(feature = "proof-certificates")]
        certificate_bytes,
        #[cfg(feature = "proof-certificates")]
        resolution_count,
        #[cfg(feature = "proof-certificates")]
        theory_count,
        #[cfg(feature = "proof-certificates")]
        trust_count,
        #[cfg(feature = "proof-certificates")]
        kernel_verified,
        #[cfg(feature = "proof-certificates")]
        strict_verified,
    }
}

fn print_bench_result(r: &BenchResult) {
    #[cfg(feature = "proof-certificates")]
    let mode = "proof-certificates=ON";
    #[cfg(not(feature = "proof-certificates"))]
    let mode = "proof-certificates=OFF";

    eprintln!(
        "[BENCH] {:<30} | {} | median={:>8}us  min={:>8}us  max={:>8}us",
        r.workload_name, mode, r.median_us, r.min_us, r.max_us,
    );

    #[cfg(feature = "proof-certificates")]
    if let Some(cert_bytes) = r.certificate_bytes {
        eprintln!(
            "[BENCH]   certificate: {}B  resolution={}  theory={}  trust={}  kernel={}  strict={}",
            cert_bytes,
            r.resolution_count.unwrap_or(0),
            r.theory_count.unwrap_or(0),
            r.trust_count.unwrap_or(0),
            r.kernel_verified.unwrap_or(false),
            r.strict_verified.unwrap_or(false),
        );
    }
}

// ---------------------------------------------------------------------------
// Benchmark tests
// ---------------------------------------------------------------------------

#[test]
fn bench_proof_certificate_overhead_simple() {
    let ctx = build_simple_workload();
    let result = bench_workload("simple (1 var, 1 assert)", &ctx);
    print_bench_result(&result);

    // Sanity: simple workload should complete in under 500ms per iteration.
    assert!(
        result.median_us < 500_000,
        "simple workload took {}us median, expected <500ms",
        result.median_us
    );
}

#[test]
fn bench_proof_certificate_overhead_medium() {
    let ctx = build_medium_workload();
    let result = bench_workload("medium (2 var, 3 assert)", &ctx);
    print_bench_result(&result);

    assert!(
        result.median_us < 2_000_000,
        "medium workload took {}us median, expected <2s",
        result.median_us
    );
}

#[test]
fn bench_proof_certificate_overhead_multi_5() {
    let ctx = build_multi_assertion_workload(5);
    let result = bench_workload("multi-assert (5)", &ctx);
    print_bench_result(&result);

    assert!(
        result.median_us < 5_000_000,
        "multi-5 workload took {}us median, expected <5s",
        result.median_us
    );
}

#[test]
fn bench_proof_certificate_overhead_multi_10() {
    let ctx = build_multi_assertion_workload(10);
    let result = bench_workload("multi-assert (10)", &ctx);
    print_bench_result(&result);

    assert!(
        result.median_us < 10_000_000,
        "multi-10 workload took {}us median, expected <10s",
        result.median_us
    );
}

#[test]
fn bench_proof_certificate_overhead_bv() {
    let ctx = build_bv_workload();
    let result = bench_workload("bitvector (u8, 2 assert)", &ctx);
    print_bench_result(&result);

    assert!(
        result.median_us < 2_000_000,
        "bv workload took {}us median, expected <2s",
        result.median_us
    );
}

/// Aggregated summary test: runs all workloads and prints a comparison table.
/// This is the primary entry point for the benchmark.
#[test]
fn bench_proof_certificate_overhead_summary() {
    let workloads: Vec<(&'static str, VerificationContext)> = vec![
        ("simple (1v, 1a)", build_simple_workload()),
        ("medium (2v, 3a)", build_medium_workload()),
        ("multi-5", build_multi_assertion_workload(5)),
        ("multi-10", build_multi_assertion_workload(10)),
        ("bitvector", build_bv_workload()),
    ];

    #[cfg(feature = "proof-certificates")]
    let mode = "proof-certificates=ON";
    #[cfg(not(feature = "proof-certificates"))]
    let mode = "proof-certificates=OFF";

    eprintln!();
    eprintln!("=== Proof Certificate Overhead Benchmark ({}) ===", mode);
    eprintln!(
        "{:<25} {:>10} {:>10} {:>10}",
        "Workload", "Median(us)", "Min(us)", "Max(us)"
    );
    eprintln!("{}", "-".repeat(60));

    let mut results = Vec::new();
    for (name, ctx) in &workloads {
        let r = bench_workload(name, ctx);
        eprintln!(
            "{:<25} {:>10} {:>10} {:>10}",
            r.workload_name, r.median_us, r.min_us, r.max_us
        );
        results.push(r);
    }

    #[cfg(feature = "proof-certificates")]
    {
        eprintln!();
        eprintln!(
            "{:<25} {:>10} {:>8} {:>8} {:>8} {:>8} {:>8}",
            "Workload", "Cert(B)", "Res", "Theory", "Trust", "Kernel", "Strict"
        );
        eprintln!("{}", "-".repeat(85));
        for r in &results {
            eprintln!(
                "{:<25} {:>10} {:>8} {:>8} {:>8} {:>8} {:>8}",
                r.workload_name,
                r.certificate_bytes
                    .map_or("-".to_string(), |b| b.to_string()),
                r.resolution_count
                    .map_or("-".to_string(), |c| c.to_string()),
                r.theory_count.map_or("-".to_string(), |c| c.to_string()),
                r.trust_count.map_or("-".to_string(), |c| c.to_string()),
                r.kernel_verified.map_or("-".to_string(), |v| v.to_string()),
                r.strict_verified.map_or("-".to_string(), |v| v.to_string()),
            );
        }
    }

    eprintln!();
    eprintln!("To compare: run this test with and without --features proof-certificates");
    eprintln!("  cargo test -p trust-vc-core --features expensive-tests bench_proof_certificate_overhead_summary -- --nocapture");
    eprintln!("  cargo test -p trust-vc-core --features expensive-tests,proof-certificates bench_proof_certificate_overhead_summary -- --nocapture");
    eprintln!();
}
