// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression guard for #77 (fixed-array dependent-index bounds completeness).
//!
//! A dependent/computed index into a fixed-size `[usize; N]` array (e.g.
//! `ar[ar[0]] += 1`) must discharge the `i < len` bounds obligation when the
//! verification context genuinely implies it — previously this returned
//! `Unknown { Incompleteness }` because the index was lifted to `Int` via
//! `bv2nat`, which ay could not relate back to the BV facts pinning the index.
//!
//! The fix discharges the bound in pure BV against the array's known static
//! length. This is a SOUNDNESS-CRITICAL specialization: it must flip ONLY the
//! genuinely-implied case to `Verified`, and a genuine out-of-bounds index — one
//! whose bounds obligation is actually emitted (here, via a subsequent read) and
//! that can be `>= len` (unbounded source, off-by-one, or weak context bound) —
//! must STILL fail closed (`Counterexample`/`Unknown`), never `Verified`.

use std::sync::atomic::{AtomicU64, Ordering};
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SOURCE: &str = r#"
// ---- TRUE: dependent index provably < N -> must Verify ----

#[trust_vc::requires(ar[0usize] == 1usize)]
#[trust_vc::requires(ar[2usize] == 2usize)]
#[trust_vc::ensures(true)]
fn dep_index(ar: &mut [usize; 20]) {
    ar[0usize] += 1usize;
    ar[ar[0usize]] += 1usize;
    assert!(ar[0usize] == 2usize);
    assert!(ar[2usize] == 3usize);
}

#[trust_vc::requires(ar[0usize] == 5usize)]
#[trust_vc::requires(ar[5usize] == 1usize)]
#[trust_vc::ensures(true)]
fn dep_index_pinned_in_bounds(ar: &mut [usize; 20]) {
    ar[ar[0usize]] += 1usize;
    assert!(ar[5usize] == 2usize);
}

#[trust_vc::requires(i < 20usize)]
#[trust_vc::requires(ar[i] == 0usize)]
#[trust_vc::ensures(true)]
fn dep_index_from_requires_bound(ar: &mut [usize; 20], i: usize) {
    ar[i] += 7usize;
    assert!(ar[i] == 7usize);
}

// ---- OOB: bound IS emitted (read of array) and genuinely out of range
//      -> must NOT Verify ----

#[trust_vc::ensures(true)]
fn oob_read_unbounded(ar: &mut [usize; 20], j: usize) {
    ar[j] += 1usize;
    assert!(ar[j] == 1usize);
}

#[trust_vc::requires(i == 20usize)]
#[trust_vc::requires(ar[0usize] == 3usize)]
#[trust_vc::ensures(true)]
fn oob_read_off_by_one(ar: &mut [usize; 20], i: usize) {
    let x = ar[i];
    assert!(x == ar[i]);
}

#[trust_vc::ensures(true)]
fn oob_read_dependent_unbounded(ar: &mut [usize; 20]) {
    let x = ar[ar[0usize]];
    assert!(x == ar[ar[0usize]]);
}

#[trust_vc::requires(ar[0usize] == 20usize)]
#[trust_vc::ensures(true)]
fn oob_read_dependent_pinned_past_end(ar: &mut [usize; 20]) {
    ar[ar[0usize]] += 1usize;
    assert!(ar[3usize] == ar[3usize]);
}

#[trust_vc::requires(i <= 20usize)]
#[trust_vc::ensures(true)]
fn oob_read_weak_bound(ar: &mut [usize; 20], i: usize) {
    let x = ar[i];
    assert!(x == ar[i]);
}
"#;

static SEQ: AtomicU64 = AtomicU64::new(0);

/// Verify `func` from a freshly-written, uniquely-named temp copy of `SOURCE`.
/// (Unique paths keep parallel test threads from racing on one file.)
fn verify(func: &str) -> VerifyResult {
    let path = std::env::temp_dir().join(format!(
        "trust_vc_dep_index_77_{}_{}.rs",
        std::process::id(),
        SEQ.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, SOURCE).expect("write temp source");
    let result = verify_function_from_file(path.to_str().unwrap(), func)
        .unwrap_or_else(|e| panic!("{func} should verify-from-file without error: {e}"));
    let _ = std::fs::remove_file(&path);
    result
}

#[test]
fn dependent_index_provably_in_bounds_verifies() {
    for f in [
        "dep_index",
        "dep_index_pinned_in_bounds",
        "dep_index_from_requires_bound",
    ] {
        let result = verify(f);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{f}: a dependent index provably < len must Verify, got {result:?}"
        );
    }
}

#[test]
fn out_of_bounds_dependent_index_never_verifies() {
    // Each of these emits a real `i < len` obligation (the array is read) for an
    // index that can be `>= len`. The gate must fail closed: NOT Verified.
    for f in [
        "oob_read_unbounded",
        "oob_read_off_by_one",
        "oob_read_dependent_unbounded",
        "oob_read_dependent_pinned_past_end",
        "oob_read_weak_bound",
    ] {
        let result = verify(f);
        assert!(
            !matches!(result, VerifyResult::Verified),
            "{f}: a genuine out-of-bounds index must NEVER verify, got {result:?}"
        );
    }
}

#[test]
fn at_least_one_oob_yields_a_decisive_counterexample() {
    // Soundness witness: a dependent index pinned exactly one past the end
    // produces a concrete refuting model (not merely Unknown), proving the
    // bound is genuinely enforced rather than skipped. The unbounded cases may
    // soundly fail closed as NotProved and are covered above.
    let result = verify("oob_read_dependent_pinned_past_end");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "the pinned-past-end dependent index should expose a counterexample, got {result:?}"
    );
}
