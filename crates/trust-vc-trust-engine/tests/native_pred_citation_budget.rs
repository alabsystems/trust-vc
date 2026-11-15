// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Consuming a native bundle costs no more than the bundle states.
//!
//! Upstream's validators, which this consumer runs on every bundle
//! (`trust_ir_build::validate_module` and `NativeVerificationBundle::validate`),
//! refuse a `trust-ir.Pred@1` citation beside an `smtlib` rendering that is
//! not the cited predicate's text. The predicate DAG's rendering is not
//! shared: the validator-legal table `pred.k = Conj([k-2, k-1])` renders
//! `pred.64` (the depth cap) to fib(64) leaves, ~5*10^14 bytes. Rendering the
//! citation whole before comparing it made consuming a bundle with this
//! 65-entry table beside `smtlib = "true"` exhaust the host; the comparison
//! renders no further than the rendering in hand.
//!
//! A counting `#[global_allocator]` holds each consume to a heap ceiling
//! WHILE it runs: an allocation past it fails, which aborts this test binary
//! ("memory allocation of … failed"), so an unbounded render fails here
//! within the ceiling instead of taking the host.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

use trust_ir::pred::PRED_FORMULA_SCHEMA;
use trust_ir::proof::ProofFormula;
use trust_ir::request::NativeVerificationBundle;
use trust_ir::value::PredId;
use trust_ir::Pred;
use trust_vc_trust_engine::TrustVcTrustEngine;

#[path = "support/admission_baseline.rs"]
mod admission_baseline;
use admission_baseline::{native_bundle_fixture, reseal_module_identity};

struct Counting;

static CURRENT: AtomicUsize = AtomicUsize::new(0);
/// Allocations that would take `CURRENT` above this fail (and so abort).
static CEILING: AtomicUsize = AtomicUsize::new(usize::MAX);

// SAFETY: every method forwards to `System` with the caller's layout and only
// adds bookkeeping; a refused allocation returns null, which is the
// `GlobalAlloc` contract for failure.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let now = CURRENT.fetch_add(layout.size(), Ordering::SeqCst) + layout.size();
        if now > CEILING.load(Ordering::SeqCst) {
            CURRENT.fetch_sub(layout.size(), Ordering::SeqCst);
            return core::ptr::null_mut();
        }
        // SAFETY: forwarded unchanged.
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        CURRENT.fetch_sub(layout.size(), Ordering::SeqCst);
        // SAFETY: forwarded unchanged.
        unsafe { System.dealloc(ptr, layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let grow = new_size.saturating_sub(layout.size());
        let now = CURRENT.fetch_add(grow, Ordering::SeqCst) + grow;
        if now > CEILING.load(Ordering::SeqCst) {
            CURRENT.fetch_sub(grow, Ordering::SeqCst);
            return core::ptr::null_mut();
        }
        // SAFETY: forwarded unchanged.
        let moved = unsafe { System.realloc(ptr, layout, new_size) };
        if !moved.is_null() {
            CURRENT.fetch_sub(layout.size().saturating_sub(new_size), Ordering::SeqCst);
        }
        moved
    }
}

#[global_allocator]
static ALLOCATOR: Counting = Counting;

/// The counter is process-wide: consumes run one at a time.
static SERIAL: Mutex<()> = Mutex::new(());

/// The heap growth one consume may use. The admission baseline consumes well
/// within it; an unbounded render of `pred.64` passes it within seconds.
const CEILING_BYTES: usize = 256 << 20;

/// Consume `bundle` under [`CEILING_BYTES`]; `Err` carries upstream's refusal.
fn consume_within_ceiling(bundle: &NativeVerificationBundle) -> Result<(), String> {
    let _serial = SERIAL
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    CEILING.store(
        CURRENT.load(Ordering::SeqCst) + CEILING_BYTES,
        Ordering::SeqCst,
    );
    let result = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(bundle)
        .map(drop)
        .map_err(|error| error.to_string());
    CEILING.store(usize::MAX, Ordering::SeqCst);
    result
}

/// The admission baseline with the predicate table `pred.0 = NonZero`,
/// `pred.1 = Interval [0, 5]`, `pred.k = Conj([k-2, k-1])` for `2 <= k <= 64`,
/// and, when `rendering` is given, its first function ensuring the citation
/// `pred.64` beside that rendering.
fn with_deep_table(rendering: Option<&str>) -> NativeVerificationBundle {
    let n = 64;
    let mut bundle = native_bundle_fixture();
    let module = &mut bundle.module;
    module.predicates = vec![Pred::NonZero, Pred::Interval { lo: 0, hi: 5 }];
    for k in 2..=n {
        module
            .predicates
            .push(Pred::Conj(vec![PredId::new(k - 2), PredId::new(k - 1)]));
    }
    if let Some(rendering) = rendering {
        let mut citation = ProofFormula::new(PRED_FORMULA_SCHEMA, format!("pred.{n}"));
        citation.smtlib = Some(rendering.to_string());
        let summary = module.functions[0].summary.take().unwrap_or_default();
        module.functions[0].summary = Some(summary.ensuring(citation));
    }
    reseal_module_identity(&mut bundle);
    bundle
}

#[test]
fn a_deep_pred_citation_is_refused_within_the_ceiling() {
    // Control: the table alone is a bundle this consumer accepts, within the
    // ceiling.
    if let Err(error) = consume_within_ceiling(&with_deep_table(None)) {
        panic!("the baseline with a 65-entry predicate table is refused: {error}");
    }
    let error = consume_within_ceiling(&with_deep_table(Some("true")))
        .expect_err("pred.64 beside `true` states two texts");
    assert!(
        error.contains("states two SMT-LIB texts"),
        "refused for another reason: {error}"
    );
}
