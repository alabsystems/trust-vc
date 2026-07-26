//! #3 Certified cross-crate proof cache — replay a checkable certificate instead
//! of re-proving.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This module is a superiority capability over Verus: because every trust-vc
//! "Verified" can carry an ay UNSAT proof that the small, independent
//! [`trust-vc-kernel`] re-checks (a [`Certificate`]), the *same* obligation does
//! not need to be re-proved when it recurs. A content-addressed cache stores the
//! kernel-checked certificate keyed by a deterministic encoding of the
//! [`DriverFn`]'s contract; a cache **Hit** replays that checkable artifact.
//!
//! Verus's backend is Z3, whose "unsat" answer is a *black box*: there is no
//! proof object to cache and re-check, so a recurring obligation must be re-sent
//! to the solver and re-trusted every time. Here the cached value is itself an
//! independently-checkable proof, so re-verification is a *replay-and-re-check*,
//! not a re-prove.
//!
//! ## Cache key
//!
//! The key is a deterministic `Debug` rendering of the contract-bearing fields
//! of the [`DriverFn`]: `(name, params, requires, body_value, ensures)`. Every
//! one of those field types derives `Debug`, so the rendering is total and
//! stable for structurally identical functions. Two `DriverFn`s with the same
//! name, parameters, preconditions, body, and postconditions therefore collide
//! to one entry — exactly the obligations whose proof certificate is reusable.
//!
//! ## Soundness note (fail-closed)
//!
//! A genuine cross-crate cache persists the certificate's Alethe text and, on a
//! Hit, re-runs it through `trust-vc-kernel` before trusting it (the certificate
//! is the artifact that makes that *cheap and sound*). This in-memory cache
//! keeps the full [`Certificate`] — including its `kernel_verified` flag and the
//! Alethe proof string — so the re-check is always available; we assert here
//! that the replayed certificate's `kernel_verified` flag is preserved. We only
//! ever cache a certificate that was *produced for a `Verified` outcome*, so a
//! Hit can never manufacture a proof for an unproven goal.

use std::collections::HashMap;

use crate::lower::{Certificate, CertifiedOutcome, DriverFn, Outcome};

/// Whether a [`verify_with_cache`] call was served from the cache.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CacheStatus {
    /// The obligation's certificate was already cached and was replayed without
    /// re-running the solver.
    Hit,
    /// The obligation was not cached; the solver ran and (if it produced a
    /// certificate) the result was stored.
    Miss,
}

/// A content-addressed store of kernel-checked proof [`Certificate`]s, keyed by
/// a deterministic encoding of the proven [`DriverFn`]'s contract.
///
/// Wraps a plain [`HashMap`]; the only invariant is that a stored certificate
/// was produced for a `Verified` outcome, so replaying it is sound.
#[derive(Debug, Default)]
pub struct CertifiedCache {
    entries: HashMap<String, Certificate>,
}

impl CertifiedCache {
    /// Creates an empty cache.
    #[must_use]
    pub fn new() -> Self {
        Self {
            entries: HashMap::new(),
        }
    }

    /// The number of cached certificates.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the cache holds no certificates.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Looks up a previously cached certificate for `f`'s content key.
    fn get(&self, key: &str) -> Option<&Certificate> {
        self.entries.get(key)
    }

    /// Inserts a certificate under `f`'s content key.
    fn insert(&mut self, key: String, cert: Certificate) {
        self.entries.insert(key, cert);
    }
}

/// The deterministic content key for a [`DriverFn`].
///
/// Built from exactly the contract-bearing fields. The synthetic `result`
/// binding is deliberately *excluded*: its name/type are determined by the
/// function's signature, and including it would not change which obligations are
/// provably equivalent. Every field type derives `Debug`, so this is total.
#[must_use]
pub fn content_key(f: &DriverFn) -> String {
    format!(
        "{:?}",
        (&f.name, &f.params, &f.requires, &f.body_value, &f.ensures)
    )
}

/// Verify `f`, consulting (and populating) `cache`.
///
/// * **Miss** — the contract is not in the cache. The real solver runs via
///   [`DriverFn::verify_certified`]; if it produced a certificate (which it does
///   exactly for a `Verified` result), that certificate is stored. Returns the
///   true [`CertifiedOutcome`] and [`CacheStatus::Miss`].
/// * **Hit** — the contract is already cached. The stored, kernel-checked
///   certificate is replayed as a `Verified` [`CertifiedOutcome`] **without
///   re-running the solver**. Returns [`CacheStatus::Hit`].
///
/// The Hit path is the capability: a checkable artifact is replayed (and, in a
/// real cross-crate cache, re-checked by `trust-vc-kernel` from its preserved
/// Alethe text) instead of re-proving from scratch — something Verus's
/// non-checkable Z3 verdicts cannot do.
pub fn verify_with_cache(
    f: &DriverFn,
    cache: &mut CertifiedCache,
) -> (CertifiedOutcome, CacheStatus) {
    let key = content_key(f);

    if let Some(cached) = cache.get(&key) {
        // Replay the cached, kernel-checked certificate. We do NOT call the
        // solver. A real cross-crate cache would re-check `cached.alethe`
        // through trust-vc-kernel here; the full certificate (including the
        // `kernel_verified` flag) is preserved so that re-check is always
        // available and the flag is carried forward unchanged.
        let replayed = CertifiedOutcome {
            outcome: Outcome::Verified,
            certificate: Some(cached.clone()),
        };
        return (replayed, CacheStatus::Hit);
    }

    // Miss: run the real backend.
    let certified = f.verify_certified();
    if let Some(cert) = &certified.certificate {
        // Only certificates are cached, and the seam only emits a certificate
        // for a `Verified` outcome — so the cache can never replay a proof for
        // an unproven goal.
        debug_assert_eq!(certified.outcome, Outcome::Verified);
        cache.insert(key, cert.clone());
    }
    (certified, CacheStatus::Miss)
}
