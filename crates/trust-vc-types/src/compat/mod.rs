// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compatibility shims for neighboring ghost/spec APIs.
//!
//! These modules reduce naming and import friction without changing TrustVc's
//! existing encoder assumptions or runtime ghost representations.

/// TrustWp-facing compatibility aliases (`FSet`, `FMap`, re-exports).
pub mod trust_wp;
