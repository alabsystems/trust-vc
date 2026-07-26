// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TrustWp-facing compatibility aliases for `trust-vc-types`.
//!
//! This facade exposes the closest safe subset of the TrustWp API while keeping
//! TrustVc semantics intact.
//!
//! | TrustWp name | TrustVc surface | Compatibility |
//! | --- | --- | --- |
//! | `Seq<T>` | `crate::Seq<T>` | Exact type re-export |
//! | `FSet<T>` | `crate::Set<T>` | Type alias plus method shims |
//! | `FMap<K, V>` | `crate::Map<K, V>` | Type alias plus method shims |
//! | `Ghost<T>` | `crate::Ghost<T>` | Exact type re-export |
//! | `Snapshot<T>` | `crate::Snapshot<T>` | Exact type re-export |
//! | `View` | `crate::View` | Exact trait re-export |
//!
//! Non-equivalences:
//! - `Seq` indexing and lengths still use `usize`, not mathematical `Int`.
//! - `FMap` aliases TrustVc's total `Map<K, V>` rather than TrustWp's
//!   domain-aware partial map.
//! - `View::view` still takes `&self` in TrustVc.
//! - TrustVc spec collections remain zero-sized ghost wrappers at runtime.

pub use crate::{Ghost, Seq, Snapshot, View};

/// TrustWp compatibility alias for TrustVc sets.
pub type FSet<T> = crate::Set<T>;

/// TrustWp compatibility alias for TrustVc maps.
pub type FMap<K, V> = crate::Map<K, V>;
