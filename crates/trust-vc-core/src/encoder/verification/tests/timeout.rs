//! Timeout-control unit tests for `verification::timeout`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::timeout::{effective_bv_timeout, BV_HARD_TIMEOUT};
use std::time::Duration;

#[test]
fn test_effective_bv_timeout_defaults_to_hard_timeout() {
    assert_eq!(
        effective_bv_timeout(None),
        BV_HARD_TIMEOUT,
        "missing rlimit should use the default BV hard timeout"
    );
}

#[test]
fn test_effective_bv_timeout_uses_smaller_explicit_rlimit() {
    assert_eq!(
        effective_bv_timeout(Some(250)),
        Duration::from_millis(250),
        "explicit rlimit below the hard cap should lower the BV timeout"
    );
}

#[test]
fn test_effective_bv_timeout_honors_larger_explicit_rlimit() {
    assert_eq!(
        effective_bv_timeout(Some(30_000)),
        Duration::from_millis(30_000),
        "explicit rlimit above the default should be honored as-is"
    );
}
