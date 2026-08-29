// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for solver memory limits (#2279, #2763).
//!
//! Verifies that `with_limits()` sets the ay process memory budget from its
//! argument, preserves opt-in per-instance term memory behavior, and that
//! `instance_term_bytes()` is queryable.

use super::*;
use crate::vc::VariableDecl;
use ay_dpll::CounterexampleStyle;
use std::process::Command;

const TERM_MEMORY_ENV_VAR: &str = "TRUST_VC_TERM_MEMORY_MB";
const TERM_MEMORY_HELPER_TEST: &str =
    "encoder::tests::term_memory_limit::test_with_limits_reports_expected_term_memory_limit_helper";

/// Expected limit encoding: "none" means None, otherwise parse as usize for Some(n).
const TERM_MEMORY_EXPECTED_LIMIT_ENV_VAR: &str = "TRUST_VC_TERM_MEMORY_EXPECTED_LIMIT";
const PROCESS_MEMORY_MB_ENV_VAR: &str = "TRUST_VC_PROCESS_MEMORY_MB";

fn encode_expected_limit(expected_limit: Option<usize>) -> String {
    match expected_limit {
        Some(bytes) => bytes.to_string(),
        None => "none".to_string(),
    }
}

fn parse_expected_limit(value: &str) -> Option<usize> {
    if value == "none" {
        None
    } else {
        Some(
            value
                .parse::<usize>()
                .expect("expected-limit env var should parse as usize"),
        )
    }
}

fn assert_with_limits_via_subprocess(
    term_override_mb: Option<&str>,
    expected_term_limit: Option<usize>,
    process_memory_mb: usize,
    scenario: &str,
) {
    let mut cmd = Command::new(
        std::env::current_exe().expect("test binary path should be available for subprocess probe"),
    );
    cmd.arg("--exact")
        .arg(TERM_MEMORY_HELPER_TEST)
        .arg("--nocapture")
        .env(
            TERM_MEMORY_EXPECTED_LIMIT_ENV_VAR,
            encode_expected_limit(expected_term_limit),
        )
        .env(PROCESS_MEMORY_MB_ENV_VAR, process_memory_mb.to_string());
    match term_override_mb {
        Some(value) => {
            cmd.env(TERM_MEMORY_ENV_VAR, value);
        }
        None => {
            cmd.env_remove(TERM_MEMORY_ENV_VAR);
        }
    }
    let output = cmd
        .output()
        .expect("term-memory subprocess probe should run");
    assert!(
        output.status.success(),
        "term-memory subprocess probe failed for {scenario} (override {:?})\nstdout:\n{}\nstderr:\n{}",
        term_override_mb,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

/// `with_limits()` sets the ay process RSS memory limit from its MB argument.
#[test]
fn test_with_limits_sets_process_memory_limit_from_argument() {
    assert_with_limits_via_subprocess(
        None,
        None,
        384,
        "process memory limit from with_limits argument",
    );
}

/// A zero process memory argument disables the ay process RSS memory limit.
#[test]
fn test_with_limits_zero_process_memory_disables_limit() {
    assert_with_limits_via_subprocess(None, None, 0, "zero process memory disables limit");
}

/// `with_limits()` does NOT set a term memory limit when env var is unset (opt-in).
#[test]
fn test_with_limits_no_term_memory_limit_when_env_unset() {
    assert_with_limits_via_subprocess(None, None, 512, "no term-memory limit without env var");
}

/// `with_limits()` honors `TRUST_VC_TERM_MEMORY_MB` when it is explicitly set.
#[test]
fn test_with_limits_honors_term_memory_limit_override() {
    assert_with_limits_via_subprocess(
        Some("16"),
        Some(16 * 1024 * 1024),
        512,
        "explicit term-memory override",
    );
}

/// Invalid overrides are silently ignored (no limit set), not fail-closed.
#[test]
fn test_with_limits_invalid_term_memory_override_sets_no_limit() {
    assert_with_limits_via_subprocess(
        Some("not-a-number"),
        None,
        512,
        "invalid term-memory override ignored",
    );
}

/// Helper invoked via a fresh subprocess so term-memory config tests avoid
/// mutating the parent test process environment.
#[test]
fn test_with_limits_reports_expected_term_memory_limit_helper() {
    let Some(expected_raw) = std::env::var_os(TERM_MEMORY_EXPECTED_LIMIT_ENV_VAR) else {
        return;
    };
    let expected_str = expected_raw
        .to_str()
        .expect("expected-limit env var should be valid UTF-8");
    let expected_limit = parse_expected_limit(expected_str);
    let process_memory_mb = std::env::var(PROCESS_MEMORY_MB_ENV_VAR)
        .expect("process-memory MB env var should be set for helper subprocess")
        .parse::<usize>()
        .expect("process-memory MB env var should parse as usize");

    let encoder = AYEncoder::new().with_limits(
        30_000,
        crate::solver_budget::ConflictBudget::bounded(400_000),
        process_memory_mb,
    );
    let term_limit = encoder.solver.term_memory_limit();
    assert_eq!(
        term_limit, expected_limit,
        "with_limits() term memory limit mismatch"
    );
    let process_limit = encoder.solver.memory_limit();
    let expected_process_limit = process_memory_limit_bytes(process_memory_mb);
    assert_eq!(
        process_limit, expected_process_limit,
        "with_limits() process memory limit mismatch"
    );
    if let Some(limit) = process_limit {
        assert!(
            limit >= process_memory_mb.saturating_mul(1024 * 1024),
            "process memory limit should preserve the configured MB floor"
        );
    }
}

/// `AYEncoder::new()` (no limits) does NOT set a term memory limit.
///
/// `AYEncoder::new()` does NOT set a term memory limit — limits are applied
/// only via `with_limits()` in the production verification path. This ensures
/// that test code using `new()` directly gets full solver headroom.
#[test]
fn test_new_encoder_has_no_term_memory_limit() {
    let encoder = AYEncoder::new();

    let limit = encoder.solver.term_memory_limit();
    assert_eq!(
        limit, None,
        "AYEncoder::new() should not set a term memory limit"
    );
}

/// `AYEncoder::new()` opts into readable counterexample values by default.
#[test]
fn test_new_encoder_defaults_to_readable_counterexample_style() {
    let encoder = AYEncoder::new();

    assert_eq!(
        encoder.solver.counterexample_style(),
        CounterexampleStyle::Readable,
        "AYEncoder::new() should prefer readable counterexample values"
    );
}

/// `instance_term_bytes()` is queryable on an encoder with limits.
#[test]
fn test_instance_term_bytes_queryable() {
    let encoder = AYEncoder::new().with_limits(
        30_000,
        crate::solver_budget::ConflictBudget::bounded(400_000),
        512,
    );

    // Even with no solving, the counter should be queryable (returns 0 or small).
    // Just verify it doesn't panic — the exact value depends on ay internals.
    let bytes = encoder.solver.instance_term_bytes();
    assert!(
        bytes < 128 * 1024 * 1024,
        "fresh encoder should use far less than 128MB, got {} bytes",
        bytes
    );
}

/// Term-memory accounting is per solver instance, not a process-global carry-over.
#[test]
fn test_instance_term_bytes_reset_for_fresh_encoder() {
    let baseline = AYEncoder::new()
        .with_limits(
            30_000,
            crate::solver_budget::ConflictBudget::bounded(400_000),
            512,
        )
        .solver
        .instance_term_bytes();

    let mut populated = AYEncoder::new().with_limits(
        30_000,
        crate::solver_budget::ConflictBudget::bounded(400_000),
        512,
    );
    for i in 0..256 {
        populated
            .declare_variable(&VariableDecl {
                bounded_len: false,
                name: format!("seq_{i}"),
                ty: crate::ir::TrustVcType::Seq(Box::new(i32_ty())),
            })
            .expect("sequence declaration should succeed");
    }
    let populated_bytes = populated.solver.instance_term_bytes();
    assert!(
        populated_bytes > baseline,
        "declaring many collection variables should grow the term store (baseline={} populated={})",
        baseline,
        populated_bytes,
    );

    let fresh_bytes = AYEncoder::new()
        .with_limits(
            30_000,
            crate::solver_budget::ConflictBudget::bounded(400_000),
            512,
        )
        .solver
        .instance_term_bytes();
    assert!(
        fresh_bytes < populated_bytes,
        "fresh encoder should not inherit populated encoder term bytes (fresh={} populated={})",
        fresh_bytes,
        populated_bytes,
    );
}
