// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression guard for the trybuild harness split from #2302/#2304.

const COMPILE_PASS_MODE_BINS: &[(&str, &str)] = &[
    (
        "mode_exec_calls_exec",
        "tests/compile-pass/mode/exec_calls_exec.rs",
    ),
    (
        "mode_proof_calls_proof",
        "tests/compile-pass/mode/proof_calls_proof.rs",
    ),
    (
        "mode_proof_calls_later_proof",
        "tests/compile-pass/mode/proof_calls_later_proof.rs",
    ),
    (
        "mode_proof_calls_spec",
        "tests/compile-pass/mode/proof_calls_spec.rs",
    ),
    (
        "mode_proof_calls_later_spec",
        "tests/compile-pass/mode/proof_calls_later_spec.rs",
    ),
    (
        "mode_spec_calls_spec",
        "tests/compile-pass/mode/spec_calls_spec.rs",
    ),
    (
        "mode_spec_calls_later_spec",
        "tests/compile-pass/mode/spec_calls_later_spec.rs",
    ),
    (
        "mode_spec_mode_calls_later_spec",
        "tests/compile-pass/mode/spec_mode_calls_later_spec.rs",
    ),
    (
        "mode_proof_calls_spec_via_crate",
        "tests/compile-pass/mode/proof_calls_spec_via_crate.rs",
    ),
    (
        "mode_exec_calls_exec_cross_module",
        "tests/compile-pass/mode/exec_calls_exec_cross_module.rs",
    ),
];

const GENERAL_COMPILE_FAIL_GLOBS: &[&str] = &[
    "tests/compile-fail/all_*.rs",
    "tests/compile-fail/ambiguous_*.rs",
    "tests/compile-fail/auto_*.rs",
    "tests/compile-fail/broadcast_unexpected_args.rs",
    "tests/compile-fail/decreases_*.rs",
    "tests/compile-fail/exec_*.rs",
    "tests/compile-fail/external_*.rs",
    "tests/compile-fail/liveness_*.rs",
    "tests/compile-fail/memoize_*.rs",
    "tests/compile-fail/proof_calls_*.rs",
    "tests/compile-fail/proof_recursive_without_decreases.rs",
    "tests/compile-fail/proof_unexpected_args.rs",
    "tests/compile-fail/returns_*.rs",
    "tests/compile-fail/spec_*.rs",
    "tests/compile-fail/trigger_*.rs",
    "tests/compile-fail/via_fn_*.rs",
];

const FOCUSED_COMPILE_FAIL_GLOBS: &[&str] = &[
    "tests/compile-fail/*_param_fail_closed.rs",
    "tests/compile-fail/contract_combined_with_proof.rs",
    "tests/compile-fail/inline_*.rs",
    "tests/compile-fail/old_*.rs",
];

#[test]
fn test_compile_fail_harness_does_not_mix_pass_cases() {
    let compile_fail_harness = include_str!("compile_fail.rs");

    for glob in GENERAL_COMPILE_FAIL_GLOBS {
        assert!(
            compile_fail_harness.contains(glob),
            "compile_fail harness must keep {glob} wired to trybuild",
        );
    }
    assert!(
        !compile_fail_harness.contains(".pass("),
        "compile_fail harness must not mix compile-pass cases into the trybuild run",
    );
    assert!(
        !compile_fail_harness.contains("tests/compile-fail/*.rs"),
        "compile_fail harness must not reintroduce the broad compile-fail glob",
    );
    for glob in FOCUSED_COMPILE_FAIL_GLOBS {
        assert!(
            !compile_fail_harness.contains(glob),
            "compile_fail harness must not overlap the focused {glob} owner",
        );
    }
}

#[test]
fn test_compile_pass_mode_cases_stay_as_standalone_test_bins() {
    let cargo_toml = include_str!("../Cargo.toml");

    for (name, path) in COMPILE_PASS_MODE_BINS {
        assert!(
            cargo_toml.contains(&format!("name = \"{name}\"")),
            "Cargo.toml must keep {name} registered as a standalone test target",
        );
        assert!(
            cargo_toml.contains(&format!("path = \"{path}\"")),
            "Cargo.toml must keep {path} wired as a compile-pass mode test target",
        );
    }

    let harness_false_count = cargo_toml.matches("harness = false").count();
    assert!(
        harness_false_count >= COMPILE_PASS_MODE_BINS.len(),
        "compile-pass mode bins must remain standalone tests, found only {harness_false_count} harness=false entries",
    );
}
