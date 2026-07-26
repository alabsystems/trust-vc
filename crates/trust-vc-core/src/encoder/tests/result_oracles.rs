// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::encoder::VerifyResult;
use std::{fs, path::PathBuf};

#[track_caller]
pub(crate) fn expect_encodes_without_error(result: &VerifyResult, context: &str) {
    if let VerifyResult::Error { message } = result {
        panic!("{context} should encode without Error, got Error: {message}");
    }
}

#[track_caller]
pub(crate) fn expect_fail_closed(result: &VerifyResult, context: &str) {
    match result {
        VerifyResult::Counterexample { .. }
        | VerifyResult::NotProved { .. }
        | VerifyResult::Unknown { .. } => {}
        VerifyResult::Verified => panic!(
            "{context} should fail closed (Counterexample, NotProved, or Unknown), got Verified"
        ),
        VerifyResult::Error { message } => {
            panic!("{context} should fail closed without encoder errors, got Error: {message}")
        }
    }
}

#[track_caller]
pub(crate) fn expect_verified(result: &VerifyResult, context: &str) {
    match result {
        VerifyResult::Verified => {}
        VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        } => panic!(
            "{context} should be Verified, got Counterexample for '{obligation_name}' with model: {model:?}"
        ),
        VerifyResult::NotProved { reason, .. } => {
            panic!("{context} should be Verified, got NotProved (no model): {reason}")
        }
        VerifyResult::Unknown { reason, .. } => {
            panic!("{context} should be Verified, got Unknown: {reason}")
        }
        VerifyResult::Error { message } => {
            panic!("{context} should be Verified, got Error: {message}")
        }
    }
}

#[track_caller]
/// Strict: requires a genuine MODEL-BEARING counterexample. A model-less
/// `NotProved` deliberately does NOT satisfy this oracle — use
/// [`expect_incompleteness_modelless_failure`] (or [`expect_fail_closed`]) when
/// either shape of failure is acceptable. Keeping this strict is what stops the
/// incompleteness mapping from silently laundering a non-proof into "we found a
/// counterexample" inside the engine's own test suite.
pub(crate) fn expect_counterexample(result: &VerifyResult, context: &str) {
    match result {
        VerifyResult::Counterexample { .. } => {}
        VerifyResult::Verified => {
            panic!("{context} should be Counterexample, got Verified")
        }
        VerifyResult::NotProved { reason, .. } => panic!(
            "{context} should be a model-bearing Counterexample, got NotProved (no model): {reason}"
        ),
        VerifyResult::Unknown { reason, .. } => {
            panic!("{context} should be Counterexample, got Unknown: {reason}")
        }
        VerifyResult::Error { message } => {
            panic!("{context} should be Counterexample, got Error: {message}")
        }
    }
}

#[track_caller]
pub(crate) fn expect_error(result: &VerifyResult, context: &str) {
    match result {
        VerifyResult::Error { .. } => {}
        VerifyResult::Verified => {
            panic!("{context} should be Error, got Verified")
        }
        VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        } => panic!(
            "{context} should be Error, got Counterexample for '{obligation_name}' with model: {model:?}"
        ),
        VerifyResult::NotProved { reason, .. } => {
            panic!("{context} should be Error, got NotProved (no model): {reason}")
        }
        VerifyResult::Unknown { reason, .. } => {
            panic!("{context} should be Error, got Unknown: {reason}")
        }
    }
}

#[track_caller]
pub(crate) fn expect_error_containing(result: &VerifyResult, substring: &str, context: &str) {
    match result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains(substring),
                "{context} error message should contain \"{substring}\", got: {message}"
            );
        }
        other => {
            panic!("{context} should be Error containing \"{substring}\", got: {other:?}")
        }
    }
}

#[track_caller]
/// Strict: requires an INCONCLUSIVE `Unknown` (resource/timeout/panic class).
/// A `NotProved` is a verdict of failure, not an inconclusive outcome, so it
/// does not satisfy this oracle — that rejection is the load-bearing
/// soundness boundary of `docs/design-unknown-as-failure.md` expressed as a
/// test oracle.
pub(crate) fn expect_unknown(result: &VerifyResult, context: &str) {
    match result {
        VerifyResult::Unknown { .. } => {}
        VerifyResult::Verified => {
            panic!("{context} should be Unknown, got Verified")
        }
        VerifyResult::NotProved { reason, .. } => panic!(
            "{context} should be an inconclusive Unknown, got NotProved (an incompleteness \
             FAILURE, no model): {reason}"
        ),
        VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        } => panic!(
            "{context} should be Unknown, got Counterexample for '{obligation_name}' with model: {model:?}"
        ),
        VerifyResult::Error { message } => {
            panic!("{context} should be Unknown, got Error: {message}")
        }
    }
}

#[track_caller]
pub(crate) fn expect_unknown_containing(result: &VerifyResult, substring: &str, context: &str) {
    match result {
        VerifyResult::Unknown { reason, .. } => {
            assert!(
                reason.contains(substring),
                "{context} unknown reason should contain \"{substring}\", got: {reason}"
            );
        }
        other => {
            panic!("{context} should be Unknown containing \"{substring}\", got: {other:?}")
        }
    }
}

#[track_caller]
pub(crate) fn expect_not_verified(result: &VerifyResult, context: &str) {
    if matches!(result, VerifyResult::Verified) {
        panic!("{context} should NOT be Verified, got Verified");
    }
}

/// Soundness oracle for the incompleteness-vs-resource Unknown split
/// (`design-unknown-as-failure.md`). A genuine theory/decision-procedure
/// gap on a proof obligation must surface as a *model-less* verification
/// FAILURE — Verus's `Invalid(None, None, None)` — never as a soft resource
/// `Unknown` and never with a fabricated counterexample model. Asserts:
///
/// * the outcome is `NotProved` — a verdict of FAILURE, structurally incapable
///   of carrying a model, so no counterexample can have been fabricated;
/// * its category is genuinely `Incompleteness`, never a resource/timeout class
///   (a timeout does not mean the fact is false);
/// * never `Verified` (the obligation is undischarged), never a soft `Unknown`
///   (that is the pre-fix divergence from Verus), never a model-bearing
///   `Counterexample` (no witness exists), and never an encoder `Error` (that is
///   a different, infrastructural failure).
#[track_caller]
pub(crate) fn expect_incompleteness_modelless_failure(result: &VerifyResult, context: &str) {
    match result {
        VerifyResult::NotProved { category, reason } => {
            assert!(
                category.is_incompleteness(),
                "{context} NotProved must carry a genuine INCOMPLETENESS category — a \
                 resource/timeout unknown must never be reported as a failure; got \
                 {category:?}: {reason}"
            );
        }
        VerifyResult::Verified => {
            panic!("{context} should NOT verify (genuine incompleteness), got Verified")
        }
        VerifyResult::Unknown { category, reason } => panic!(
            "{context} should be a model-less NotProved failure (Verus Invalid(None,None,None)), \
             got a soft Unknown — this is exactly the divergence from Verus the design removes; \
             got {category:?}: {reason}"
        ),
        VerifyResult::Counterexample { model, .. } => panic!(
            "{context} incompleteness must never produce a model — the decision procedure \
             produced no witness; got Counterexample with model: {model:?}"
        ),
        VerifyResult::Error { message } => {
            panic!("{context} should be a model-less incompleteness failure, got Error: {message}")
        }
    }
}

/// Soundness boundary oracle, opposite side: a RESOURCE-class inconclusive
/// outcome (timeout / rlimit / cancellation / solver panic) must stay a soft
/// `Unknown` and must NEVER be promoted into a verification failure. More
/// budget might still prove the fact, so calling it a failure would be wrong.
#[track_caller]
#[allow(dead_code)] // Shared oracle retained for resource-limit regression lanes.
pub(crate) fn expect_resource_unknown_not_failure(result: &VerifyResult, context: &str) {
    match result {
        VerifyResult::Unknown { category, reason } => {
            assert!(
                !category.is_incompleteness(),
                "{context} expected a RESOURCE-class Unknown, got incompleteness \
                 {category:?}: {reason}"
            );
        }
        VerifyResult::NotProved { category, reason } => panic!(
            "{context} a resource/timeout Unknown must NEVER become a verification failure — \
             a timeout does not mean the fact is false; got NotProved {category:?}: {reason}"
        ),
        other => panic!("{context} should be a resource-class Unknown, got: {other:?}"),
    }
}

#[track_caller]
pub(crate) fn expect_verified_or_unknown(result: &VerifyResult, context: &str) {
    match result {
        VerifyResult::Verified | VerifyResult::Unknown { .. } => {}
        VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        } => panic!(
            "{context} should return Verified or Unknown, got Counterexample for '{obligation_name}' with model: {model:?}"
        ),
        VerifyResult::NotProved { reason, .. } => panic!(
            "{context} should return Verified or Unknown, got NotProved (no model): {reason}"
        ),
        VerifyResult::Error { message } => {
            panic!("{context} should return Verified or Unknown, got Error: {message}")
        }
    }
}

fn normalize_source(source: &str) -> String {
    let stripped: String = source.chars().filter(|ch| !ch.is_whitespace()).collect();
    // Collapse fully-qualified paths so `crate::encoder::VerifyResult::X` matches
    // the same banned patterns as the short form `VerifyResult::X`.
    stripped.replace("crate::encoder::VerifyResult::", "VerifyResult::")
}

fn find_matching_paren(source: &str, start: usize) -> Option<usize> {
    let bytes = source.as_bytes();
    let mut depth = 0usize;
    for (idx, byte) in bytes.iter().enumerate().skip(start) {
        match byte {
            b'(' => depth += 1,
            b')' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(idx);
                }
            }
            _ => {}
        }
    }
    None
}

fn raw_verifyresult_matches(source: &str) -> Vec<String> {
    let mut hits = Vec::new();
    let mut search_start = 0usize;
    while let Some(rel_idx) = source[search_start..].find("matches!(") {
        let idx = search_start + rel_idx;
        let open_idx = idx + "matches!".len();
        let Some(close_idx) = find_matching_paren(source, open_idx) else {
            break;
        };
        let body = &source[idx..=close_idx];
        if body.contains("VerifyResult::") {
            hits.push(body.to_string());
        }
        search_start = close_idx + 1;
    }
    hits
}

fn discover_test_files(dir: &std::path::Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    if let Ok(entries) = fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                files.extend(discover_test_files(&path));
            } else if path.extension().is_some_and(|ext| ext == "rs") {
                let name = path.file_name().unwrap().to_str().unwrap();
                // Exclude mod.rs, this file, and proptest files (prop_assert!
                // requires bool expressions — panic-based helpers don't work).
                if name != "mod.rs" && name != "result_oracles.rs" && !name.starts_with("proptest_")
                {
                    files.push(path);
                }
            }
        }
    }
    files
}

/// Recursively find `*_tests.rs` and `*_proof_tests.rs` files in `dir`,
/// covering test files outside `encoder/tests/` (#2636).
fn discover_suffixed_test_files(dir: &std::path::Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    if let Ok(entries) = fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                files.extend(discover_suffixed_test_files(&path));
            } else if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
                if (name.ends_with("_tests.rs") || name.ends_with("_proof_tests.rs"))
                    && name != "result_oracles.rs"
                {
                    files.push(path);
                }
            }
        }
    }
    files
}

#[test]
fn test_targeted_verification_tests_use_named_oracles() {
    const BANNED_PATTERNS: [(&str, &str); 10] = [
        (
            "!matches!(result, VerifyResult::Error { .. })",
            "!matches!(result,VerifyResult::Error{..})",
        ),
        (
            "VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. }",
            "VerifyResult::Counterexample{..}|VerifyResult::Unknown{..}",
        ),
        (
            "VerifyResult::Counterexample { .. } | VerifyResult::Error { .. }",
            "VerifyResult::Counterexample{..}|VerifyResult::Error{..}",
        ),
        (
            "!matches!(result, VerifyResult::Verified)",
            "!matches!(result,VerifyResult::Verified)",
        ),
        (
            "VerifyResult::Verified | VerifyResult::Unknown { .. }",
            "VerifyResult::Verified|VerifyResult::Unknown{..}",
        ),
        (
            "VerifyResult::Unknown { .. } | VerifyResult::Counterexample { .. }",
            "VerifyResult::Unknown{..}|VerifyResult::Counterexample{..}",
        ),
        (
            "VerifyResult::Error { .. } | VerifyResult::Counterexample { .. }",
            "VerifyResult::Error{..}|VerifyResult::Counterexample{..}",
        ),
        (
            "VerifyResult::Unknown { .. } | VerifyResult::Verified",
            "VerifyResult::Unknown{..}|VerifyResult::Verified",
        ),
        // Negation patterns that accept Error as passing (#2466 P1-978):
        (
            "!matches!(result, VerifyResult::Counterexample { .. })",
            "!matches!(result,VerifyResult::Counterexample{..})",
        ),
        (
            "!matches!(result, VerifyResult::Unknown { .. })",
            "!matches!(result,VerifyResult::Unknown{..})",
        ),
    ];

    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let tests_dir = manifest_dir.join("src/encoder/tests");
    let src_dir = manifest_dir.join("src");

    // Discover encoder test files (all .rs in encoder/tests/)
    let mut test_files = discover_test_files(&tests_dir);
    // Also discover *_tests.rs and *_proof_tests.rs anywhere in src/ (#2636)
    let suffixed = discover_suffixed_test_files(&src_dir);
    for path in suffixed {
        if !test_files.contains(&path) {
            test_files.push(path);
        }
    }

    assert!(
        test_files.len() > 40,
        "auto-discovery found only {} test files — expected >40",
        test_files.len()
    );

    for path in &test_files {
        let source = fs::read_to_string(path)
            .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
        let normalized = normalize_source(&source);
        let relative = path.strip_prefix(&manifest_dir).unwrap();
        let raw_matches = raw_verifyresult_matches(&normalized);
        assert!(
            raw_matches.is_empty(),
            "{} reintroduced raw VerifyResult matches: {:?}; use named helpers from result_oracles.rs instead",
            relative.display(),
            raw_matches,
        );
        for (display, normalized_pattern) in BANNED_PATTERNS {
            assert!(
                !normalized.contains(normalized_pattern),
                "{} reintroduced raw verification-result pattern `{display}`; use named helpers from result_oracles.rs instead",
                relative.display(),
            );
        }
    }
}
