// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! End-to-end pins for the report's accounting invariant:
//!
//! ```text
//! verified + counterexample + unknown + error + skipped + not_analyzed
//!     + file_error
//!     == number of check targets scanned in the file
//! ```
//!
//! For every fixture here that parses, that is the `fn` item count: none of them
//! registers a `#[trust_vc::trait_spec]`/`trait_impl`, which is the only thing
//! that adds per-impl conformance obligations as targets in their own right. A
//! fixture that does NOT parse contributes one `file_error` target instead — its
//! function count is unknown, not zero.
//!
//! # What these are guarding against
//!
//! `cargo trust-vc check --json` used to report only the functions it VERIFIED.
//! A function whose sole contract was spelled through a legal Rust rename —
//!
//! ```ignore
//! use trust_vc::ensures as promises;
//! #[promises(result == 42u64)]
//! pub fn liar() -> u64 { 7u64 }
//! ```
//!
//! — was invisible to attribute discovery, so it appeared in NO bucket at all:
//! `"functions": []`, `{"verified":0,...,"skipped":0}`, exit 0. The author wrote
//! a FALSE postcondition and the tool answered with what looks exactly like a
//! clean pass. No false proof was emitted; the failure was that nothing was said
//! at all.
//!
//! The SAME silence survived one level up, at the file. A file that failed to
//! parse also produced `"functions": []`, an all-zero summary and exit 0 — and
//! there it swallowed not one contract but every contract in the file. Both are
//! closed the same way and are pinned together here.
//!
//! Making the buckets a PARTITION of the scanned set is what closes that. A
//! dropped function, or a file nobody could read, no longer produces a quiet
//! report — it produces a sum that does not add up, and these tests fail.

use serde_json::Value;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

fn cargo_trust_vc_bin() -> PathBuf {
    for key in [
        "CARGO_BIN_EXE_cargo-trust-vc",
        "CARGO_BIN_EXE_cargo_trust_vc",
    ] {
        if let Ok(path) = std::env::var(key) {
            return PathBuf::from(path);
        }
    }
    let binary_name = format!("cargo-trust-vc{}", std::env::consts::EXE_SUFFIX);
    if let Ok(target_dir) = std::env::var("CARGO_TARGET_DIR") {
        let candidate = PathBuf::from(target_dir).join("debug").join(&binary_name);
        if candidate.exists() {
            return candidate;
        }
    }
    let fallback = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/debug")
        .join(&binary_name);
    if fallback.exists() {
        return fallback;
    }
    panic!("cargo-trust-vc binary not found; build the workspace first");
}

fn temp_dir(label: &str) -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after UNIX_EPOCH")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "trust_vc_not_analyzed_{label}_{}_{}",
        std::process::id(),
        unique
    ));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    dir
}

struct CheckRun {
    json: Value,
    exit_code: i32,
}

impl CheckRun {
    fn bucket(&self, name: &str) -> u64 {
        self.json["summary"][name]
            .as_u64()
            .unwrap_or_else(|| panic!("summary is missing `{name}`: {}", self.json["summary"]))
    }

    /// `file_error` is serialized only when nonzero, so it is read leniently.
    /// Its ABSENCE is itself pinned, by
    /// `a_valid_file_reports_no_file_level_failure`.
    fn file_error(&self) -> u64 {
        self.json["summary"]["file_error"].as_u64().unwrap_or(0)
    }

    fn summed_buckets(&self) -> u64 {
        [
            "verified",
            "counterexample",
            "unknown",
            "error",
            "skipped",
            "not_analyzed",
        ]
        .iter()
        .map(|name| self.bucket(name))
        .sum::<u64>()
            + self.file_error()
    }

    fn entry(&self, name: &str) -> &Value {
        self.json["functions"]
            .as_array()
            .expect("functions is an array")
            .iter()
            .find(|entry| entry["name"] == name)
            .unwrap_or_else(|| {
                panic!(
                    "function `{name}` is absent from the report — a scanned function must \
                     never be silently dropped. Report was: {}",
                    serde_json::to_string_pretty(&self.json).unwrap_or_default()
                )
            })
    }

    fn result_of(&self, name: &str) -> &str {
        self.entry(name)["result"]
            .as_str()
            .expect("result is a string")
    }
}

fn run_check(source: &str, label: &str) -> CheckRun {
    let dir = temp_dir(label);
    let file = dir.join(format!("{label}.rs"));
    std::fs::write(&file, source).expect("write fixture");
    run_check_on(&file)
}

fn run_check_on(file: &Path) -> CheckRun {
    let output = Command::new(cargo_trust_vc_bin())
        .args(["trust-vc", "check", "--json"])
        .arg(file)
        .env("TRUST_VC_DISABLE_VC_CACHE", "1")
        .output()
        .expect("run cargo-trust-vc");
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let json: Value = serde_json::from_str(&stdout).unwrap_or_else(|err| {
        panic!(
            "check did not emit JSON ({err}).\nstdout:\n{stdout}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stderr)
        )
    });
    CheckRun {
        json,
        exit_code: output.status.code().unwrap_or(-1),
    }
}

/// Counts `fn` items exactly where the scanner counts them: free functions,
/// inherent- and trait-impl methods, trait methods, and the same inside inline
/// modules. Deliberately re-derived here from `syn` rather than asked of the
/// scanner, so this is an INDEPENDENT denominator and not the scanner grading
/// its own homework.
fn count_fn_items(source: &str) -> usize {
    fn count_items(items: &[syn::Item]) -> usize {
        let mut total = 0;
        for item in items {
            match item {
                syn::Item::Fn(_) => total += 1,
                syn::Item::Impl(block) => {
                    total += block
                        .items
                        .iter()
                        .filter(|i| matches!(i, syn::ImplItem::Fn(_)))
                        .count();
                }
                syn::Item::Trait(block) => {
                    total += block
                        .items
                        .iter()
                        .filter(|i| matches!(i, syn::TraitItem::Fn(_)))
                        .count();
                }
                syn::Item::Mod(module) => {
                    if let Some((_, items)) = &module.content {
                        total += count_items(items);
                    }
                }
                _ => {}
            }
        }
        total
    }
    let file: syn::File = syn::parse_file(source).expect("fixture parses as Rust");
    count_items(&file.items)
}

/// One fixture carrying every shape the report has to account for.
const MIXED_SHAPES: &str = r#"
use trust_vc::ensures as promises;

// 1. A truthful contract in the canonical spelling — must verify.
#[trust_vc::ensures(result == 8u64)]
pub fn truthful(x: u64) -> u64 { let _ = x; 8u64 }

// 2. A FALSE contract in the canonical spelling — must be refuted.
#[trust_vc::ensures(result == 42u64)]
pub fn canonical_liar() -> u64 { 7u64 }

// 3. A FALSE contract reached through a legal `use ... as ...` rename. This is
//    the shape that used to vanish from the report entirely.
#[promises(result == 42u64)]
pub fn aliased_liar() -> u64 { 7u64 }

// 4. A marker attribute with no contract — a recognized, deliberately skipped
//    target.
#[trust_vc::proof]
pub fn marker_only() {}

// 5. A plain helper with no annotations whatsoever — legitimate and common.
pub fn plain_helper(x: u64) -> u64 { x + 1 }

// 6. A helper carrying an attribute that has nothing to do with verification.
//    (`#[inline]` is deliberately NOT used here: `inline` is also a trust_vc
//    marker name, so it lands in `skipped` rather than `not_analyzed`.)
#[allow(dead_code)]
pub fn attributed_helper(x: u64) -> u64 { x + 2 }

mod inner {
    // 7. A function inside an inline module.
    pub fn nested_helper() -> u64 { 3u64 }
}
"#;

#[test]
fn every_scanned_function_appears_in_exactly_one_bucket() {
    let run = run_check(MIXED_SHAPES, "mixed_shapes");
    let scanned = count_fn_items(MIXED_SHAPES) as u64;

    assert_eq!(
        run.summed_buckets(),
        scanned,
        "the report's buckets must PARTITION the scanned functions, but \
         {} bucketed vs {scanned} `fn` items scanned.\nReport: {}",
        run.summed_buckets(),
        serde_json::to_string_pretty(&run.json).unwrap_or_default()
    );

    let entries = run.json["functions"]
        .as_array()
        .expect("functions is an array");
    assert_eq!(
        entries.len() as u64,
        scanned,
        "every scanned function needs its own report entry"
    );
    assert_eq!(
        entries.len() as u64,
        run.summed_buckets(),
        "the summary must count exactly the entries it lists"
    );
}

/// The defect itself: a false contract behind a rename must never be silent.
///
/// It is resolved back to the canonical spelling, so it REFUTES. The one answer
/// that must never appear is `verified` — and the one absence that must never
/// appear is no entry at all.
#[test]
fn an_aliased_false_contract_is_refuted_not_dropped() {
    let run = run_check(
        "use trust_vc::ensures as promises;\n\
         #[promises(result == 42u64)]\n\
         pub fn aliased_attr_liar_must_not_verify() -> u64 { 7u64 }\n",
        "aliased_liar",
    );
    assert_eq!(
        run.result_of("aliased_attr_liar_must_not_verify"),
        "counterexample",
        "a false postcondition written through `use trust_vc::ensures as ..` must be refuted"
    );
    assert_eq!(run.bucket("counterexample"), 1);
    assert_eq!(run.exit_code, 1, "a refuted contract must fail the check");
}

/// The alias lane and the canonical lane must produce the SAME verdict for the
/// same program. Renaming an import is not a proof-relevant act.
#[test]
fn the_alias_lane_agrees_with_the_canonical_lane() {
    let aliased = run_check(
        "use trust_vc::{requires as pre, ensures as post};\n\
         #[pre(x > 0u64)]\n\
         #[post(result > 0u64)]\n\
         pub fn f(x: u64) -> u64 { x }\n",
        "alias_truthful",
    );
    let canonical = run_check(
        "#[trust_vc::requires(x > 0u64)]\n\
         #[trust_vc::ensures(result > 0u64)]\n\
         pub fn f(x: u64) -> u64 { x }\n",
        "canonical_truthful",
    );
    assert_eq!(
        aliased.result_of("f"),
        canonical.result_of("f"),
        "aliased and canonical spellings of the same contract disagreed"
    );
    assert_eq!(aliased.result_of("f"), "verified");
}

/// A contract written as a body MACRO is a proof claim the source-verification
/// lane cannot read. It used to drop the whole function; it must now say so.
#[test]
fn a_macro_form_contract_is_reported_with_its_reason() {
    let run = run_check(
        "pub fn macroform_only_liar(x: u64) -> u64 {\n\
         \x20   trust_vc::requires!(x > 0);\n\
         \x20   trust_vc::ensures!(result == 42u64);\n\
         \x20   7u64\n\
         }\n",
        "macro_form",
    );
    let entry = run.entry("macroform_only_liar");
    assert_eq!(
        entry["result"], "not_analyzed",
        "a macro-form contract must be reported, not dropped"
    );
    let detail = entry["detail"].as_str().unwrap_or_default();
    assert!(
        detail.contains("body macro") && detail.contains("not checked"),
        "the reason must state that the claim was NOT checked; got: {detail}"
    );
    assert_eq!(run.summed_buckets(), 1);
}

/// Honest reporting must not become noisy reporting: a file of ordinary helpers
/// still exits 0, and a true contract sitting beside them still verifies.
#[test]
fn plain_helpers_are_not_analyzed_and_do_not_redden_the_run() {
    let source = "pub fn helper_a(x: u64) -> u64 { x + 1 }\n\
                  fn helper_b() {}\n\
                  fn helper_c(a: u64, b: u64) -> u64 { a * b }\n\
                  #[trust_vc::ensures(result == 8u64)]\n\
                  pub fn truthful(x: u64) -> u64 { let _ = x; 8u64 }\n";
    let run = run_check(source, "plain_helpers");

    assert_eq!(run.exit_code, 0, "uncontracted helpers must not fail a run");
    assert_eq!(run.bucket("not_analyzed"), 3);
    assert_eq!(run.bucket("verified"), 1);
    assert_eq!(run.summed_buckets(), count_fn_items(source) as u64);
    assert_eq!(run.result_of("truthful"), "verified");
    for helper in ["helper_a", "helper_b", "helper_c"] {
        assert_eq!(run.result_of(helper), "not_analyzed");
        assert_eq!(
            run.entry(helper)["detail"],
            "no contract attributes",
            "an uncontracted helper's reason must be plain and honest"
        );
    }
}

/// The control: the canonical spelling is untouched by any of this.
#[test]
fn the_canonical_spelling_still_refutes_with_its_counterexample() {
    let run = run_check(
        "#[trust_vc::ensures(result == 42u64)]\n\
         pub fn canonical_attr_liar_must_refute() -> u64 { 7u64 }\n",
        "canonical_control",
    );
    assert_eq!(
        run.result_of("canonical_attr_liar_must_refute"),
        "counterexample"
    );
    let detail = run.entry("canonical_attr_liar_must_refute")["detail"]
        .as_str()
        .unwrap_or_default();
    assert!(
        detail.contains("result = 7"),
        "the control lost its counterexample binding; got: {detail}"
    );
    assert_eq!(run.exit_code, 1);
}

/// THE file-level defect: a syntax error must not read as a clean pass.
///
/// One level up from the dropped-function case, the same silence survived. A
/// file that failed to PARSE produced an empty scan, and an empty scan is what an
/// empty file produces: `"functions": []`, an all-zero summary and **exit 0**,
/// with nothing but a stderr line to distinguish it. The contracts in the file —
/// including this fixture's FALSE one — were never looked at, and the report said
/// so nowhere.
#[test]
fn a_syntax_error_is_a_reported_failure_not_a_clean_pass() {
    // A false postcondition sitting behind an unbalanced brace: if the parse
    // failure were still silent, this liar would go unmentioned.
    let run = run_check(
        "#[trust_vc::ensures(result == 42u64)]\n\
         pub fn liar_behind_a_syntax_error() -> u64 {\n\
         \x20   7u64\n",
        "syntax_error",
    );

    assert_ne!(
        run.exit_code,
        0,
        "a file that could not be parsed must never exit 0.\nReport: {}",
        serde_json::to_string_pretty(&run.json).unwrap_or_default()
    );

    let errors = run.json["file_errors"].as_array().unwrap_or_else(|| {
        panic!(
            "the report must carry a file-level error entry.\nReport: {}",
            serde_json::to_string_pretty(&run.json).unwrap_or_default()
        )
    });
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(errors[0]["result"], "error");
    assert!(
        errors[0]["file"]
            .as_str()
            .unwrap_or_default()
            .ends_with("syntax_error.rs"),
        "the entry must name the file it is about: {}",
        errors[0]["file"]
    );
    let detail = errors[0]["detail"].as_str().unwrap_or_default();
    assert!(
        detail.contains("cannot parse source"),
        "the entry must carry the parse message; got: {detail}"
    );

    assert_eq!(run.file_error(), 1);
    assert_eq!(
        run.summed_buckets(),
        1,
        "the failed file is one accounted-for target, not zero"
    );
    assert!(
        run.json["functions"]
            .as_array()
            .expect("functions is an array")
            .is_empty(),
        "an unparsed file has no known functions to report"
    );
}

/// The control, and the no-drift pin: a file that DOES parse says nothing new.
///
/// Neither the top-level `file_errors` array nor the summary's `file_error`
/// count appears, so the report over valid input is the schema it always was.
#[test]
fn a_valid_file_reports_no_file_level_failure() {
    let source = "#[trust_vc::ensures(result == 7u64)]\n\
                  pub fn honest() -> u64 { 7u64 }\n";
    let run = run_check(source, "valid_control");

    assert_eq!(run.exit_code, 0);
    assert!(
        run.json.get("file_errors").is_none(),
        "the file-error array must be ABSENT for a scannable file, not empty"
    );
    assert!(
        run.json["summary"].get("file_error").is_none(),
        "the file-error count must be ABSENT for a scannable file, not zero"
    );
    assert_eq!(run.summed_buckets(), count_fn_items(source) as u64);
    assert_eq!(run.result_of("honest"), "verified");
}

/// One unparseable file in a crate must not be absorbed by its healthy
/// neighbours: the good file still verifies, and the bad file still reddens the
/// run.
#[test]
fn a_bad_file_beside_a_good_one_stays_visible() {
    let dir = temp_dir("crate_with_one_bad_file");
    let src = dir.join("src");
    std::fs::create_dir_all(&src).expect("create src");
    std::fs::write(
        src.join("good.rs"),
        "#[trust_vc::ensures(result == 7u64)]\npub fn honest() -> u64 { 7u64 }\n",
    )
    .expect("write good");
    std::fs::write(src.join("bad.rs"), "pub fn broken( -> u64 {\n").expect("write bad");

    let run = run_check_on(&dir);
    assert_ne!(run.exit_code, 0, "one unparsed file must fail the run");
    assert_eq!(run.bucket("verified"), 1, "the good file still verifies");
    assert_eq!(run.file_error(), 1);
    let errors = run.json["file_errors"]
        .as_array()
        .expect("file_errors present");
    assert!(
        errors[0]["file"]
            .as_str()
            .unwrap_or_default()
            .ends_with("bad.rs"),
        "{}",
        errors[0]["file"]
    );
}

/// A name filter cannot rule a function IN or OUT of a file that never parsed,
/// so it must not answer "no such function" — that would be a claim about source
/// nobody read.
#[test]
fn a_function_filter_over_an_unparsed_file_still_reports_the_failure() {
    let dir = temp_dir("filtered_syntax_error");
    let file = dir.join("filtered_syntax_error.rs");
    std::fs::write(&file, "pub fn broken( -> u64 {\n").expect("write fixture");

    let output = Command::new(cargo_trust_vc_bin())
        .args(["trust-vc", "check", "--json", "--function", "anything"])
        .arg(&file)
        .env("TRUST_VC_DISABLE_VC_CACHE", "1")
        .output()
        .expect("run cargo-trust-vc");
    assert_ne!(output.status.code().unwrap_or(-1), 0);
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let json: Value = serde_json::from_str(&stdout).unwrap_or_else(|err| {
        panic!(
            "check did not emit JSON ({err}).\nstdout:\n{stdout}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stderr)
        )
    });
    assert_eq!(
        json["summary"]["file_error"], 1,
        "a filtered run over an unparsed file must still report the failure"
    );
}

/// An ambiguous rename is DECLINED, never guessed. The function stays visible
/// with a reason rather than taking one arbitrary reading of the contract.
#[test]
fn an_ambiguous_rename_leaves_the_function_visible_and_unresolved() {
    let source = "use trust_vc::ensures as post;\n\
                  use trust_vc::requires as post;\n\
                  #[post(result == 42u64)]\n\
                  pub fn ambiguous(x: u64) -> u64 { let _ = x; 7u64 }\n";
    let run = run_check(source, "ambiguous_rename");
    assert_eq!(
        run.result_of("ambiguous"),
        "not_analyzed",
        "an ambiguous rename must not be silently resolved one way"
    );
    let detail = run.entry("ambiguous")["detail"]
        .as_str()
        .unwrap_or_default();
    assert!(
        detail.contains("post"),
        "the reason must name the attribute that was not understood; got: {detail}"
    );
    assert_eq!(run.summed_buckets(), count_fn_items(source) as u64);
}
