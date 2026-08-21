// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! FV-3 regression: `cargo trust-vc check` must honour the SAME pointer-width
//! contract as the library entry point.
//!
//! `trust_vc_core::verify_function_from_file` implements the #2778 dual-arch
//! rule (`vc_extraction.rs`): a unit with no `global size_of usize` directive
//! whose proof mentions `usize`/`isize` is verified at BOTH a 32-bit and a
//! 64-bit `usize`, because Rust permits both and a proof is sound only if it
//! holds at every width the target may have. The doc comment there states the
//! contract verbatim — "Under-approximating would be unsound (a genuinely
//! width-dependent proof verified at only one width)".
//!
//! The CLI did not implement it: it installed the host width (or a pinned
//! directive width) and solved ONCE. On a 64-bit host the byte-identical unit
//!
//! ```ignore
//! #[trust_vc::requires(x <= 4294967295)]
//! #[trust_vc::ensures(result >= x)]
//! fn dbl(x: usize) -> usize { x * 2 }
//! ```
//!
//! came back `"result": "verified"` from `cargo trust-vc check --json` while
//! `verify_function_from_file` produced a counterexample (at a 32-bit `usize`,
//! `x = 4294967295` makes `x * 2` overflow, so `result >= x` is FALSE). Two
//! entry points, one file, opposite verdicts — a proof hole against trust-vc's
//! own declared portability contract.
//!
//! Routing the CLI through the dual-width plan can only ADD rejections, so it
//! cannot introduce a hole. The three pins below keep it from degenerating into
//! blanket rejection or blanket double-solving:
//!
//! * `width_polymorphic_true_at_both_widths_still_verifies` — a unit that names
//!   `usize` and is genuinely true at 32 AND 64 bits must still verify.
//! * `non_width_polymorphic_unit_is_unchanged` — a unit that names no
//!   `usize`/`isize` must keep its verdict (and, per the unit-level pin in
//!   `verify.rs`, stay on the single-solve `WidthPlan::Host` path).
//! * `pinned_directive_width_still_wins` — `global size_of usize == 8` pins the
//!   target architecture, so the SAME false-at-32-bit unit verifies again; the
//!   dual path must not override an explicit directive.

use serde_json::Value;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("repo root should canonicalize")
}

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
    let fallback = repo_root().join("target/debug").join(&binary_name);
    assert!(
        fallback.exists(),
        "cargo-trust-vc binary not found; run `targo build -p targo-trust-vc --bin cargo-trust-vc` first"
    );
    fallback
}

fn temp_crate_dir() -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after UNIX_EPOCH")
        .as_nanos();
    let sequence = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!(
        "cargo_trust_vc_dual_width_{}_{}_{}",
        std::process::id(),
        unique,
        sequence
    ))
}

/// Writes a standalone crate whose `src/lib.rs` is exactly `source`.
fn write_crate(source: &str) -> PathBuf {
    let root = temp_crate_dir();
    std::fs::create_dir_all(root.join("src")).expect("src dir should be created");
    std::fs::write(
        root.join("Cargo.toml"),
        "[package]\nname = \"dual_width_probe\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[dependencies]\n\n[workspace]\n",
    )
    .expect("manifest should be written");
    std::fs::write(root.join("src/lib.rs"), source).expect("source should be written");
    root
}

fn check_function(root: &Path, function: &str) -> (Value, String) {
    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(root)
        // Soundness verdicts must never be read out of a warm cache.
        .env("TRUST_VC_DISABLE_VC_CACHE", "1")
        .arg("check")
        .arg("--json")
        .arg("--function")
        .arg(function)
        .arg(".")
        .output()
        .expect("cargo-trust-vc should execute");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let json: Value = serde_json::from_str(&stdout)
        .unwrap_or_else(|err| panic!("stdout should be cargo-trust-vc JSON: {err}\n{stdout}"));
    (json, stderr)
}

fn function_result(report: &Value, function: &str) -> String {
    let functions = report["functions"]
        .as_array()
        .expect("functions should be an array");
    assert_eq!(
        functions.len(),
        1,
        "expected exactly one checked function `{function}`: {report:#?}"
    );
    assert_eq!(functions[0]["name"], function);
    functions[0]["result"]
        .as_str()
        .expect("function result should be a string")
        .to_string()
}

/// The unit under test is FALSE at a 32-bit `usize`, so it must not verify.
///
/// A `counterexample` or `unknown` both satisfy the soundness bar
/// (over-rejection is acceptable); an `error` does NOT — that would mean the
/// probe failed for infrastructure reasons and proved nothing.
fn assert_rejected(root: &Path, function: &str) {
    let (report, stderr) = check_function(root, function);
    let result = function_result(&report, function);
    assert!(
        result == "counterexample" || result == "unknown",
        "`{function}` is FALSE at a 32-bit usize and must not verify, and must \
         be rejected for a real reason (got `{result}`)\nstderr={stderr}\nreport={report:#?}"
    );
}

fn assert_verifies(root: &Path, function: &str) {
    let (report, stderr) = check_function(root, function);
    assert_eq!(
        function_result(&report, function),
        "verified",
        "`{function}` must still verify\nstderr={stderr}\nreport={report:#?}"
    );
}

/// THE REPRODUCER. Byte-identical source, two entry points, one verdict.
///
/// `x * 2` with `x: usize` and `x <= 4294967295` overflows a 32-bit `usize`,
/// so `result >= x` is false there. Before the fix the CLI answered
/// `"verified"`.
#[test]
fn width_polymorphic_false_at_32_bits_is_rejected_by_the_cli() {
    let root = write_crate(
        r#"#[trust_vc::requires(x <= 4294967295)]
#[trust_vc::ensures(result >= x)]
fn dbl(x: usize) -> usize { x * 2 }
"#,
    );
    assert_rejected(&root, "dbl");
    let _ = std::fs::remove_dir_all(&root);
}

/// NARROWNESS PIN 1 — the fix must not reject every `usize` unit.
///
/// Same shape as the reproducer (names `usize`, doubles its argument) but with
/// a precondition that holds at BOTH widths, so both passes discharge and the
/// combined verdict stays `verified`.
#[test]
fn width_polymorphic_true_at_both_widths_still_verifies() {
    let root = write_crate(
        r#"#[trust_vc::requires(x <= 100)]
#[trust_vc::ensures(result >= x)]
fn dbl_small(x: usize) -> usize { x * 2 }
"#,
    );
    assert_verifies(&root, "dbl_small");
    let _ = std::fs::remove_dir_all(&root);
}

/// NARROWNESS PIN 2 — a unit that names no `usize`/`isize` is untouched.
///
/// `u32` is width-invariant, so this stays on the single-solve host-width path.
/// The "no second solve" half of this pin is asserted directly on `WidthPlan`
/// by `non_width_polymorphic_unit_plans_a_single_host_solve` in `verify.rs`;
/// here we pin the verdict end to end.
#[test]
fn non_width_polymorphic_unit_is_unchanged() {
    let root = write_crate(
        r#"#[trust_vc::requires(x <= 4294967295)]
#[trust_vc::ensures(result >= x)]
fn dbl_u64(x: u64) -> u64 { x * 2 }
"#,
    );
    assert_verifies(&root, "dbl_u64");
    let _ = std::fs::remove_dir_all(&root);
}

/// NARROWNESS PIN 3 — an explicit `global size_of usize == 8` directive pins
/// the target architecture, so the unit is verified ONLY at 64 bits and the
/// otherwise-rejected reproducer verifies again. The dual path must never
/// override a directive; that would make the directive unusable.
#[test]
fn pinned_directive_width_still_wins() {
    let root = write_crate(
        r#"global size_of usize == 8;

#[trust_vc::requires(x <= 4294967295)]
#[trust_vc::ensures(result >= x)]
fn dbl_pinned(x: usize) -> usize { x * 2 }
"#,
    );
    assert_verifies(&root, "dbl_pinned");
    let _ = std::fs::remove_dir_all(&root);
}
