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
        "cargo-trust-vc binary not found; run `targo --unverified build -p targo-trust-vc --bin cargo-trust-vc` first"
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

// ---------------------------------------------------------------------------
// FV-2: the width PLAN under-approximated.
//
// `width_plan_for` decided dual-vs-single by scanning the FUNCTION's token
// stream for a literal `usize`/`isize`. `usize` reaches a unit through routes
// that leave no such token inside the function — a type alias, a nested alias, a
// struct field, a numeric literal suffix — so the selector answered `Host`, the
// 32-bit pass that refutes never ran, and a program that is FALSE at a 32-bit
// `usize` came back `"verified"` from `cargo trust-vc check --json` on a 64-bit
// host.
//
// The rest of the pipeline was never blind: prepending `global size_of usize ==
// 4;` to each of these files yields a counterexample for every one of them
// (measured before the fix). Only the plan selector could not see the route —
// the worst place for the blindness, because it decides whether the refuting
// pass runs at all.
//
// Each reproducer below is paired with a control of the SAME shape that is true
// at both widths, so a fix that simply rejects everything with an alias or a
// struct field fails the pair.
// ---------------------------------------------------------------------------

/// `usize` behind a type alias — no `usize` token in `dbl`.
#[test]
fn width_behind_a_type_alias_is_rejected() {
    let root = write_crate(
        r#"type Idx = usize;

#[trust_vc::requires(x <= 4294967295)]
#[trust_vc::ensures(result >= x)]
fn dbl_alias(x: Idx) -> Idx { x * 2 }

#[trust_vc::requires(x <= 100)]
#[trust_vc::ensures(result >= x)]
fn dbl_alias_small(x: Idx) -> Idx { x * 2 }
"#,
    );
    assert_rejected(&root, "dbl_alias");
    // NARROWNESS PIN: the same alias route, true at both widths, still verifies.
    assert_verifies(&root, "dbl_alias_small");
    let _ = std::fs::remove_dir_all(&root);
}

/// `usize` behind a NESTED alias — two hops from any `usize` token.
#[test]
fn width_behind_a_nested_type_alias_is_rejected() {
    let root = write_crate(
        r#"type Idx = usize;
type Idx2 = Idx;

#[trust_vc::requires(x <= 4294967295)]
#[trust_vc::ensures(result >= x)]
fn dbl_nested(x: Idx2) -> Idx2 { x * 2 }
"#,
    );
    assert_rejected(&root, "dbl_nested");
    let _ = std::fs::remove_dir_all(&root);
}

/// `isize` behind an alias. `2 * 1073741824` overflows a 32-bit `isize`
/// (`isize::MAX == 2^31 - 1`) but not a 64-bit one.
#[test]
fn isize_behind_a_type_alias_is_rejected() {
    let root = write_crate(
        r#"type SIdx = isize;

#[trust_vc::requires(x >= 0)]
#[trust_vc::requires(x <= 1073741824)]
#[trust_vc::ensures(result >= x)]
fn dbl_isize(x: SIdx) -> SIdx { x * 2 }
"#,
    );
    assert_rejected(&root, "dbl_isize");
    let _ = std::fs::remove_dir_all(&root);
}

/// `usize` reached through a STRUCT FIELD. The function's tokens name only the
/// struct and the field.
#[test]
fn width_behind_a_struct_field_is_rejected() {
    let root = write_crate(
        r#"struct Holder { n: usize }

#[trust_vc::requires(h.n <= 4294967295)]
fn field_dbl(h: Holder) { assert!(h.n * 2 >= h.n); }

#[trust_vc::requires(h.n <= 100)]
fn field_dbl_small(h: Holder) { assert!(h.n * 2 >= h.n); }
"#,
    );
    assert_rejected(&root, "field_dbl");
    // NARROWNESS PIN: same struct-field route, true at both widths.
    assert_verifies(&root, "field_dbl_small");
    let _ = std::fs::remove_dir_all(&root);
}

/// `usize` present ONLY as a numeric literal suffix.
///
/// This one was a CLI-ONLY hole: the library's copy of the predicate handled
/// `Literal` tokens, the CLI's hand-copied twin did not. Both entry points now
/// call the one implementation in `trust_vc_core::ir`, so the copies cannot
/// drift apart again.
#[test]
fn width_from_a_numeric_literal_suffix_is_rejected() {
    let root = write_crate(
        r#"#[trust_vc::ensures(result == 4294967296)]
fn suffix_add() -> u64 { (4294967295usize + 1) as u64 }
"#,
    );
    assert_rejected(&root, "suffix_add");
    let _ = std::fs::remove_dir_all(&root);
}

// ---------------------------------------------------------------------------
// FV-4: the width plan was not consulted by the trait-impl CONFORMANCE lane.
//
// The two fixes above widened the PREDICATE and unified its two copies. They did
// not widen WHO CALLS IT. `width_plan_for` / `run_under_width_plan` are reached
// only from `load_context_and_report` and `verify_result_for` — the FUNCTION
// lane. The conformance lane (`verify_conformance_obligation`) instead installed
// `install_pointer_width_for`, which returns ONLY a pinned `global size_of
// usize` directive and otherwise leaves the host's 64-bit `usize` in force, and
// the library entry point it delegates to
// (`trust_vc_core::verify_trait_conformance_obligation`) did exactly the same.
// So a trait-impl conformance obligation that is FALSE at a 32-bit `usize`
// reported `"verified"` — and the conformance lane is, by design, the ONLY
// channel through which a non-conforming impl is reported.
//
// The reproducer below is unmasked: with TWO impls the function lane no longer
// flags anything, so before the fix `cargo trust-vc check --json` returned
// `"verified": 3, "counterexample": 0` for the whole file.
//
// The plan now lives in the library, so BOTH entry points get it, and each
// reproducer is paired with a control of the same shape that is true at both
// widths.
// ---------------------------------------------------------------------------

/// A trait `ensures` that the impl body satisfies at a 64-bit `usize` and
/// violates at a 32-bit one. `x * 2` with `x <= 4294967295` overflows a 32-bit
/// `usize`, so `result >= x` is false there.
const CONFORMANCE_WIDTH_SOURCE: &str = r#"#[trust_vc::trait_spec]
trait Doubler {
    #[trust_vc::requires(x <= 4294967295)]
    #[trust_vc::ensures(result >= x)]
    fn dbl(x: usize) -> usize;
}

struct Honest;
struct Wide;

#[trust_vc::trait_impl]
impl Doubler for Honest {
    fn dbl(x: usize) -> usize { x }
}

#[trust_vc::trait_impl]
impl Doubler for Wide {
    fn dbl(x: usize) -> usize { x * 2 }
}
"#;

/// THE REPRODUCER. Addressed by the exact obligation name `cargo trust-vc check`
/// reports, which is the same name `list_trait_conformance_obligations` emits.
#[test]
fn conformance_false_at_32_bits_is_rejected_by_the_cli() {
    let root = write_crate(CONFORMANCE_WIDTH_SOURCE);
    assert_rejected(&root, "trait impl conformance Doubler::dbl for Wide");
    // NARROWNESS PIN, same file, same trait, same `usize` contract: the honest
    // impl conforms at BOTH widths and must still verify. A fix that rejected
    // the whole width-polymorphic file would pass the line above and fail here.
    assert_verifies(&root, "trait impl conformance Doubler::dbl for Honest");
    let _ = std::fs::remove_dir_all(&root);
}

/// NARROWNESS PIN — a width-polymorphic conformance obligation that holds at 32
/// AND 64 bits must still verify. `x + 1` under `x < 100` cannot overflow at
/// either width, so both passes discharge.
#[test]
fn conformance_true_at_both_widths_still_verifies() {
    let root = write_crate(
        r#"#[trust_vc::trait_spec]
trait Inc {
    #[trust_vc::requires(x < 100)]
    #[trust_vc::ensures(result > x)]
    fn inc(x: usize) -> usize;
}

struct S;

#[trust_vc::trait_impl]
impl Inc for S {
    fn inc(x: usize) -> usize { x + 1 }
}
"#,
    );
    assert_verifies(&root, "trait impl conformance Inc::inc for S");
    let _ = std::fs::remove_dir_all(&root);
}

/// NARROWNESS PIN — a conformance obligation over `u32` names no
/// `usize`/`isize`, so the file stays on the single-solve plan and its verdict
/// is untouched.
#[test]
fn conformance_non_width_polymorphic_is_unchanged() {
    let root = write_crate(
        r#"#[trust_vc::trait_spec]
trait Adder {
    #[trust_vc::requires(x <= 100)]
    #[trust_vc::ensures(result >= x)]
    fn add(x: u32) -> u32;
}

struct Plain;

#[trust_vc::trait_impl]
impl Adder for Plain {
    fn add(x: u32) -> u32 { x + 1 }
}
"#,
    );
    assert_verifies(&root, "trait impl conformance Adder::add for Plain");
    let _ = std::fs::remove_dir_all(&root);
}

/// NARROWNESS PIN — `global size_of usize == 8` pins the target architecture for
/// the conformance lane too, so the otherwise-rejected impl verifies again. The
/// dual path must never override an explicit directive.
#[test]
fn conformance_pinned_directive_width_still_wins() {
    let mut source = String::from("global size_of usize == 8;\n\n");
    source.push_str(CONFORMANCE_WIDTH_SOURCE);
    let root = write_crate(&source);
    assert_verifies(&root, "trait impl conformance Doubler::dbl for Wide");
    let _ = std::fs::remove_dir_all(&root);
}
