// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! PINS: a refuted obligation must report the SOURCE LINE it fails on.
//!
//! # Why this file exists
//!
//! The file-context lane — `verify_one_detailed`, which is the lane the whole
//! ported Verus corpus runs through — recorded no source position for any
//! obligation. Every counterexample case in the evidence gate therefore failed
//! with "refuted obligation `<kind> <name>` has no readable source line
//! (location None), so the upstream `FAILS` marker cannot be checked": the
//! engine could say WHICH obligation was refuted and never WHERE.
//!
//! # Why a WRONG line would be worse than none
//!
//! The gate cross-checks the reported line against upstream Verus's own
//! `FAILS`-marked line. A line that is merely PLAUSIBLE — the function's line,
//! the enclosing block's line — would make cases pass and fail for the wrong
//! reason, which is unrecoverable evidence: the number would look like
//! progress. So every pin below states the expected line as a LITERAL and also
//! re-reads that line out of the fixture and requires it to carry the fixture's
//! own `// FAILS` marker. The literal fails when the line moves; the marker
//! re-read fails when the literal was updated to whatever the engine happened
//! to print.

use super::{verify_one_detailed, ObligationStatus};
use crate::scan::AnnotatedFunction;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

/// The fixture. EVERY line that an obligation must be reported on carries
/// `// FAILS`, exactly as the ported corpus marks upstream's own marked lines.
///
/// Written as one const so the line numbers the pins assert are the line
/// numbers of this text, counting the first line (`// line 1`) as line 1.
const FIXTURE: &str = r#"// line 1 — do not renumber without updating the pins below
// line 2

#[trust_vc::requires(a < 100)]
#[trust_vc::ensures(result == a)] // FAILS
fn bad_postcondition(a: u32) -> u32 {
    a + 1
}

#[trust_vc::requires(x < 10)]
#[trust_vc::ensures(true)]
fn bad_assert(x: u32) {
    let y = x;
    trust_vc::assert!(y > 5); // FAILS
}

#[trust_vc::requires(n < 5)]
#[trust_vc::ensures(result == n)]
fn callee(n: u32) -> u32 {
    n
}

#[trust_vc::ensures(true)]
fn bad_call_site_precondition() {
    let k: u32 = 9;
    let _r = callee(k); // FAILS
}

#[trust_vc::ensures(true)]
fn bad_overflow(a: u8, b: u8) {
    let _c = a + b; // FAILS
}

#[trust_vc::requires(v.len() == 3)]
#[trust_vc::ensures(true)]
fn bad_index_bound(v: &Vec<u32>) -> u32 {
    v[5] // FAILS
}

#[trust_vc::ensures(true)]
fn bad_loop_invariant_at_entry(n: u32) {
    let mut i: u32 = 1;
    while i < n
    {
        trust_vc::invariant!(i == 0); // FAILS
        i = i + 1;
    }
}

#[trust_vc::ensures(true)]
fn bad_loop_invariant_at_back_edge(n: u32) {
    let mut i: u32 = 0;
    while i < n
    {
        trust_vc::invariant!(i == 0); // FAILS
        i = i + 1;
    }
}

#[trust_vc::ensures(true)]
fn bad_assert_in_branch(c: bool, x: u32) {
    if c {
        trust_vc::assert!(x == 3); // FAILS
    }
}

#[trust_vc::ensures(true)]
fn bad_assert_in_nested_block(x: u32) {
    {
        let z = x;
        trust_vc::assert!(z == 7); // FAILS
    }
}

#[trust_vc::ensures(true)]
fn bad_assert_by_nonlinear(x: int, y: int, z: int) {
    trust_vc::assert_by_nonlinear!(x * y == y * z); // FAILS
}

#[trust_vc::ensures(true)]
fn bad_assert_forall_by() {
    trust_vc::assert_forall_by!(|k: int| k > k, { // FAILS
    });
}

#[trust_vc::ensures(true)]
fn bad_closure_ensures() {
    let f = trust_vc::closure!( // FAILS
        |y: u64| -> u64
        requires(y == 2u64)
        ensures(|z: u64| z == 3u64)
        y
    );
    let _ = f;
}
"#;

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

fn fixture_path() -> PathBuf {
    let sequence = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "trust_vc_source_location_pins_{}_{sequence}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("temp dir should be creatable");
    let path = dir.join("pins.rs");
    std::fs::write(&path, FIXTURE).expect("fixture should be writable");
    path
}

fn scanned_target(path: &Path, name: &str) -> AnnotatedFunction {
    crate::scan::scan_file(path)
        .into_iter()
        .find(|func| func.name == name)
        .unwrap_or_else(|| panic!("scan should discover `{name}` in {}", path.display()))
}

/// The lines every REFUTED obligation of `name` was reported on, read the way
/// the evidence gate reads them.
///
/// Mirrors `evidence::failing_obligations_from_verification`, which collects
/// every FAILING obligation — `Counterexample`, the model-less `NotProved`, and
/// `Error` — and falls back to the localized failure when none is listed. An
/// `Unknown` is a resource non-decision and is deliberately not collected.
///
/// The mirror must stay exact: an obligation the gate reads and this helper
/// drops would make a green pin here mean nothing.
fn refuted_locations(path: &Path, name: &str) -> Vec<(Option<usize>, String)> {
    let verification = verify_one_detailed(&scanned_target(path, name));
    let mut located: Vec<(Option<usize>, String)> = verification
        .obligations
        .iter()
        .filter(|obligation| {
            matches!(
                obligation.status,
                ObligationStatus::Counterexample
                    | ObligationStatus::NotProved
                    | ObligationStatus::Error
            )
        })
        .filter_map(|obligation| {
            // The STRUCTURED line where the engine recorded one — the channel
            // the evidence gate now reads — with the rendering carried beside
            // it so a failure message shows what was actually reported.
            Some((
                obligation.source_location.as_ref().map(|loc| loc.line()),
                obligation.location.clone()?,
            ))
        })
        .collect();
    if located.is_empty() {
        if let Some(failure) = &verification.verdict.localized_failure {
            located.extend(failure.location.clone().map(|location| (None, location)));
        }
    }
    assert!(
        !located.is_empty(),
        "`{name}` must report at least one LOCATED refuted obligation; verdict {:?}, detail {:?}, obligations {:?}",
        verification.verdict.result,
        verification.verdict.detail,
        verification
            .obligations
            .iter()
            .map(|o| (o.name.clone(), o.kind.clone(), o.status, o.location.clone()))
            .collect::<Vec<_>>()
    );
    located
}

/// Asserts `name`'s refutation is reported on `expected_line` of the fixture,
/// and that `expected_line` is one the fixture itself marks `// FAILS`.
///
/// The second half is what stops this test from being updated INTO agreement
/// with a regression: a pin re-pointed at whatever the engine printed would
/// land on an unmarked line and fail.
fn pin_refuted_line(path: &Path, name: &str, expected_line: usize) {
    let locations = refuted_locations(path, name);
    let lines: Vec<usize> = locations
        .iter()
        .filter_map(|(structured, rendered)| {
            structured.or_else(|| {
                let (_, tail) = rendered.rsplit_once(".rs:")?;
                tail.split(':').next()?.parse::<usize>().ok()
            })
        })
        .collect();
    assert!(
        lines.contains(&expected_line),
        "`{name}` must report a refuted obligation on line {expected_line}; got {locations:?}"
    );
    let marked = FIXTURE
        .lines()
        .nth(expected_line - 1)
        .unwrap_or_else(|| panic!("fixture has no line {expected_line}"));
    assert!(
        marked.contains("// FAILS"),
        "line {expected_line} of the fixture must be the marked failing line, found `{marked}`"
    );
}

#[test]
fn a_failing_postcondition_is_reported_on_its_ensures_clause() {
    // Upstream marks a failing postcondition on the `ensures` line itself
    // (`evals/verus/ported/nonlinear.rs:141`), not on the return expression.
    pin_refuted_line(&fixture_path(), "bad_postcondition", 5);
}

#[test]
fn a_failing_assert_is_reported_on_the_assert_statement() {
    pin_refuted_line(&fixture_path(), "bad_assert", 14);
}

#[test]
fn a_failing_call_site_precondition_is_reported_at_the_call() {
    // The CALL's line, not the callee's `requires` line: the obligation is the
    // caller's.
    pin_refuted_line(&fixture_path(), "bad_call_site_precondition", 26);
}

#[test]
fn a_failing_overflow_check_is_reported_on_the_arithmetic_statement() {
    pin_refuted_line(&fixture_path(), "bad_overflow", 31);
}

#[test]
fn a_failing_index_bound_is_reported_on_the_indexing_statement() {
    pin_refuted_line(&fixture_path(), "bad_index_bound", 37);
}

#[test]
fn a_loop_invariant_refuted_at_entry_is_reported_on_the_invariant() {
    pin_refuted_line(&fixture_path(), "bad_loop_invariant_at_entry", 45);
}

#[test]
fn a_loop_invariant_refuted_at_the_back_edge_is_reported_on_the_invariant() {
    // Same line as the entry check, and that is the point: upstream marks the
    // invariant, and the two checks differ in PHASE, not in position.
    pin_refuted_line(&fixture_path(), "bad_loop_invariant_at_back_edge", 55);
}

#[test]
fn an_obligation_inside_a_branch_is_reported_on_its_own_statement() {
    // NOT on the `if` line: `visit_stmt` recurses, so the innermost enclosing
    // statement wins.
    pin_refuted_line(&fixture_path(), "bad_assert_in_branch", 63);
}

#[test]
fn an_obligation_inside_a_nested_block_is_reported_on_its_own_statement() {
    pin_refuted_line(&fixture_path(), "bad_assert_in_nested_block", 71);
}

#[test]
fn a_failing_assert_by_is_reported_on_the_assert_by_statement() {
    // `assert ... by` used to push straight into the obligation vector,
    // bypassing the ambient-location stamp — it was the single largest class of
    // still-unlocated corpus refutations.
    pin_refuted_line(&fixture_path(), "bad_assert_by_nonlinear", 77);
}

#[test]
fn a_failing_assert_forall_by_is_reported_on_the_assert_statement() {
    pin_refuted_line(&fixture_path(), "bad_assert_forall_by", 82);
}

/// A closure's def-side `ensures` refutation carries the closure statement's
/// line — and is NOT yet a listed obligation, which is a separate gap.
///
/// The def-side check runs in an isolated child context whose failing verdict
/// crosses back as the function's `detail` alone: `verification.obligations`
/// holds only the enclosing function's `postcondition`, and
/// `localized_failure` is `None`. So the evidence gate — which counts refuted
/// OBLIGATIONS — still cannot see this failure at all, and locating it does not
/// change that. What this pin fixes in place is the position: the child inherits
/// the ambient location of the statement that binds the closure, which is the
/// first line of the multi-line `closure!` and is where the gate's span reader
/// would start before walking to the closing delimiter.
#[test]
fn a_closure_spec_obligation_carries_the_closure_statement_line() {
    let path = fixture_path();
    let verification = verify_one_detailed(&scanned_target(&path, "bad_closure_ensures"));
    let detail = verification
        .verdict
        .detail
        .as_deref()
        .unwrap_or_default()
        .to_string();
    assert!(
        detail.contains("closure_def_side_ensures (at "),
        "the closure def-side refutation must be the reported failure, got {detail:?}"
    );
    assert!(
        detail.contains("pins.rs:88:5"),
        "the closure def-side refutation must name line 88 of the fixture, got {detail:?}"
    );
    assert!(
        FIXTURE
            .lines()
            .nth(87)
            .is_some_and(|line| line.contains("// FAILS")),
        "line 88 of the fixture must be the marked failing line"
    );
    // The gap, pinned so it cannot close silently: no LISTED obligation carries
    // this refutation, so the gate's `exactly 1 refuted obligation` rule still
    // does not see it.
    assert!(
        verification
            .obligations
            .iter()
            .all(|obligation| !matches!(
                obligation.status,
                ObligationStatus::Counterexample
                    | ObligationStatus::NotProved
                    | ObligationStatus::Error
            )),
        "if the closure def-side failure ever becomes a listed obligation, fold          this case back into `pin_refuted_line`: {:?}",
        verification
            .obligations
            .iter()
            .map(|o| (o.name.clone(), o.status, o.location.clone()))
            .collect::<Vec<_>>()
    );
}

/// The counterpart pin: a lane with NO usable position must report NO position.
///
/// `extract_verification_conditions_with_file_context` is the unlocated entry
/// point (no path, so no `file:line:column` can be rendered). It must stay
/// unlocated rather than fall back to something plausible — a fabricated
/// location is exactly what the gate cannot detect.
#[test]
fn the_unlocated_entry_point_stays_unlocated() {
    let path = fixture_path();
    let source = std::fs::read_to_string(&path).expect("fixture readable");
    let ast = trust_vc_core::parse_file_allow_tracked(&source).expect("fixture parses");
    let func = match trust_vc_core::resolve_function_in_file(&ast, "bad_assert") {
        trust_vc_core::FunctionResolution::Unique(func) => func,
        _ => panic!("fixture should resolve `bad_assert` uniquely"),
    };
    let ctx = trust_vc_core::extract_verification_conditions_with_file_context(&ast, func)
        .expect("extraction should succeed");
    assert!(
        ctx.obligations()
            .iter()
            .all(|obligation| obligation.location().is_none()),
        "the path-less entry point must raise no located obligation: {:?}",
        ctx.obligations()
            .iter()
            .map(|o| (o.name().to_string(), o.location().map(str::to_string)))
            .collect::<Vec<_>>()
    );
}
