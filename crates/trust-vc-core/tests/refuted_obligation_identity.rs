// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A refuted obligation carries THREE separable channels: a NAME, a LOCATION,
//! and (when the user wrote one) a diagnostic LABEL.
//!
//! REGRESSION PIN. The source-location work (`288017da`, merged at `225c1773`)
//! made the file-context lane record a position for every obligation. It
//! changed no renderer — but the renderer in `encoder/verification/solve.rs`
//! had been gluing the position INTO the reported obligation name
//! (`format!("{} (at {})", display, loc)`) since long before, and that glue
//! only became REACHABLE once positions started arriving. The reported name
//! turned from `assertion_0` into `assertion_0 (at f.rs:2:5)`, and
//! `VerificationContext::apply_proof_note_verdict` — which finds the failing
//! obligation BY NAME so it can attach the user's
//! `#[verifier::proof_note]` / `#[verifier::custom_err]` text — stopped
//! matching anything at all. A user-supplied label silently stopped reaching
//! the message: a LOST CAPABILITY, not a cosmetic string.
//!
//! These pins are written so the same class cannot return through a different
//! renderer: the NAME must be a name (no position glued in), the POSITION must
//! be readable as its own field, and the LABEL must reach the message. Each
//! positive pin has its REFUTED twin, so a channel that starts answering
//! unconditionally fails here.

use std::fs;
use std::path::{Path, PathBuf};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fixture(name: &str, code: &str) -> PathBuf {
    let dir = Path::new("target/refuted_obligation_identity");
    fs::create_dir_all(dir).expect("fixture dir");
    let path = dir.join(format!("{name}.rs"));
    fs::write(&path, code).expect("write fixture");
    path
}

fn verify(name: &str, code: &str) -> VerifyResult {
    let path = fixture(name, code);
    verify_function_from_file(path.to_str().expect("utf-8 path"), "f")
        .unwrap_or_else(|err| panic!("{name} should extract: {err}"))
}

/// Line 1 is the signature; the failing assert is line 2, column 5.
const FAILING_ASSERT: &str = "\
fn f(x: u32) {
    trust_vc::assert!(x > 0u32);
}
";

/// THE NAME IS A NAME. The reported obligation name must carry no source
/// position, no rendered `file:line:column`, and none of the ` (at ` glue that
/// used to introduce one.
#[test]
fn a_refuted_obligation_name_carries_no_source_position() {
    let result = verify("name_is_a_name", FAILING_ASSERT);
    let VerifyResult::Counterexample {
        obligation_name, ..
    } = &result
    else {
        panic!("a false assert must refute, got {result:?}");
    };
    assert!(
        !obligation_name.contains(" (at "),
        "the obligation NAME must not carry its location, got {obligation_name:?}"
    );
    assert!(
        !obligation_name.contains(".rs"),
        "the obligation NAME must not carry a file path, got {obligation_name:?}"
    );
    assert_eq!(
        obligation_name, "assertion_0",
        "the reported name must be the obligation's own name"
    );
}

/// THE LOCATION IS A FIELD, and it names the failing statement.
#[test]
fn a_refuted_obligation_carries_its_location_as_its_own_field() {
    let result = verify("location_is_a_field", FAILING_ASSERT);
    let VerifyResult::Counterexample { location, .. } = &result else {
        panic!("a false assert must refute, got {result:?}");
    };
    let location = location
        .as_deref()
        .expect("the file-context lane must record a position");
    assert!(
        location.ends_with("location_is_a_field.rs:2:5"),
        "the location field must name the failing statement, got {location:?}"
    );
}

/// LIAR TWIN for the location pin: the field must hold the REAL position, not
/// a plausible default. Here the SECOND assert fails, so the answer must be
/// line 3 — not line 2 (the passing statement) and not line 1 (which is what
/// `Span::call_site()`, the synthesized-token fallback, reports).
#[test]
fn the_reported_location_is_refuted_for_every_line_but_the_failing_one() {
    let code = "\
fn f(x: u32) {
    trust_vc::assert!(x >= 0u32);
    trust_vc::assert!(x > 0u32);
}
";
    let result = verify("liar_twin_line", code);
    let VerifyResult::Counterexample { location, .. } = &result else {
        panic!("the second assert must refute, got {result:?}");
    };
    let location = location.as_deref().expect("a position must be recorded");
    assert!(
        location.ends_with("liar_twin_line.rs:3:5"),
        "the FAILING statement is on line 3, got {location:?}"
    );
    for wrong in ["liar_twin_line.rs:1:", "liar_twin_line.rs:2:"] {
        assert!(
            !location.contains(wrong),
            "line {wrong} is not where the refutation is, got {location:?}"
        );
    }
}

/// LIAR TWIN for "a location is recorded": the path-less entry point must
/// report NO location rather than a plausible one, and the NAME channel must
/// be unaffected by its absence.
#[test]
fn the_unlocated_lane_reports_no_location_and_still_reports_the_name() {
    let ast = trust_vc_core::parse_file_allow_tracked(FAILING_ASSERT).expect("fixture parses");
    let func = match trust_vc_core::resolve_function_in_file(&ast, "f") {
        trust_vc_core::FunctionResolution::Unique(func) => func,
        _ => panic!("fixture should resolve `f` uniquely"),
    };
    let ctx = trust_vc_core::extract_verification_conditions_with_file_context(&ast, func)
        .expect("extraction should succeed");
    let result = ctx.verify();
    let VerifyResult::Counterexample {
        obligation_name,
        location,
        ..
    } = &result
    else {
        panic!("a false assert must refute, got {result:?}");
    };
    assert!(
        location.is_none(),
        "the path-less lane must not invent a location, got {location:?}"
    );
    assert_eq!(
        obligation_name, "assertion_0",
        "the name channel is unaffected by the missing location"
    );
}

/// THE LABEL IS A LABEL, and it reaches the message. This is the capability the
/// regression removed: a user-written `custom_err` on a failing assert must be
/// the reported message.
#[test]
fn a_user_label_on_a_refuted_obligation_reaches_the_message() {
    let code = "\
fn f() {
    #[verifier::custom_err(\"the label the user wrote\")]
    trust_vc::assert!(1u32 > 2u32);
}
";
    let result = verify("label_reaches_message", code);
    let VerifyResult::Error { message } = &result else {
        panic!("a labeled refutation reports through the error channel, got {result:?}");
    };
    assert!(
        message.contains("the label the user wrote"),
        "the user's label must be the reported message, got {message:?}"
    );
}

/// LIAR TWIN for the label pin: the SAME failing assert with NO label must stay
/// a plain counterexample. The label channel must never fabricate one.
#[test]
fn an_unlabeled_refutation_is_refuted_for_the_label_channel() {
    let code = "\
fn f() {
    trust_vc::assert!(1u32 > 2u32);
}
";
    let result = verify("no_label_no_message", code);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "an unlabeled refutation must stay a counterexample, got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// The label channel and the names the ENGINE decorates
// ---------------------------------------------------------------------------

/// COVERAGE for the seam the round-1 review expected to be broken here, and a
/// CORRECTION to it: the verifier DECORATES a reported obligation name with a
/// dual-width tag (`vc_extraction::tag_result_with_arch`) that the obligation
/// table does not carry, and the by-name label lookup in
/// `apply_proof_note_verdict` matches the name exactly — so a `usize`
/// postcondition reported as `postcondition_32bit_64bit` looked like a lost
/// label. MEASURED: it is not one. `tag_result_with_arch` rewrites
/// `Counterexample`/`NotProved`/`Unknown` and passes `Error` through untouched,
/// and the label is applied to each width's verdict BEFORE the widths are
/// combined — so a labeled clause is already an `Error` by the time the tag
/// would be appended. An undecorating lookup was written, measured to change
/// nothing on any shape that could be reached, and DROPPED rather than landed
/// as code no test can tell apart. These three pins stay: they are what would
/// catch it if that ordering ever changed.
#[test]
fn a_label_on_a_dual_width_clause_reaches_the_message() {
    let code = "\
#[trust_vc::ensures(#![verifier::custom_err(\"the dual-width label\")] result == 5usize)]
fn f(n: usize) -> usize {
    n
}
";
    let result = verify("arch_tagged_label", code);
    let VerifyResult::Error { message } = &result else {
        panic!("a labeled dual-width refutation reports through the error channel, got {result:?}");
    };
    assert!(
        message.contains("the dual-width label"),
        "the user's label must survive the arch tag, got {message:?}"
    );
}

/// LIAR TWIN, and the pin that proves the decoration really is present: the
/// SAME clause with NO label stays a plain counterexample, and its reported
/// name still carries the `_32bit_64bit` tag. Without this the pin above could
/// pass on a shape that was never decorated at all.
#[test]
fn an_unlabeled_dual_width_refutation_keeps_its_arch_tagged_name() {
    let code = "\
#[trust_vc::ensures(result == 5usize)]
fn f(n: usize) -> usize {
    n
}
";
    let result = verify("arch_tagged_no_label", code);
    let VerifyResult::Counterexample {
        obligation_name, ..
    } = &result
    else {
        panic!("an unlabeled dual-width refutation must stay a counterexample, got {result:?}");
    };
    assert_eq!(
        obligation_name, "postcondition_32bit_64bit",
        "the dual-width tag is the decoration the label lookup has to see past"
    );
}

/// The fixed-width companion: a clause whose name carries no tag at all
/// resolves by its own name and gets its own label. Together with the two
/// above, the label channel is pinned on both sides of the dual-width split.
#[test]
fn a_label_on_a_fixed_width_clause_is_unaffected() {
    let code = "\
#[trust_vc::ensures(#![verifier::custom_err(\"the fixed width label\")] result == 5u32)]
fn f(n: u32) -> u32 {
    n
}
";
    let result = verify("fixed_width_label", code);
    let VerifyResult::Error { message } = &result else {
        panic!(
            "a labeled fixed-width refutation reports through the error channel, got {result:?}"
        );
    };
    assert!(
        message.contains("the fixed width label"),
        "the undecorated lookup must not disturb the ordinary case, got {message:?}"
    );
}
