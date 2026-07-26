// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Verus `uninterp spec fn f(x: int) -> bool;` — a spec function DECLARED with
//! NO body (upstream `assert_forall_by.rs::test_forallstmt_implies` uses two).
//!
//! Two things are pinned here, and the second is cardinal.
//!
//! 1. **It is not silently dropped.** A bodyless free fn is not valid Rust, so
//!    `syn` hands it back as `Item::Verbatim` — and every consumer matches on
//!    `Item::Fn`. Before `mark_bodyless_spec_fns_uninterp`, the declaration
//!    simply VANISHED: the symbol did not exist and any call to it failed to
//!    resolve, naming neither the function nor the missing surface.
//!
//! 2. **It is STRICTLY uninterpreted.** The `ItemFn` we synthesize carries an
//!    EMPTY block. If that empty body were ever lowered into a defining axiom, we
//!    would be inventing a definition the source never wrote — proving more than
//!    Verus. So: no body axiom is ever emitted, and — unlike `#[opaque]`, whose
//!    body is merely hidden — NO `reveal!` can turn one on, because there is no
//!    body to reveal.
//!
//! The sharpest statement of (2) is that NEITHER `f(3)` NOR `!f(3)` is provable.
//! An uninterpreted predicate constrains nothing; a test that only checked
//! "`f(3)` is not provable" would still pass if the symbol had been pinned to
//! `false`.

use trust_vc_core::{
    extract_verification_conditions_with_file_context, parse_file_allow_tracked, VerifyResult,
};

/// Verify one function of `source` through the FILE path (the path the corpus
/// runs, and the only one that parses a bodyless declaration).
fn verify(source: &str, case: &str) -> VerifyResult {
    let file = parse_file_allow_tracked(source).expect("source should parse");
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == case => Some(func),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} should exist"));
    match extract_verification_conditions_with_file_context(&file, func) {
        Ok(vc) => vc.verify(),
        Err(err) => VerifyResult::Error {
            message: err.to_string(),
        },
    }
}

const UNINTERP: &str = r#"
use trust_vc_types::int;

// Verus: `uninterp spec fn p(x: int) -> bool;`
#[trust_vc::spec]
fn p(x: int) -> bool;

// An ordinary spec fn WITH a body, for the non-vacuity control.
#[trust_vc::spec]
fn interpreted(x: int) -> int {
    x + 1
}

// The symbol EXISTS and is a genuine function: congruence holds.
#[trust_vc::ensures(true)]
fn declared_symbol_is_congruent() {
    trust_vc::assert!(p(3int) == p(3int));
}

// CARDINAL (a): nothing is known about p. `p(3)` must NOT be provable.
#[trust_vc::ensures(true)]
fn value_is_not_provable() {
    trust_vc::assert!(p(3int));
}

// CARDINAL (b): ... and neither is its NEGATION. Together with (a) this pins
// "strictly uninterpreted": the empty synthesized body was not lowered into an
// axiom pinning p to any value.
#[trust_vc::ensures(true)]
fn negation_is_not_provable() {
    trust_vc::assert!(!p(3int));
}

// CARDINAL (c): `reveal!` cannot conjure a body that never existed. Unlike an
// `#[opaque]` fn (whose body is hidden but real), there is nothing to reveal —
// so p stays uninterpreted and this must STILL be refuted.
#[trust_vc::ensures(true)]
fn reveal_cannot_conjure_a_body() {
    trust_vc::reveal!(p);
    trust_vc::assert!(p(3int));
}

// NON-VACUITY CONTROL: an interpreted spec fn still gets its defining axiom. If
// this ever fails, every case above passes for the vacuous reason that NO spec
// fn axiom is emitted at all.
#[trust_vc::ensures(true)]
fn interpreted_fn_still_has_its_body() {
    trust_vc::assert!(interpreted(3int) == 4int);
}

// The uninterpreted predicate is USABLE as a hypothesis — this is what upstream
// `test_forallstmt_implies` relies on. Assumed for all x, it holds at 3.
#[trust_vc::requires(forall|x: int| p(x))]
#[trust_vc::ensures(true)]
fn hypothesis_about_an_uninterpreted_predicate_is_usable() {
    trust_vc::assert!(p(3int));
}
"#;

/// The declaration SURVIVES parsing (it used to be dropped on the floor) and
/// denotes a real function symbol.
#[test]
fn bodyless_spec_fn_is_declared_not_dropped() {
    match verify(UNINTERP, "declared_symbol_is_congruent") {
        VerifyResult::Verified => {}
        VerifyResult::Error { message } => panic!(
            "the bodyless declaration `spec fn p(x: int) -> bool;` did not produce a usable \
             symbol: {message}. Before this surface existed it parsed as `syn::Item::Verbatim` \
             and was SILENTLY DROPPED."
        ),
        other => panic!("`p(3) == p(3)` must verify by congruence, got {other:?}"),
    }
}

/// CARDINAL. An uninterpreted predicate constrains NOTHING, so neither `p(3)`
/// nor `!p(3)` may be provable. If the synthesized empty body were lowered into
/// a defining axiom, one of these two would flip to `Verified` — a definition
/// the source never wrote, proving more than Verus.
#[test]
fn uninterpreted_fn_pins_no_value() {
    for case in ["value_is_not_provable", "negation_is_not_provable"] {
        match verify(UNINTERP, case) {
            VerifyResult::Counterexample { .. } => {}
            VerifyResult::Verified => panic!(
                "*** CARDINAL *** `{case}` VERIFIED. A Verus `uninterp spec fn` has NO body, \
                 so nothing about its value is derivable. Something lowered the EMPTY block we \
                 synthesize for it into a defining axiom, fabricating a definition the source \
                 never wrote."
            ),
            other => panic!("{case} must be refuted, got {other:?}"),
        }
    }
}

/// CARDINAL. `#[opaque]` hides a body that EXISTS, and `reveal!` un-hides it.
/// An `uninterp` fn has no body at all, so a `reveal!` must not make one appear.
#[test]
fn reveal_on_an_uninterp_fn_conjures_nothing() {
    match verify(UNINTERP, "reveal_cannot_conjure_a_body") {
        VerifyResult::Counterexample { .. } => {}
        VerifyResult::Verified => panic!(
            "*** CARDINAL *** `reveal!(p)` on a BODYLESS spec fn made `p(3)` provable. There is \
             no body to reveal — the reveal path fabricated one."
        ),
        // A fail-closed rejection of `reveal!` on a bodyless fn would also be
        // sound (Verus rejects it), so an Error is acceptable; Verified is not.
        VerifyResult::Error { .. } => {}
        other => panic!("expected refutation or a fail-closed error, got {other:?}"),
    }
}

/// Without this, every cardinal case above would pass vacuously.
#[test]
fn interpreted_spec_fns_still_get_their_body_axiom() {
    match verify(UNINTERP, "interpreted_fn_still_has_its_body") {
        VerifyResult::Verified => {}
        other => panic!(
            "NON-VACUITY CONTROL FAILED: an ordinary spec fn with a body no longer gets its \
             defining axiom ({other:?}). The `uninterp` cases above are therefore meaningless."
        ),
    }
}

/// The shape upstream `test_forallstmt_implies` actually needs: an uninterpreted
/// predicate is still usable when a `requires` supplies a fact about it.
#[test]
fn uninterpreted_predicate_is_usable_under_a_hypothesis() {
    match verify(
        UNINTERP,
        "hypothesis_about_an_uninterpreted_predicate_is_usable",
    ) {
        VerifyResult::Verified => {}
        other => panic!(
            "`requires forall|x| p(x)` must let `p(3)` be assumed — this is the shape upstream \
             test_forallstmt_implies relies on. Got {other:?}"
        ),
    }
}
