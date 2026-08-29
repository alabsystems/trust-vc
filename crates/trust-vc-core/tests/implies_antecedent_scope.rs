// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The Verus `implies` KEYWORD lets an `assert forall|x| A implies B by { .. }`
//! block ASSUME `A` while proving `B` (upstream `assert_forall_by.rs`
//! `test_forallstmt2`). That assumption is the ONLY thing in this feature that
//! ADDS proving power, so it is the only place a cardinal unsoundness could hide.
//!
//! Assuming `A` inside the block is the standard "fix an arbitrary x, assume
//! A(x), prove B(x)" step and is sound — but ONLY if the assumption stays inside
//! the block and the fact that ESCAPES stays the guarded `forall x. A ==> B`.
//! Two distinct leaks would each prove more than Verus:
//!
//!   1. the antecedent leaks OUTWARD as a free assumption of the enclosing
//!      function (so a claim about the CALLER's values is proved from nothing);
//!   2. the published fact is the UNGUARDED `forall x. B` (so `B` is known at
//!      values of `x` for which `A` is false).
//!
//! Both are refuted here, each with a non-vacuity control — without them,
//! "nothing leaked" is indistinguishable from "the feature does nothing".
//!
//! The port's `test_forallstmt2_fails1` covers (2) as an upstream case; (1) has
//! no upstream case (upstream's antecedent never mentions an outer variable), so
//! it is pinned here.

use trust_vc_core::{
    extract_verification_conditions_with_file_context, parse_file_allow_tracked, VerifyResult,
};

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

const SOURCE: &str = r#"
use trust_vc_types::int;

#[trust_vc::spec]
#[trust_vc::opaque]
fn f1(i: int) -> int {
    i + 1
}

// CARDINAL (1): the antecedent mentions `y`, a PARAMETER of the enclosing
// function — a value the caller chooses. Assuming `y > 100` to prove the
// implication must not make `y > 100` a fact about the function.
#[trust_vc::ensures(true)]
fn antecedent_must_not_leak_to_enclosing_scope(y: int) {
    trust_vc::assert_forall_by!(assert forall|x: int| y > 100int implies f1(x) > x by {
        trust_vc::reveal!(f1);
    });
    trust_vc::assert!(y > 100int);
}

// CARDINAL (2): the escaping fact is `forall x. 0 <= x ==> 1 <= f1(x)`, which
// says NOTHING at x == -5. (f1(-5) == -4.)
#[trust_vc::ensures(true)]
fn published_fact_must_stay_guarded() {
    trust_vc::assert_forall_by!(assert forall|x: int| 0int <= x implies 1int <= f1(x) by {
        trust_vc::reveal!(f1);
    });
    trust_vc::assert!(1int <= f1(-5int));
}

// NON-VACUITY (a): the guarded fact IS published and IS usable inside its guard.
// Without this, both cardinal cases could "pass" because nothing was proved at
// all.
#[trust_vc::ensures(true)]
fn guarded_fact_is_usable_in_range() {
    trust_vc::assert_forall_by!(assert forall|x: int| 0int <= x implies 1int <= f1(x) by {
        trust_vc::reveal!(f1);
    });
    trust_vc::assert!(1int <= f1(7int));
}

// NON-VACUITY (b): the by-block really DOES receive the antecedent. `1 <= f1(x)`
// is FALSE for x == -1 (f1(-1) == 0), so revealing f1 alone cannot discharge the
// goal — it goes through only because `implies` hands the block `0 <= x`.
#[trust_vc::ensures(true)]
fn by_block_really_assumes_the_antecedent() {
    trust_vc::assert_forall_by!(assert forall|x: int| 0int <= x implies 1int <= f1(x) by {
        trust_vc::reveal!(f1);
    });
}
"#;

/// CARDINAL. A by-block assumption must not escape as a fact about the enclosing
/// function's parameters.
#[test]
fn implies_antecedent_does_not_leak_into_the_enclosing_scope() {
    match verify(SOURCE, "antecedent_must_not_leak_to_enclosing_scope") {
        VerifyResult::Counterexample { .. } => {}
        VerifyResult::Verified => panic!(
            "*** CARDINAL SOUNDNESS FAILURE *** `y > 100` VERIFIED for an arbitrary caller-chosen \
             `y`. The `implies` antecedent, which may only be assumed INSIDE the by-block, leaked \
             out as a free assumption of the enclosing function. Verus scopes it to the block; \
             this proves strictly more."
        ),
        // CLOSED (ay `e7385d1a3`): the refutation-power gap this arm briefly
        // tolerated — a native-API-declared head refused as a projection
        // binding, so the SAT certificates declined and the genuinely SAT
        // counterexample surfaced as `NotProved (quantifier-unhandled)` — is
        // fixed at the solver, and this pin is back to Counterexample-only.
        // ay's `native_declaration_projection_binding.rs` carries the
        // solver-level twin of this exact query.
        other => panic!("expected a counterexample on `y > 100`, got {other:?}"),
    }
}

/// CARDINAL. The fact that escapes the block is the GUARDED implication, never
/// the unguarded consequent.
#[test]
fn published_fact_from_an_implies_block_stays_guarded() {
    match verify(SOURCE, "published_fact_must_stay_guarded") {
        // Unknown-as-failure (docs/design-unknown-as-failure.md): a model-less
        // NotProved is a genuine verification FAILURE — the false `1 <= f1(-5)`
        // was correctly NOT proved, so it guards the fact as faithfully as a
        // model-bearing Counterexample. The CARDINAL direction is still Verified.
        VerifyResult::Counterexample { .. } | VerifyResult::NotProved { .. } => {}
        VerifyResult::Verified => panic!(
            "*** CARDINAL SOUNDNESS FAILURE *** `1 <= f1(-5)` VERIFIED. The block proved \
             `forall x. 0 <= x ==> 1 <= f1(x)`, but the published fact was the UNGUARDED \
             `forall x. 1 <= f1(x)` — the antecedent was dropped from the conclusion. f1(-5) is \
             -4, so this is false of a real execution."
        ),
        other => {
            panic!("expected `1 <= f1(-5)` to be rejected (Counterexample or NotProved), got {other:?}")
        }
    }
}

/// Without these two, "nothing leaked" would be indistinguishable from "the
/// `implies` form proves nothing at all".
#[test]
fn implies_block_is_not_vacuous() {
    match verify(SOURCE, "by_block_really_assumes_the_antecedent") {
        VerifyResult::Verified => {}
        other => panic!(
            "NON-VACUITY FAILED: the `implies` by-block did NOT receive the antecedent — \
             `1 <= f1(x)` is false at x == -1, so revealing f1 alone cannot discharge it. If this \
             fails, the leak tests above are meaningless. Got {other:?}"
        ),
    }
    match verify(SOURCE, "guarded_fact_is_usable_in_range") {
        VerifyResult::Verified => {}
        other => panic!(
            "NON-VACUITY FAILED: the guarded fact was not usable at x == 7, inside its own guard. \
             The block published nothing, so the leak tests above are meaningless. Got {other:?}"
        ),
    }
}
