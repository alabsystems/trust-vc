// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! `assert … by { .. }` on the FILE path, with a SCOPED `reveal` (#34).
//!
//! Upstream: `source/rust_verify_test/tests/assert_forall_by.rs`
//! (pinned ref a40d57c73650cd3648b09386bfdb96ab5c270626), with
//! `#[verifier(opaque)] spec fn f1(i: int) -> int { i + 1 }`:
//!
//! * `test_assertby1` — `assert(f1(3) > 3) by { reveal(f1); }` then
//!   `assert(f1(3) > 3);` PASSES: the by-block's proven CONCLUSION persists.
//! * `test_assertby1_fail1` — `assert(f1(3) > 4) by { reveal(f1); }` FAILS.
//! * `test_assertby1_fail2` — same by-block then `assert(f1(3) == 4);` FAILS:
//!   the `reveal` is SCOPED to the block; f1 is opaque again outside.
//!
//! CARDINAL SOUNDNESS PIN ([`by_block_reveal_does_not_leak`]): a scoped reveal
//! that leaked into the query-level reveal set would let trust-vc prove
//! `f1(3) == 4` where Verus refutes it — the proves-more-than-Verus direction.
//! That test must stay red-on-leak forever.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn battery_path() -> String {
    format!(
        "{}/tests/data/assert_by_scoped_reveal.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verdict(func: &str) -> VerifyResult {
    verify_function_from_file(&battery_path(), func)
        .unwrap_or_else(|err| panic!("extract/verify {func} must not error: {err:?}"))
}

/// (1) The feature exists at all: `assert_by!(cond, { reveal!(f1); })` on the
/// file path discharges the conclusion under the scoped reveal. Before #34 this
/// hard-errored ("Unsupported assert_by!() in vc_extraction").
#[test]
fn by_block_reveal_proves() {
    let result = verdict("by_block_reveal_proves");
    assert!(
        matches!(result, VerifyResult::Verified),
        "by_block_reveal_proves: the by-block's scoped reveal!(f1) must discharge \
         `f1(3) > 3` — if this is not Verified, scoped reveal does nothing; got {result:?}"
    );
}

/// (2) Upstream `test_assertby1`: the by-block's proven CONCLUSION persists as a
/// fact for later statements, even though f1 is opaque again out there.
#[test]
fn by_block_fact_persists() {
    let result = verdict("by_block_fact_persists");
    assert!(
        matches!(result, VerifyResult::Verified),
        "by_block_fact_persists (upstream test_assertby1): the assert_by conclusion \
         must persist as a fact for the following assert!, got {result:?}"
    );
}

/// (3) **THE CARDINAL PIN** — upstream `test_assertby1_fail2`.
///
/// `assert(f1(3) > 3) by { reveal(f1); }` followed by `assert(f1(3) == 4);`.
/// The trailing assert is provable ONLY from f1's body, which Verus has opaque
/// again outside the block. It MUST NOT verify. If it does, the by-block's
/// reveal leaked into the query-level reveal set and trust-vc proves MORE than
/// Verus — a cardinal soundness failure, not a completeness gap.
#[test]
fn by_block_reveal_does_not_leak() {
    let result = verdict("by_block_reveal_does_not_leak");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "*** CARDINAL SOUNDNESS FAILURE (upstream test_assertby1_fail2) *** \
         the reveal!(f1) inside the assert_by proof block LEAKED past the block: \
         `f1(3) == 4` (provable only from f1's hidden body) was accepted, so \
         trust-vc proves MORE than Verus. A scoped reveal must NEVER enter the \
         query-level revealed_fns. Got {result:?}"
    );
}

/// (4) Control for (1): with NO reveal in the block, f1 stays opaque and the
/// conclusion is not provable. Pins that (1) verifies BECAUSE of the reveal and
/// not because the by-block broke opacity.
#[test]
fn no_reveal_stays_opaque() {
    let result = verdict("no_reveal_stays_opaque");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "no_reveal_stays_opaque: an assert_by with an EMPTY proof block VERIFIED a \
         goal provable only from the opaque body of f1 — opacity leaked into the \
         by-block (proves more than Verus!), got {result:?}"
    );
}

/// (5) Upstream `test_assertby1_fail1`: a FALSE conclusion fails even with the
/// reveal — the by-block is not a free pass.
#[test]
fn by_block_false_conclusion_fails() {
    let result = verdict("by_block_false_conclusion_fails");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "by_block_false_conclusion_fails (upstream test_assertby1_fail1): \
         `f1(3) > 4` is FALSE under the revealed body and must refute, got {result:?}"
    );
}

/// (6) Plumbing smoke test: a trivial conclusion with an empty proof block.
#[test]
fn by_block_trivial_verifies() {
    let result = verdict("by_block_trivial");
    assert!(
        matches!(result, VerifyResult::Verified),
        "by_block_trivial: `assert_by!(1int + 1int == 2int, {{}})` must verify, \
         got {result:?}"
    );
}

/// (7) The proof block's OWN assertions are CHECKED, not assumed: a false inner
/// assert sinks the query.
#[test]
fn by_block_inner_assert_is_checked() {
    let result = verdict("by_block_inner_assert_is_checked");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "by_block_inner_assert_is_checked: a FALSE assert inside the proof block \
         (`f1(3) == 5` under the revealed body) VERIFIED — proof-block assertions \
         are being assumed rather than checked, got {result:?}"
    );
}

/// (8) The scoped reveal reaches the block's INNER assertions too, not only the
/// conclusion: `assert!(f1(3) == 4)` inside the block is provable exactly
/// because the reveal is in scope there.
#[test]
fn by_block_inner_assert_uses_scoped_reveal() {
    let result = verdict("by_block_inner_assert_uses_scoped_reveal");
    assert!(
        matches!(result, VerifyResult::Verified),
        "by_block_inner_assert_uses_scoped_reveal: the scoped reveal must be in \
         effect for the block's inner assertions as well as its conclusion, \
         got {result:?}"
    );
}

/// (9) The `reveal!(typo)` guard still fires for a SCOPED reveal — a scoped
/// reveal of an unknown function must fail closed, not silently no-op.
#[test]
fn by_block_reveal_typo_fails_closed() {
    let result = verify_function_from_file(&battery_path(), "by_block_reveal_typo_fails_closed");
    let text = match &result {
        Err(err) => format!("{err:?}"),
        Ok(VerifyResult::Error { message }) => message.clone(),
        Ok(verdict) => {
            panic!("scoped reveal!(no_such_function_anywhere) must fail closed, got {verdict:?}")
        }
    };
    assert!(
        text.contains("no_such_function_anywhere"),
        "scoped reveal!(typo) must fail through the reveal typo guard, got: {text}"
    );
}

/// (10) Scope isolation between sibling by-blocks: a reveal in block A must not
/// be visible in block B. Same leak class as (3), one level out.
#[test]
fn reveal_does_not_leak_into_sibling_block() {
    let result = verdict("reveal_does_not_leak_into_sibling_block");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "*** SCOPED-REVEAL LEAK *** a reveal!(f1) in one assert_by proof block was \
         visible inside a LATER assert_by block (which has no reveal of its own): \
         `f1(3) == 4` was proven from the opaque body. Got {result:?}"
    );
}

/// (11) The QUANTIFIED by-block — upstream's `assert forall |i| .. by { .. }`,
/// the `assert_forall_by.rs` keystone shape — also honours the scoped reveal.
#[test]
fn forall_by_block_reveal_proves() {
    let result = verdict("forall_by_block_reveal_proves");
    assert!(
        matches!(result, VerifyResult::Verified),
        "forall_by_block_reveal_proves: the scoped reveal!(f1) inside an \
         `assert forall |i| .. by {{ .. }}` block must discharge `f1(i) > i`, \
         got {result:?}"
    );
}

/// (12) CARDINAL PIN for the quantified form: the forall-by block's reveal must
/// not leak past the block either.
#[test]
fn forall_by_block_reveal_does_not_leak() {
    let result = verdict("forall_by_block_reveal_does_not_leak");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "*** CARDINAL SOUNDNESS FAILURE *** the reveal!(f1) inside an \
         `assert forall |i| .. by {{ .. }}` proof block LEAKED past the block: \
         `f1(3) == 4` (provable only from f1's hidden body) was accepted, so \
         trust-vc proves MORE than Verus. Got {result:?}"
    );
}

/// (13) CARDINAL PIN, postcondition direction: a by-block's scoped reveal must
/// not leak into the function's `ensures` either. The postcondition is verified
/// with f1 opaque (the by-block's proven conclusion `f1(3) > 3` is forwarded,
/// but that does not entail `f1(3) == 4`).
#[test]
fn scoped_reveal_does_not_leak_into_ensures() {
    let result = verdict("scoped_reveal_does_not_leak_into_ensures");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "*** CARDINAL SOUNDNESS FAILURE *** the by-block's reveal!(f1) LEAKED \
         into the function's ENSURES: `f1(3) == 4` was proven from f1's hidden \
         body at the postcondition, which Verus checks with f1 opaque. \
         Got {result:?}"
    );
}
