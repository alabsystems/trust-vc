// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN (seqs.rs `test1_seq_to_set_contains_matches_source_contains`,
//! 2026-09-13): a `requires(s.contains(v))` hypothesis discharges the goal
//! `s.to_set().contains(v)` on a SYMBOLIC `Seq<i32>`, and the SAME shapes with a
//! false claim are REFUTED.
//!
//! Two encoder levers, both exact:
//! * SPELLING (2026-09-14). `Seq::contains` is built as
//!   `not (forall i: Int. 0 <= i < len => s[int2bv(i)] != v)`, the dual of
//!   `exists i. 0 <= i < len && s[int2bv(i)] == v`. ay's term constructor
//!   eliminates double negation, so every negated occurrence — a
//!   `!s.contains(v)` hypothesis or the verifier's negated goal — is the guarded
//!   universal itself. Measured against the ay 0.26.0 sibling API:
//!   `(not (exists ..))` is `unknown (incomplete)` even with `len == 0` asserted,
//!   while the guarded `forall` is `sat` with a validated model, and the
//!   hypothesis/goal pair `exists` + `not exists` (two bound variables) is
//!   `unknown (incomplete)` where `not forall` + `forall` is `unsat`. That
//!   `(not (exists ..))` was the real obstacle behind both the pin's old red and
//!   the unrefuted liars; the 2026-09-13 reading ("ay does not alpha-normalize",
//!   "the negated-membership forall is incomplete") mis-attributed it.
//! * MEMO (`SeqContainsQuantifiedMemo`). Alpha-equivalent occurrences, keyed on
//!   the fully COERCED guarded body, are one term, so `P` and `not P` are
//!   propositional.
//!
//! SOUNDNESS PINS (adversarial review of `e57a3039`): the first memo key was
//! `(receiver, value, length)` taken BEFORE the signedness-directed width
//! coercions. ay interns `-1i32` and `4294967295u32` as one `#xffffffff`, so a
//! `requires(s.contains(-1i32))` hypothesis on a `Seq<i64>` (`s[i] == sext(..)`)
//! was handed back for the goal `s.contains(4294967295u32)` (`s[i] == zext(..)`)
//! and three false claims VERIFIED. The direct-source path does not type-check,
//! so it accepts the mixed-width literal. Those three shapes are pinned below
//! as must-never-verify.
//!
//! LIARS. Refuted (`Counterexample`, `s = []`): the negated hypothesis with a
//! literal and with a symbolic needle (the port file's twins), and the goal with
//! no hypothesis at all. Two liars still fail CLOSED, each pinned to its
//! measured reason so a change shows up here:
//! * `negated_goal_liar` (`requires(s.contains(5))`, goal `!s.to_set().contains(5)`)
//!   is a POSITIVE membership, which ay skolemizes to the ground
//!   `select(s, int2bv(k)) == 5`. Next to the encoder's ground seed
//!   `select(s, #x0) == g` that ground query is `unknown (incomplete)` at ay
//!   0.26.0; without the seed it is `sat`.
//! * `other_element_liar` (`requires(s.contains(5))`, goal
//!   `s.to_set().contains(6)`) mixes a positive and a negated membership, and ay
//!   answers `unknown ((incomplete quantifier-unhandled))` with or without the seed.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_sci_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
    let _ = std::fs::remove_file(&p);
    result
}

const SRC: &str = r#"
use trust_vc_types::Seq;

// CONTROL (the corpus shape): the hypothesis names the goal's element.
#[trust_vc::requires(s.contains(5i32))]
#[trust_vc::ensures(true)]
fn to_set_contains_from_source_contains(s: Seq<i32>) {
    trust_vc::assert!(s.to_set().contains(5i32));
}

// CONTROL: a symbolic needle.
#[trust_vc::requires(s.contains(needle))]
#[trust_vc::ensures(true)]
fn to_set_contains_from_source_contains_variable(s: Seq<i32>, needle: i32) {
    trust_vc::assert!(s.to_set().contains(needle));
}

// CONTROL: the two spellings agree in the other direction too.
#[trust_vc::requires(s.to_set().contains(5i32))]
#[trust_vc::ensures(true)]
fn source_contains_from_to_set_contains(s: Seq<i32>) {
    trust_vc::assert!(s.contains(5i32));
}

// LIAR: a DIFFERENT element is not implied.
#[trust_vc::requires(s.contains(5i32))]
#[trust_vc::ensures(true)]
fn other_element_liar(s: Seq<i32>) {
    trust_vc::assert!(s.to_set().contains(6i32));
}

// LIAR: the negated goal.
#[trust_vc::requires(s.contains(5i32))]
#[trust_vc::ensures(true)]
fn negated_goal_liar(s: Seq<i32>) {
    trust_vc::assert!(!s.to_set().contains(5i32));
}

// LIAR: no hypothesis at all.
#[trust_vc::ensures(true)]
fn no_hypothesis_liar(s: Seq<i32>) {
    trust_vc::assert!(s.to_set().contains(5i32));
}

// LIAR (the port file's twin): the hypothesis says the element is ABSENT.
#[trust_vc::requires(!s.contains(9i32))]
#[trust_vc::ensures(true)]
fn absent_element_liar(s: Seq<i32>) {
    trust_vc::assert!(s.to_set().contains(9i32));
}

// LIAR (the port file's twin): the same with a symbolic needle.
#[trust_vc::requires(!s.contains(needle))]
#[trust_vc::ensures(true)]
fn absent_variable_liar(s: Seq<i32>, needle: i32) {
    trust_vc::assert!(s.to_set().contains(needle));
}

// CONTROL: an absent element stays absent through `to_set`.
#[trust_vc::requires(!s.contains(9i32))]
#[trust_vc::ensures(true)]
fn absent_element_stays_absent(s: Seq<i32>) {
    trust_vc::assert!(!s.to_set().contains(9i32));
}
"#;

const WIDTH_SRC: &str = r#"
use trust_vc_types::Seq;

// SOUNDNESS: `-1i32` sign-extends to 0xffff_ffff_ffff_ffff, `4294967295u32`
// zero-extends to 0x0000_0000_ffff_ffff — different i64 elements.
#[trust_vc::requires(s.contains(-1i32))]
#[trust_vc::ensures(true)]
fn sext_hypothesis_zext_goal(s: Seq<i64>) {
    trust_vc::assert!(s.contains(4294967295u32));
}

// SOUNDNESS: the same pair in the other order.
#[trust_vc::requires(s.contains(4294967295u32))]
#[trust_vc::ensures(true)]
fn zext_hypothesis_sext_goal(s: Seq<i64>) {
    trust_vc::assert!(s.contains(-1i32));
}

// SOUNDNESS: `-1i8` is 0xffff as an i16 element, `255u8` is 0x00ff.
#[trust_vc::requires(s.contains(-1i8))]
#[trust_vc::ensures(true)]
fn sext_hypothesis_zext_goal_i16(s: Seq<i16>) {
    trust_vc::assert!(s.contains(255u8));
}

// CONTROL: the same mixed-width value on both sides still shares one term.
#[trust_vc::requires(s.contains(-1i32))]
#[trust_vc::ensures(true)]
fn same_extension_both_sides(s: Seq<i64>) {
    trust_vc::assert!(s.contains(-1i32));
}
"#;

#[test]
fn to_set_contains_from_source_contains_verifies() {
    let r = verify("c1", "to_set_contains_from_source_contains", SRC);
    assert!(
        matches!(r, VerifyResult::Verified),
        "`requires(s.contains(5))` must discharge `s.to_set().contains(5)`; got {r:?}"
    );
}

#[test]
fn to_set_contains_from_source_contains_variable_verifies() {
    let r = verify("c2", "to_set_contains_from_source_contains_variable", SRC);
    assert!(
        matches!(r, VerifyResult::Verified),
        "`requires(s.contains(needle))` must discharge `s.to_set().contains(needle)`; got {r:?}"
    );
}

#[test]
fn source_contains_from_to_set_contains_verifies() {
    let r = verify("c3", "source_contains_from_to_set_contains", SRC);
    assert!(
        matches!(r, VerifyResult::Verified),
        "`requires(s.to_set().contains(5))` must discharge `s.contains(5)`; got {r:?}"
    );
}

#[test]
fn absent_element_stays_absent_verifies() {
    let r = verify("c4", "absent_element_stays_absent", SRC);
    assert!(
        matches!(r, VerifyResult::Verified),
        "`requires(!s.contains(9))` must discharge `!s.to_set().contains(9)`; got {r:?}"
    );
}

fn assert_refuted(tmp_id: &str, func: &str) {
    let r = verify(tmp_id, func, SRC);
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "liar `{func}` makes a false claim about a symbolic Seq (`s = []` refutes it) and must be refuted; got {r:?}"
    );
}

#[test]
fn absent_element_liar_is_refuted() {
    assert_refuted("ae", "absent_element_liar");
}

#[test]
fn absent_variable_liar_is_refuted() {
    assert_refuted("av", "absent_variable_liar");
}

#[test]
fn no_hypothesis_liar_is_refuted() {
    assert_refuted("no", "no_hypothesis_liar");
}

fn assert_fails_closed_with(tmp_id: &str, func: &str, recorded: &str) {
    let r = verify(tmp_id, func, SRC);
    assert!(
        !matches!(r, VerifyResult::Verified),
        "CARDINAL: the liar `{func}` must never verify; got {r:?}"
    );
    // Target: a Counterexample. Today: fails CLOSED with the measured ay 0.26.0
    // incompleteness (see the module doc) — pinned so a change is visible.
    match &r {
        VerifyResult::NotProved { reason, .. } | VerifyResult::Unknown { reason, .. } => assert!(
            reason.contains(recorded),
            "liar `{func}` should fail closed with the recorded `{recorded}`; got {r:?}"
        ),
        other => panic!("liar `{func}` should fail closed with `{recorded}`; got {other:?}"),
    }
}

#[test]
fn negated_goal_liar_fails_closed_next_to_the_ground_seed() {
    assert_fails_closed_with("ne", "negated_goal_liar", "unknown (incomplete)");
}

#[test]
fn other_element_liar_fails_closed_quantifier_unhandled() {
    assert_fails_closed_with(
        "ot",
        "other_element_liar",
        "unknown ((incomplete quantifier-unhandled))",
    );
}

fn assert_never_verifies(tmp_id: &str, func: &str) {
    let r = verify(tmp_id, func, WIDTH_SRC);
    assert!(
        !matches!(r, VerifyResult::Verified),
        "CARDINAL: `{func}` relates two DIFFERENT elements (sign- vs zero-extension of one interned BV constant) and must never verify; got {r:?}"
    );
}

#[test]
fn sext_hypothesis_does_not_discharge_zext_goal() {
    assert_never_verifies("w1", "sext_hypothesis_zext_goal");
}

#[test]
fn zext_hypothesis_does_not_discharge_sext_goal() {
    assert_never_verifies("w2", "zext_hypothesis_sext_goal");
}

#[test]
fn sext_hypothesis_does_not_discharge_zext_goal_i16() {
    assert_never_verifies("w3", "sext_hypothesis_zext_goal_i16");
}

#[test]
fn same_extension_both_sides_verifies() {
    let r = verify("w4", "same_extension_both_sides", WIDTH_SRC);
    assert!(
        matches!(r, VerifyResult::Verified),
        "the identical mixed-width hypothesis must discharge its own goal; got {r:?}"
    );
}
