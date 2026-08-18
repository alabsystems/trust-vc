// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression: bare `Seq == Seq` (`===` / spec-eq) between two structurally
//! distinct but pointwise-equal CONCRETE seqs must be DECIDED — `Verified` when
//! equal, `Counterexample` when a length or element differs.
//!
//! The bare compare path (`encode_seq_extensional_eq`) encodes a BV-companion
//! pointwise quantifier tuned for symbolic-length operands; it does not unroll a
//! concrete `Seq::new(n, |i| ..)` / `push`-chain, so
//! `assert(Seq::new(5,|i| 10*i) === empty.push(0)..push(40))` stayed `unknown` —
//! the exact gap behind upstream `seqs.rs::test1` / `auto_extensionality_syntax*`
//! (`assert(s1 =~= s2); assert(s1 === s2);`). When both operands have a static
//! length within the finite-unroll cap, the compare now routes through the same
//! `build_ext_eq_expr` finite form `assert_seqs_equal!` uses.
//!
//! SOUNDNESS (cardinal — no false `Verified`): the finite conjunction is exactly
//! the extensional definition instantiated at each concrete in-bounds index, so a
//! wrong element refutes and a length mismatch refutes via the `len_eq` conjunct.
//! Symbolic-length operands are untouched (kept on the quantifier path).

use super::*;
use crate::encoder::VerifyResult;

fn verdict(code: &str, name: &str) -> VerifyResult {
    let file = parse_file(code).expect("fixture should parse");
    let func =
        find_function(&file, name).unwrap_or_else(|| panic!("fixture should define fn {name}"));
    extract_verification_conditions(func)
        .unwrap_or_else(|err| panic!("fn {name} should extract: {err}"))
        .verify()
}

fn assert_verified(code: &str, name: &str) {
    match verdict(code, name) {
        VerifyResult::Verified => {}
        other => {
            panic!("fn {name} should verify (concrete pointwise-equal seqs are ==), got: {other:?}")
        }
    }
}

/// A false `Verified` here would be the cardinal soundness failure. Fail-closed
/// (Counterexample, model-less NotProved, or Unknown) is acceptable;
/// `Verified` is NOT. `NotProved` is the fail-closed incompleteness verdict,
/// not a fabricated counterexample.
fn assert_not_verified(code: &str, name: &str) {
    match verdict(code, name) {
        VerifyResult::Counterexample { .. }
        | VerifyResult::NotProved { .. }
        | VerifyResult::Unknown { .. } => {}
        VerifyResult::Verified => {
            panic!("fn {name} must NOT verify (unequal seqs) — a false Verified is unsound")
        }
        other => panic!("fn {name} unexpected verdict: {other:?}"),
    }
}

/// `Seq::new(5, |i| 10*i) === empty.push(0).push(10).push(20).push(30).push(40)`.
/// Pointwise equal (both are `[0,10,20,30,40]`), structurally distinct terms.
#[test]
fn concrete_generator_vs_push_chain_speceq_verifies() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            let s1 = trust_vc_types::Seq::<i32>::new(5usize, trust_vc_types::SpecFn::new(|i: usize| 10i32 * (i as i32)));
            let s2 = trust_vc_types::Seq::<i32>::empty().push(0i32).push(10i32).push(20i32).push(30i32).push(40i32);
            trust_vc::assert!(s1 == s2);
        }
    "#;
    assert_verified(code, "test");
}

/// Faithful port of upstream `seqs.rs::auto_extensionality_syntax2`:
/// `assert_seqs_equal!(s1 == s2); assert(s1 == s2);` — the follow-up spec-eq now
/// discharges.
#[test]
fn auto_extensionality_syntax2_port_verifies() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            let s1 = trust_vc_types::Seq::<i32>::new(5usize, trust_vc_types::SpecFn::new(|i: usize| 10i32 * (i as i32)));
            trust_vc::assert!(s1.len() == 5usize);
            trust_vc::assert!(s1.index(3usize) == 30i32);
            let s2 = trust_vc_types::Seq::<i32>::empty().push(0i32).push(10i32).push(20i32).push(30i32).push(40i32);
            trust_vc::assert_seqs_equal!(s1 == s2);
            trust_vc::assert!(s1 == s2);
        }
    "#;
    assert_verified(code, "test");
}

/// SOUNDNESS: a differing final element (`40` vs `99`) must refute.
#[test]
fn concrete_wrong_element_refutes() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            let s1 = trust_vc_types::Seq::<i32>::new(5usize, trust_vc_types::SpecFn::new(|i: usize| 10i32 * (i as i32)));
            let s2 = trust_vc_types::Seq::<i32>::empty().push(0i32).push(10i32).push(20i32).push(30i32).push(99i32);
            trust_vc::assert!(s1 == s2);
        }
    "#;
    assert_not_verified(code, "test");
}

/// SOUNDNESS: a length mismatch (3 vs 4) must refute.
#[test]
fn concrete_wrong_length_refutes() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            let a = trust_vc_types::Seq::<i32>::empty().push(0i32).push(10i32).push(20i32);
            let b = trust_vc_types::Seq::<i32>::empty().push(0i32).push(10i32).push(20i32).push(30i32);
            trust_vc::assert!(a == b);
        }
    "#;
    assert_not_verified(code, "test");
}

/// F3 (point-interval length folding): the never-green calc_basic seq-concat
/// shape — `a == b + c` over LET-BOUND push chains — decides. The let-binding
/// assumptions entail concrete lengths (`len(a)=2, len(b)=len(c)=1`), the
/// declaration-time pin registers them as Int literals, and every companion
/// bridge folds to a ground BV literal (the probe_M2 shape ay decides in
/// milliseconds; the symbolic-bridge form was Unknown after 150s+ —
/// docs/probes/2026-07-18-ay-lane/dump-smt2/RESULTS.txt).
#[test]
fn point_interval_concat_of_let_bound_chains_verifies() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            let a = trust_vc_types::Seq::<u8>::empty().push(1u8).push(2u8);
            let b = trust_vc_types::Seq::<u8>::empty().push(1u8);
            let c = trust_vc_types::Seq::<u8>::empty().push(2u8);
            trust_vc::assert!(a == b + c);
        }
    "#;
    assert_verified(code, "test");
}

/// F3 SOUNDNESS: the fold must not weaken refutation — a WRONG concat claim
/// over the same point-interval lengths must still refute (here the element
/// order is swapped, so lengths agree and only the pointwise facts refute).
#[test]
fn point_interval_wrong_concat_order_refutes() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            let a = trust_vc_types::Seq::<u8>::empty().push(1u8).push(2u8);
            let b = trust_vc_types::Seq::<u8>::empty().push(1u8);
            let c = trust_vc_types::Seq::<u8>::empty().push(2u8);
            trust_vc::assert!(a == c + b);
        }
    "#;
    assert_not_verified(code, "test");
}

/// F3 SOUNDNESS: a wrong LENGTH claim about a pinned sequence must still
/// COUNTEREXAMPLE — the pin registers the literal (len 1), so the false goal
/// `len == 2` folds to a refuted ground fact, not a weakened tautology.
#[test]
fn point_interval_wrong_length_claim_counterexamples() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            let s = trust_vc_types::Seq::<u8>::empty().push(1u8);
            trust_vc::assert!(s.len() == 2usize);
        }
    "#;
    match verdict(code, "test") {
        VerifyResult::Counterexample { .. } => {}
        other => panic!(
            "wrong length claim over a pinned point-interval seq must COUNTEREXAMPLE \
             (fold must not weaken refutation), got: {other:?}"
        ),
    }
}

/// F3 SOUNDNESS (goal polarity): a length CLAIM that no assumption entails
/// must NOT verify — pins are harvested from positive assumptions only, never
/// from the goal itself.
#[test]
fn point_interval_unentailed_goal_length_claim_is_not_verified() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test(s: Seq<u8>) {
            trust_vc::assert!(s.len() == 2usize);
        }
    "#;
    assert_not_verified(code, "test");
}

/// F3 requires-derived pin: `requires s.len() == 2` pins the length at
/// declaration; a CONSISTENT downstream length fact verifies and an
/// INCONSISTENT one still refutes.
#[test]
fn point_interval_requires_len_pin_keeps_refutation() {
    let ok = r#"
        #[trust_vc::requires(s.len() == 2usize)]
        #[trust_vc::ensures(true)]
        fn test(s: Seq<u8>) {
            trust_vc::assert!(s.len() == 2usize);
        }
    "#;
    assert_verified(ok, "test");
    let bad = r#"
        #[trust_vc::requires(s.len() == 2usize)]
        #[trust_vc::ensures(true)]
        fn test(s: Seq<u8>) {
            trust_vc::assert!(s.len() == 3usize);
        }
    "#;
    assert_not_verified(bad, "test");
}

/// Regression (NC4 right-operand companion): SYMBOLIC-length `Seq == Seq` as a
/// `requires` assumption must ENCODE — in BOTH operand orders.
///
/// `encode_seq_extensional_eq` pushes the carrier-representability side
/// condition `0 <= len <= 2^64 - 1` for BOTH operand lengths
/// (`len_as_index_bv`), but only the LEFT length had the guarded BV companion
/// bridge that makes the condition provable. The RIGHT length's side condition
/// was genuinely unprovable (SAT probe:
/// `docs/probes/2026-07-18-ay-lane/dump-css/side1_probe.smt2`), so
/// `check_assumption_side_conditions` failed the whole file closed with
/// "index/length not representable in the BitVec(64) carrier"
/// (core_special_setup.rs seq-equality case). Both orders are pinned so
/// whichever operand lands on the right keeps its companion.
#[test]
fn symbolic_length_speceq_assumption_encodes_left_to_right() {
    let code = r#"
        #[trust_vc::requires(a == b)]
        #[trust_vc::ensures(true)]
        fn test(a: Seq<i32>, b: Seq<i32>) {
            trust_vc::assert!(a == b);
        }
    "#;
    match verdict(code, "test") {
        VerifyResult::Verified => {}
        VerifyResult::Error { message } => panic!(
            "symbolic-length seq equality assumption must encode without the \
             representability side-condition error, got Error: {message}"
        ),
        other => panic!("fn test should verify (requires a == b entails a == b), got: {other:?}"),
    }
}

/// Same regression, reversed operand order (`b == a`) — exercises the mirrored
/// companion assignment (the previously-uncovered right slot).
#[test]
fn symbolic_length_speceq_assumption_encodes_right_to_left() {
    let code = r#"
        #[trust_vc::requires(b == a)]
        #[trust_vc::ensures(true)]
        fn test(a: Seq<i32>, b: Seq<i32>) {
            trust_vc::assert!(b == a);
        }
    "#;
    match verdict(code, "test") {
        VerifyResult::Verified => {}
        VerifyResult::Error { message } => panic!(
            "symbolic-length seq equality assumption must encode without the \
             representability side-condition error, got Error: {message}"
        ),
        other => panic!("fn test should verify (requires b == a entails b == a), got: {other:?}"),
    }
}
