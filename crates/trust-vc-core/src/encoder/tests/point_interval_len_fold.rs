//! F3 point-interval length folding — direct encoder tests.
//!
//! A spec-Seq length that DENOTES a concrete carrier-representable value must
//! fold to the BitVec literal at every Int→BV bridge site
//! (`len_index_companion`, `len_index_companion_maybe_negative`,
//! `len_as_index_bv`, `try_folded_len_index_bv`) instead of minting a fresh
//! companion var bridged via `bv2int` — the mixed bridge ay cannot decide
//! even at pinned values (docs/probes/2026-07-18-ay-lane probe_B1/M1d), while
//! literal companions produce the pure ground-BV probe_M2 shape it decides in
//! milliseconds. SYMBOLIC lengths must keep the incumbent bridge byte-for-byte
//! (fail-closed), and a concrete NEGATIVE length (violated view precondition)
//! must keep the guarded symbolic path so the inert-bridge refutation is
//! unchanged.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use ay_dpll::api::TermKind;

fn with_parser<R>(run: impl FnOnce(&mut AstExpressionParser<'_>) -> R) -> R {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let variables = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();
    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    run(&mut parser)
}

/// Concrete Int length → the companion IS the BV literal (ground fact), not a
/// fresh var with a `bv2int` bridge.
#[test]
fn len_index_companion_folds_concrete_len_to_bv_literal() {
    with_parser(|parser| {
        let len = parser.solver.int_const(2);
        let companion = parser.len_index_companion(len).expect("companion");
        assert!(
            matches!(parser.solver.term_kind(companion), TermKind::Const),
            "concrete length 2 must fold to a ground BV literal companion, got {:?}",
            parser.solver.term_kind(companion),
        );
        // And it is exactly bv(2): interning makes the folded companion
        // term-identical to a freshly-built literal.
        let expected = parser
            .solver
            .try_bv_const(2, crate::ir::pointer_width())
            .unwrap();
        assert_eq!(
            companion, expected,
            "folded companion must be the interned bv literal 2"
        );
    });
}

/// A length that is Int arithmetic over numerals (even if some builder left
/// it unfolded, ay folds `1 + 1` at term build) still folds to the literal.
#[test]
fn len_index_companion_folds_numeral_arithmetic_len() {
    with_parser(|parser| {
        let one = parser.solver.int_const(1);
        let sum = parser.solver.try_add(one, one).unwrap();
        let companion = parser.len_index_companion(sum).expect("companion");
        let expected = parser
            .solver
            .try_bv_const(2, crate::ir::pointer_width())
            .unwrap();
        assert_eq!(
            companion, expected,
            "numeral-arithmetic length 1+1 must fold to bv literal 2"
        );
    });
}

/// SYMBOLIC Int length → the incumbent fresh-var companion with the `bv2int`
/// bridge is kept byte-for-byte (no behavior change; fail-closed).
#[test]
fn len_index_companion_symbolic_len_keeps_fresh_var_bridge() {
    with_parser(|parser| {
        let len = parser.solver.fresh_var("__trust_vc_len_s", Sort::Int);
        let companion = parser.len_index_companion(len).expect("companion");
        assert!(
            matches!(parser.solver.term_kind(companion), TermKind::Var { .. }),
            "symbolic length must keep the fresh companion var, got {:?}",
            parser.solver.term_kind(companion),
        );
        let name = parser.solver.format_term(companion);
        assert!(
            name.contains("__trust_vc_len_idx"),
            "symbolic companion must be the incumbent __trust_vc_len_idx var, got {name}"
        );
    });
}

/// Concrete NEGATIVE length (violated view precondition) → the maybe-negative
/// variant must NOT fold; the guarded symbolic bridge stays so the
/// inert-bridge refutation path is unchanged.
#[test]
fn len_index_companion_maybe_negative_concrete_negative_keeps_symbolic_path() {
    with_parser(|parser| {
        let len = parser.solver.int_const(-1);
        let companion = parser
            .len_index_companion_maybe_negative(len)
            .expect("companion");
        assert!(
            matches!(parser.solver.term_kind(companion), TermKind::Var { .. }),
            "negative concrete length must keep the guarded symbolic companion, got {:?}",
            parser.solver.term_kind(companion),
        );
    });
}

/// Concrete non-negative length → the maybe-negative variant folds exactly
/// like the unconditional companion (the `len >= 0` guard is denotationally
/// true).
#[test]
fn len_index_companion_maybe_negative_concrete_nonneg_folds() {
    with_parser(|parser| {
        let len = parser.solver.int_const(3);
        let companion = parser
            .len_index_companion_maybe_negative(len)
            .expect("companion");
        let expected = parser
            .solver
            .try_bv_const(3, crate::ir::pointer_width())
            .unwrap();
        assert_eq!(companion, expected);
    });
}

/// Ground index view: a concrete length folds to the BV literal with NO
/// carrier-representability obligation pushed (denotationally in-range).
#[test]
fn len_as_index_bv_folds_concrete_and_pushes_no_representability_obligation() {
    with_parser(|parser| {
        let len = parser.solver.int_const(5);
        let bv = parser.len_as_index_bv(len).expect("index view");
        let expected = parser
            .solver
            .try_bv_const(5, crate::ir::pointer_width())
            .unwrap();
        assert_eq!(bv, expected, "concrete length must fold to the bv literal");
        assert!(
            parser.overflow_checks.is_empty(),
            "a denotationally in-carrier length must not push a representability obligation"
        );
    });
}

/// Ground index view for a SYMBOLIC declared length keeps the incumbent
/// behavior: the `int2bv` lowering plus the pushed carrier-representability
/// obligation (fail-closed pin of the NC4 shape).
#[test]
fn len_as_index_bv_symbolic_keeps_int2bv_and_representability_obligation() {
    with_parser(|parser| {
        let len = parser.solver.fresh_var("__trust_vc_len_s", Sort::Int);
        let bv = parser.len_as_index_bv(len).expect("index view");
        assert!(
            !matches!(parser.solver.term_kind(bv), TermKind::Const),
            "symbolic length must not fold to a literal"
        );
        let label = parser
            .overflow_checks
            .iter()
            .map(|(label, _)| label.as_ref().to_string())
            .collect::<Vec<_>>()
            .join("; ");
        assert!(
            label.contains("not representable in the BitVec"),
            "symbolic length crossing must keep the representability obligation, got: [{label}]"
        );
    });
}

/// Bounds-check fold view: a concrete length yields `Some(bv literal)` from
/// `try_folded_len_index_bv` so ground index bounds stay pure BV.
#[test]
fn try_folded_len_index_bv_folds_concrete_len() {
    with_parser(|parser| {
        let len = parser.solver.int_const(4);
        let folded = parser
            .try_folded_len_index_bv(len)
            .expect("fold probe")
            .expect("concrete length must fold");
        let expected = parser
            .solver
            .try_bv_const(4, crate::ir::pointer_width())
            .unwrap();
        assert_eq!(folded, expected);
    });
}
