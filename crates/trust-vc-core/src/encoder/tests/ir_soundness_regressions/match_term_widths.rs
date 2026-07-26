//! #2131 regressions: match arm width coercion and result term-width tracking.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ========================================================================
// #2131: encode_match must coerce mixed-width arm bodies before ITE
// ========================================================================
//
// Before #2131, IR encode_match built `ite(cond, body, else)` directly and
// panicked when branch sorts differed (e.g., BV8 vs BV32).

/// DISCRIMINATING: `match tag { 1u32 => small:u8, _ => big:u32 }` must encode
/// and evaluate with the u8 arm zero-extended to u32.
fn build_2131_mixed_width_match_expr() -> TrustVcExpr {
    let u8_ty = TrustVcType::Uint { width: 8 };
    let u32_ty = TrustVcType::Uint { width: 32 };
    TrustVcExpr::Match {
        scrutinee: Box::new(TrustVcExpr::Var {
            name: "tag".into(),
            ty: u32_ty.clone(),
        }),
        arms: vec![
            MatchArm {
                pattern: MatchPattern::Lit(TrustVcExpr::IntLit {
                    value: 1,
                    ty: u32_ty.clone(),
                }),
                body: TrustVcExpr::Var {
                    name: "small".into(),
                    ty: u8_ty,
                },
                guard: None,
            },
            MatchArm {
                pattern: MatchPattern::Wildcard,
                body: TrustVcExpr::Var {
                    name: "big".into(),
                    ty: u32_ty.clone(),
                },
                guard: None,
            },
        ],
        ty: u32_ty,
    }
}

struct MatchTerms {
    tag: Term,
    small: Term,
    big: Term,
    result: Option<Term>,
}

fn setup_2131_match_env() -> (QuantifierTestEnv, MatchTerms) {
    let mut env = QuantifierTestEnv::new();
    let tag = env.solver.declare_const("tag", Sort::bitvec(32));
    let small = env.solver.declare_const("small", Sort::bitvec(8));
    let big = env.solver.declare_const("big", Sort::bitvec(32));
    env.variables.insert("tag".into(), tag);
    env.variables.insert("small".into(), small);
    env.variables.insert("big".into(), big);
    env.var_types
        .insert("tag".into(), TrustVcType::Uint { width: 32 });
    env.var_types
        .insert("small".into(), TrustVcType::Uint { width: 8 });
    env.var_types
        .insert("big".into(), TrustVcType::Uint { width: 32 });
    (
        env,
        MatchTerms {
            tag,
            small,
            big,
            result: None,
        },
    )
}

fn assert_2131_match_value(
    env: &mut QuantifierTestEnv,
    terms: &MatchTerms,
    tag_val: i64,
    expected: i64,
    label: &str,
) {
    env.solver.try_push().unwrap();
    let tag_val_bv = env.solver.try_bv_const(tag_val, 32).unwrap();
    let small_10 = env.solver.try_bv_const(10, 8).unwrap();
    let big_20 = env.solver.try_bv_const(20, 32).unwrap();
    let expected_bv = env.solver.try_bv_const(expected, 32).unwrap();
    let tag_is = env.solver.try_eq(terms.tag, tag_val_bv).unwrap();
    let small_is = env.solver.try_eq(terms.small, small_10).unwrap();
    let big_is = env.solver.try_eq(terms.big, big_20).unwrap();
    let result = terms
        .result
        .as_ref()
        .cloned()
        .expect("#2131 test bug: match result term must be set before assertion");
    let wrong = env.solver.try_neq(result, expected_bv).unwrap();
    env.solver.try_assert_term(tag_is).unwrap();
    env.solver.try_assert_term(small_is).unwrap();
    env.solver.try_assert_term(big_is).unwrap();
    env.solver.try_assert_term(wrong).unwrap();
    let sat = env.solver.try_check_sat().unwrap();
    env.solver.try_pop().unwrap();
    assert!(
        sat.is_unsat(),
        "#2131: {} expected {}u32, got {:?}",
        label,
        expected,
        sat
    );
}

#[test]
fn test_2131_match_mixed_width_arms_encode_and_evaluate() {
    let expr = build_2131_mixed_width_match_expr();
    let (mut env, mut terms) = setup_2131_match_env();

    let mut parser = env.parser();
    parser.term_widths.insert(terms.tag, (32, false));
    parser.term_widths.insert(terms.small, (8, false));
    parser.term_widths.insert(terms.big, (32, false));

    let match_term = parser
        .encode_trust_vc_expr(&expr)
        .expect("#2131: mixed-width match should encode without sort mismatch");
    terms.result = Some(match_term);
    let width_info = parser.term_widths.get(&match_term);
    assert!(
        width_info.is_some(),
        "#2131: match result term should have term_widths metadata"
    );
    assert_eq!(
        *width_info.unwrap(),
        (32, false),
        "#2131: match result should be tracked as u32"
    );
    drop(parser);

    assert_2131_match_value(&mut env, &terms, 1, 10, "tag==1 arm");
    assert_2131_match_value(&mut env, &terms, 2, 20, "wildcard arm");
}

// ========================================================================
