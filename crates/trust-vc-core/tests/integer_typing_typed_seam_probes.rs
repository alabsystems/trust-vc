//! Targeted probes of the TYPED SEAM
//! (`VerificationContext::from_typed_parts`) against trust-vc's integer
//! semantics (design-trust-proof-backend.md §5b).
//!
//! Every `Never` case is FALSE under every reading on offer — the exact
//! integers (Verus spec), two's complement in the node's DECLARED type, and
//! two's complement in each operand's own type — so none may come back
//! `Verified`. `Must` cases are TRUE under every reading and must not be
//! refuted. `Rule` cases are decided only by §5b's own rules (named in the
//! case); they are reported, and asserted separately.
//!
//! Prints `CASE|<name>|<class>|<got>|<raw>` per case.

use trust_vc_core::ir::{
    ArithOp, CompareOp, IntConstKind, LogicOp, MatchArm, MatchPattern, QuantifierKind,
    SpecialArithOp, TrustVcExpr, TrustVcType, WrappingMode,
};
use trust_vc_core::vc::{SolverMode, TypedProofObligation, VariableDecl, VerificationContext};
use trust_vc_core::VerifyResult;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Got {
    Verified,
    Refuted,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Class {
    /// False under every reading: must not be Verified.
    Never,
    /// True under every reading: must not be refuted.
    Must,
    /// §5b's own rule says Verified.
    RuleTrue,
    /// §5b's own rule says false.
    RuleFalse,
}

#[derive(Clone, Copy)]
struct Mode {
    exec: bool,
    assert: bool,
    bv: bool,
}

const SPEC: Mode = Mode {
    exec: false,
    assert: false,
    bv: false,
};
const EXEC: Mode = Mode {
    exec: true,
    assert: true,
    bv: false,
};
const BV: Mode = Mode {
    exec: false,
    assert: true,
    bv: true,
};

fn run(
    params: &[(&str, TrustVcType)],
    requires: &[TrustVcExpr],
    goal: TrustVcExpr,
    mode: Mode,
) -> (Got, VerifyResult) {
    let mut variables: Vec<VariableDecl> = params
        .iter()
        .map(|(n, t)| VariableDecl::new((*n).to_string(), t.clone()))
        .collect();
    variables.push(VariableDecl::new("result".to_string(), TrustVcType::Bool));
    let mut obligations: Vec<TypedProofObligation> = requires
        .iter()
        .enumerate()
        .map(|(i, r)| TypedProofObligation::requires(format!("r5_requires_{i}"), r.clone()))
        .collect();
    let mut g = if mode.assert {
        TypedProofObligation::assert("r5_goal", goal)
    } else {
        TypedProofObligation::ensures("r5_ensures_0", goal)
    };
    if mode.bv {
        g = g.with_solver_mode(SolverMode::BitVector);
    }
    obligations.push(g);
    let mut ctx = VerificationContext::from_typed_parts(variables, obligations);
    if mode.exec {
        ctx.enable_overflow_checks();
    }
    let raw = ctx.verify();
    let got = match &raw {
        VerifyResult::Verified => Got::Verified,
        VerifyResult::Counterexample { .. } | VerifyResult::NotProved { .. } => Got::Refuted,
        _ => Got::Unknown,
    };
    (got, raw)
}

fn u(w: u32) -> TrustVcType {
    TrustVcType::Uint { width: w }
}
fn i(w: u32) -> TrustVcType {
    TrustVcType::Int { width: w }
}
fn int() -> TrustVcType {
    TrustVcType::MathInt
}
fn lit(v: i128, t: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::IntLit { value: v, ty: t }
}
fn var(n: &str, t: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: n.to_string(),
        ty: t,
    }
}
fn cmp(op: CompareOp, l: TrustVcExpr, r: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op,
        left: Box::new(l),
        right: Box::new(r),
    }
}
fn eq(l: TrustVcExpr, r: TrustVcExpr) -> TrustVcExpr {
    cmp(CompareOp::Eq, l, r)
}
fn arith(op: ArithOp, l: TrustVcExpr, r: TrustVcExpr, t: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Arith {
        op,
        left: Box::new(l),
        right: Box::new(r),
        ty: t,
    }
}
fn special(op: SpecialArithOp, l: TrustVcExpr, r: TrustVcExpr, t: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::SpecialArith {
        op,
        left: Box::new(l),
        right: Box::new(r),
        ty: t,
    }
}
fn wrapping(
    mode: WrappingMode,
    op: ArithOp,
    l: TrustVcExpr,
    r: TrustVcExpr,
    t: TrustVcType,
) -> TrustVcExpr {
    TrustVcExpr::WrappingArith {
        mode,
        op,
        left: Box::new(l),
        right: Box::new(r),
        ty: t,
    }
}
fn cast(e: TrustVcExpr, from: TrustVcType, to: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Cast {
        expr: Box::new(e),
        from_ty: from,
        to_ty: to,
    }
}
fn and(l: TrustVcExpr, r: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(l),
        right: Box::new(r),
    }
}

/// x: u8 == 0, y: i16 == -1 — the r4 mixed pair.
fn mixed_pair() -> (Vec<(&'static str, TrustVcType)>, Vec<TrustVcExpr>) {
    (
        vec![("x", u(8)), ("y", i(16))],
        vec![
            eq(var("x", u(8)), lit(0, u(8))),
            eq(var("y", i(16)), lit(-1, i(16))),
        ],
    )
}
fn x8() -> TrustVcExpr {
    var("x", u(8))
}
fn y16() -> TrustVcExpr {
    var("y", i(16))
}
/// `x + y` declared `decl` — exact -1; u8-wrap 255; i16-wrap -1.
fn mixed_sum(decl: TrustVcType) -> TrustVcExpr {
    arith(ArithOp::Add, x8(), y16(), decl)
}

struct Case {
    name: &'static str,
    class: Class,
    params: Vec<(&'static str, TrustVcType)>,
    requires: Vec<TrustVcExpr>,
    goal: TrustVcExpr,
    mode: Mode,
}

fn case(
    name: &'static str,
    class: Class,
    pr: (Vec<(&'static str, TrustVcType)>, Vec<TrustVcExpr>),
    goal: TrustVcExpr,
    mode: Mode,
) -> Case {
    Case {
        name,
        class,
        params: pr.0,
        requires: pr.1,
        goal,
        mode,
    }
}

fn cases() -> Vec<Case> {
    let mut v = Vec::new();
    // --- WrappingArith over MIXED operands (not derived by 9def8d43). ---
    for (name, decl) in [
        ("wrapping_add_mixed_decl_u8", u(8)),
        ("wrapping_add_mixed_decl_i16", i(16)),
    ] {
        for mode in [SPEC, EXEC] {
            v.push(case(
                name,
                Class::Never,
                mixed_pair(),
                // readings: u8 255, i16 -1, exact -1
                cmp(
                    CompareOp::Gt,
                    wrapping(
                        WrappingMode::Wrapping,
                        ArithOp::Add,
                        x8(),
                        y16(),
                        decl.clone(),
                    ),
                    lit(1000, i(16)),
                ),
                mode,
            ));
        }
    }
    v.push(case(
        "saturating_add_mixed_decl_u8",
        Class::Never,
        mixed_pair(),
        // readings: u8 saturate 0, i16 -1, exact -1
        cmp(
            CompareOp::Gt,
            wrapping(WrappingMode::Saturating, ArithOp::Add, x8(), y16(), u(8)),
            lit(1000, i(16)),
        ),
        SPEC,
    ));
    v.push(case(
        "wrapping_sub_mixed_decl_u8_eq_65535",
        Class::Never,
        (
            vec![("x", u(8)), ("y", i(16))],
            vec![eq(x8(), lit(0, u(8))), eq(y16(), lit(1, i(16)))],
        ),
        // readings: u8 255, i16 -1, exact -1
        eq(
            wrapping(WrappingMode::Wrapping, ArithOp::Sub, x8(), y16(), u(8)),
            lit(65535, u(32)),
        ),
        SPEC,
    ));
    // --- Shift of a mixed (exact) result, declared u8. ---
    for (name, op) in [
        ("shl_of_mixed_sum", SpecialArithOp::Shl),
        ("shr_of_mixed_sum", SpecialArithOp::Shr),
    ] {
        v.push(case(
            name,
            Class::Never,
            mixed_pair(),
            // readings: exact -2 / -1; u8 254 / 127; i16 -2 / -1
            cmp(
                CompareOp::Gt,
                special(op, mixed_sum(u(8)), lit(1, u(32)), u(8)),
                lit(1000, i(16)),
            ),
            SPEC,
        ));
    }
    // --- Cast of a mixed result whose producer says from_ty u8. ---
    v.push(case(
        "cast_mixed_from_u8_to_u32_eq_65535",
        Class::Never,
        mixed_pair(),
        // readings: exact -1 -> 4294967295; u8 255 -> 255
        eq(cast(mixed_sum(u(8)), u(8), u(32)), lit(65535, u(32))),
        SPEC,
    ));
    v.push(case(
        "cast_mixed_from_int_to_u8_is_255",
        Class::Must,
        mixed_pair(),
        // exact -1 as u8 = 255 (Rust `as` truncation); u8 reading 255.
        eq(cast(mixed_sum(int()), int(), u(8)), lit(255, u(8))),
        SPEC,
    ));
    // --- Bitwise NOT of a mixed result. ---
    v.push(case(
        "bitnot_of_mixed_sum_ne_0",
        Class::Never,
        mixed_pair(),
        // readings: exact !(-1) = 0; u8 !255 = 0; i16 0
        cmp(
            CompareOp::Ne,
            TrustVcExpr::Not(Box::new(mixed_sum(u(8)))),
            lit(0, i(16)),
        ),
        SPEC,
    ));
    v.push(case(
        "bitnot_of_mixed_sum_eq_0",
        Class::Must,
        mixed_pair(),
        eq(TrustVcExpr::Not(Box::new(mixed_sum(u(8)))), lit(0, i(16))),
        SPEC,
    ));
    // --- Match with arms of two types (left open by the fix). ---
    for (name, decl) in [
        ("match_mixed_arms_decl_u8", u(8)),
        ("match_mixed_arms_decl_i16", i(16)),
    ] {
        let (mut params, mut requires) = mixed_pair();
        params.push(("s", u(8)));
        params.push(("z", i(16)));
        requires.push(eq(var("s", u(8)), lit(1, u(8))));
        requires.push(eq(var("z", i(16)), lit(256, i(16))));
        let m = TrustVcExpr::Match {
            scrutinee: Box::new(var("s", u(8))),
            arms: vec![
                MatchArm::new(MatchPattern::Lit(lit(0, u(8))), x8()),
                MatchArm::new(MatchPattern::Wildcard, y16()),
            ],
            ty: decl,
        };
        for mode in [SPEC, EXEC] {
            v.push(case(
                name,
                Class::Never,
                (params.clone(), requires.clone()),
                // readings: -1 >= 256; u8 255 >= 256; i16 -1 >= 256 — all false
                cmp(CompareOp::Ge, m.clone(), var("z", i(16))),
                mode,
            ));
        }
    }
    // --- Nat-DECLARED subtraction of two u8 values (declared nat wins). ---
    {
        let (params, mut requires) = (
            vec![("x", u(8)), ("w", u(8))],
            vec![eq(x8(), lit(0, u(8))), eq(var("w", u(8)), lit(1, u(8)))],
        );
        let d = arith(ArithOp::Sub, x8(), var("w", u(8)), TrustVcType::Nat);
        v.push(case(
            "nat_declared_sub_gt_300",
            Class::Never,
            (params.clone(), requires.clone()),
            // readings: exact -1, u8 255, nat-clamp 0
            cmp(CompareOp::Gt, d.clone(), lit(300, i(16))),
            SPEC,
        ));
        // Vacuity canary: a harmless premise over the nat-declared term, and a
        // false goal. Verified means the premises became inconsistent.
        requires.push(cmp(CompareOp::Le, d, lit(1000, i(16))));
        v.push(case(
            "nat_declared_sub_premise_vacuity",
            Class::Never,
            (params, requires),
            eq(x8(), lit(1, u(8))),
            SPEC,
        ));
    }
    // --- A malformed literal read two ways in one VC (bits vs value). ---
    {
        let (params, requires) = (
            vec![("z", int())],
            vec![eq(var("z", int()), lit(-1, int()))],
        );
        let bad = || lit(-1, u(8));
        v.push(case(
            "malformed_neg_u8_literal_both_readings",
            Class::Never,
            (params, requires),
            // value reading: -1 > 0 false; bits reading: 255 == -1 false
            and(
                cmp(CompareOp::Gt, bad(), lit(0, u(8))),
                eq(bad(), var("z", int())),
            ),
            SPEC,
        ));
    }
    // --- An i32 literal in an i32-DECLARED node beside a u8 operand. ---
    {
        let pr = || (vec![("x", u(8))], vec![eq(x8(), lit(100, u(8)))]);
        let node = || arith(ArithOp::Add, x8(), lit(200, i(32)), i(32));
        // The producer typed the literal AND the node `i32`: §5b rule 1 (two
        // fixed types -> exact) and the declared type both give 300; only the
        // placeholder reading of `Int{32}` (a u8 literal, u8 arithmetic) gives 44.
        v.push(case(
            "i32_literal_in_i32_node_eq_44",
            Class::RuleFalse,
            pr(),
            eq(node(), lit(44, i(16))),
            SPEC,
        ));
        v.push(case(
            "i32_literal_in_i32_node_eq_300",
            Class::RuleTrue,
            pr(),
            eq(node(), lit(300, i(16))),
            SPEC,
        ));
    }
    // --- An untyped literal TREE beside an `int` peer. ---
    {
        let tree = || {
            arith(
                ArithOp::Add,
                lit(2_147_483_647, i(32)),
                lit(1, i(32)),
                i(32),
            )
        };
        // §5b rule 2: every literal of the tree is a value of the `int` peer,
        // so the tree is `int` arithmetic (2147483648), as in Verus.
        v.push(case(
            "untyped_tree_vs_int_peer_wraps",
            Class::RuleFalse,
            (
                vec![("z", int())],
                vec![eq(var("z", int()), lit(-2_147_483_648, int()))],
            ),
            eq(var("z", int()), tree()),
            SPEC,
        ));
        v.push(case(
            "untyped_tree_vs_int_peer_exact",
            Class::RuleTrue,
            (
                vec![("z", int())],
                vec![eq(var("z", int()), lit(2_147_483_648, int()))],
            ),
            eq(var("z", int()), tree()),
            SPEC,
        ));
    }
    // --- Var-to-var pin across types: x: u8 == y: i16 == 200. ---
    {
        let pr = || {
            (
                vec![("x", u(8)), ("y", i(16))],
                vec![eq(y16(), lit(200, i(16))), eq(x8(), y16())],
            )
        };
        let sum = || arith(ArithOp::Add, x8(), lit(56, u(8)), u(8));
        v.push(case(
            "pin_x_eq_y_u8_sum_wraps_to_0",
            Class::RuleTrue,
            pr(),
            eq(sum(), lit(0, u(8))),
            SPEC,
        ));
        v.push(case(
            "pin_x_eq_y_u8_sum_is_not_256",
            Class::RuleFalse,
            pr(),
            eq(sum(), lit(256, u(16))),
            SPEC,
        ));
    }
    // --- A negative shift amount, spec (not by bit_vector). ---
    v.push(case(
        "shl_by_negative_i16_amount_eq_1",
        Class::Never,
        (
            vec![("k", i(16))],
            vec![eq(var("k", i(16)), lit(-1, i(16)))],
        ),
        // readings: 0 (read unsigned/saturated), 128 (mod 8) — never 1
        eq(
            special(SpecialArithOp::Shl, lit(1, u(8)), var("k", i(16)), u(8)),
            lit(1, u(8)),
        ),
        SPEC,
    ));
    // --- Exec: shift by >= width, division by zero (Rust panics). ---
    v.push(case(
        "exec_shl_by_width_eq_0",
        Class::RuleFalse, // exec assert: `1u8 << 8` panics (shift overflow)
        (vec![("k", u(32))], vec![eq(var("k", u(32)), lit(8, u(32)))]),
        eq(
            special(SpecialArithOp::Shl, lit(1, u(8)), var("k", u(32)), u(8)),
            lit(0, u(8)),
        ),
        EXEC,
    ));
    v.push(case(
        "exec_div_by_zero_u8",
        Class::RuleFalse,
        (
            vec![("x", u(8)), ("w", u(8))],
            vec![eq(x8(), lit(5, u(8))), eq(var("w", u(8)), lit(0, u(8)))],
        ),
        eq(
            arith(ArithOp::Div, x8(), var("w", u(8)), u(8)),
            lit(0, u(8)),
        ),
        EXEC,
    ));
    v.push(case(
        "exec_div_by_zero_mixed",
        Class::RuleFalse,
        (
            vec![("x", u(8)), ("y", i(16))],
            vec![eq(x8(), lit(5, u(8))), eq(y16(), lit(0, i(16)))],
        ),
        eq(arith(ArithOp::Div, x8(), y16(), u(8)), lit(0, u(8))),
        EXEC,
    ));
    // --- Negation of an unsigned value. ---
    v.push(case(
        "neg_of_u8_gt_1000",
        Class::Never,
        (vec![("x", u(8))], vec![eq(x8(), lit(1, u(8)))]),
        // readings: u8 255, exact -1
        cmp(
            CompareOp::Gt,
            TrustVcExpr::Neg(Box::new(x8())),
            lit(1000, i(16)),
        ),
        SPEC,
    ));
    // --- u128 / i128 extremes, mixed (exact at 129 bits). ---
    {
        let pr = || {
            (
                vec![("x", u(128)), ("y", i(128))],
                vec![
                    eq(
                        var("x", u(128)),
                        TrustVcExpr::IntConst {
                            ty: u(128),
                            kind: IntConstKind::Max,
                        },
                    ),
                    eq(var("y", i(128)), lit(-1, i(128))),
                ],
            )
        };
        let x = || var("x", u(128));
        let y = || var("y", i(128));
        v.push(case(
            "u128max_plus_neg1_gt_x",
            Class::Never,
            pr(),
            cmp(CompareOp::Gt, arith(ArithOp::Add, x(), y(), u(128)), x()),
            SPEC,
        ));
        v.push(case(
            "u128max_times_neg1_gt_x",
            Class::Never,
            pr(),
            cmp(CompareOp::Gt, arith(ArithOp::Mul, x(), y(), u(128)), x()),
            SPEC,
        ));
        v.push(case(
            "u128max_times_neg1_lt_0",
            Class::RuleTrue,
            pr(),
            cmp(
                CompareOp::Lt,
                arith(ArithOp::Mul, x(), y(), u(128)),
                lit(0, i(128)),
            ),
            SPEC,
        ));
        v.push(case(
            "u128max_xor_neg1_gt_1",
            Class::Never,
            pr(),
            cmp(
                CompareOp::Gt,
                special(SpecialArithOp::BitXor, x(), y(), u(128)),
                lit(1, i(128)),
            ),
            SPEC,
        ));
        v.push(case(
            "u128max_or_neg1_eq_neg1",
            Class::Must,
            pr(),
            eq(special(SpecialArithOp::BitOr, x(), y(), u(128)), y()),
            SPEC,
        ));
        v.push(case(
            "u128max_and_neg1_eq_x",
            Class::Must,
            pr(),
            eq(special(SpecialArithOp::BitAnd, x(), y(), u(128)), x()),
            SPEC,
        ));
    }
    // --- IntConst beside a wider signed operand. ---
    v.push(case(
        "i8min_minus_i16_one_gt_0",
        Class::Never,
        (vec![("y", i(16))], vec![eq(y16(), lit(1, i(16)))]),
        // readings: exact -129; declared i16 -129 (i8 wrap 127 is not declared)
        cmp(
            CompareOp::Gt,
            arith(
                ArithOp::Sub,
                TrustVcExpr::IntConst {
                    ty: i(8),
                    kind: IntConstKind::Min,
                },
                y16(),
                i(16),
            ),
            lit(0, i(16)),
        ),
        SPEC,
    ));
    // --- Let bound at a narrower declared type than its value. ---
    for (name, value) in [
        ("let_u8_bound_to_i16", y16()),
        ("let_u8_bound_to_mixed_sum", mixed_sum(u(8))),
    ] {
        v.push(case(
            name,
            Class::Never,
            mixed_pair(),
            // readings: -1, u8 255 — never > 1000
            TrustVcExpr::Let {
                name: "t".to_string(),
                ty: u(8),
                value: Box::new(value),
                body: Box::new(cmp(CompareOp::Gt, var("t", u(8)), lit(1000, i(16)))),
            },
            SPEC,
        ));
    }
    // --- Quantifier body over a mixed sum. ---
    {
        let (params, requires) = mixed_pair();
        let body = TrustVcExpr::Implies {
            premise: Box::new(eq(var("q", u(8)), lit(0, u(8)))),
            conclusion: Box::new(cmp(
                CompareOp::Gt,
                arith(ArithOp::Add, var("q", u(8)), y16(), u(8)),
                lit(1000, i(16)),
            )),
        };
        v.push(case(
            "forall_mixed_sum_gt_1000",
            Class::Never,
            (params, requires),
            TrustVcExpr::Quantifier {
                kind: QuantifierKind::Forall,
                bound_vars: vec![("q".to_string(), u(8))],
                body: Box::new(body),
                triggers: None,
                trigger_inference_mode: None,
            },
            SPEC,
        ));
    }
    // --- by(bit_vector) over the mixed pair. ---
    v.push(case(
        "bv_mixed_sum_gt_1000",
        Class::Never,
        mixed_pair(),
        cmp(CompareOp::Gt, mixed_sum(u(8)), lit(1000, i(16))),
        BV,
    ));
    v.push(case(
        "bv_wrapping_mixed_gt_1000",
        Class::Never,
        mixed_pair(),
        cmp(
            CompareOp::Gt,
            wrapping(WrappingMode::Wrapping, ArithOp::Add, x8(), y16(), u(8)),
            lit(1000, i(16)),
        ),
        BV,
    ));
    v
}

#[test]
fn typed_seam_probes() {
    let mut never_verified = Vec::new();
    let mut must_refuted = Vec::new();
    let mut rule_wrong = Vec::new();
    for c in cases() {
        let (got, raw) = run(&c.params, &c.requires, c.goal.clone(), c.mode);
        let raw_s: String = format!("{raw:?}").chars().take(200).collect();
        let tag = format!(
            "{}{}",
            c.name,
            if c.mode.bv {
                "[bv]"
            } else if c.mode.exec {
                "[exec]"
            } else {
                "[spec]"
            }
        );
        println!("CASE|{tag}|{:?}|{got:?}|{raw_s}", c.class);
        match (c.class, got) {
            (Class::Never, Got::Verified) => never_verified.push(tag),
            (Class::Must, Got::Refuted) => must_refuted.push(tag),
            (Class::RuleTrue, Got::Refuted) | (Class::RuleFalse, Got::Verified) => {
                rule_wrong.push(tag)
            }
            _ => {}
        }
    }
    println!("SUMMARY never_verified={never_verified:?}");
    println!("SUMMARY must_refuted={must_refuted:?}");
    println!("SUMMARY rule_wrong={rule_wrong:?}");
    assert!(
        never_verified.is_empty() && must_refuted.is_empty() && rule_wrong.is_empty(),
        "FALSE VERIFIED {never_verified:?}; FALSE COUNTEREXAMPLE {must_refuted:?}; \
         against the §5b rule {rule_wrong:?}"
    );
}
