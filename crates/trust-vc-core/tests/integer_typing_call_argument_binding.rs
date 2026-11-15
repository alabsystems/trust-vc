//! An INLINE spec function's call binds its arguments at the parameter types
//! (design-trust-proof-backend.md §5b rule 11) exactly as a non-inline call
//! does: `substitute_inline_calls` binds each argument by
//! `bind_call_argument` before the body lands, and leaves a call whose
//! argument its parameter's type cannot hold unexpanded, for the dispatch
//! to refuse. With `fid(q: u8) -> u8 { q }` declared inline and `y: i8 ==
//! -56`, the argument was substituted bare, so `fid(y) < 0` and `fid(y) ==
//! -56i8` were `Verified` in the spec and exec lanes — a `u8`-returning
//! function proven negative.
//!
//! A NON-inline call with a COMPOSITE argument binds it too: `g0(p: Seq<u8>)
//! -> u8 { p[0] }` applied to `t: Seq<i8>` with `t[0] == -56` gave `g0(t) ==
//! 200` `Verified` (a non-integer parameter type passed any argument).
//!
//! The exec lane's DEMAND-INLINE retry (`maybe_retry_with_demand_inlining`)
//! re-encodes a non-inline call with its body substituted; it goes through
//! the same binding, so the non-inline `fid(y) < 0` (`y: i8`) that the retry
//! upgraded to `Verified` is refused ("call to `fid` passes a value of type
//! `i8` for parameter 0 of type `u8`").
//!
//! Each `lie_*` must not be `Verified`; each `same_*` twin is the honest call
//! (`Verified`); each `ctrl_*` an honestly-false goal (refuted).

use trust_vc_core::ir::{CompareOp, TrustVcExpr, TrustVcType};
use trust_vc_core::vc::{
    ObligationKind, ProofObligation, TypedProofObligation, VariableDecl, VerificationContext,
};
use trust_vc_core::VerifyResult;

const U8: TrustVcType = TrustVcType::Uint { width: 8 };
const I8: TrustVcType = TrustVcType::Int { width: 8 };
const INT: TrustVcType = TrustVcType::MathInt;

fn lit(value: i128, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::IntLit { value, ty }
}
fn var(name: &str, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty,
    }
}
fn cmp(op: CompareOp, left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op,
        left: Box::new(left),
        right: Box::new(right),
    }
}
fn fid(arg: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: "fid".to_string(),
        args: vec![arg],
        return_ty: U8,
    }
}

fn fdbl(arg: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: "fdbl".to_string(),
        args: vec![arg],
        return_ty: INT,
    }
}

fn fcast(arg: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: "fcast".to_string(),
        args: vec![arg],
        return_ty: U8,
    }
}

fn g0(arg: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: "g0".to_string(),
        args: vec![arg],
        return_ty: U8,
    }
}
fn first(receiver: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Index {
        receiver: Box::new(receiver),
        index: Box::new(lit(0, TrustVcType::Uint { width: 64 })),
        receiver_name: None,
        elem_ty: ty,
    }
}

fn verify(inline: bool, goal: TrustVcExpr, exec: bool) -> VerifyResult {
    let seq_u8 = TrustVcType::Seq(Box::new(U8));
    let seq_i8 = TrustVcType::Seq(Box::new(I8));
    let decls = vec![
        VariableDecl::new("t".to_string(), seq_i8.clone()),
        VariableDecl::new("p".to_string(), seq_u8.clone()),
        VariableDecl::new("x".to_string(), U8),
        VariableDecl::new("y".to_string(), I8),
        VariableDecl::new("q".to_string(), U8),
        VariableDecl::new("result".to_string(), TrustVcType::Bool),
    ];
    let obligations = vec![
        TypedProofObligation::requires(
            "c_requires_0",
            cmp(CompareOp::Eq, var("x", U8), lit(200, U8)),
        ),
        TypedProofObligation::requires(
            "c_requires_1",
            cmp(
                CompareOp::Eq,
                var("y", I8),
                TrustVcExpr::Neg(Box::new(lit(56, I8))),
            ),
        ),
        TypedProofObligation::requires(
            "c_requires_2",
            cmp(
                CompareOp::Eq,
                TrustVcExpr::CollectionOp {
                    op: trust_vc_core::ir::CollectionOp::Len,
                    receiver: Box::new(var("t", seq_i8.clone())),
                    receiver_name: Some("t".to_string()),
                    args: vec![],
                    ty: TrustVcType::Uint { width: 64 },
                },
                lit(1, TrustVcType::Uint { width: 64 }),
            ),
        ),
        TypedProofObligation::requires(
            "c_requires_3",
            cmp(
                CompareOp::Eq,
                first(var("t", seq_i8.clone()), I8),
                TrustVcExpr::Neg(Box::new(lit(56, I8))),
            ),
        ),
        TypedProofObligation::ensures("c_goal", goal),
    ];
    let mut ctx = VerificationContext::from_typed_parts(decls, obligations);
    ctx.declare_helper_function_typed("fid", U8, vec![("q".to_string(), U8)]);
    ctx.push_obligation(
        ProofObligation::new_typed(
            "__body_axiom_fid",
            cmp(CompareOp::Eq, fid(var("q", U8)), var("q", U8)),
            ObligationKind::BroadcastAssume,
        )
        .with_bound_vars(vec!["q".to_string()])
        .with_inline(inline),
    );
    // `fdbl(d: int) -> int { d + d }`, inline: a `u8` argument lands as the
    // integer it denotes, so `fdbl(x) == 400` for `x == 200` (substituted
    // bare, `x + x` was a `u8` sum under an `int` claim: refused).
    ctx.declare_helper_function_typed("fdbl", INT, vec![("d".to_string(), INT)]);
    ctx.push_obligation(
        ProofObligation::new_typed(
            "__body_axiom_fdbl",
            cmp(
                CompareOp::Eq,
                fdbl(var("d", INT)),
                TrustVcExpr::Arith {
                    op: trust_vc_core::ir::ArithOp::Add,
                    left: Box::new(var("d", INT)),
                    right: Box::new(var("d", INT)),
                    ty: INT,
                },
            ),
            ObligationKind::BroadcastAssume,
        )
        .with_bound_vars(vec!["d".to_string()])
        .with_inline(true),
    );
    // `fcast(c: int) -> u8 { c as u8 }`, inline: the body reads `c` at `int`,
    // so a `u8` argument must land lifted (substituted bare, the cast's
    // `from_ty: int` disagreed with its `u8` operand: refused).
    ctx.declare_helper_function_typed("fcast", U8, vec![("c".to_string(), INT)]);
    ctx.push_obligation(
        ProofObligation::new_typed(
            "__body_axiom_fcast",
            cmp(
                CompareOp::Eq,
                fcast(var("c", INT)),
                TrustVcExpr::Cast {
                    expr: Box::new(var("c", INT)),
                    from_ty: INT,
                    to_ty: U8,
                },
            ),
            ObligationKind::BroadcastAssume,
        )
        .with_bound_vars(vec!["c".to_string()])
        .with_inline(true),
    );
    ctx.declare_helper_function_typed("g0", U8, vec![("p".to_string(), seq_u8.clone())]);
    ctx.push_obligation(
        ProofObligation::new_typed(
            "__body_axiom_g0",
            cmp(
                CompareOp::Eq,
                g0(var("p", seq_u8.clone())),
                first(var("p", seq_u8), U8),
            ),
            ObligationKind::BroadcastAssume,
        )
        .with_bound_vars(vec!["p".to_string()]),
    );
    if exec {
        ctx.enable_overflow_checks();
    }
    ctx.verify()
}

fn class(result: &VerifyResult) -> &'static str {
    match result {
        VerifyResult::Verified => "Verified",
        VerifyResult::Counterexample { .. } | VerifyResult::NotProved { .. } => "Refuted",
        _ => "Unknown",
    }
}

#[test]
fn every_call_binds_its_arguments() {
    let cases: Vec<(&str, bool, TrustVcExpr)> = vec![
        (
            "lie_inline_fid_i8_arg_lt_0",
            true,
            cmp(CompareOp::Lt, fid(var("y", I8)), lit(0, I8)),
        ),
        (
            "lie_inline_fid_i8_arg_eq_neg56",
            true,
            cmp(
                CompareOp::Eq,
                fid(var("y", I8)),
                TrustVcExpr::Neg(Box::new(lit(56, I8))),
            ),
        ),
        (
            "lie_noninline_fid_i8_arg_lt_0",
            false,
            cmp(CompareOp::Lt, fid(var("y", I8)), lit(0, I8)),
        ),
        (
            "lie_noninline_g0_seq_i8_arg_eq_200",
            false,
            cmp(
                CompareOp::Eq,
                g0(var("t", TrustVcType::Seq(Box::new(I8)))),
                lit(200, U8),
            ),
        ),
        (
            "same_inline_fid_u8_arg_eq_200",
            true,
            cmp(CompareOp::Eq, fid(var("x", U8)), lit(200, U8)),
        ),
        (
            "ctrl_inline_fid_u8_arg_eq_201",
            true,
            cmp(CompareOp::Eq, fid(var("x", U8)), lit(201, U8)),
        ),
        (
            "same_inline_fdbl_u8_arg_lifted_eq_400",
            true,
            cmp(CompareOp::Eq, fdbl(var("x", U8)), lit(400, INT)),
        ),
        (
            "same_inline_fcast_u8_arg_lifted_eq_200",
            true,
            cmp(CompareOp::Eq, fcast(var("x", U8)), lit(200, U8)),
        ),
        (
            "lie_inline_fdbl_u8_arg_wraps_eq_144",
            true,
            cmp(CompareOp::Eq, fdbl(var("x", U8)), lit(144, INT)),
        ),
    ];
    let mut wrong = Vec::new();
    for (name, inline, goal) in cases {
        for exec in [false, true] {
            let got = verify(inline, goal.clone(), exec);
            println!("INLARG|{name}|exec={exec}|{}", class(&got));
            let ok = if name.starts_with("lie_") {
                class(&got) != "Verified"
            } else if name.starts_with("same_") {
                class(&got) == "Verified"
            } else {
                class(&got) == "Refuted"
            };
            if !ok {
                let raw: String = format!("{got:?}").chars().take(200).collect();
                wrong.push(format!("{name} exec={exec}: {} ({raw})", class(&got)));
            }
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}
