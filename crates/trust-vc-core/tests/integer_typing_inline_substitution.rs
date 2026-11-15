//! An INLINE spec-function body is validated where it is substituted
//! (design-trust-proof-backend.md §5b rule 13): the typing validator runs on
//! the tree the encoder reads, after inline expansion, because an inline body
//! is never encoded as an axiom of its own.
//!
//! Context: `s: Seq<u8>`, `s.len() == 1`, `s[0] == 200`, and `f(p: Seq<u8>)`
//! declared inline. Measured by the r10 verifier: a body `p[0]` declared `i8`
//! made `f(s) == -56` `Verified` at 9fd50172 (a REGRESSION — `Unknown` at its
//! parent, whose per-dispatch element-read check 9fd50172 deleted), and the
//! same lie one level up, `p.take(1)` declared `Seq<i8>` then read at `i8`,
//! was `Verified` at both; in the spec and the exec lane alike. The honest
//! body stays `Verified` and an honestly-false goal is refuted.

use trust_vc_core::ir::{CollectionOp, CompareOp, TrustVcExpr, TrustVcType};
use trust_vc_core::vc::{
    ObligationKind, ProofObligation, TypedProofObligation, VariableDecl, VerificationContext,
};
use trust_vc_core::VerifyResult;

const U8: TrustVcType = TrustVcType::Uint { width: 8 };
const I8: TrustVcType = TrustVcType::Int { width: 8 };
const I16: TrustVcType = TrustVcType::Int { width: 16 };
const U64: TrustVcType = TrustVcType::Uint { width: 64 };

fn lit(value: i128, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::IntLit { value, ty }
}
fn seq_u8(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: TrustVcType::Seq(Box::new(U8)),
    }
}
fn eq(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(left),
        right: Box::new(right),
    }
}
fn first(receiver: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Index {
        receiver: Box::new(receiver),
        index: Box::new(lit(0, U64)),
        receiver_name: Some("p".to_string()),
        elem_ty: ty,
    }
}
fn call(arg: TrustVcExpr, ret: &TrustVcType) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: "f".to_string(),
        args: vec![arg],
        return_ty: ret.clone(),
    }
}

/// `f(p: Seq<u8>) -> ret { body }` declared INLINE, goal `f(s) == rhs`.
fn verify(ret: TrustVcType, body: TrustVcExpr, rhs: TrustVcExpr, exec: bool) -> VerifyResult {
    let seq = TrustVcType::Seq(Box::new(U8));
    let decls = vec![
        VariableDecl::new("s".to_string(), seq.clone()),
        VariableDecl::new("p".to_string(), seq.clone()),
        VariableDecl::new("result".to_string(), TrustVcType::Bool),
    ];
    let len = TrustVcExpr::CollectionOp {
        op: CollectionOp::Len,
        receiver: Box::new(seq_u8("s")),
        receiver_name: Some("s".to_string()),
        args: vec![],
        ty: U64,
    };
    let obligations = vec![
        TypedProofObligation::requires("c_requires_0", eq(len, lit(1, U64))),
        TypedProofObligation::requires("c_requires_1", eq(first(seq_u8("s"), U8), lit(200, U8))),
        TypedProofObligation::ensures("c_goal", eq(call(seq_u8("s"), &ret), rhs)),
    ];
    let mut ctx = VerificationContext::from_typed_parts(decls, obligations);
    ctx.declare_helper_function_typed("f", ret.clone(), vec![("p".to_string(), seq)]);
    ctx.push_obligation(
        ProofObligation::new_typed(
            "__body_axiom_f",
            eq(call(seq_u8("p"), &ret), body),
            ObligationKind::BroadcastAssume,
        )
        .with_bound_vars(vec!["p".to_string()])
        .with_inline(true),
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
fn an_inline_body_is_validated_after_substitution() {
    let take_i8 = || TrustVcExpr::CollectionOp {
        op: CollectionOp::Take,
        receiver: Box::new(seq_u8("p")),
        receiver_name: Some("p".to_string()),
        args: vec![lit(1, TrustVcType::MathInt)],
        ty: TrustVcType::Seq(Box::new(I8)),
    };
    let mut wrong = Vec::new();
    for exec in [false, true] {
        for (name, ret, body, rhs, expect) in [
            ("lie_read_at_i8", I8, first(seq_u8("p"), I8), -56, "Unknown"),
            (
                "lie_take_declared_seq_i8",
                I8,
                first(take_i8(), I8),
                -56,
                "Unknown",
            ),
            ("same_read", U8, first(seq_u8("p"), U8), 200, "Verified"),
            (
                "ctrl_read_is_201",
                U8,
                first(seq_u8("p"), U8),
                201,
                "Refuted",
            ),
        ] {
            let got = verify(ret, body, lit(rhs, I16), exec);
            println!("INLINE|{name}|exec={exec}|{}", class(&got));
            if class(&got) != expect {
                let raw: String = format!("{got:?}").chars().take(240).collect();
                wrong.push(format!("{name} exec={exec}: {} ({raw})", class(&got)));
            }
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}
