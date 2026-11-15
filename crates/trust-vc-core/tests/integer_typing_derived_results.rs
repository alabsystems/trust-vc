//! Every typed-seam claim the encoder reads is DERIVED
//! (design-trust-proof-backend.md §5b rule 13).
//!
//! Context: `s: Seq<u8>` with `s.len() == 1` and `s[0] == 200` (a map `m:
//! Map<u8, u8>` with `m[200] == 7`, a set `st: Set<u8>` holding 200). Each
//! `lie_*` goal is FALSE under the declarations the context makes — the one
//! element is 200, never -56 — and was `Verified` when the r10 verifier
//! measured it (at 9fd50172, in the spec and the exec lane): a result type the
//! validator did not re-derive (`to_set`, `to_multiset`, `dom`, `view`,
//! `map_values` and its closure's return, `fold_left`, `Set::map`,
//! `Map::map_values`), a join that FORGETS the element type (a conditional,
//! `let` or `match` declared at a type parameter, `Poly` or an opaque type),
//! and a map key of another integer type. Each `same_*` twin is the honest
//! program and stays `Verified`; each `ctrl_*` is an honestly-false goal on
//! the same context and is refuted (the context is not vacuous).

use trust_vc_core::ir::{
    CollectionOp, CompareOp, MatchArm, MatchPattern, TrustVcExpr, TrustVcType,
};
use trust_vc_core::vc::{TypedProofObligation, VariableDecl, VerificationContext};
use trust_vc_core::VerifyResult;

fn lit(value: i128, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::IntLit { value, ty }
}
fn var(name: &str, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty,
    }
}
fn eq(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(left),
        right: Box::new(right),
    }
}
const U8: TrustVcType = TrustVcType::Uint { width: 8 };
const I8: TrustVcType = TrustVcType::Int { width: 8 };
const I16: TrustVcType = TrustVcType::Int { width: 16 };
const U64: TrustVcType = TrustVcType::Uint { width: 64 };
fn seq(ty: TrustVcType) -> TrustVcType {
    TrustVcType::Seq(Box::new(ty))
}
fn set(ty: TrustVcType) -> TrustVcType {
    TrustVcType::Set(Box::new(ty))
}
fn map(key: TrustVcType, value: TrustVcType) -> TrustVcType {
    TrustVcType::Map(Box::new(key), Box::new(value))
}
fn cop(
    op: CollectionOp,
    receiver: TrustVcExpr,
    name: &str,
    args: Vec<TrustVcExpr>,
    ty: TrustVcType,
) -> TrustVcExpr {
    TrustVcExpr::CollectionOp {
        op,
        receiver: Box::new(receiver),
        receiver_name: Some(name.to_string()),
        args,
        ty,
    }
}
fn index_at(receiver: TrustVcExpr, name: &str, at: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Index {
        receiver: Box::new(receiver),
        index: Box::new(at),
        receiver_name: Some(name.to_string()),
        elem_ty: ty,
    }
}
fn first(receiver: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
    index_at(receiver, "s", lit(0, U64), ty)
}
fn closure(params: Vec<(&str, TrustVcType)>, ret: TrustVcType, body: TrustVcExpr) -> TrustVcExpr {
    let arg_tys = params.iter().map(|(_, ty)| ty.clone()).collect();
    TrustVcExpr::SpecClosure {
        params: params
            .into_iter()
            .map(|(name, ty)| (name.to_string(), ty))
            .collect(),
        body: Box::new(body),
        ty: TrustVcType::SpecFn(arg_tys, Box::new(ret)),
    }
}
fn identity(param: TrustVcType, ret: TrustVcType) -> TrustVcExpr {
    closure(vec![("x", param.clone())], ret, var("x", param))
}
fn s() -> TrustVcExpr {
    var("s", seq(U8))
}
fn m() -> TrustVcExpr {
    var("m", map(U8, U8))
}
fn st() -> TrustVcExpr {
    var("st", set(U8))
}

/// The pinned context the goal is read in.
fn context(vars: &[&str]) -> (Vec<VariableDecl>, Vec<TypedProofObligation>) {
    let mut decls = Vec::new();
    let mut requires = Vec::new();
    for name in vars {
        match *name {
            "s" => {
                decls.push(VariableDecl::new("s".to_string(), seq(U8)));
                requires.push(eq(
                    cop(CollectionOp::Len, s(), "s", vec![], U64),
                    lit(1, U64),
                ));
                requires.push(eq(first(s(), U8), lit(200, U8)));
            }
            "m" => {
                decls.push(VariableDecl::new("m".to_string(), map(U8, U8)));
                let key = lit(200, U8);
                requires.push(cop(
                    CollectionOp::ContainsKey,
                    m(),
                    "m",
                    vec![key.clone()],
                    TrustVcType::Bool,
                ));
                requires.push(eq(index_at(m(), "m", key, U8), lit(7, U8)));
            }
            "st" => {
                decls.push(VariableDecl::new("st".to_string(), set(U8)));
                requires.push(cop(
                    CollectionOp::Contains,
                    st(),
                    "st",
                    vec![lit(200, U8)],
                    TrustVcType::Bool,
                ));
            }
            other => unreachable!("{other}"),
        }
    }
    decls.push(VariableDecl::new("result".to_string(), TrustVcType::Bool));
    let requires = requires
        .into_iter()
        .enumerate()
        .map(|(k, expr)| TypedProofObligation::requires(format!("c_requires_{k}"), expr))
        .collect();
    (decls, requires)
}

fn verify(vars: &[&str], goal: TrustVcExpr, exec: bool) -> VerifyResult {
    let (decls, mut obligations) = context(vars);
    obligations.push(TypedProofObligation::ensures("c_goal", goal));
    let mut ctx = VerificationContext::from_typed_parts(decls, obligations);
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

enum Expect {
    /// A lying declaration: refused.
    Refused,
    /// The honest program.
    Verified,
    /// An honestly-false goal on the same context.
    Refuted,
}

struct Case {
    name: &'static str,
    vars: &'static [&'static str],
    goal: fn() -> TrustVcExpr,
    expect: Expect,
}

fn map_values(f: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
    cop(CollectionOp::SeqMapValues, s(), "s", vec![f], ty)
}
fn fold_left(ret: TrustVcType, ty: TrustVcType) -> TrustVcExpr {
    let f = closure(vec![("acc", U8), ("x", U8)], ret, var("x", U8));
    cop(CollectionOp::SeqFoldLeft, s(), "s", vec![lit(0, U8), f], ty)
}
fn ite_over_s(ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Ite {
        cond: Box::new(TrustVcExpr::BoolLit(true)),
        then_branch: Box::new(s()),
        else_branch: Box::new(s()),
        ty,
    }
}
fn let_over_s(ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Let {
        name: "v".to_string(),
        ty: ty.clone(),
        value: Box::new(s()),
        body: Box::new(eq(
            index_at(var("v", ty), "v", lit(0, U64), I8),
            lit(-56, I16),
        )),
    }
}
fn type_param() -> TrustVcType {
    TrustVcType::TypeParam("T".to_string())
}
fn contains(receiver: TrustVcExpr, needle: TrustVcExpr) -> TrustVcExpr {
    cop(
        CollectionOp::Contains,
        receiver,
        "s",
        vec![needle],
        TrustVcType::Bool,
    )
}

fn cases() -> Vec<Case> {
    vec![
        Case {
            name: "lie_to_set_declared_set_i8",
            vars: &["s"],
            goal: || {
                contains(
                    cop(CollectionOp::ToSet, s(), "s", vec![], set(I8)),
                    lit(-56, I8),
                )
            },
            expect: Expect::Refused,
        },
        Case {
            name: "same_to_set",
            vars: &["s"],
            goal: || {
                contains(
                    cop(CollectionOp::ToSet, s(), "s", vec![], set(U8)),
                    lit(200, U8),
                )
            },
            expect: Expect::Verified,
        },
        Case {
            name: "ctrl_to_set_holds_201",
            vars: &["s"],
            goal: || {
                contains(
                    cop(CollectionOp::ToSet, s(), "s", vec![], set(U8)),
                    lit(201, U8),
                )
            },
            expect: Expect::Refuted,
        },
        Case {
            name: "lie_to_multiset_declared_multiset_i8",
            vars: &["s"],
            goal: || {
                let ms = TrustVcType::Multiset(Box::new(I8));
                let bag = cop(CollectionOp::ToMultiset, s(), "s", vec![], ms);
                let count = cop(
                    CollectionOp::Count,
                    bag,
                    "s",
                    vec![lit(-56, I8)],
                    TrustVcType::Nat,
                );
                eq(count, lit(1, TrustVcType::Nat))
            },
            expect: Expect::Refused,
        },
        Case {
            name: "lie_dom_declared_set_i8",
            vars: &["m"],
            goal: || {
                let dom = cop(CollectionOp::Dom, m(), "m", vec![], set(I8));
                cop(
                    CollectionOp::Contains,
                    dom,
                    "m",
                    vec![lit(-56, I8)],
                    TrustVcType::Bool,
                )
            },
            expect: Expect::Refused,
        },
        Case {
            name: "lie_view_declared_seq_i8",
            vars: &["s"],
            goal: || {
                eq(
                    first(cop(CollectionOp::View, s(), "s", vec![], seq(I8)), I8),
                    lit(-56, I16),
                )
            },
            expect: Expect::Refused,
        },
        Case {
            name: "same_view",
            vars: &["s"],
            goal: || {
                eq(
                    first(cop(CollectionOp::View, s(), "s", vec![], seq(U8)), U8),
                    lit(200, I16),
                )
            },
            expect: Expect::Verified,
        },
        Case {
            name: "lie_map_values_result_seq_i8",
            vars: &["s"],
            goal: || {
                eq(
                    first(map_values(identity(U8, U8), seq(I8)), I8),
                    lit(-56, I16),
                )
            },
            expect: Expect::Refused,
        },
        Case {
            name: "lie_map_values_closure_returns_i8",
            vars: &["s"],
            goal: || {
                eq(
                    first(map_values(identity(U8, I8), seq(I8)), I8),
                    lit(-56, I16),
                )
            },
            expect: Expect::Refused,
        },
        Case {
            name: "same_map_values",
            vars: &["s"],
            goal: || {
                eq(
                    first(map_values(identity(U8, U8), seq(U8)), U8),
                    lit(200, I16),
                )
            },
            expect: Expect::Verified,
        },
        Case {
            name: "ctrl_map_values_is_neg56",
            vars: &["s"],
            goal: || {
                eq(
                    first(map_values(identity(U8, U8), seq(U8)), U8),
                    lit(-56, I16),
                )
            },
            expect: Expect::Refuted,
        },
        Case {
            name: "lie_fold_left_declared_i8",
            vars: &["s"],
            goal: || eq(fold_left(U8, I8), lit(-56, I16)),
            expect: Expect::Refused,
        },
        Case {
            name: "same_fold_left",
            vars: &["s"],
            goal: || eq(fold_left(U8, U8), lit(200, I16)),
            expect: Expect::Verified,
        },
        Case {
            name: "lie_set_map_declared_set_i8",
            vars: &["st"],
            goal: || {
                let mapped = cop(
                    CollectionOp::SetMap,
                    st(),
                    "st",
                    vec![identity(U8, U8)],
                    set(I8),
                );
                cop(
                    CollectionOp::Contains,
                    mapped,
                    "st",
                    vec![lit(-56, I8)],
                    TrustVcType::Bool,
                )
            },
            expect: Expect::Refused,
        },
        Case {
            name: "lie_map_map_values_declared_map_u8_i8",
            vars: &["m"],
            goal: || {
                let mapped = cop(
                    CollectionOp::MapMapValues,
                    m(),
                    "m",
                    vec![identity(U8, U8)],
                    map(U8, I8),
                );
                eq(index_at(mapped, "m", lit(200, U8), I8), lit(7, I16))
            },
            expect: Expect::Refused,
        },
        Case {
            name: "lie_ite_at_type_parameter_forgets_u8",
            vars: &["s"],
            goal: || eq(first(ite_over_s(type_param()), I8), lit(-56, I16)),
            expect: Expect::Refused,
        },
        Case {
            name: "ctrl_ite_at_seq_u8_is_neg56",
            vars: &["s"],
            goal: || eq(first(ite_over_s(seq(U8)), U8), lit(-56, I16)),
            expect: Expect::Refuted,
        },
        Case {
            name: "lie_let_at_type_parameter_forgets_u8",
            vars: &["s"],
            goal: || let_over_s(type_param()),
            expect: Expect::Refused,
        },
        Case {
            name: "lie_let_at_opaque_forgets_u8",
            vars: &["s"],
            goal: || let_over_s(TrustVcType::Opaque("X".to_string())),
            expect: Expect::Refused,
        },
        Case {
            name: "lie_match_at_poly_forgets_u8",
            vars: &["s"],
            goal: || {
                let joined = TrustVcExpr::Match {
                    scrutinee: Box::new(s()),
                    arms: vec![MatchArm::new(
                        MatchPattern::Ident("g".to_string()),
                        var("g", seq(U8)),
                    )],
                    ty: TrustVcType::Poly,
                };
                eq(first(joined, I8), lit(-56, I16))
            },
            expect: Expect::Refused,
        },
        Case {
            name: "lie_map_key_i8_reads_key_200",
            vars: &["m"],
            goal: || eq(index_at(m(), "m", lit(-56, I8), U8), lit(7, U8)),
            expect: Expect::Refused,
        },
        Case {
            name: "same_map_key_u8",
            vars: &["m"],
            goal: || eq(index_at(m(), "m", lit(200, U8), U8), lit(7, U8)),
            expect: Expect::Verified,
        },
    ]
}

fn judge(name: &str, got: &VerifyResult, expect: &Expect, wrong: &mut Vec<String>) {
    let ok = match expect {
        Expect::Refused => class(got) == "Unknown",
        Expect::Verified => matches!(got, VerifyResult::Verified),
        Expect::Refuted => class(got) == "Refuted",
    };
    if !ok {
        let raw: String = format!("{got:?}").chars().take(240).collect();
        wrong.push(format!("{name}: {} ({raw})", class(got)));
    }
}

/// Every collection result, closure return, join type and map key the
/// encoder reads is the one its operands derive (spec and exec lanes).
#[test]
fn every_seam_claim_is_derived() {
    let mut wrong = Vec::new();
    for case in cases() {
        for exec in [false, true] {
            let got = verify(case.vars, (case.goal)(), exec);
            println!("DERIVED|{}|exec={exec}|{}", case.name, class(&got));
            judge(
                &format!("{} exec={exec}", case.name),
                &got,
                &case.expect,
                &mut wrong,
            );
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}
