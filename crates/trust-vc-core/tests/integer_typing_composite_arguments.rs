//! A COMPOSITE key / element / value argument is bound at the collection's
//! key / element type (design-trust-proof-backend.md §5b rule 10:
//! "element, key and value arguments are bound at the collection's element
//! type"; rule 13: "a map key is bound at the key type"). A `Seq<i8>` key of
//! a `Map<Seq<u8>, u8>` (the `m[t]` index, `contains_key`), a `Seq<i8>`
//! needle of a `Set<Seq<u8>>`, and a `Seq<i8>` pushed onto a
//! `Seq<Seq<u8>>` must not be read as the `Seq<u8>` with the same bits
//! (with `t == [-56]` and `s == [200]`, `m[t] == m[s]`). Each `lie_*` is
//! ill-typed (Rust and Verus reject it) and must be refused like the
//! integer-key twin `m[-56i8]` is. A guard: it passes before and after the
//! rule-11 composite-argument check.

use trust_vc_core::ir::{CollectionOp, CompareOp, TrustVcExpr, TrustVcType};
use trust_vc_core::vc::{TypedProofObligation, VariableDecl, VerificationContext};
use trust_vc_core::VerifyResult;

const U8: TrustVcType = TrustVcType::Uint { width: 8 };
const I8: TrustVcType = TrustVcType::Int { width: 8 };
const U64: TrustVcType = TrustVcType::Uint { width: 64 };

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
fn seq(ty: TrustVcType) -> TrustVcType {
    TrustVcType::Seq(Box::new(ty))
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
fn index(receiver: TrustVcExpr, name: &str, at: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Index {
        receiver: Box::new(receiver),
        index: Box::new(at),
        receiver_name: Some(name.to_string()),
        elem_ty: ty,
    }
}
fn map_ty() -> TrustVcType {
    TrustVcType::Map(Box::new(seq(U8)), Box::new(U8))
}
fn set_ty() -> TrustVcType {
    TrustVcType::Set(Box::new(seq(U8)))
}
fn s() -> TrustVcExpr {
    var("s", seq(U8))
}
fn t() -> TrustVcExpr {
    var("t", seq(I8))
}
fn m() -> TrustVcExpr {
    var("m", map_ty())
}
fn st() -> TrustVcExpr {
    var("st", set_ty())
}

fn verify(goal: TrustVcExpr, exec: bool) -> VerifyResult {
    let decls = vec![
        VariableDecl::new("s".to_string(), seq(U8)),
        VariableDecl::new("t".to_string(), seq(I8)),
        VariableDecl::new("m".to_string(), map_ty()),
        VariableDecl::new("st".to_string(), set_ty()),
        VariableDecl::new("ss".to_string(), seq(seq(U8))),
        VariableDecl::new("result".to_string(), TrustVcType::Bool),
    ];
    let requires = vec![
        eq(cop(CollectionOp::Len, s(), "s", vec![], U64), lit(1, U64)),
        eq(index(s(), "s", lit(0, U64), U8), lit(200, U8)),
        eq(cop(CollectionOp::Len, t(), "t", vec![], U64), lit(1, U64)),
        eq(
            index(t(), "t", lit(0, U64), I8),
            TrustVcExpr::Neg(Box::new(lit(56, I8))),
        ),
        cop(
            CollectionOp::ContainsKey,
            m(),
            "m",
            vec![s()],
            TrustVcType::Bool,
        ),
        eq(index(m(), "m", s(), U8), lit(7, U8)),
        cop(
            CollectionOp::Contains,
            st(),
            "st",
            vec![s()],
            TrustVcType::Bool,
        ),
    ];
    let mut obligations: Vec<TypedProofObligation> = requires
        .into_iter()
        .enumerate()
        .map(|(k, expr)| TypedProofObligation::requires(format!("c_requires_{k}"), expr))
        .collect();
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

#[test]
fn a_composite_argument_is_bound_at_its_element_type() {
    let cases: Vec<(&str, TrustVcExpr)> = vec![
        (
            "lie_map_index_seq_i8_key",
            eq(index(m(), "m", t(), U8), lit(7, U8)),
        ),
        (
            "lie_map_contains_key_seq_i8",
            cop(
                CollectionOp::ContainsKey,
                m(),
                "m",
                vec![t()],
                TrustVcType::Bool,
            ),
        ),
        (
            "lie_set_contains_seq_i8",
            cop(
                CollectionOp::Contains,
                st(),
                "st",
                vec![t()],
                TrustVcType::Bool,
            ),
        ),
        ("lie_push_seq_i8_onto_seq_seq_u8_reads_200", {
            let ss = var("ss", seq(seq(U8)));
            let pushed = cop(CollectionOp::Push, ss, "ss", vec![t()], seq(seq(U8)));
            let last = cop(CollectionOp::Last, pushed, "ss", vec![], seq(U8));
            eq(index(last, "ss", lit(0, U64), U8), lit(200, U8))
        }),
        (
            "same_map_index_seq_u8_key",
            eq(index(m(), "m", s(), U8), lit(7, U8)),
        ),
        (
            "ctrl_map_index_is_8",
            eq(index(m(), "m", s(), U8), lit(8, U8)),
        ),
    ];
    let mut wrong = Vec::new();
    for (name, goal) in cases {
        for exec in [false, true] {
            let got = verify(goal.clone(), exec);
            println!("COMPARG|{name}|exec={exec}|{}", class(&got));
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
