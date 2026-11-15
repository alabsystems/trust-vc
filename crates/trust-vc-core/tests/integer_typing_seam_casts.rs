//! Typed-seam claims the IR typing validator (§5b rule 13) derives. Every
//! `lie_*` below was `Verified` in the spec and the exec lane before the
//! checks it pins.
//!
//! * A CAST's `from_ty` is its operand's own type, whatever that type is
//!   (`typing_check::claims::cast_operand_agrees`); only integer `from_ty`s
//!   were compared. With `s: Seq<u8>`, `s[0] == 200`, the identity cast `s as
//!   Seq<i8>` (`from_ty: Seq<i8>`) re-read the element as -56, and
//!   `(cast)[0] as int != s[0] as int` was `Verified`, a contradiction; a
//!   `Set<u8>` so cast contained -56; with `y: i8 == -56`, `Cast { y,
//!   from_ty: char, to_ty: u32 } == 200` was `Verified` beside the honest `y
//!   as u32 == 4294967240` (their `!=` too); and the identity cast `x_u8 as
//!   T` (`T` a type parameter) compared equal to `-56i8` for `x == 200`.
//! * `subset_of` / `superset_of` between collections of DIFFERENT element
//!   types is refused like `==` is: `st: Set<u8> ∋ 200`, `st ⊆ t: Set<i8>`
//!   made `t.contains(-56i8)` `Verified` — the carrier bits compared.
//! * The same `from_ty` lie reached a `take` COUNT (§5b rule 10 reads a count
//!   by its own sign, and the cast's declared `char` is that sign): with `y:
//!   i8 == -56` and `s.len() == 300`, `s.take(y as char as char).len() ==
//!   200` was `Verified` (the count -56 is out of the domain).
//!
//! Each `same_*` is the honest twin (`Verified`), each `ctrl_*` an
//! honestly-false goal on the same context (refuted: not vacuous).

use trust_vc_core::ir::{CollectionOp, CompareOp, TrustVcExpr, TrustVcType};
use trust_vc_core::vc::{TypedProofObligation, VariableDecl, VerificationContext};
use trust_vc_core::VerifyResult;

const U8: TrustVcType = TrustVcType::Uint { width: 8 };
const I8: TrustVcType = TrustVcType::Int { width: 8 };
const I16: TrustVcType = TrustVcType::Int { width: 16 };
const U32: TrustVcType = TrustVcType::Uint { width: 32 };
const U64: TrustVcType = TrustVcType::Uint { width: 64 };
const INT: TrustVcType = TrustVcType::MathInt;

fn lit(value: i128, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::IntLit { value, ty }
}
fn neg(magnitude: i128, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Neg(Box::new(lit(magnitude, ty)))
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
fn eq(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    cmp(CompareOp::Eq, left, right)
}
fn seq(ty: TrustVcType) -> TrustVcType {
    TrustVcType::Seq(Box::new(ty))
}
fn set(ty: TrustVcType) -> TrustVcType {
    TrustVcType::Set(Box::new(ty))
}
fn tparam() -> TrustVcType {
    TrustVcType::TypeParam("T".to_string())
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
fn first(receiver: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Index {
        receiver: Box::new(receiver),
        index: Box::new(lit(0, U64)),
        receiver_name: Some("s".to_string()),
        elem_ty: ty,
    }
}
fn cast(expr: TrustVcExpr, from: TrustVcType, to: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Cast {
        expr: Box::new(expr),
        from_ty: from,
        to_ty: to,
    }
}
fn s() -> TrustVcExpr {
    var("s", seq(U8))
}
fn take_len(count: TrustVcExpr) -> TrustVcExpr {
    let taken = cop(
        CollectionOp::Take,
        var("s300", seq(U8)),
        "s300",
        vec![count],
        seq(U8),
    );
    cop(CollectionOp::Len, taken, "s300", vec![], U64)
}
fn contains(receiver: TrustVcExpr, name: &str, needle: TrustVcExpr) -> TrustVcExpr {
    cop(
        CollectionOp::Contains,
        receiver,
        name,
        vec![needle],
        TrustVcType::Bool,
    )
}

fn verify(vars: &[&str], extra: Vec<TrustVcExpr>, goal: TrustVcExpr, exec: bool) -> VerifyResult {
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
            "x" => {
                decls.push(VariableDecl::new("x".to_string(), U8));
                requires.push(eq(var("x", U8), lit(200, U8)));
            }
            "y" => {
                decls.push(VariableDecl::new("y".to_string(), I8));
                requires.push(eq(var("y", I8), neg(56, I8)));
            }
            "st" => {
                decls.push(VariableDecl::new("st".to_string(), set(U8)));
                requires.push(contains(var("st", set(U8)), "st", lit(200, U8)));
            }
            "t" => decls.push(VariableDecl::new("t".to_string(), set(I8))),
            "s300" => {
                decls.push(VariableDecl::new("s300".to_string(), seq(U8)));
                requires.push(eq(
                    cop(CollectionOp::Len, var("s300", seq(U8)), "s300", vec![], U64),
                    lit(300, U64),
                ));
            }
            other => unreachable!("{other}"),
        }
    }
    requires.extend(extra);
    decls.push(VariableDecl::new("result".to_string(), TrustVcType::Bool));
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

fn subset(
    op: CollectionOp,
    receiver: (&str, TrustVcType),
    other: (&str, TrustVcType),
) -> Vec<TrustVcExpr> {
    vec![cop(
        op,
        var(receiver.0, receiver.1),
        receiver.0,
        vec![var(other.0, other.1)],
        TrustVcType::Bool,
    )]
}

#[allow(clippy::type_complexity)]
fn cases() -> Vec<(
    &'static str,
    &'static [&'static str],
    Vec<TrustVcExpr>,
    TrustVcExpr,
)> {
    let cast_seq_i8 = || cast(s(), seq(I8), seq(I8));
    vec![
        (
            "lie_cast_seq_u8_declared_from_seq_i8",
            &["s"],
            vec![],
            eq(first(cast_seq_i8(), I8), lit(-56, I16)),
        ),
        (
            "lie_cast_seq_read_differs_from_honest_read",
            &["s"],
            vec![],
            cmp(
                CompareOp::Ne,
                cast(first(cast_seq_i8(), I8), I8, INT),
                cast(first(s(), U8), U8, INT),
            ),
        ),
        (
            "same_cast_seq_u8_identity",
            &["s"],
            vec![],
            eq(first(cast(s(), seq(U8), seq(U8)), U8), lit(200, I16)),
        ),
        (
            "ctrl_s0_is_201",
            &["s"],
            vec![],
            eq(first(s(), U8), lit(201, I16)),
        ),
        (
            "lie_cast_set_u8_declared_from_set_i8",
            &["st"],
            vec![],
            contains(
                cast(var("st", set(U8)), set(I8), set(I8)),
                "st",
                neg(56, I8),
            ),
        ),
        (
            "lie_cast_i8_declared_from_char_to_u32",
            &["y"],
            vec![],
            eq(cast(var("y", I8), TrustVcType::Char, U32), lit(200, U32)),
        ),
        (
            "lie_cast_i8_from_char_differs_from_honest",
            &["y"],
            vec![],
            cmp(
                CompareOp::Ne,
                cast(var("y", I8), TrustVcType::Char, U32),
                cast(var("y", I8), I8, U32),
            ),
        ),
        (
            "same_cast_i8_to_u32",
            &["y"],
            vec![],
            eq(cast(var("y", I8), I8, U32), lit(4_294_967_240, U32)),
        ),
        (
            "ctrl_y_is_neg55",
            &["y"],
            vec![],
            eq(var("y", I8), neg(55, I8)),
        ),
        (
            "lie_cast_u8_identity_type_param_eq_neg56",
            &["x"],
            vec![],
            eq(cast(var("x", U8), tparam(), tparam()), neg(56, I8)),
        ),
        (
            // Decided by the constant evaluator before any validation (oracle,
            // seed 7): a ground goal is validated before it is folded.
            "lie_cast_u32_literal_declared_from_char",
            &[],
            vec![],
            cmp(
                CompareOp::Ne,
                cast(lit(3_132_225_413, U32), TrustVcType::Char, U64),
                neg(12, TrustVcType::Int { width: 32 }),
            ),
        ),
        (
            "lie_take_count_i8_declared_from_char",
            &["s300", "y"],
            vec![],
            eq(
                take_len(cast(var("y", I8), TrustVcType::Char, TrustVcType::Char)),
                lit(200, U64),
            ),
        ),
        (
            "same_take_count_200",
            &["s300"],
            vec![],
            eq(take_len(lit(200, U64)), lit(200, U64)),
        ),
        (
            "lie_subset_set_u8_of_set_i8",
            &["st", "t"],
            subset(CollectionOp::Subset, ("st", set(U8)), ("t", set(I8))),
            contains(var("t", set(I8)), "t", neg(56, I8)),
        ),
        (
            "lie_superset_set_i8_of_set_u8",
            &["st", "t"],
            subset(CollectionOp::Superset, ("t", set(I8)), ("st", set(U8))),
            contains(var("t", set(I8)), "t", neg(56, I8)),
        ),
        (
            "ctrl_t_contains_neg56_without_subset",
            &["st", "t"],
            vec![],
            contains(var("t", set(I8)), "t", neg(56, I8)),
        ),
    ]
}

#[test]
fn a_cast_and_a_subset_are_derived() {
    let mut wrong = Vec::new();
    for (name, vars, extra, goal) in cases() {
        for exec in [false, true] {
            let got = verify(vars, extra.clone(), goal.clone(), exec);
            println!("SEAMCAST|{name}|exec={exec}|{}", class(&got));
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
