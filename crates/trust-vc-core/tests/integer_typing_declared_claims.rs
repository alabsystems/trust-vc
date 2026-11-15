//! The typed seam's DECLARED types are claims the one IR typing validator
//! re-derives, bottom-up, at every depth (design-trust-proof-backend.md §5b
//! rule 13, `ir_lowering::validate_ir_typing`).
//!
//! Measured before (r9 re-verifier, at 50b27076 and 3319adfa alike): the
//! element-read check compared the read with its RECEIVER's declared type,
//! and trusted that receiver. With `s: Seq<u8>`, `s.len() == 1`, `s[0] ==
//! 200`, reading the element at `i8` through a `take`, `push`, `subrange` or
//! `reverse` declared `Seq<i8>`, a `let` or a conditional at `Seq<i8>`, or a
//! map `insert` declared `Map<u8, i8>` gave -56: `== -56` `Verified`, the
//! true `== 200` refuted, spec and exec (14 + 14). A literal DECLARED at a
//! type that cannot hold it was read at that type: `IntLit { -1, nat } < 0`,
//! `let v: nat = IntLit { -1, nat }; v < 0` and `IntLit { -1, u8 } == 255u8`
//! were `Verified`.
//!
//! The `by(compute)` evaluator reads the IR too: it decided `x_u8 + 0u8`
//! DECLARED `i8` (refuted `== -56`) — a lie it now leaves undecided.
//!
//! Every `lie_*` case carries a disagreeing claim and must be REFUSED
//! (`Unknown`); every `same_*` twin states the same program with honest
//! claims and must be decided correctly.

use trust_vc_core::ir::{
    ArithOp, CollectionOp, CompareOp, MatchArm, MatchPattern, SpecialArithOp, TrustVcExpr,
    TrustVcType,
};
use trust_vc_core::vc::{SolverMode, TypedProofObligation, VariableDecl, VerificationContext};
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
fn compare(op: CompareOp, l: TrustVcExpr, r: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op,
        left: Box::new(l),
        right: Box::new(r),
    }
}
fn eq(l: TrustVcExpr, r: TrustVcExpr) -> TrustVcExpr {
    compare(CompareOp::Eq, l, r)
}
fn u(width: u32) -> TrustVcType {
    TrustVcType::Uint { width }
}
fn i(width: u32) -> TrustVcType {
    TrustVcType::Int { width }
}
fn seq(t: TrustVcType) -> TrustVcType {
    TrustVcType::Seq(Box::new(t))
}
fn cop(
    op: CollectionOp,
    recv: TrustVcExpr,
    args: Vec<TrustVcExpr>,
    ty: TrustVcType,
) -> TrustVcExpr {
    TrustVcExpr::CollectionOp {
        op,
        receiver: Box::new(recv),
        receiver_name: Some("s".to_string()),
        args,
        ty,
    }
}
fn index(recv: TrustVcExpr, elem_ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Index {
        receiver: Box::new(recv),
        index: Box::new(lit(0, u(64))),
        receiver_name: Some("s".to_string()),
        elem_ty,
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Want {
    /// A disagreeing claim: refused.
    Refused,
    Verified,
    Refuted,
}

struct Case {
    name: String,
    vars: Vec<(&'static str, TrustVcType)>,
    requires: Vec<TrustVcExpr>,
    goal: TrustVcExpr,
    exec: bool,
    /// Decided by `by(compute)` (the IR evaluator), not the solver.
    compute: bool,
    want: Want,
}

fn run(c: &Case) -> VerifyResult {
    let mut variables: Vec<VariableDecl> = c
        .vars
        .iter()
        .map(|(n, t)| VariableDecl::new((*n).to_string(), t.clone()))
        .collect();
    variables.push(VariableDecl::new("result".to_string(), TrustVcType::Bool));
    let mut obligations: Vec<TypedProofObligation> = c
        .requires
        .iter()
        .enumerate()
        .map(|(k, r)| TypedProofObligation::requires(format!("c_requires_{k}"), r.clone()))
        .collect();
    obligations.push(if c.compute {
        TypedProofObligation::assert("c_goal", c.goal.clone()).with_solver_mode(SolverMode::Compute)
    } else {
        TypedProofObligation::ensures("c_goal", c.goal.clone())
    });
    let mut ctx = VerificationContext::from_typed_parts(variables, obligations);
    if c.exec {
        ctx.enable_overflow_checks();
    }
    ctx.verify()
}

fn cases() -> Vec<Case> {
    let s = || var("s", seq(u(8)));
    let s_pin = || {
        vec![
            eq(cop(CollectionOp::Len, s(), vec![], u(64)), lit(1, u(64))),
            eq(index(s(), u(8)), lit(200, u(8))),
        ]
    };
    let x = || var("x", u(8));
    let mut cs = Vec::new();
    for exec in [false, true] {
        let tag = if exec { "exec" } else { "spec" };
        // An element read through a receiver declaring `Seq<claim>`: with
        // the honest `u8` claim the element is 200; with `i8` it is refused.
        type Receiver = Box<dyn Fn(TrustVcExpr, TrustVcType) -> TrustVcExpr>;
        let receivers: Vec<(&str, Receiver)> = vec![
            (
                "take",
                Box::new(|s, t| {
                    cop(
                        CollectionOp::Take,
                        s,
                        vec![lit(1, TrustVcType::MathInt)],
                        seq(t),
                    )
                }),
            ),
            (
                "push",
                Box::new(|s, t| cop(CollectionOp::Push, s, vec![lit(7, u(8))], seq(t))),
            ),
            (
                "subrange",
                Box::new(|s, t| {
                    cop(
                        CollectionOp::Subrange,
                        s,
                        vec![lit(0, TrustVcType::MathInt), lit(1, TrustVcType::MathInt)],
                        seq(t),
                    )
                }),
            ),
            (
                "reverse",
                Box::new(|s, t| cop(CollectionOp::Reverse, s, vec![], seq(t))),
            ),
            (
                "let",
                Box::new(|s, t: TrustVcType| TrustVcExpr::Let {
                    name: "v".to_string(),
                    ty: seq(t.clone()),
                    value: Box::new(s),
                    body: Box::new(var("v", seq(t))),
                }),
            ),
            (
                "ite",
                Box::new(|s: TrustVcExpr, t| TrustVcExpr::Ite {
                    cond: Box::new(TrustVcExpr::BoolLit(true)),
                    then_branch: Box::new(s.clone()),
                    else_branch: Box::new(s),
                    ty: seq(t),
                }),
            ),
            (
                "take_then_reverse",
                Box::new(|s, t| {
                    let inner = cop(
                        CollectionOp::Take,
                        s,
                        vec![lit(1, TrustVcType::MathInt)],
                        seq(u(8)),
                    );
                    cop(CollectionOp::Reverse, inner, vec![], seq(t))
                }),
            ),
        ];
        for (name, receiver) in &receivers {
            for (rhs, want) in [(-56, Want::Refused), (200, Want::Refused)] {
                cs.push(Case {
                    name: format!("lie_{tag}_{name}_seq_i8_read_i8_{rhs}"),
                    vars: vec![("s", seq(u(8)))],
                    requires: s_pin(),
                    goal: eq(index(receiver(s(), i(8)), i(8)), lit(rhs, i(16))),
                    exec,
                    compute: false,
                    want,
                });
            }
            for (rhs, want) in [(200, Want::Verified), (-56, Want::Refuted)] {
                cs.push(Case {
                    name: format!("same_{tag}_{name}_seq_u8_read_u8_{rhs}"),
                    vars: vec![("s", seq(u(8)))],
                    requires: s_pin(),
                    goal: eq(index(receiver(s(), u(8)), u(8)), lit(rhs, i(16))),
                    exec,
                    compute: false,
                    want,
                });
            }
        }
        // A map `insert` declared `Map<u8, i8>`, then `get` at `i8`.
        let map_u = TrustVcType::Map(Box::new(u(8)), Box::new(u(8)));
        let map_i = TrustVcType::Map(Box::new(u(8)), Box::new(i(8)));
        let insert = |ty: TrustVcType| TrustVcExpr::CollectionOp {
            op: CollectionOp::Insert,
            receiver: Box::new(var("m", map_u.clone())),
            receiver_name: Some("m".to_string()),
            args: vec![lit(0, u(8)), lit(200, u(8))],
            ty,
        };
        let get = |map: TrustVcExpr, ty: TrustVcType| TrustVcExpr::CollectionOp {
            op: CollectionOp::Get,
            receiver: Box::new(map),
            receiver_name: Some("m".to_string()),
            args: vec![lit(0, u(8))],
            ty,
        };
        cs.push(Case {
            name: format!("lie_{tag}_map_insert_map_u8_i8_get_i8"),
            vars: vec![("m", map_u.clone())],
            requires: vec![],
            goal: eq(get(insert(map_i.clone()), i(8)), lit(-56, i(16))),
            exec,
            compute: false,
            want: Want::Refused,
        });
        cs.push(Case {
            name: format!("same_{tag}_map_insert_get_u8"),
            vars: vec![("m", map_u.clone())],
            requires: vec![],
            goal: eq(get(insert(map_u.clone()), u(8)), lit(200, i(16))),
            exec,
            compute: false,
            want: Want::Verified,
        });
        // A `match` binder at another composite type than its scrutinee.
        cs.push(Case {
            name: format!("lie_{tag}_match_binder_seq_i8"),
            vars: vec![("s", seq(u(8)))],
            requires: s_pin(),
            goal: eq(
                index(
                    TrustVcExpr::Match {
                        scrutinee: Box::new(s()),
                        arms: vec![MatchArm::new(
                            MatchPattern::Ident("g".to_string()),
                            var("g", seq(i(8))),
                        )],
                        ty: seq(i(8)),
                    },
                    i(8),
                ),
                lit(-56, i(16)),
            ),
            exec,
            compute: false,
            want: Want::Refused,
        });
        // Scalar joins and bindings declared `i8` over `u8` operands.
        let x_pin = || vec![eq(x(), lit(200, u(8)))];
        let scalar: Vec<(&str, TrustVcExpr)> = vec![
            (
                "ite",
                TrustVcExpr::Ite {
                    cond: Box::new(TrustVcExpr::BoolLit(true)),
                    then_branch: Box::new(x()),
                    else_branch: Box::new(x()),
                    ty: i(8),
                },
            ),
            (
                "match",
                TrustVcExpr::Match {
                    scrutinee: Box::new(x()),
                    arms: vec![MatchArm::new(MatchPattern::Wildcard, x())],
                    ty: i(8),
                },
            ),
            (
                "bitand",
                TrustVcExpr::SpecialArith {
                    op: SpecialArithOp::BitAnd,
                    left: Box::new(x()),
                    right: Box::new(x()),
                    ty: i(8),
                },
            ),
            (
                "add",
                TrustVcExpr::Arith {
                    op: ArithOp::Add,
                    left: Box::new(x()),
                    right: Box::new(lit(0, u(8))),
                    ty: i(8),
                },
            ),
            (
                "let",
                TrustVcExpr::Let {
                    name: "v".to_string(),
                    ty: i(8),
                    value: Box::new(x()),
                    body: Box::new(var("v", i(8))),
                },
            ),
        ];
        for (name, tree) in scalar {
            cs.push(Case {
                name: format!("lie_{tag}_{name}_declared_i8_over_u8"),
                vars: vec![("x", u(8))],
                requires: x_pin(),
                goal: eq(tree, lit(200, i(16))),
                exec,
                compute: false,
                want: Want::Refused,
            });
        }
        // Literals declared at a type that cannot hold them.
        let nat = TrustVcType::Nat;
        let int = TrustVcType::MathInt;
        let literal: Vec<(&str, TrustVcExpr)> = vec![
            (
                "nat_neg1_lt_0",
                compare(CompareOp::Lt, lit(-1, nat.clone()), lit(0, int.clone())),
            ),
            (
                "let_nat_of_nat_neg1_lt_0",
                TrustVcExpr::Let {
                    name: "v".to_string(),
                    ty: nat.clone(),
                    value: Box::new(lit(-1, nat.clone())),
                    body: Box::new(compare(
                        CompareOp::Lt,
                        var("v", nat.clone()),
                        lit(0, int.clone()),
                    )),
                },
            ),
            ("u8_neg1_eq_255", eq(lit(-1, u(8)), lit(255, u(8)))),
            ("u8_300_eq_44", eq(lit(300, u(8)), lit(44, u(8)))),
            ("i8_200_eq_neg56", eq(lit(200, i(8)), lit(-56, i(8)))),
        ];
        for (name, goal) in literal {
            cs.push(Case {
                name: format!("lie_{tag}_literal_{name}"),
                vars: vec![],
                requires: vec![],
                goal,
                exec,
                compute: false,
                want: Want::Refused,
            });
        }
        // `-128i8` is a negated magnitude, not a lie.
        cs.push(Case {
            name: format!("same_{tag}_literal_neg128_i8"),
            vars: vec![],
            requires: vec![],
            goal: eq(TrustVcExpr::Neg(Box::new(lit(128, i(8)))), lit(-128, i(16))),
            exec,
            compute: false,
            want: Want::Verified,
        });
    }
    // A `nat` difference declared `nat` (it is an `int`).
    let n = || var("n", TrustVcType::Nat);
    let mm = || var("mm", TrustVcType::Nat);
    let sub = |ty| TrustVcExpr::Arith {
        op: ArithOp::Sub,
        left: Box::new(n()),
        right: Box::new(mm()),
        ty,
    };
    let pins = vec![
        eq(n(), lit(0, TrustVcType::Nat)),
        eq(mm(), lit(1, TrustVcType::Nat)),
    ];
    cs.push(Case {
        name: "lie_spec_nat_sub_declared_nat_ge_0".to_string(),
        vars: vec![("n", TrustVcType::Nat), ("mm", TrustVcType::Nat)],
        requires: pins.clone(),
        goal: compare(
            CompareOp::Ge,
            sub(TrustVcType::Nat),
            lit(0, TrustVcType::MathInt),
        ),
        exec: false,
        compute: false,
        want: Want::Refused,
    });
    cs.push(Case {
        name: "same_spec_nat_sub_declared_int_eq_neg1".to_string(),
        vars: vec![("n", TrustVcType::Nat), ("mm", TrustVcType::Nat)],
        requires: pins,
        goal: eq(sub(TrustVcType::MathInt), lit(-1, TrustVcType::MathInt)),
        exec: false,
        compute: false,
        want: Want::Verified,
    });
    // `by(compute)` evaluates the IR itself: a lie is refused there too.
    let x = || var("x", u(8));
    let compute: Vec<(&str, Vec<TrustVcExpr>, TrustVcExpr, Want)> = vec![
        (
            "lie_compute_literal_nat_neg1_lt_0",
            vec![],
            compare(
                CompareOp::Lt,
                lit(-1, TrustVcType::Nat),
                lit(0, TrustVcType::MathInt),
            ),
            Want::Refused,
        ),
        (
            "lie_compute_literal_u8_neg1_eq_255",
            vec![],
            eq(lit(-1, u(8)), lit(255, u(8))),
            Want::Refused,
        ),
        (
            "lie_compute_add_declared_i8_over_u8",
            vec![eq(x(), lit(200, u(8)))],
            eq(
                TrustVcExpr::Arith {
                    op: ArithOp::Add,
                    left: Box::new(x()),
                    right: Box::new(lit(0, u(8))),
                    ty: i(8),
                },
                lit(-56, i(16)),
            ),
            Want::Refused,
        ),
        (
            "same_compute_add_u8",
            vec![eq(x(), lit(200, u(8)))],
            eq(
                TrustVcExpr::Arith {
                    op: ArithOp::Add,
                    left: Box::new(x()),
                    right: Box::new(lit(0, u(8))),
                    ty: u(8),
                },
                lit(200, i(16)),
            ),
            Want::Verified,
        ),
    ];
    for (name, requires, goal, want) in compute {
        cs.push(Case {
            name: name.to_string(),
            vars: vec![("x", u(8))],
            requires,
            goal,
            exec: false,
            compute: true,
            want,
        });
    }
    cs
}

#[test]
fn every_declared_claim_is_derived_before_it_is_read() {
    let mut wrong = Vec::new();
    for c in cases() {
        let got = run(&c);
        let class = match &got {
            VerifyResult::Verified => Want::Verified,
            VerifyResult::Counterexample { .. } | VerifyResult::NotProved { .. } => Want::Refuted,
            _ => Want::Refused,
        };
        let raw: String = format!("{got:?}")
            .replace('\n', " ")
            .chars()
            .take(200)
            .collect();
        println!("CLAIM|{}|{class:?}|{raw}", c.name);
        // A refused (`Unknown`) honest case is incompleteness, not a wrong
        // verdict; every other disagreement is.
        let ok = class == c.want || (class == Want::Refused && c.want != Want::Refused);
        if !ok {
            wrong.push(format!("{}: want {:?}, got {class:?}", c.name, c.want));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}
