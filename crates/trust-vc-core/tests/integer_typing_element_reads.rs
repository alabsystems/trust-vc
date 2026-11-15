//! An element READ is a value of its collection's element type
//! (design-trust-proof-backend.md §5b rule 10: a value's sign comes from the
//! value, or from the collection it was read from). The typed seam lets a
//! producer DECLARE the node's type (`Index::elem_ty`, a `CollectionOp`'s
//! `ty`); where that names another integer type than the receiver's element
//! type, the read is refused — like a variable whose node type disagrees with
//! its declaration.
//!
//! Measured before (r9 verifier, identical at 44e93f72 and 50b27076): with
//! `s: Seq<u8>`, `s.len() == 1`, `s[0] == 200`, the element read declared
//! `i8`, `i16` or `i64` was sign-extended from the 8-bit term, so `s[0] ==
//! -56` came back `Verified` and the true `s[0] == 200` refuted — through a
//! cast to `int`, a `let` at `i8`, a `[u8; 1]` array, a `Map<u8, u8>` `get` and
//! `first`/`last`, in spec and exec obligations alike (16 false `Verified`, 4
//! false refutations). The other declared-type lies the r6 verifier probed
//! (a variable, a `let` body, a match binder, a `wrapping_*` node, a call
//! argument, a function's return, a length, a shift, a cast's `from_ty`) are
//! pinned here too.
//!
//! `f_*` must not be `Verified`; `t_*` (true under the value's own type) must
//! not be refuted.

use trust_vc_core::ir::{
    ArithOp, CollectionOp, CompareOp, MatchArm, MatchPattern, QuantifierKind, SpecialArithOp,
    TrustVcExpr, TrustVcType, WrappingMode,
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
fn eq(l: TrustVcExpr, r: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(l),
        right: Box::new(r),
    }
}
fn u(w: u32) -> TrustVcType {
    TrustVcType::Uint { width: w }
}
fn i(w: u32) -> TrustVcType {
    TrustVcType::Int { width: w }
}
fn seq_u8() -> TrustVcType {
    TrustVcType::Seq(Box::new(u(8)))
}

/// A helper function declaration: name, return type, parameters.
type HelperSig = (&'static str, TrustVcType, Vec<(&'static str, TrustVcType)>);

struct Case {
    name: String,
    vars: Vec<(&'static str, TrustVcType)>,
    requires: Vec<TrustVcExpr>,
    goal: TrustVcExpr,
    fns: Vec<HelperSig>,
    exec: bool,
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
        .map(|(k, r)| TypedProofObligation::requires(format!("e_requires_{k}"), r.clone()))
        .collect();
    obligations.push(TypedProofObligation::ensures("e_goal", c.goal.clone()));
    let mut ctx = VerificationContext::from_typed_parts(variables, obligations);
    for (name, ret, params) in &c.fns {
        ctx.declare_helper_function_typed(
            name,
            ret.clone(),
            params
                .iter()
                .map(|(n, t)| ((*n).to_string(), t.clone()))
                .collect(),
        );
    }
    if c.exec {
        ctx.enable_overflow_checks();
    }
    ctx.verify()
}

fn index(recv: &str, recv_ty: TrustVcType, elem_ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Index {
        receiver: Box::new(var(recv, recv_ty)),
        index: Box::new(lit(0, u(64))),
        receiver_name: Some(recv.to_string()),
        elem_ty,
    }
}

fn len(recv: &str, recv_ty: TrustVcType, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::CollectionOp {
        op: CollectionOp::Len,
        receiver: Box::new(var(recv, recv_ty)),
        receiver_name: Some(recv.to_string()),
        args: vec![],
        ty,
    }
}

/// `forall |p: T| name(p) == p` for a helper `name: T -> T`.
fn identity_axiom(name: &str, ty: TrustVcType) -> TrustVcExpr {
    let call = |arg: TrustVcExpr| TrustVcExpr::FnCall {
        name: name.to_string(),
        args: vec![arg],
        return_ty: ty.clone(),
    };
    let p = var("p", ty.clone());
    TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("p".to_string(), ty.clone())],
        body: Box::new(eq(call(p.clone()), p)),
        triggers: None,
        trigger_inference_mode: None,
    }
}

/// Element reads of a `Seq<u8>` / `[u8; 1]` / `Map<u8, u8>` whose element is
/// 200, at a declared type that is not the element type.
fn element_read_cases() -> Vec<Case> {
    let mut cs = Vec::new();
    let s_pin = vec![
        eq(len("s", seq_u8(), u(64)), lit(1, u(64))),
        eq(index("s", seq_u8(), u(8)), lit(200, u(8))),
    ];
    for exec in [false, true] {
        let tag = if exec { "exec" } else { "spec" };
        for (elem, rhs, truth) in [
            (i(8), -56, false),
            (i(8), 200, true),
            (i(16), -56, false),
            (i(16), 200, true),
            (i(64), -56, false),
            (u(16), 200, true),
        ] {
            let prefix = if truth { "t" } else { "f" };
            cs.push(Case {
                name: format!(
                    "{prefix}_{tag}_seq_index_elem_{}_eq_{rhs}",
                    elem.to_type_string()
                ),
                vars: vec![("s", seq_u8())],
                requires: s_pin.clone(),
                goal: eq(index("s", seq_u8(), elem), lit(rhs, i(16))),
                fns: vec![],
                exec,
            });
        }
        cs.push(Case {
            name: format!("f_{tag}_seq_index_elem_i8_as_int_eq_neg56"),
            vars: vec![("s", seq_u8())],
            requires: s_pin.clone(),
            goal: eq(
                TrustVcExpr::Cast {
                    expr: Box::new(index("s", seq_u8(), i(8))),
                    from_ty: i(8),
                    to_ty: TrustVcType::MathInt,
                },
                lit(-56, TrustVcType::MathInt),
            ),
            fns: vec![],
            exec,
        });
        cs.push(Case {
            name: format!("f_{tag}_seq_index_elem_i8_let_eq_neg56"),
            vars: vec![("s", seq_u8())],
            requires: s_pin.clone(),
            goal: eq(
                TrustVcExpr::Let {
                    name: "v".to_string(),
                    ty: i(8),
                    value: Box::new(index("s", seq_u8(), i(8))),
                    body: Box::new(var("v", i(8))),
                },
                lit(-56, i(16)),
            ),
            fns: vec![],
            exec,
        });
        let id16 = |arg: TrustVcExpr| TrustVcExpr::FnCall {
            name: "e_id16".to_string(),
            args: vec![arg],
            return_ty: i(16),
        };
        let mut req = s_pin.clone();
        req.push(identity_axiom("e_id16", i(16)));
        cs.push(Case {
            name: format!("f_{tag}_seq_index_elem_i8_call_arg_eq_neg56"),
            vars: vec![("s", seq_u8())],
            requires: req,
            goal: eq(id16(index("s", seq_u8(), i(8))), lit(-56, i(16))),
            fns: vec![("e_id16", i(16), vec![("p", i(16))])],
            exec,
        });
        let arr = TrustVcType::Array(Box::new(u(8)), 1);
        cs.push(Case {
            name: format!("f_{tag}_array_index_elem_i8_eq_neg56"),
            vars: vec![("a", arr.clone())],
            requires: vec![eq(index("a", arr.clone(), u(8)), lit(200, u(8)))],
            goal: eq(index("a", arr.clone(), i(8)), lit(-56, i(16))),
            fns: vec![],
            exec,
        });
        let map = TrustVcType::Map(Box::new(u(8)), Box::new(u(8)));
        let get = |ty: TrustVcType| TrustVcExpr::CollectionOp {
            op: CollectionOp::Get,
            receiver: Box::new(var("m", map.clone())),
            receiver_name: Some("m".to_string()),
            args: vec![lit(0, u(8))],
            ty,
        };
        let has0 = TrustVcExpr::CollectionOp {
            op: CollectionOp::ContainsKey,
            receiver: Box::new(var("m", map.clone())),
            receiver_name: Some("m".to_string()),
            args: vec![lit(0, u(8))],
            ty: TrustVcType::Bool,
        };
        cs.push(Case {
            name: format!("f_{tag}_map_get_ty_i8_eq_neg56"),
            vars: vec![("m", map.clone())],
            requires: vec![has0, eq(get(u(8)), lit(200, u(8)))],
            goal: eq(get(i(8)), lit(-56, i(16))),
            fns: vec![],
            exec,
        });
        for op in [CollectionOp::First, CollectionOp::Last] {
            cs.push(Case {
                name: format!("f_{tag}_seq_{op:?}_ty_i8_eq_neg56"),
                vars: vec![("s", seq_u8())],
                requires: s_pin.clone(),
                goal: eq(
                    TrustVcExpr::CollectionOp {
                        op,
                        receiver: Box::new(var("s", seq_u8())),
                        receiver_name: Some("s".to_string()),
                        args: vec![],
                        ty: i(8),
                    },
                    lit(-56, i(16)),
                ),
                fns: vec![],
                exec,
            });
        }
    }
    cs
}

/// The other declared-type lies of the r6 probes, over `x: u8 == 200`.
fn declared_type_lie_cases() -> Vec<Case> {
    let pin_x200 = vec![eq(var("x", u(8)), lit(200, u(8)))];
    let xs = vec![("x", u(8))];
    let mut cs = Vec::new();
    let mut pair = |name: &str, goal: &dyn Fn(i128) -> TrustVcExpr, case: &dyn Fn() -> Case| {
        for (prefix, rhs) in [("f", -56), ("t", 200)] {
            let mut c = case();
            c.name = format!("{prefix}_{name}_{rhs}");
            c.goal = goal(rhs);
            cs.push(c);
        }
    };
    let plain = |vars: Vec<(&'static str, TrustVcType)>, requires: Vec<TrustVcExpr>| Case {
        name: String::new(),
        vars,
        requires,
        goal: TrustVcExpr::BoolLit(true),
        fns: vec![],
        exec: false,
    };
    pair(
        "var_ty_i8",
        &|rhs| eq(var("x", i(8)), lit(rhs, i(16))),
        &|| plain(xs.clone(), pin_x200.clone()),
    );
    let pushed = || {
        let seq_ty = seq_u8();
        let empty = TrustVcExpr::FnCall {
            name: "__trust_vc_collection_ctor_Seq_u8_empty".to_string(),
            args: vec![],
            return_ty: seq_ty.clone(),
        };
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Push,
            receiver: Box::new(empty),
            receiver_name: Some("__trust_vc_collection_ctor_Seq_u8_empty".to_string()),
            args: vec![lit(200, u(8))],
            ty: seq_ty,
        }
    };
    pair(
        "pushed_seq_index_elem_i8",
        &|rhs| {
            eq(
                TrustVcExpr::Index {
                    receiver: Box::new(pushed()),
                    index: Box::new(lit(0, u(64))),
                    receiver_name: Some("__trust_vc_collection_ctor_Seq_u8_empty".to_string()),
                    elem_ty: i(8),
                },
                lit(rhs, i(16)),
            )
        },
        &|| plain(vec![], vec![]),
    );
    let call = |ret: TrustVcType| TrustVcExpr::FnCall {
        name: "e_h".to_string(),
        args: vec![var("x", u(8))],
        return_ty: ret,
    };
    pair(
        "fncall_return_ty_i8",
        &|rhs| eq(call(i(8)), lit(rhs, i(16))),
        &|| {
            let mut c = plain(
                xs.clone(),
                vec![pin_x200[0].clone(), eq(call(u(8)), var("x", u(8)))],
            );
            c.fns = vec![("e_h", u(8), vec![("p", u(8))])];
            c
        },
    );
    pair(
        "len_ty_i8",
        &|rhs| eq(len("s", seq_u8(), i(8)), lit(rhs, i(16))),
        &|| {
            plain(
                vec![("s", seq_u8())],
                vec![eq(len("s", seq_u8(), u(64)), lit(200, u(64)))],
            )
        },
    );
    pair(
        "wrapping_add_ty_i8",
        &|rhs| {
            eq(
                TrustVcExpr::WrappingArith {
                    mode: WrappingMode::Wrapping,
                    op: ArithOp::Add,
                    left: Box::new(var("x", u(8))),
                    right: Box::new(lit(0, u(8))),
                    ty: i(8),
                },
                lit(rhs, i(16)),
            )
        },
        &|| plain(xs.clone(), pin_x200.clone()),
    );
    pair(
        "let_body_reads_binder_i8",
        &|rhs| {
            eq(
                TrustVcExpr::Let {
                    name: "v".to_string(),
                    ty: u(8),
                    value: Box::new(var("x", u(8))),
                    body: Box::new(var("v", i(8))),
                },
                lit(rhs, i(16)),
            )
        },
        &|| plain(xs.clone(), pin_x200.clone()),
    );
    pair(
        "match_binder_i8",
        &|rhs| {
            eq(
                TrustVcExpr::Match {
                    scrutinee: Box::new(var("x", u(8))),
                    arms: vec![MatchArm::new(
                        MatchPattern::Ident("g".to_string()),
                        var("g", i(8)),
                    )],
                    ty: i(8),
                },
                lit(rhs, i(16)),
            )
        },
        &|| plain(xs.clone(), pin_x200.clone()),
    );
    pair(
        "shift_ty_i8",
        &|rhs| {
            eq(
                TrustVcExpr::SpecialArith {
                    op: SpecialArithOp::Shl,
                    left: Box::new(var("x", u(8))),
                    right: Box::new(lit(0, u(32))),
                    ty: i(8),
                },
                lit(rhs, i(16)),
            )
        },
        &|| plain(xs.clone(), pin_x200.clone()),
    );
    pair(
        "call_arg_node_ty_i8",
        &|rhs| {
            eq(
                TrustVcExpr::FnCall {
                    name: "e_id16".to_string(),
                    args: vec![var("x", i(8))],
                    return_ty: i(16),
                },
                lit(rhs, i(16)),
            )
        },
        &|| {
            let mut c = plain(
                xs.clone(),
                vec![pin_x200[0].clone(), identity_axiom("e_id16", i(16))],
            );
            c.fns = vec![("e_id16", i(16), vec![("p", i(16))])];
            c
        },
    );
    // A cast whose declared `from_ty` is `u8` over an `i8` -56: read at the
    // operand's own type, it is -56 (`t`), not 200 (`f`).
    for (prefix, rhs) in [("f", 200), ("t", -56)] {
        cs.push(Case {
            name: format!("{prefix}_cast_from_ty_u8_over_i8_{rhs}"),
            vars: vec![("y", i(8))],
            requires: vec![eq(
                var("y", i(8)),
                TrustVcExpr::Neg(Box::new(lit(56, i(8)))),
            )],
            goal: eq(
                TrustVcExpr::Cast {
                    expr: Box::new(var("y", i(8))),
                    from_ty: u(8),
                    to_ty: i(16),
                },
                lit(rhs, i(16)),
            ),
            fns: vec![],
            exec: false,
        });
    }
    cs
}

fn check(cases: Vec<Case>) {
    let mut wrong = Vec::new();
    for c in cases {
        let r = run(&c);
        let class = match &r {
            VerifyResult::Verified => "Verified",
            VerifyResult::Counterexample { .. } | VerifyResult::NotProved { .. } => "Refuted",
            _ => "Unknown",
        };
        let raw: String = format!("{r:?}")
            .replace('\n', " ")
            .chars()
            .take(240)
            .collect();
        println!("ELEM|{}|{class}|{raw}", c.name);
        if c.name.starts_with("f_") && class == "Verified" {
            wrong.push(format!("FALSE VERIFIED {}", c.name));
        }
        if c.name.starts_with("t_") && class == "Refuted" {
            wrong.push(format!("FALSE REFUTATION {}", c.name));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}

#[test]
fn an_element_read_is_a_value_of_its_collections_element_type() {
    check(element_read_cases());
}

#[test]
fn a_declared_node_type_never_rereads_a_value() {
    check(declared_type_lie_cases());
}
