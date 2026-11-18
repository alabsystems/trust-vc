//! Path-sensitive typed values, including termination-only return symbols.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_vcir::vcgen::{
    self,
    term::{Sort, Term},
    FnVcs, Source,
};
use trust_vc_vcir::*;

fn id(number: u64) -> FnId {
    FnId(DefHash::new(9, number))
}
fn read(local: u32, ty: Ty) -> Expr {
    Expr::read(Place::local(LocalId(local)), ty, SpanId(0))
}
fn stmt(kind: StmtKind) -> Stmt {
    Stmt {
        span: SpanId(0),
        kind,
    }
}
fn local(name: &str, ty: Ty, kind: LocalKind) -> LocalDecl {
    LocalDecl {
        name: name.into(),
        ty,
        mode: Mode::Spec,
        prophecy: trust_vc_vcir::DeclProphecy::Default,
        mutable: false,
        kind,
        span: SpanId(0),
    }
}
fn function(number: u64, parameters: Vec<(&str, Ty)>, result: Ty) -> FnDecl {
    let mut locals = vec![local("result", result, LocalKind::Return)];
    locals.extend(
        parameters
            .iter()
            .map(|(name, ty)| local(name, ty.clone(), LocalKind::Param)),
    );
    FnDecl {
        id: id(number),
        name: format!("f{number}"),
        span: SpanId(0),
        mode: Mode::Spec,
        role: FnRole::Item,
        kind: FnKind::Function,
        copy_premises: Vec::new(),
        type_params: vec!["A".into()],
        locals,
        params: (1..=parameters.len())
            .map(|index| LocalId(u32::try_from(index).unwrap()))
            .collect(),
        ret: LocalId(0),
        requires: vec![],
        ensures: vec![],
        recommends: vec![],
        decreases: vec![],
        decreases_when: None,
        decreases_by: None,
        unwind: None,
        attrs: FnAttrs::default(),
        body: Body::None,
    }
}
fn call(number: u64, args: Vec<Expr>) -> Expr {
    Expr::new(
        Ty::Param(0),
        SpanId(0),
        ExprKind::Call {
            callee: id(number),
            type_args: vec![Ty::Param(0)],
            args,
        },
    )
}
fn assertion() -> Stmt {
    stmt(StmtKind::Assert {
        expr: Expr::bool_lit(true, SpanId(0)),
        site: SiteId(0),
        attrs: ClauseAttrs::default(),
    })
}
fn exit() -> Stmt {
    stmt(StmtKind::Return {
        value: None,
        site: SiteId(1),
    })
}

fn checked_queries(krate: &VcCrate, function: u64) -> Vec<vcgen::Query> {
    assert!(check_crate(krate).is_empty(), "{:?}", check_crate(krate));
    let vcs = vcgen::generate(krate);
    let FnVcs::Checks(checks) = vcs.get(id(function)).unwrap() else {
        panic!("{vcs:?}");
    };
    checks.iter().map(|check| check.query.clone()).collect()
}

fn type_identity(query: &vcgen::Query) -> Term {
    let symbol = query
        .symbols
        .iter()
        .find(|symbol| symbol.sort == Sort::TypeId)
        .unwrap();
    Term::var(symbol.name.clone(), symbol.sort)
}

fn member(name: &str, identity: &Term) -> Term {
    Term::call(
        "has_type",
        vec![Term::var(name, Sort::Poly), identity.clone()],
        Sort::Bool,
    )
}

#[test]
fn conditional_fresh_poly_membership_stays_under_its_branch() {
    for negated in [false, true] {
        let mut krate = VcCrate::new("conditional typed value");
        krate.fns.push(function(1, vec![], Ty::Param(0)));
        let mut caller = function(2, vec![("branch", Ty::Bool)], Ty::Unit);
        caller.mode = Mode::Proof;
        caller
            .locals
            .push(local("branch_value", Ty::Param(0), LocalKind::Let));
        let branch = read(1, Ty::Bool);
        let branch = if negated {
            branch.not(SpanId(0))
        } else {
            branch
        };
        caller.body = Body::Stmts(Block::new(vec![
            stmt(StmtKind::If {
                cond: branch,
                then_block: Block::new(vec![stmt(StmtKind::Let {
                    local: LocalId(2),
                    init: Some(call(1, vec![])),
                })]),
                else_block: Block::default(),
            }),
            assertion(),
            exit(),
        ]));
        krate.fns.push(caller);
        let queries = checked_queries(&krate, 2);
        assert_eq!(queries.len(), 1);
        let query = &queries[0];
        let value = query
            .symbols
            .iter()
            .find(|symbol| symbol.display == "branch_value")
            .unwrap();
        let branch = query
            .symbols
            .iter()
            .find(|symbol| symbol.display == "branch")
            .unwrap();
        let branch = Term::var(branch.name.clone(), Sort::Bool);
        let guard = if negated {
            std::ops::Not::not(branch)
        } else {
            branch
        };
        let membership = member(&value.name, &type_identity(query));
        assert!(query
            .hypotheses
            .iter()
            .any(|hypothesis| hypothesis.source == Source::TypeFact
                && hypothesis.term == Term::implies(guard.clone(), membership.clone())));
        assert!(query.hypotheses.iter().all(
            |hypothesis| hypothesis.source != Source::TypeFact || hypothesis.term != membership
        ));
    }
}

#[test]
fn an_uninitialized_poly_local_does_not_supply_a_member() {
    for initialized in [false, true] {
        for goal in [false, true] {
            let mut krate = VcCrate::new("uninitialized typed local");
            krate.fns.push(function(1, vec![], Ty::Param(0)));
            let mut caller = function(2, vec![], Ty::Unit);
            caller.mode = Mode::Proof;
            caller
                .locals
                .push(local("value", Ty::Param(0), LocalKind::Let));
            caller.body = Body::Stmts(Block::new(vec![
                stmt(StmtKind::Let {
                    local: LocalId(1),
                    init: initialized.then(|| call(1, vec![])),
                }),
                stmt(StmtKind::Assert {
                    expr: Expr::bool_lit(goal, SpanId(0)),
                    site: SiteId(0),
                    attrs: ClauseAttrs::default(),
                }),
                exit(),
            ]));
            krate.fns.push(caller);
            assert!(check_crate(&krate).is_empty());
            let vcs = vcgen::generate(&krate);
            let Some(FnVcs::Checks(checks)) = vcs.get(id(2)) else {
                panic!("{vcs:?}");
            };
            assert_eq!(checks.len(), 1);
            if !initialized {
                assert!(checks[0]
                    .query
                    .symbols
                    .iter()
                    .all(|symbol| symbol.sort != Sort::Poly));
                let mut without_declaration = krate.clone();
                let Body::Stmts(body) = &mut without_declaration.fns[1].body else {
                    unreachable!()
                };
                body.stmts.remove(0);
                let baseline = vcgen::generate(&without_declaration);
                let Some(FnVcs::Checks(baseline)) = baseline.get(id(2)) else {
                    panic!("{baseline:?}");
                };
                assert_eq!(checks[0].query.symbols, baseline[0].query.symbols);
                assert_eq!(checks[0].query.hypotheses, baseline[0].query.hypotheses);
            }
            #[cfg(feature = "solve")]
            if !goal {
                let result = trust_vc_vcir::solve::check(
                    &checks[0].query,
                    "unused abstract storage",
                    &Default::default(),
                );
                assert!(
                    matches!(result, trust_vc_vcir::solve::Verdict::Refuted { .. }),
                    "{result:?}"
                );
            }
        }
    }
}

#[test]
fn recursive_return_membership_uses_each_exact_call_guard() {
    let mut krate = VcCrate::new("conditional recursive return");
    let mut recursive = function(
        1,
        vec![
            ("n", Ty::nat()),
            ("value", Ty::Param(0)),
            ("branch", Ty::Bool),
        ],
        Ty::Param(0),
    );
    let n = read(1, Ty::nat());
    let branch = read(3, Ty::Bool);
    let one = Expr::int_lit(1, Ty::nat(), SpanId(0));
    let argument = Expr::binary(BinOp::Sub, n.clone(), one, Ty::int(), SpanId(0)).cast(
        CastKind::As,
        Ty::nat(),
        SpanId(0),
    );
    let recurse = call(1, vec![argument, read(2, Ty::Param(0)), branch.clone()]);
    recursive.body = Body::Spec(Expr::new(
        Ty::Param(0),
        SpanId(0),
        ExprKind::If {
            cond: Box::new(branch),
            then_expr: Box::new(recurse.clone()),
            else_expr: Box::new(recurse),
        },
    ));
    recursive.decreases = vec![n.clone()];
    recursive.decreases_when = Some(Expr::binary(
        BinOp::Gt,
        n,
        Expr::int_lit(0, Ty::nat(), SpanId(0)),
        Ty::Bool,
        SpanId(0),
    ));
    krate.fns.push(recursive);
    krate.rec_groups.push(RecGroup {
        members: vec![(id(1), 1)],
    });
    let queries = checked_queries(&krate, 1);
    assert_eq!(queries.len(), 2);
    for query in &queries {
        let identity = type_identity(query);
        let branch = query
            .symbols
            .iter()
            .find(|symbol| symbol.display == "branch")
            .unwrap();
        let branch = Term::var(branch.name.clone(), Sort::Bool);
        for (name, guard) in [
            ("rc0_0", branch.clone()),
            ("rc1_0", std::ops::Not::not(branch)),
        ] {
            assert!(query
                .symbols
                .iter()
                .any(|symbol| symbol.name == name && symbol.sort == Sort::Poly));
            let membership = member(name, &identity);
            assert!(query
                .hypotheses
                .iter()
                .any(|hypothesis| hypothesis.source == Source::TypeFact
                    && hypothesis.term == Term::implies(guard.clone(), membership.clone())));
            assert!(query
                .hypotheses
                .iter()
                .all(|hypothesis| hypothesis.source != Source::TypeFact
                    || hypothesis.term != membership));
        }
    }
}
