//! Local broadcast contracts use exact declarations, scope guards and AY.
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

fn predicate(id: u64, name: &str) -> FnDecl {
    let mut f = Fb::new(id, name, Mode::Spec, Ty::Bool);
    f.param("x", Ty::int());
    f.decl
}

fn rule() -> FnDecl {
    let mut f = Fb::new(3, "rule", Mode::Proof, Ty::Unit);
    let x = f.param("x", Ty::int());
    let x = f.rd(x);
    let p = f.call(fn_id(1), vec![x.clone()], Ty::Bool);
    let q = f.call(fn_id(2), vec![x], Ty::Bool);
    f.requires(p.clone());
    f.ensures(q);
    f.decl.attrs.external_body = true;
    f.decl.attrs.broadcast_triggers = Some(vec![vec![p]]);
    f.decl
}

fn base(caller: FnDecl) -> VcCrate {
    krate(vec![predicate(1, "p"), predicate(2, "q"), rule(), caller])
}

fn application(f: &mut Fb, id: u64, n: i128) -> Expr {
    let n = f.lit(n, Ty::int());
    f.call(fn_id(id), vec![n], Ty::Bool)
}

#[test]
fn broadcast_requires_actual_use_original_precondition_and_matching_value() {
    for (enable, seed, argument, want) in [
        (true, true, 7, "P"),
        (false, true, 7, "R"),
        (true, false, 7, "R"),
        (true, true, 8, "R"),
    ] {
        let mut f = Fb::new(4, "caller", Mode::Proof, Ty::Unit);
        if seed {
            let p = application(&mut f, 1, 7);
            f.requires(p);
        }
        let mut statements = Vec::new();
        if enable {
            statements.push(f.stmt(StmtKind::BroadcastUse { callee: fn_id(3) }));
        }
        let q = application(&mut f, 2, argument);
        statements.push(f.assert(q));
        statements.push(f.ret(None));
        let k = base(f.body(statements));
        assert_eq!(verdicts(&checks_of(&k, 4)), want);
    }
}

#[test]
fn a_branch_broadcast_does_not_license_its_sibling_or_unconditional_join() {
    for (both, sibling_check) in [(false, false), (false, true), (true, false), (true, true)] {
        let mut f = Fb::new(4, "caller", Mode::Proof, Ty::Unit);
        let flag = f.param("flag", Ty::Bool);
        let p = application(&mut f, 1, 7);
        f.requires(p);
        let enable = f.stmt(StmtKind::BroadcastUse { callee: fn_id(3) });
        let q = application(&mut f, 2, 7);
        let within = f.assert(q.clone());
        let sibling = f.assert(q.clone());
        let condition = f.rd(flag);
        let branch = f.stmt(StmtKind::If {
            cond: condition,
            then_block: Block::new(vec![enable.clone(), within]),
            else_block: Block::new({
                let mut branch = Vec::new();
                if both {
                    branch.push(enable);
                }
                if sibling_check {
                    branch.push(sibling);
                }
                branch
            }),
        });
        let after = f.assert(q);
        let ret = f.ret(None);
        let k = base(f.body(vec![branch, after, ret]));
        assert_eq!(
            verdicts(&checks_of(&k, 4)),
            match (both, sibling_check) {
                (false, false) => "PR",
                // A failing assertion is assumed afterward, as upstream does.
                (false, true) => "PRP",
                (true, false) => "PP",
                (true, true) => "PPP",
            }
        );
    }
}

#[test]
fn broadcast_identity_is_not_a_same_spelled_unmarked_function() {
    let mut f = Fb::new(4, "caller", Mode::Proof, Ty::Unit);
    let wrong = f.stmt(StmtKind::BroadcastUse { callee: fn_id(5) });
    let mut other = Fb::new(5, "rule", Mode::Proof, Ty::Unit);
    let other_ret = other.ret(None);
    let other = other.body(vec![other_ret]);
    let ret = f.ret(None);
    let mut k = base(f.body(vec![wrong, ret]));
    k.fns.push(other);
    assert!(check_crate(&k)
        .iter()
        .any(|e| e.message.contains("broadcast use")));
}

#[test]
fn proof_body_and_external_assumption_classification_are_preserved() {
    let mut f = Fb::new(4, "caller", Mode::Proof, Ty::Unit);
    let ret = f.ret(None);
    let mut k = base(f.body(vec![ret]));
    assert!(matches!(
        generate(&k)
            .fns
            .iter()
            .find(|(id, _)| *id == fn_id(3))
            .unwrap()
            .1,
        FnVcs::Trusted
    ));
    let rule = k.fns.iter_mut().find(|decl| decl.id == fn_id(3)).unwrap();
    rule.attrs.external_body = false;
    rule.body = Body::Stmts(Block::new(vec![Stmt::new(
        SpanId(1),
        StmtKind::Return {
            value: None,
            site: SiteId(1),
        },
    )]));
    assert_eq!(verdicts(&checks_of(&k, 3)), "R");
}

#[test]
fn broadcast_edges_participate_in_recursion_checks() {
    let mut f = Fb::new(4, "caller", Mode::Proof, Ty::Unit);
    let enable = f.stmt(StmtKind::BroadcastUse { callee: fn_id(3) });
    let ret = f.ret(None);
    let mut k = base(f.body(vec![enable, ret]));
    let rule = k.fns.iter_mut().find(|decl| decl.id == fn_id(3)).unwrap();
    rule.attrs.external_body = false;
    rule.body = Body::Stmts(Block::new(vec![
        Stmt::new(
            SpanId(1),
            StmtKind::Call {
                callee: fn_id(4),
                type_args: vec![],
                args: vec![],
                dest: None,
                site: SiteId(1),
            },
        ),
        Stmt::new(
            SpanId(2),
            StmtKind::Return {
                value: None,
                site: SiteId(2),
            },
        ),
    ]));
    assert!(check_crate(&k).is_empty());
    for (_, result) in generate(&k)
        .fns
        .iter()
        .filter(|(id, _)| [fn_id(3), fn_id(4)].contains(id))
    {
        assert!(matches!(result, FnVcs::Refused(problem) if problem.tag == "broadcast-recursion"));
    }
}

#[test]
fn source_nat_binder_domain_survives_the_integer_call_abi() {
    for (value, expected) in [(7, "P"), (-1, "R")] {
        let mut r = Fb::new(3, "nat_rule", Mode::Proof, Ty::Unit);
        let x = r.param("x", Ty::nat());
        let x = r.rd(x);
        let x = r.int_of(x);
        let p = r.call(fn_id(1), vec![x.clone()], Ty::Bool);
        let q = r.call(fn_id(2), vec![x], Ty::Bool);
        r.requires(p.clone());
        r.ensures(q);
        r.decl.attrs.external_body = true;
        r.decl.attrs.broadcast_triggers = Some(vec![vec![p]]);
        let mut f = Fb::new(4, "caller", Mode::Proof, Ty::Unit);
        let p = application(&mut f, 1, value);
        f.requires(p);
        let enable = f.stmt(StmtKind::BroadcastUse { callee: fn_id(3) });
        let q = application(&mut f, 2, value);
        let check = f.assert(q);
        let ret = f.ret(None);
        let k = krate(vec![
            predicate(1, "p"),
            predicate(2, "q"),
            r.decl,
            f.body(vec![enable, check, ret]),
        ]);
        assert_eq!(verdicts(&checks_of(&k, 4)), expected);
    }
}

#[test]
fn zero_parameter_broadcast_is_ground_and_direct_call_is_rejected() {
    for (value, expected) in [(7, "P"), (8, "R")] {
        let mut r = Fb::new(3, "ground_rule", Mode::Proof, Ty::Unit);
        let q = application(&mut r, 2, 7);
        r.ensures(q);
        r.decl.attrs.external_body = true;
        r.decl.attrs.broadcast_triggers = Some(vec![]);
        let mut f = Fb::new(4, "caller", Mode::Proof, Ty::Unit);
        let enable = f.stmt(StmtKind::BroadcastUse { callee: fn_id(3) });
        let q = application(&mut f, 2, value);
        let assertion = f.assert(q);
        let ret = f.ret(None);
        let k = krate(vec![
            predicate(2, "q"),
            r.decl,
            f.body(vec![enable, assertion, ret]),
        ]);
        assert_eq!(verdicts(&checks_of(&k, 4)), expected);
        let mut invalid = k.clone();
        let caller = invalid.fns.iter_mut().find(|f| f.id == fn_id(4)).unwrap();
        if let Body::Stmts(block) = &mut caller.body {
            block.stmts[0] = Stmt::new(
                SpanId(1),
                StmtKind::Call {
                    callee: fn_id(3),
                    type_args: vec![],
                    args: vec![],
                    dest: None,
                    site: SiteId(99),
                },
            );
        }
        assert!(check_crate(&invalid)
            .iter()
            .any(|e| e.message
                == "cannot call a broadcast_forall function with 0 arguments directly"));
    }
}

#[test]
fn mutable_by_value_parameter_cannot_supply_a_broadcast_contract() {
    let mut f = Fb::new(4, "caller", Mode::Proof, Ty::Unit);
    let enable = f.stmt(StmtKind::BroadcastUse { callee: fn_id(3) });
    let ret = f.ret(None);
    let mut source = base(f.body(vec![enable, ret]));
    let supplier = source
        .fns
        .iter_mut()
        .find(|decl| decl.id == fn_id(3))
        .unwrap();
    supplier.locals[supplier.params[0].index()].mutable = true;
    let errors = check_crate(&source);
    assert!(
        errors.iter().any(|error| error
            .message
            .contains("a broadcast requires immutable spec parameter values")),
        "{errors:?}"
    );
    assert!(
        matches!(generate(&source).fns.iter().find(|(id, _)| *id == fn_id(4)).unwrap().1,
        FnVcs::Refused(ref error) if error.tag == "broadcast-contract")
    );
}
