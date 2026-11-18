use super::*;

fn copy_call(statement: bool) -> VcCrate {
    let mut target = original();
    target.copy_premises = vec![Ty::Param(0)];
    let mut caller = original();
    caller.id = id(10);
    caller.copy_premises = vec![Ty::Param(0)];
    let argument = Expr::read(Place::local(LocalId(1)), Ty::Param(0), SpanId(0));
    if statement {
        target.mode = Mode::Proof;
        caller.mode = Mode::Proof;
        caller.locals.push(local(Ty::Param(0), LocalKind::Let));
        caller.locals[2].mutable = true;
        caller.body = Body::Stmts(Block::new(vec![
            Stmt::new(
                SpanId(0),
                StmtKind::Let {
                    local: LocalId(2),
                    init: None,
                },
            ),
            Stmt::new(
                SpanId(0),
                StmtKind::Call {
                    dest: Some(Place::local(LocalId(2))),
                    callee: target.id,
                    type_args: vec![Ty::Param(0)],
                    args: vec![argument],
                    site: SiteId(0),
                },
            ),
            Stmt::new(
                SpanId(0),
                StmtKind::Return {
                    value: Some(Expr::read(
                        Place::local(LocalId(2)),
                        Ty::Param(0),
                        SpanId(0),
                    )),
                    site: SiteId(1),
                },
            ),
        ]));
    } else {
        caller.body = Body::Spec(Expr::new(
            Ty::Param(0),
            SpanId(0),
            ExprKind::Call {
                callee: target.id,
                type_args: vec![Ty::Param(0)],
                args: vec![argument],
            },
        ));
    }
    let mut source = VcCrate::new("Copy calls use the actual caller context");
    source.fns = vec![target, caller];
    source
}

#[test]
fn ordinary_and_spec_calls_discharge_copy_bounds_in_the_caller() {
    for statement in [false, true] {
        let mut source = copy_call(statement);
        assert!(
            check_crate(&source).is_empty(),
            "{:?}",
            check_crate(&source)
        );
        source.fns[1].copy_premises.clear();
        assert!(has_malformed(
            &source,
            id(10),
            "a target Copy premise is not discharged by the caller typing context"
        ));
        source.fns[1].copy_premises = vec![Ty::Tuple(vec![Ty::Param(0), Ty::Bool])];
        assert!(
            has_malformed(
                &source,
                id(10),
                "a target Copy premise is not discharged by the caller typing context"
            ),
            "a compound premise cannot donate Copy to one component"
        );
    }
}

#[test]
fn structural_shared_references_discharge_calls_but_mutable_references_do_not() {
    for mutable in [false, true] {
        let mut source = copy_call(false);
        let actual = if mutable {
            Ty::MutRef(Box::new(Ty::Param(0)))
        } else {
            Ty::Ref {
                mutable: false,
                inner: Box::new(Ty::Param(0)),
            }
        };
        source.fns[1].copy_premises.clear();
        source.fns[1].locals[0].ty = actual.clone();
        source.fns[1].locals[1].ty = actual.clone();
        source.fns[1].body = Body::Spec(Expr::new(
            actual.clone(),
            SpanId(0),
            ExprKind::Call {
                callee: id(1),
                type_args: vec![actual.clone()],
                args: vec![Expr::read(Place::local(LocalId(1)), actual, SpanId(0))],
            },
        ));
        if mutable {
            assert!(has_malformed(
                &source,
                id(10),
                "a target Copy premise is not discharged by the caller typing context"
            ));
        } else {
            assert!(
                check_crate(&source).is_empty(),
                "{:?}",
                check_crate(&source)
            );
        }
    }
}

#[test]
fn a_ground_instance_cannot_supply_its_own_copy_proof_or_change_its_context() {
    let mut source = super::source();
    source.fns[0].copy_premises = vec![Ty::Param(0)];
    source.fns[1].copy_premises = vec![Ty::Bool];
    assert!(
        check_crate(&source).is_empty(),
        "{:?}",
        check_crate(&source)
    );
    source.fns[1].copy_premises.clear();
    assert!(has_malformed(
        &source,
        id(2),
        "an instance Copy context disagrees with its native origin"
    ));
    let mut source = super::source();
    let noncopy = Ty::MutRef(Box::new(Ty::Bool));
    source.fns[0].copy_premises = vec![Ty::Param(0)];
    source.fns[1].copy_premises = vec![noncopy.clone()];
    source.fns[1].attrs.instance.as_mut().unwrap().type_args = vec![noncopy.clone()];
    for local in &mut source.fns[1].locals {
        local.ty = noncopy.clone();
    }
    assert!(has_malformed(
        &source,
        id(2),
        "a target Copy premise is not discharged by the caller typing context"
    ));
}

#[test]
fn malformed_and_imported_copy_assumptions_are_rejected() {
    let mut source = VcCrate::new("no imported Copy authority");
    let mut function = original();
    function.copy_premises = vec![Ty::Param(1)];
    source.fns.push(function);
    assert!(check_crate(&source)
        .iter()
        .any(|e| e.class == WfClass::Malformed && e.message.contains("Copy premise")));
    source.fns[0].copy_premises = vec![Ty::Param(0)];
    source.fns[0].role = FnRole::Imported;
    assert!(
        !check_crate(&source).is_empty(),
        "the current imported fragment has no Copy premise producer"
    );
    source.fns[0].copy_premises.clear();
    assert!(
        check_crate(&source).is_empty(),
        "the ordinary imported signature stays supported"
    );
}

#[test]
fn distinct_native_premise_positions_survive_equal_ground_substitutions() {
    let mut source = super::source();
    source.fns[0].type_params = vec!["T".into(), "U".into()];
    source.fns[0].copy_premises = vec![Ty::Param(0), Ty::Param(1)];
    source.fns[1].attrs.instance.as_mut().unwrap().type_args = vec![Ty::Bool, Ty::Bool];
    source.fns[1].copy_premises = vec![Ty::Bool, Ty::Bool];
    assert!(
        check_crate(&source).is_empty(),
        "{:?}",
        check_crate(&source)
    );
    source.fns[1].copy_premises.pop();
    assert!(has_malformed(
        &source,
        id(2),
        "an instance Copy context disagrees with its native origin"
    ));
}
