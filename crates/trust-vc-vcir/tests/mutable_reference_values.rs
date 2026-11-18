//! Real opaque-reference queries and checked owned-storage transitions.
//! These are VcIR semantic controls, not native SDK/borrow-checker qualification.
use trust_vc_vcir::vcgen::{self, FnVcs, Query};
use trust_vc_vcir::*;

fn span() -> SpanId {
    SpanId(0)
}
fn id() -> FnId {
    FnId(DefHash::new(133, 1))
}
fn scalar() -> Ty {
    Ty::uint(32)
}
fn reference(ty: Ty) -> Ty {
    Ty::MutRef(Box::new(ty))
}
fn integer(value: i128) -> Expr {
    Expr::int_lit(value, scalar(), span())
}
fn read(local: LocalId, ty: Ty) -> Expr {
    Expr::read(Place::local(local), ty, span())
}
fn current(value: Expr) -> Expr {
    let Ty::MutRef(ty) = &value.ty else {
        panic!("reference")
    };
    Expr::new(
        (**ty).clone(),
        span(),
        ExprKind::MutRefCurrent(Box::new(value)),
    )
}
fn future(value: Expr) -> Expr {
    let Ty::MutRef(ty) = &value.ty else {
        panic!("reference")
    };
    Expr::new(
        (**ty).clone(),
        span(),
        ExprKind::MutRefFuture(Box::new(value)),
    )
}
fn field(value: Expr, index: u32) -> Expr {
    let Ty::Tuple(types) = &value.ty else {
        panic!("tuple")
    };
    Expr::new(
        types[index as usize].clone(),
        span(),
        ExprKind::TupleField {
            base: Box::new(value),
            index,
        },
    )
}
fn eq(a: Expr, b: Expr) -> Expr {
    Expr::binary(BinOp::Eq, a, b, Ty::Bool, span())
}
fn local(ty: Ty, mode: Mode, kind: LocalKind) -> LocalDecl {
    LocalDecl {
        name: "value".into(),
        ty,
        mode,
        kind,
        prophecy: DeclProphecy::Default,
        mutable: kind == LocalKind::Let,
        span: span(),
    }
}
fn function(result: Ty) -> FnDecl {
    FnDecl {
        id: id(),
        name: "opaque_refs".into(),
        span: span(),
        mode: Mode::Exec,
        role: FnRole::Item,
        kind: FnKind::Function,
        copy_premises: Vec::new(),
        type_params: vec![],
        locals: vec![local(result, Mode::Exec, LocalKind::Return)],
        params: vec![],
        ret: LocalId(0),
        requires: vec![],
        ensures: vec![],
        recommends: vec![],
        decreases: vec![],
        decreases_when: None,
        decreases_by: None,
        unwind: None,
        attrs: FnAttrs::default(),
        body: Body::Stmts(Block::default()),
    }
}
fn add(f: &mut FnDecl, ty: Ty, mode: Mode, kind: LocalKind) -> LocalId {
    let id = LocalId(f.locals.len() as u32);
    f.locals.push(local(ty, mode, kind));
    if kind == LocalKind::Param {
        f.params.push(id);
    }
    id
}
fn stmt(kind: StmtKind) -> Stmt {
    Stmt::new(span(), kind)
}
fn assertion(expr: Expr, site: u32) -> Stmt {
    stmt(StmtKind::Assert {
        expr,
        site: SiteId(site),
        attrs: ClauseAttrs::default(),
    })
}
fn ret(value: Option<Expr>) -> Stmt {
    stmt(StmtKind::Return {
        value,
        site: SiteId(9),
    })
}
fn clause(expr: Expr) -> Clause {
    Clause {
        expr,
        span: span(),
        attrs: ClauseAttrs::default(),
    }
}
fn krate(f: FnDecl) -> VcCrate {
    let mut k = VcCrate::new("opaque mutable references");
    k.fns.push(f);
    k
}
fn queries(k: &VcCrate) -> Vec<Query> {
    assert!(check_crate(k).is_empty(), "{:?}", check_crate(k));
    let generated = vcgen::generate(k);
    let Some(FnVcs::Checks(checks)) = generated.get(id()) else {
        panic!("{generated:?}")
    };
    assert!(!checks.is_empty());
    checks.iter().map(|check| check.query.clone()).collect()
}
fn pure_control(kind: u32) -> VcCrate {
    let mut f = function(Ty::Unit);
    let a = add(&mut f, reference(scalar()), Mode::Spec, LocalKind::Param);
    let b = add(&mut f, reference(scalar()), Mode::Spec, LocalKind::Param);
    let ar = || read(a, reference(scalar()));
    let br = || read(b, reference(scalar()));
    let updated = || {
        Expr::new(
            reference(scalar()),
            span(),
            ExprKind::MutRefUpdate {
                reference: Box::new(ar()),
                value: Box::new(integer(7)),
            },
        )
    };
    let goal = match kind {
        0 => eq(current(updated()), integer(7)),
        1 => eq(future(updated()), future(ar())),
        2 => eq(current(updated()), integer(8)),
        3 => {
            f.requires.push(clause(eq(current(ar()), current(br()))));
            f.requires.push(clause(eq(future(ar()), future(br()))));
            eq(ar(), br())
        }
        4 => {
            f.requires.push(clause(eq(current(ar()), integer(7))));
            eq(updated(), ar())
        }
        _ => panic!(),
    };
    f.body = Body::Stmts(Block::new(vec![assertion(goal, 0), ret(None)]));
    krate(f)
}
fn scalar_loan(correct: bool) -> VcCrate {
    let mut f = function(Ty::Unit);
    let value = add(&mut f, scalar(), Mode::Exec, LocalKind::Let);
    let loan = add(&mut f, reference(scalar()), Mode::Exec, LocalKind::Let);
    f.body = Body::Stmts(Block::new(vec![
        stmt(StmtKind::Let {
            local: value,
            init: Some(integer(0)),
        }),
        stmt(StmtKind::Let {
            local: loan,
            init: None,
        }),
        stmt(StmtKind::BorrowMut {
            dest: loan,
            place: Place::local(value),
        }),
        stmt(StmtKind::Assign {
            place: Place::deref(loan),
            value: integer(7),
        }),
        assertion(
            eq(read(value, scalar()), integer(if correct { 7 } else { 8 })),
            0,
        ),
        ret(None),
    ]));
    krate(f)
}
fn returned_field(kind: u32) -> VcCrate {
    let tuple = Ty::Tuple(vec![scalar(), scalar()]);
    let mut f = function(reference(scalar()));
    let parent = add(
        &mut f,
        reference(tuple.clone()),
        Mode::Exec,
        LocalKind::Param,
    );
    let child = add(&mut f, reference(scalar()), Mode::Exec, LocalKind::Let);
    let parent_read = || read(parent, reference(tuple.clone()));
    let result = || read(LocalId(0), reference(scalar()));
    let goal = match kind {
        0 => eq(future(result()), field(future(parent_read()), 0)),
        1 => eq(
            field(future(parent_read()), 1),
            field(current(parent_read()), 1),
        ),
        2 => eq(future(result()), current(result())),
        3 => eq(
            field(future(parent_read()), 1),
            field(current(parent_read()), 0),
        ),
        4 => eq(current(result()), field(current(parent_read()), 0)),
        _ => panic!(),
    };
    f.ensures.push(clause(goal));
    f.body = Body::Stmts(Block::new(vec![
        stmt(StmtKind::Let {
            local: child,
            init: None,
        }),
        stmt(StmtKind::BorrowMut {
            dest: child,
            place: Place {
                local: parent,
                projections: vec![Projection::Deref, Projection::TupleField(0)],
            },
        }),
        ret(Some(read(child, reference(scalar())))),
    ]));
    krate(f)
}
fn refusal(k: VcCrate, tag: &str) {
    assert!(check_crate(&k).is_empty(), "{:?}", check_crate(&k));
    let generated = vcgen::generate(&k);
    assert!(
        matches!(generated.get(id()),Some(FnVcs::Refused(problem)) if problem.tag==tag),
        "{generated:?}"
    );
}
#[test]
fn opaque_projections_and_updates_construct_real_typed_queries() {
    for kind in 0..=4 {
        assert_eq!(queries(&pure_control(kind)).len(), 1);
    }
}
#[test]
fn scalar_borrow_writeback_and_automatic_resolution_generate_both_twins() {
    for correct in [false, true] {
        assert_eq!(queries(&scalar_loan(correct)).len(), 1);
    }
}
#[test]
fn returned_field_loan_preserves_parent_and_sibling_without_resolving_child() {
    for kind in 0..=4 {
        assert_eq!(queries(&returned_field(kind)).len(), 1);
    }
}
#[test]
fn current_read_of_storage_with_a_future_borrow_write_is_refused() {
    let mut k = scalar_loan(true);
    let Body::Stmts(block) = &mut k.fns[0].body else {
        panic!()
    };
    block.stmts.swap(3, 4);
    refusal(k, "mut-ref-borrowed");
}
#[test]
fn moving_a_reference_invalidates_its_old_owned_storage() {
    let mut f = function(Ty::Unit);
    let original = add(&mut f, reference(scalar()), Mode::Exec, LocalKind::Param);
    let moved = add(&mut f, reference(scalar()), Mode::Exec, LocalKind::Let);
    f.body = Body::Stmts(Block::new(vec![
        stmt(StmtKind::Let {
            local: moved,
            init: Some(read(original, reference(scalar()))),
        }),
        assertion(
            eq(current(read(original, reference(scalar()))), integer(0)),
            0,
        ),
        ret(None),
    ]));
    refusal(krate(f), "mut-ref-moved");
}
#[test]
fn resolving_an_intermediate_reborrow_does_not_release_ancestor_storage() {
    let mut f = function(Ty::Unit);
    let value = add(&mut f, scalar(), Mode::Exec, LocalKind::Let);
    let parent = add(&mut f, reference(scalar()), Mode::Exec, LocalKind::Let);
    let child = add(&mut f, reference(scalar()), Mode::Exec, LocalKind::Let);
    f.body = Body::Stmts(Block::new(vec![
        stmt(StmtKind::Let {
            local: value,
            init: Some(integer(0)),
        }),
        stmt(StmtKind::Let {
            local: parent,
            init: None,
        }),
        stmt(StmtKind::BorrowMut {
            dest: parent,
            place: Place::local(value),
        }),
        stmt(StmtKind::Let {
            local: child,
            init: None,
        }),
        stmt(StmtKind::BorrowMut {
            dest: child,
            place: Place::deref(parent),
        }),
        assertion(eq(read(value, scalar()), integer(0)), 0),
        stmt(StmtKind::Assign {
            place: Place::deref(child),
            value: integer(1),
        }),
        ret(None),
    ]));
    refusal(krate(f), "mut-ref-borrowed");
}
fn nested_bounds() -> VcCrate {
    let inner = reference(Ty::uint(8));
    let mut f = function(Ty::Unit);
    let value = add(
        &mut f,
        reference(inner.clone()),
        Mode::Spec,
        LocalKind::Param,
    );
    let projected = current(current(read(value, reference(inner))));
    let goal = Expr::binary(
        BinOp::Le,
        projected,
        Expr::int_lit(255, Ty::uint(8), span()),
        Ty::Bool,
        span(),
    );
    f.body = Body::Stmts(Block::new(vec![assertion(goal, 0), ret(None)]));
    krate(f)
}
#[test]
fn nested_reference_projection_typing_reaches_the_query() {
    assert_eq!(queries(&nested_bounds()).len(), 1);
}
#[test]
fn has_resolved_and_future_are_prophetic_but_current_alone_is_not() {
    for (kind, expected) in [(0, false), (1, true), (2, true)] {
        let mut f = function(if kind == 2 { Ty::Bool } else { scalar() });
        f.mode = Mode::Spec;
        f.locals[0].mode = Mode::Spec;
        let value = add(&mut f, reference(scalar()), Mode::Spec, LocalKind::Param);
        f.body = Body::Spec(match kind {
            0 => current(read(value, reference(scalar()))),
            1 => future(read(value, reference(scalar()))),
            _ => Expr::new(
                Ty::Bool,
                span(),
                ExprKind::HasResolved(Box::new(read(value, reference(scalar())))),
            ),
        });
        let k = krate(f);
        assert_eq!(
            !check_crate(&k).is_empty(),
            expected,
            "{:?}",
            check_crate(&k)
        );
    }
}
#[cfg(feature = "solve")]
#[path = "mutable_reference_values/call_unwind.rs"]
mod call_unwind;

#[cfg(feature = "solve")]
#[path = "mutable_reference_values/call_result_provenance.rs"]
mod call_result_provenance;

#[cfg(feature = "solve")]
#[path = "mutable_reference_values/call_result_state.rs"]
mod call_result_state;

#[cfg(feature = "solve")]
#[path = "mutable_reference_values/owned_loops.rs"]
mod owned_loops;

#[cfg(feature = "solve")]
#[path = "mutable_reference_values/owned_loop_state.rs"]
mod owned_loop_state;

#[cfg(feature = "solve")]
#[path = "mutable_reference_values/field_mode_ownership.rs"]
mod field_mode_ownership;

#[cfg(feature = "solve")]
mod solver {
    use super::*;
    use trust_vc_vcir::solve::{check_detailed, Limits, Verdict};
    fn verdict(k: VcCrate, correct: bool) {
        for query in queries(&k) {
            let result = check_detailed(
                &query,
                "opaque mutable reference control",
                &Limits::default(),
            );
            assert!(
                if correct {
                    matches!(result.verdict, Verdict::Proved { .. })
                } else {
                    matches!(result.verdict, Verdict::Refuted { .. })
                },
                "{result:?}"
            );
        }
    }
    #[test]
    fn update_changes_current_and_preserves_future_with_a_false_twin() {
        for (kind, correct) in [(0, true), (1, true), (2, false)] {
            verdict(pure_control(kind), correct);
        }
    }
    #[test]
    fn equal_components_do_not_imply_reference_identity() {
        verdict(pure_control(3), false);
        verdict(pure_control(4), false);
    }
    #[test]
    fn scalar_storage_writeback_has_strict_solver_verdicts() {
        verdict(scalar_loan(true), true);
        verdict(scalar_loan(false), false);
    }
    #[test]
    fn returned_tuple_field_loan_preserves_sibling_and_does_not_resolve_moved_child() {
        for (kind, correct) in [(0, true), (1, true), (2, false), (3, false), (4, true)] {
            verdict(returned_field(kind), correct);
        }
    }
    #[test]
    fn nested_typed_projection_has_its_actual_u8_bound() {
        verdict(nested_bounds(), true);
    }
}
