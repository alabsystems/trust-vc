//! Resolution obligations across generic consumption, joins and enum guards.
use super::*;
use crate::{AdtDecl, ClauseAttrs, DefHash, FieldDecl, LocalDecl, SiteId, VariantDecl, VcCrate};

fn id() -> AdtId {
    AdtId(DefHash::new(181, 1))
}
fn source(nested: bool) -> VcCrate {
    let mut source = crate::vcgen::closed_templates::tests::source();
    let decl = &mut source.fns[1];
    decl.mode = Mode::Exec;
    decl.type_params = vec!["A".into(), "B".into(), "C".into()];
    decl.locals[0].ty = Ty::Unit;
    decl.locals[0].mode = Mode::Exec;
    decl.locals[1].mode = Mode::Exec;
    decl.locals[1].ty = if nested {
        Ty::Adt(
            id(),
            vec![Ty::Tuple(vec![
                Ty::Adt(id(), vec![Ty::Tuple(vec![Ty::Param(0), Ty::Param(1)])]),
                Ty::Param(2),
            ])],
        )
    } else {
        Ty::Adt(id(), vec![Ty::Param(0)])
    };
    source.adts.push(AdtDecl {
        id: id(),
        name: "ActualOption".into(),
        type_params: vec!["T".into()],
        span: SpanId(0),
        kind: AdtKind::Enum,
        variants: vec![
            VariantDecl {
                name: "Some".into(),
                fields: vec![FieldDecl {
                    name: "0".into(),
                    ty: Ty::Param(0),
                    mode: Mode::Exec,
                }],
            },
            VariantDecl {
                name: "None".into(),
                fields: vec![],
            },
        ],
    });
    source
}
fn field() -> Place {
    Place {
        local: LocalId(1),
        projections: vec![Projection::Field {
            variant: 0,
            field: 0,
        }],
    }
}
fn marker() -> Stmt {
    Stmt::new(
        SpanId(0),
        StmtKind::Assume {
            expr: Expr::bool_lit(true, SpanId(0)),
            attrs: ClauseAttrs::default(),
        },
    )
}
fn local(ty: Ty, kind: LocalKind) -> LocalDecl {
    let mut local = crate::vcgen::closed_templates::tests::source().fns[1].locals[1].clone();
    local.ty = ty;
    local.kind = kind;
    local.mode = Mode::Exec;
    local.mutable = true;
    local
}
fn points(plan: &Plan, block: &Block, index: usize) -> Vec<Place> {
    plan.before_points(&block.stmts[index] as *const Stmt as usize, SpanId(0))
        .unwrap()
}

#[test]
fn nested_targets_retain_every_parent_variant_without_concrete_loan_slots() {
    let source = source(true);
    let ctx = Ctx::new(&source);
    let decl = &source.fns[1];
    let classifier = Classifier::new(&ctx, decl);
    assert!(!classifier.contains(&decl.locals[1].ty, SpanId(0)).unwrap());
    assert!(classifier
        .contains_abstract(&decl.locals[1].ty, SpanId(0))
        .unwrap());
    let block = Block::new(vec![marker()]);
    let plan = analyze(&ctx, decl, &block, &classifier).unwrap();
    assert!(
        plan.places.is_empty(),
        "abstract targets cannot release concrete loans"
    );
    let target = Place {
        local: LocalId(1),
        projections: vec![
            Projection::Field {
                variant: 0,
                field: 0,
            },
            Projection::TupleField(0),
            Projection::Field {
                variant: 0,
                field: 0,
            },
            Projection::TupleField(1),
        ],
    };
    assert!(points(&plan, &block, 0).contains(&target));
    let target = plan.value_target(&target, SpanId(0)).unwrap().unwrap();
    assert_eq!(target.ty(), &Ty::Param(1));
    assert_eq!(target.guards().len(), 2);
    assert_eq!(target.guards()[0].prefix(), &Place::local(LocalId(1)));
    assert_eq!(target.guards()[1].prefix().projections.len(), 2);
    assert!(target
        .guards()
        .iter()
        .all(|g| g.datatype() == id() && g.variant() == 0));
    let mut single = source.clone();
    single.adts[0].variants.pop();
    let ctx = Ctx::new(&single);
    let decl = &single.fns[1];
    let classifier = Classifier::new(&ctx, decl);
    let plan = analyze(&ctx, decl, &block, &classifier).unwrap();
    let target = plan
        .value_target(target.place(), SpanId(0))
        .unwrap()
        .unwrap();
    assert_eq!(
        target.guards().len(),
        2,
        "even single-variant enum ancestors retain explicit guard provenance"
    );
}

#[test]
fn future_generic_let_assignment_call_and_return_each_block_early_resolution() {
    for action in 0..4 {
        let mut source = source(false);
        source.fns[1]
            .locals
            .push(local(Ty::Param(0), LocalKind::Let));
        let value = Expr::read(field(), Ty::Param(0), SpanId(0));
        let consume = match action {
            0 => StmtKind::Let {
                local: LocalId(2),
                init: Some(value),
            },
            1 => StmtKind::Assign {
                place: Place::local(LocalId(2)),
                value,
            },
            2 => {
                source.fns[0].mode = Mode::Exec;
                source.fns[0].locals[0].ty = Ty::Unit;
                source.fns[0].locals[0].mode = Mode::Exec;
                source.fns[0].locals[1].mode = Mode::Exec;
                StmtKind::Call {
                    callee: source.fns[0].id,
                    type_args: vec![Ty::Param(0)],
                    args: vec![value],
                    dest: None,
                    site: SiteId(0),
                }
            }
            _ => {
                source.fns[1].locals[0].ty = Ty::Param(0);
                StmtKind::Return {
                    value: Some(value),
                    site: SiteId(0),
                }
            }
        };
        let mut statements = vec![];
        if action == 1 {
            statements.push(Stmt::new(
                SpanId(0),
                StmtKind::Let {
                    local: LocalId(2),
                    init: None,
                },
            ));
        }
        let before = statements.len();
        statements.extend([marker(), Stmt::new(SpanId(0), consume), marker()]);
        let block = Block::new(statements);
        let ctx = Ctx::new(&source);
        let decl = &source.fns[1];
        let classifier = Classifier::new(&ctx, decl);
        let plan = analyze(&ctx, decl, &block, &classifier).unwrap();
        assert!(
            !points(&plan, &block, before).contains(&field()),
            "action {action}"
        );
        assert!(
            !points(&plan, &block, before + 2).contains(&field()),
            "moved value cannot acquire later facts, action {action}"
        );
        if action != 3 {
            let state = plan
                .after_state(&block.stmts[before + 1] as *const Stmt as usize, SpanId(0))
                .unwrap()
                .unwrap();
            assert!(
                state.moved.is_empty(),
                "abstract consumption must retain legal Spec snapshot observations"
            );
        }
    }
}

#[test]
fn uninitialized_and_branch_moved_values_never_acquire_resolution_facts() {
    let mut source = source(false);
    source.fns[1]
        .locals
        .push(local(Ty::Param(0), LocalKind::Let));
    let block = Block::new(vec![
        Stmt::new(
            SpanId(0),
            StmtKind::Let {
                local: LocalId(2),
                init: None,
            },
        ),
        marker(),
        Stmt::new(
            SpanId(0),
            StmtKind::If {
                cond: Expr::bool_lit(true, SpanId(0)),
                then_block: Block::new(vec![Stmt::new(
                    SpanId(0),
                    StmtKind::Assign {
                        place: Place::local(LocalId(2)),
                        value: Expr::read(field(), Ty::Param(0), SpanId(0)),
                    },
                )]),
                else_block: Block::new(vec![]),
            },
        ),
        marker(),
    ]);
    let ctx = Ctx::new(&source);
    let decl = &source.fns[1];
    let classifier = Classifier::new(&ctx, decl);
    let plan = analyze(&ctx, decl, &block, &classifier).unwrap();
    for index in [1, 3] {
        let selected = points(&plan, &block, index);
        assert!(!selected.contains(&Place::local(LocalId(2))));
        assert!(!selected.contains(&field()));
    }
}

#[test]
fn dereferences_and_spec_fields_supply_no_abstract_drop_facts() {
    let mut source = source(false);
    source.adts[0].variants[0].fields[0].mode = Mode::Spec;
    source.fns[1]
        .locals
        .push(local(Ty::MutRef(Box::new(Ty::Param(1))), LocalKind::Param));
    source.fns[1].params.push(LocalId(2));
    let block = Block::new(vec![marker()]);
    let ctx = Ctx::new(&source);
    let decl = &source.fns[1];
    let classifier = Classifier::new(&ctx, decl);
    let plan = analyze(&ctx, decl, &block, &classifier).unwrap();
    assert!(plan.value_targets.is_empty());
    assert!(!points(&plan, &block, 0).iter().any(Place::has_deref));
    assert_eq!(plan.places, vec![Place::local(LocalId(2))]);
    // Copy supplies a copied value, never a resolution target at its
    // referenced address or permission to resolve/release that reference.
    let mut copy_source = source.clone();
    copy_source.fns[1].copy_premises = vec![Ty::Param(1)];
    let ctx = Ctx::new(&copy_source);
    let decl = &copy_source.fns[1];
    let classifier = Classifier::new(&ctx, decl);
    let plan = analyze(&ctx, decl, &block, &classifier).unwrap();
    assert!(plan.value_targets.is_empty());
    assert!(!points(&plan, &block, 0).iter().any(Place::has_deref));
    assert_eq!(plan.places, vec![Place::local(LocalId(2))]);
}

#[test]
fn exhausted_abstract_analysis_never_refills_or_returns_an_empty_successful_plan() {
    let source = source(true);
    let ctx = Ctx::new(&source);
    let decl = &source.fns[1];
    let classifier = Classifier::new(&ctx, decl);
    let block = Block::new(vec![marker()]);
    let remaining = classifier.work().remaining().get();
    classifier.work().charge(remaining, SpanId(0)).unwrap();
    for _ in 0..2 {
        let error = analyze(&ctx, decl, &block, &classifier)
            .err()
            .expect("actual exhausted ledger refuses");
        assert_eq!(error.tag, "resolution-size");
        assert_eq!(classifier.work().remaining().get(), 0);
    }
}

#[test]
fn checked_copy_transfers_preserve_forward_initialization_without_deref_targets() {
    for copy in [false, true] {
        let mut source = source(false);
        if copy {
            source.fns[1].copy_premises = vec![Ty::Param(0)];
        }
        source.fns[1]
            .locals
            .push(local(Ty::Param(0), LocalKind::Let));
        let block = Block::new(vec![
            Stmt::new(
                SpanId(0),
                StmtKind::Let {
                    local: LocalId(2),
                    init: Some(Expr::read(field(), Ty::Param(0), SpanId(0))),
                },
            ),
            marker(),
        ]);
        let ctx = Ctx::new(&source);
        let decl = &source.fns[1];
        let classifier = Classifier::new(&ctx, decl);
        let plan = analyze(&ctx, decl, &block, &classifier).unwrap();
        assert_eq!(
            points(&plan, &block, 1).contains(&field()),
            copy,
            "only a discharged Copy context preserves the source"
        );
        assert!(!plan
            .value_targets
            .iter()
            .any(|target| target.place().has_deref()));
        assert!(
            plan.places.is_empty(),
            "abstract Copy adds no concrete loan carrier"
        );
    }
}

#[test]
fn copy_only_consumers_retain_the_same_debited_classifier_cell_without_targets() {
    let mut source = source(false);
    source.fns[1].locals[1].ty = Ty::Ref {
        mutable: false,
        inner: Box::new(Ty::Param(0)),
    };
    source.fns[1].copy_premises = vec![Ty::Param(0)];
    let block = Block::new(vec![marker()]);
    let ctx = Ctx::new(&source);
    let decl = &source.fns[1];
    let classifier = Classifier::new(&ctx, decl);
    let work = classifier.work();
    let initial = work.remaining().get();
    let plan = analyze(&ctx, decl, &block, &classifier).unwrap();
    assert!(std::ptr::eq(plan.remaining().unwrap(), work.remaining()));
    assert!(
        work.remaining().get() < initial,
        "the original eligibility scan was paid"
    );
    assert!(plan.places.is_empty() && plan.value_targets.is_empty());
    assert!(points(&plan, &block, 0).is_empty());
    let remaining = work.remaining().get();
    assert_eq!(
        plan.charge(remaining + 1, SpanId(0)).unwrap_err().tag,
        "resolution-size"
    );
    assert_eq!(
        work.remaining().get(),
        remaining,
        "a rejected debit preserves the original shared balance"
    );
    plan.charge(remaining, SpanId(0)).unwrap();
    assert_eq!(work.remaining().get(), 0);
    assert_eq!(
        analyze(&ctx, decl, &block, &classifier).err().unwrap().tag,
        "resolution-size"
    );
    assert_eq!(
        work.remaining().get(),
        0,
        "analysis cannot refill the same cell"
    );
    let mut unconstrained = source.clone();
    unconstrained.fns[1].copy_premises.clear();
    let ctx = Ctx::new(&unconstrained);
    let decl = &unconstrained.fns[1];
    let classifier = Classifier::new(&ctx, decl);
    assert!(analyze(&ctx, decl, &block, &classifier)
        .unwrap()
        .remaining()
        .is_none());
}

#[test]
fn nested_field_expressions_consume_only_the_exact_selected_generic_field() {
    let mut source = source(true);
    source.fns[1]
        .locals
        .push(local(Ty::Param(0), LocalKind::Let));
    let root = Expr::read(
        Place::local(LocalId(1)),
        source.fns[1].locals[1].ty.clone(),
        SpanId(0),
    );
    let outer = Expr::new(
        Ty::Tuple(vec![
            Ty::Adt(id(), vec![Ty::Tuple(vec![Ty::Param(0), Ty::Param(1)])]),
            Ty::Param(2),
        ]),
        SpanId(0),
        ExprKind::Field {
            base: Box::new(root),
            variant: 0,
            field: 0,
        },
    );
    let inner = Expr::new(
        Ty::Adt(id(), vec![Ty::Tuple(vec![Ty::Param(0), Ty::Param(1)])]),
        SpanId(0),
        ExprKind::TupleField {
            base: Box::new(outer),
            index: 0,
        },
    );
    let pair = Expr::new(
        Ty::Tuple(vec![Ty::Param(0), Ty::Param(1)]),
        SpanId(0),
        ExprKind::Field {
            base: Box::new(inner),
            variant: 0,
            field: 0,
        },
    );
    let first = Expr::new(
        Ty::Param(0),
        SpanId(0),
        ExprKind::TupleField {
            base: Box::new(pair),
            index: 0,
        },
    );
    let first_place = Place {
        local: LocalId(1),
        projections: vec![
            Projection::Field {
                variant: 0,
                field: 0,
            },
            Projection::TupleField(0),
            Projection::Field {
                variant: 0,
                field: 0,
            },
            Projection::TupleField(0),
        ],
    };
    let mut untouched = first_place.clone();
    *untouched.projections.last_mut().unwrap() = Projection::TupleField(1);
    let block = Block::new(vec![
        marker(),
        Stmt::new(
            SpanId(0),
            StmtKind::Let {
                local: LocalId(2),
                init: Some(first),
            },
        ),
        marker(),
    ]);
    let ctx = Ctx::new(&source);
    let decl = &source.fns[1];
    let classifier = Classifier::new(&ctx, decl);
    let plan = analyze(&ctx, decl, &block, &classifier).unwrap();
    for index in [0, 2] {
        let selected = points(&plan, &block, index);
        assert!(!selected.contains(&first_place));
        assert!(
            selected.contains(&untouched),
            "the unconsumed sibling remains conditionally initialized and safe"
        );
    }
}
