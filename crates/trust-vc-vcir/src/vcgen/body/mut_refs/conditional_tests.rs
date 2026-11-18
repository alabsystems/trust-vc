//! Guarded resolution facts do not become reference/loan authority.
use super::*;
use crate::{AdtDecl, AdtId, BinOp, Body, ClauseAttrs, DefHash, FieldDecl, VariantDecl, VcCrate};

fn id() -> AdtId {
    AdtId(DefHash::new(182, 1))
}
fn source(parameter: u32) -> VcCrate {
    let mut source = crate::vcgen::closed_templates::tests::source();
    let decl = &mut source.fns[1];
    decl.mode = Mode::Exec;
    decl.type_params = vec!["A".into(), "B".into()];
    decl.locals[0].ty = Ty::Unit;
    decl.locals[0].mode = Mode::Exec;
    decl.locals[1].mode = Mode::Exec;
    decl.locals[1].ty = Ty::Adt(id(), vec![Ty::Adt(id(), vec![Ty::Param(parameter)])]);
    source.adts.push(AdtDecl {
        id: id(),
        name: "GuardedOption".into(),
        type_params: vec!["T".into()],
        span: SpanId(0),
        kind: crate::AdtKind::Enum,
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
fn target() -> Place {
    Place {
        local: LocalId(1),
        projections: vec![
            Projection::Field {
                variant: 0,
                field: 0,
            },
            Projection::Field {
                variant: 0,
                field: 0,
            },
        ],
    }
}
fn block() -> Block {
    Block::new(vec![Stmt::new(
        SpanId(0),
        StmtKind::Assume {
            expr: Expr::bool_lit(true, SpanId(0)),
            attrs: ClauseAttrs::default(),
        },
    )])
}

#[test]
fn nested_resolution_guards_every_parent_and_never_releases_or_caches_loans() {
    let source = source(0);
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let decl = &source.fns[1];
    let block = block();
    let mut generator = Gen::new(&ctx, &tables, decl);
    generator.resolution = resolution::analyze(&ctx, decl, &block, &generator.classifier).unwrap();
    generator.types = generator.fresh_types(decl).unwrap();
    let shape = ctx
        .shape(&decl.locals[1].ty, generator.types.owner(), SpanId(0))
        .unwrap();
    let value = generator.fresh(&shape, "source_before").unwrap();
    let reference = Term::var("existing_reference", Sort::Poly);
    let mut path = Path {
        declared: [LocalId(1)].into_iter().collect(),
        env: [(LocalId(1), value)].into_iter().collect(),
        live: true,
        loans: vec![Loan {
            places: vec![Place::local(LocalId(1))],
            reference: reference.clone(),
        }],
        resolved: vec![reference.clone()],
        ..Path::default()
    };
    generator
        .resolve_places(&mut path, &[target()], SpanId(0))
        .unwrap();
    assert_eq!(path.loans.len(), 1);
    assert_eq!(path.loans[0].reference, reference);
    assert_eq!(path.resolved, vec![reference]);
    let first = generator.facts.last().unwrap().hypothesis.term.clone();
    let Term::Implies(conditions, fact) = &first else {
        panic!("guarded resolution only")
    };
    let Term::And(conditions) = &**conditions else {
        panic!("both variant guards are mandatory")
    };
    assert_eq!(conditions.len(), 2);
    assert!(matches!(&**fact, Term::Call { name, .. } if name == "has_resolved"));
    // Replacing the source value must build new guards/selectors, without a
    // cache hit from the old SSA value or any reference-alias side effect.
    let next = generator.fresh(&shape, "source_after").unwrap();
    path.env.insert(LocalId(1), next);
    generator
        .resolve_places(&mut path, &[target()], SpanId(0))
        .unwrap();
    assert_ne!(first, generator.facts.last().unwrap().hypothesis.term);
    assert_eq!(path.loans.len(), 1);
    assert_eq!(path.resolved.len(), 1);
}

#[test]
fn another_current_field_type_cannot_reuse_an_abstract_resolution_target() {
    let old_source = source(0);
    let old_ctx = Ctx::new(&old_source);
    let old_decl = &old_source.fns[1];
    let block = block();
    let classifier = resolution::Classifier::new(&old_ctx, old_decl);
    let plan = resolution::analyze(&old_ctx, old_decl, &block, &classifier).unwrap();
    let current = source(1);
    let ctx = Ctx::new(&current);
    let tables = Tables::build(&ctx, &current);
    let decl = &current.fns[1];
    let mut generator = Gen::new(&ctx, &tables, decl);
    generator.resolution = plan;
    generator.types = generator.fresh_types(decl).unwrap();
    let shape = ctx
        .shape(&decl.locals[1].ty, generator.types.owner(), SpanId(0))
        .unwrap();
    let value = generator.fresh(&shape, "different_type").unwrap();
    let mut path = Path {
        declared: [LocalId(1)].into_iter().collect(),
        env: [(LocalId(1), value)].into_iter().collect(),
        live: true,
        ..Path::default()
    };
    let facts_before = generator.facts.len();
    let error = generator
        .resolve_places(&mut path, &[target()], SpanId(0))
        .unwrap_err();
    assert_eq!(error.tag, "resolution-type");
    assert_eq!(generator.facts.len(), facts_before);
}

#[test]
fn total_enum_selectors_are_logical_values_until_all_owned_parent_guards_hold() {
    let source = source(0);
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let decl = &source.fns[1];
    let block = block();
    let mut generator = Gen::new(&ctx, &tables, decl);
    generator.resolution = resolution::analyze(&ctx, decl, &block, &generator.classifier).unwrap();
    generator.types = generator.fresh_types(decl).unwrap();
    let root_ty = &decl.locals[1].ty;
    let shape = ctx
        .shape(root_ty, generator.types.owner(), SpanId(0))
        .unwrap();
    let value = generator.fresh(&shape, "owned_source").unwrap();
    let mut path = Path {
        declared: [LocalId(1)].into_iter().collect(),
        env: [(LocalId(1), value.clone())].into_iter().collect(),
        live: true,
        ..Path::default()
    };
    let read = Expr::read(target(), Ty::Param(0), SpanId(0));
    // Logical observation is legal; it must not become an owned transfer.
    let predicate = Expr::new(
        Ty::Bool,
        SpanId(0),
        ExprKind::HasResolved(Box::new(read.clone())),
    );
    assert!(generator.body_expr(&path, &predicate).is_ok());
    let facts_before = generator.facts.len();
    assert_eq!(
        generator.consume(&mut path, &read).unwrap_err().tag,
        "abstract-owned-origin"
    );
    assert_eq!(
        generator.facts.len(),
        facts_before,
        "origin checking adds no facts"
    );
    let Val::Leaf(outer) = ctx
        .test_enum(root_ty, &generator.types, 0, value.clone(), SpanId(0))
        .unwrap()
    else {
        panic!()
    };
    let inner_ty = Ty::Adt(id(), vec![Ty::Param(0)]);
    let inner = ctx
        .project_enum(root_ty, &generator.types, 0, 0, value.clone(), SpanId(0))
        .unwrap();
    let Val::Leaf(inner_some) = ctx
        .test_enum(&inner_ty, &generator.types, 0, inner.clone(), SpanId(0))
        .unwrap()
    else {
        panic!()
    };
    let Val::Leaf(inner_none) = ctx
        .test_enum(&inner_ty, &generator.types, 1, inner, SpanId(0))
        .unwrap()
    else {
        panic!()
    };
    path.guard = vec![inner_some.clone()];
    assert!(
        generator.consume(&mut path, &read).is_err(),
        "missing outer guard cannot be inferred from an inner selector"
    );
    path.guard = vec![outer.clone()];
    assert!(
        generator.consume(&mut path, &read).is_err(),
        "missing inner guard stays unknown"
    );
    path.guard = vec![Term::and([outer.clone(), inner_some])];
    generator.consume(&mut path, &read).unwrap();
    path.guard = vec![outer, inner_none.not()];
    generator.consume(&mut path, &read).unwrap();
    let next = generator.fresh(&shape, "reassigned_source").unwrap();
    path.env.insert(LocalId(1), next);
    assert!(
        generator.consume(&mut path, &read).is_err(),
        "old SSA guards cannot authorize a new value"
    );
}

#[test]
fn field_expression_and_constructor_branches_cannot_launder_unowned_selectors() {
    let mut source = source(0);
    // Both variants have a same-typed field: wrong-variant selectors are
    // well typed, so denial cannot be attributed to a missing field index.
    source.adts[0].variants[1].fields = source.adts[0].variants[0].fields.clone();
    let mut owned = source.fns[1].locals[1].clone();
    owned.ty = Ty::Param(0);
    owned.kind = LocalKind::Param;
    source.fns[1].locals.push(owned);
    source.fns[1].params.push(LocalId(2));
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let decl = &source.fns[1];
    let mut generator = Gen::new(&ctx, &tables, decl);
    let block = block();
    generator.resolution = resolution::analyze(&ctx, decl, &block, &generator.classifier).unwrap();
    generator.types = generator.fresh_types(decl).unwrap();
    let shape = ctx
        .shape(&decl.locals[1].ty, generator.types.owner(), SpanId(0))
        .unwrap();
    let root = generator.fresh(&shape, "unselected").unwrap();
    let argument_shape = ctx
        .shape(&Ty::Param(0), generator.types.owner(), SpanId(0))
        .unwrap();
    let argument = generator.fresh(&argument_shape, "owned_argument").unwrap();
    let mut path = Path {
        declared: [LocalId(1), LocalId(2)].into_iter().collect(),
        env: [(LocalId(1), root), (LocalId(2), argument)]
            .into_iter()
            .collect(),
        live: true,
        ..Path::default()
    };
    let inner = Expr::new(
        Ty::Adt(id(), vec![Ty::Param(0)]),
        SpanId(0),
        ExprKind::Field {
            base: Box::new(Expr::read(
                Place::local(LocalId(1)),
                decl.locals[1].ty.clone(),
                SpanId(0),
            )),
            variant: 0,
            field: 0,
        },
    );
    let selector = Expr::new(
        Ty::Param(0),
        SpanId(0),
        ExprKind::Field {
            base: Box::new(inner),
            variant: 0,
            field: 0,
        },
    );
    assert_eq!(
        generator.consume(&mut path, &selector).unwrap_err().tag,
        "abstract-owned-origin"
    );
    let ctor = Expr::new(
        Ty::Adt(id(), vec![Ty::Param(0)]),
        SpanId(0),
        ExprKind::Ctor {
            adt: id(),
            variant: 0,
            fields: vec![Expr::read(
                Place::local(LocalId(2)),
                Ty::Param(0),
                SpanId(0),
            )],
        },
    );
    let active = Expr::new(
        Ty::Param(0),
        SpanId(0),
        ExprKind::Field {
            base: Box::new(ctor.clone()),
            variant: 0,
            field: 0,
        },
    );
    generator.consume(&mut path, &active).unwrap();
    let inactive = Expr::new(
        Ty::Param(0),
        SpanId(0),
        ExprKind::Field {
            base: Box::new(ctor),
            variant: 1,
            field: 0,
        },
    );
    assert!(generator.consume(&mut path, &inactive).is_err());
    let branch = Expr::new(
        Ty::Param(0),
        SpanId(0),
        ExprKind::If {
            cond: Box::new(Expr::bool_lit(true, SpanId(0))),
            then_expr: Box::new(active),
            else_expr: Box::new(selector),
        },
    );
    generator.consume(&mut path, &branch).unwrap();
    let branch = Expr::new(
        Ty::Param(0),
        SpanId(0),
        ExprKind::If {
            cond: Box::new(Expr::bool_lit(false, SpanId(0))),
            then_expr: Box::new(branch),
            else_expr: Box::new(inactive),
        },
    );
    assert!(generator.consume(&mut path, &branch).is_err());
}

#[test]
fn enum_place_reads_are_typed_without_opening_storage_or_borrow_writes() {
    let mut source = source(0);
    let decl = &mut source.fns[1];
    let mut result = decl.locals[1].clone();
    result.kind = LocalKind::Let;
    result.ty = Ty::Param(0);
    decl.locals.push(result);
    let read = Expr::read(target(), Ty::Param(0), SpanId(0));
    decl.body = Body::Stmts(Block::new(vec![Stmt::new(
        SpanId(0),
        StmtKind::Let {
            local: LocalId(2),
            init: Some(read.clone()),
        },
    )]));
    assert!(
        crate::check_crate(&source).is_empty(),
        "represented enum read uses the exact substituted field type"
    );
    for projection in [
        Projection::Field {
            variant: 2,
            field: 0,
        },
        Projection::Field {
            variant: 0,
            field: 2,
        },
    ] {
        let mut invalid = source.clone();
        let mut place = target();
        place.projections[0] = projection;
        invalid.fns[1].body = Body::Stmts(Block::new(vec![Stmt::new(
            SpanId(0),
            StmtKind::Let {
                local: LocalId(2),
                init: Some(Expr::read(place, Ty::Param(0), SpanId(0))),
            },
        )]));
        assert!(crate::check_crate(&invalid)
            .iter()
            .any(|error| error.class == crate::WfClass::Malformed));
    }
    let mut wrong_arity = source.clone();
    wrong_arity.fns[1].locals[1].ty = Ty::Adt(id(), vec![]);
    assert!(crate::check_crate(&wrong_arity)
        .iter()
        .any(|error| error.class == crate::WfClass::Malformed));
    let mut write = source.clone();
    write.fns[1].locals[1].mutable = true;
    write.fns[1].body = Body::Stmts(Block::new(vec![Stmt::new(
        SpanId(0),
        StmtKind::Assign {
            place: target(),
            value: read,
        },
    )]));
    assert!(
        crate::check_crate(&write)
            .iter()
            .any(|error| error.class == crate::WfClass::Malformed),
        "read support grants no enum writeback"
    );
    let mut borrow = source.clone();
    borrow.fns[1].locals[1].mutable = true;
    borrow.fns[1].locals[2].ty = Ty::MutRef(Box::new(Ty::Param(0)));
    borrow.fns[1].body = Body::Stmts(Block::new(vec![Stmt::new(
        SpanId(0),
        StmtKind::BorrowMut {
            dest: LocalId(2),
            place: target(),
        },
    )]));
    assert!(
        crate::check_crate(&borrow)
            .iter()
            .any(|error| error.class == crate::WfClass::Malformed),
        "read support grants no mutable borrow"
    );
    let mut ghost_field = source.clone();
    ghost_field.adts[0].variants[0].fields[0].mode = Mode::Spec;
    assert!(
        !crate::check_crate(&ghost_field).is_empty(),
        "actual field modes still forbid a Spec value in Exec storage"
    );
}

#[test]
fn borrowed_generic_pointees_and_pure_snapshots_do_not_create_ownership() {
    let mut source = source(0);
    source.fns[1].locals[1].ty = Ty::MutRef(Box::new(Ty::Param(0)));
    source.fns[0].locals[0].ty = Ty::Param(0);
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let decl = &source.fns[1];
    let block = block();
    let mut generator = Gen::new(&ctx, &tables, decl);
    generator.resolution = resolution::analyze(&ctx, decl, &block, &generator.classifier).unwrap();
    generator.types = generator.fresh_types(decl).unwrap();
    let shape = ctx
        .shape(&decl.locals[1].ty, generator.types.owner(), SpanId(0))
        .unwrap();
    let value = generator.fresh(&shape, "borrowed").unwrap();
    let mut path = Path {
        declared: [LocalId(1)].into_iter().collect(),
        env: [(LocalId(1), value)].into_iter().collect(),
        live: true,
        ..Path::default()
    };
    let read = Expr::read(
        Place {
            local: LocalId(1),
            projections: vec![Projection::Deref],
        },
        Ty::Param(0),
        SpanId(0),
    );
    assert!(
        generator.body_expr(&path, &read).is_ok(),
        "logical current-value observation is preserved"
    );
    let before = generator.facts.len();
    assert_eq!(
        generator.consume(&mut path, &read).unwrap_err().tag,
        "abstract-owned-origin"
    );
    assert_eq!(generator.facts.len(), before);
    let pure = Expr::new(
        Ty::Param(0),
        SpanId(0),
        ExprKind::Call {
            callee: source.fns[0].id,
            type_args: vec![Ty::Param(0)],
            args: vec![read],
        },
    );
    assert_eq!(
        generator.consume(&mut path, &pure).unwrap_err().tag,
        "abstract-owned-origin"
    );
    assert_eq!(generator.facts.len(), before);
}

#[test]
fn checked_copy_dereferences_preserve_storage_loans_and_require_kept_available_sources() {
    for mutable in [false, true] {
        let mut source = source(0);
        source.fns[1].copy_premises = vec![Ty::Param(0)];
        source.fns[1].locals[1].ty = if mutable {
            Ty::MutRef(Box::new(Ty::Param(0)))
        } else {
            Ty::Ref {
                mutable: false,
                inner: Box::new(Ty::Param(0)),
            }
        };
        let ctx = Ctx::new(&source);
        let tables = Tables::build(&ctx, &source);
        let decl = &source.fns[1];
        let mut generator = Gen::new(&ctx, &tables, decl);
        let block = block();
        generator.resolution =
            resolution::analyze(&ctx, decl, &block, &generator.classifier).unwrap();
        generator.types = generator.fresh_types(decl).unwrap();
        let shape = ctx
            .shape(&decl.locals[1].ty, generator.types.owner(), SpanId(0))
            .unwrap();
        let value = generator.fresh(&shape, "copy_source").unwrap();
        let existing = Term::var("unrelated_existing_loan", Sort::Poly);
        let mut path = Path {
            declared: [LocalId(1)].into_iter().collect(),
            env: [(LocalId(1), value)].into_iter().collect(),
            live: true,
            resolved: vec![existing.clone()],
            ..Path::default()
        };
        let read = Expr::read(
            Place {
                local: LocalId(1),
                projections: vec![Projection::Deref],
            },
            Ty::Param(0),
            SpanId(0),
        );
        let before = generator.facts.len();
        generator.consume(&mut path, &read).unwrap();
        generator.consume(&mut path, &read).unwrap();
        assert!(path.moved.is_empty(), "copying creates no pointee move");
        assert!(path.loans.is_empty(), "copying creates no loan");
        assert_eq!(path.resolved, vec![existing]);
        assert_eq!(generator.facts.len(), before, "copy typing adds no facts");
        path.moved.push(Place::local(LocalId(1)));
        assert_eq!(
            generator.consume(&mut path, &read).unwrap_err().tag,
            "mut-ref-moved"
        );
        path.moved.clear();
        path.declared.clear();
        assert_eq!(
            generator.consume(&mut path, &read).unwrap_err().tag,
            "abstract-owned-origin"
        );
    }
    let mut source = source(0);
    source.fns[1].copy_premises = vec![Ty::Param(0)];
    source.fns[1].locals[1].mode = Mode::Spec;
    source.fns[1].locals[1].ty = Ty::Ref {
        mutable: false,
        inner: Box::new(Ty::Param(0)),
    };
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let decl = &source.fns[1];
    let mut generator = Gen::new(&ctx, &tables, decl);
    let block = block();
    generator.resolution = resolution::analyze(&ctx, decl, &block, &generator.classifier).unwrap();
    generator.types = generator.fresh_types(decl).unwrap();
    let shape = ctx
        .shape(&decl.locals[1].ty, generator.types.owner(), SpanId(0))
        .unwrap();
    let value = generator.fresh(&shape, "logical_copy_source").unwrap();
    let mut path = Path {
        declared: [LocalId(1)].into_iter().collect(),
        env: [(LocalId(1), value)].into_iter().collect(),
        live: true,
        ..Path::default()
    };
    let read = Expr::read(
        Place {
            local: LocalId(1),
            projections: vec![Projection::Deref],
        },
        Ty::Param(0),
        SpanId(0),
    );
    assert_eq!(
        generator.consume(&mut path, &read).unwrap_err().tag,
        "abstract-owned-origin"
    );
}

#[test]
fn copy_premises_do_not_make_inactive_enum_selectors_owned() {
    let mut source = source(0);
    source.fns[1].copy_premises = vec![Ty::Param(0)];
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let decl = &source.fns[1];
    let mut generator = Gen::new(&ctx, &tables, decl);
    let block = block();
    generator.resolution = resolution::analyze(&ctx, decl, &block, &generator.classifier).unwrap();
    generator.types = generator.fresh_types(decl).unwrap();
    let shape = ctx
        .shape(&decl.locals[1].ty, generator.types.owner(), SpanId(0))
        .unwrap();
    let value = generator.fresh(&shape, "inactive_copy_source").unwrap();
    let mut path = Path {
        declared: [LocalId(1)].into_iter().collect(),
        env: [(LocalId(1), value)].into_iter().collect(),
        live: true,
        ..Path::default()
    };
    let read = Expr::read(target(), Ty::Param(0), SpanId(0));
    let before = generator.facts.len();
    assert_eq!(
        generator.consume(&mut path, &read).unwrap_err().tag,
        "abstract-owned-origin"
    );
    assert_eq!(generator.facts.len(), before);
}

#[test]
fn copied_referenced_enum_fields_need_every_current_ssa_parent_guard() {
    let mut source = source(0);
    source.fns[1].copy_premises = vec![Ty::Param(0)];
    let root_ty = source.fns[1].locals[1].ty.clone();
    source.fns[1].locals[1].ty = Ty::Ref {
        mutable: false,
        inner: Box::new(root_ty.clone()),
    };
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let decl = &source.fns[1];
    let mut generator = Gen::new(&ctx, &tables, decl);
    let block = block();
    generator.resolution = resolution::analyze(&ctx, decl, &block, &generator.classifier).unwrap();
    generator.types = generator.fresh_types(decl).unwrap();
    let shape = ctx
        .shape(&decl.locals[1].ty, generator.types.owner(), SpanId(0))
        .unwrap();
    let value = generator.fresh(&shape, "referenced_enum").unwrap();
    let mut place = target();
    place.projections.insert(0, Projection::Deref);
    let read = Expr::read(place, Ty::Param(0), SpanId(0));
    let mut path = Path {
        declared: [LocalId(1)].into_iter().collect(),
        env: [(LocalId(1), value.clone())].into_iter().collect(),
        live: true,
        ..Path::default()
    };
    let Val::Leaf(outer) = ctx
        .test_enum(&root_ty, &generator.types, 0, value.clone(), SpanId(0))
        .unwrap()
    else {
        panic!()
    };
    let inner = ctx
        .project_enum(&root_ty, &generator.types, 0, 0, value, SpanId(0))
        .unwrap();
    let Val::Leaf(inner_guard) = ctx
        .test_enum(
            &Ty::Adt(id(), vec![Ty::Param(0)]),
            &generator.types,
            0,
            inner,
            SpanId(0),
        )
        .unwrap()
    else {
        panic!()
    };
    assert!(generator.consume(&mut path, &read).is_err());
    path.guard = vec![outer.clone()];
    assert!(generator.consume(&mut path, &read).is_err());
    path.guard = vec![outer, inner_guard];
    let before = generator.facts.len();
    generator.consume(&mut path, &read).unwrap();
    assert_eq!(generator.facts.len(), before);
    let next = generator.fresh(&shape, "replaced_referenced_enum").unwrap();
    path.env.insert(LocalId(1), next);
    assert!(
        generator.consume(&mut path, &read).is_err(),
        "stale SSA variant tests cannot authorize a copy"
    );
}

fn copy_forward_source(assertion: bool) -> VcCrate {
    let mut source = source(0);
    let sink = &mut source.fns[0];
    sink.mode = Mode::Exec;
    for local in &mut sink.locals {
        local.mode = Mode::Exec;
    }
    sink.locals[0].ty = Ty::Unit;
    sink.body = Body::Stmts(Block::new(vec![Stmt::new(
        SpanId(0),
        StmtKind::Return {
            value: None,
            site: crate::SiteId(0),
        },
    )]));
    let sink_id = sink.id;
    let forward = &mut source.fns[1];
    forward.copy_premises = vec![Ty::Param(0)];
    forward.locals[1].ty = Ty::Ref {
        mutable: false,
        inner: Box::new(Ty::Param(0)),
    };
    // There is deliberately no owned abstract result or temporary. The real
    // consuming argument below is what needs the checked copied value.
    forward.body = Body::Stmts(Block::new(vec![
        Stmt::new(
            SpanId(0),
            StmtKind::Call {
                callee: sink_id,
                type_args: vec![Ty::Param(0)],
                args: vec![Expr::read(
                    Place {
                        local: LocalId(1),
                        projections: vec![Projection::Deref],
                    },
                    Ty::Param(0),
                    SpanId(0),
                )],
                dest: None,
                site: crate::SiteId(0),
            },
        ),
        Stmt::new(
            SpanId(0),
            StmtKind::Assert {
                expr: Expr::bool_lit(assertion, SpanId(0)),
                site: crate::SiteId(1),
                attrs: ClauseAttrs::default(),
            },
        ),
        Stmt::new(
            SpanId(0),
            StmtKind::Return {
                value: None,
                site: crate::SiteId(2),
            },
        ),
    ]));
    source
}

#[test]
fn default_generation_checks_copy_only_forward_calls_and_their_false_twins() {
    for assertion in [true, false] {
        let source = copy_forward_source(assertion);
        assert!(
            crate::check_crate(&source).is_empty(),
            "{:?}",
            crate::check_crate(&source)
        );
        let generated = crate::vcgen::generate(&source);
        let (_, crate::vcgen::FnVcs::Checks(checks)) = generated
            .fns
            .iter()
            .find(|(id, _)| *id == source.fns[1].id)
            .unwrap()
        else {
            panic!("{generated:?}")
        };
        let assertions = checks
            .iter()
            .filter(|check| matches!(check.kind, CheckKind::Assert { .. }))
            .collect::<Vec<_>>();
        assert_eq!(assertions.len(), 1);
        assert_eq!(assertions[0].query.goal, Term::Bool(assertion));
        #[cfg(feature = "solve")]
        {
            let result = crate::solve::check(
                &assertions[0].query,
                "Copy-only forwarding",
                &crate::solve::Limits::default(),
            );
            if assertion {
                assert!(
                    matches!(result, crate::solve::Verdict::Proved { .. }),
                    "{result:?}"
                );
            } else {
                assert!(
                    matches!(result, crate::solve::Verdict::Refuted { .. }),
                    "{result:?}"
                );
            }
        }
    }
}

#[test]
fn exhausted_retained_copy_work_adds_no_origin_fact_or_loan_effect() {
    let source = copy_forward_source(true);
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let decl = &source.fns[1];
    let Body::Stmts(block) = &decl.body else {
        unreachable!()
    };
    let mut generator = Gen::new(&ctx, &tables, decl);
    generator.resolution = resolution::analyze(&ctx, decl, block, &generator.classifier).unwrap();
    generator.types = generator.fresh_types(decl).unwrap();
    let shape = ctx
        .shape(&decl.locals[1].ty, generator.types.owner(), SpanId(0))
        .unwrap();
    let value = generator.fresh(&shape, "exhausted_shared_copy").unwrap();
    let mut path = Path {
        declared: [LocalId(1)].into_iter().collect(),
        env: [(LocalId(1), value)].into_iter().collect(),
        live: true,
        ..Path::default()
    };
    let StmtKind::Call { args, .. } = &block.stmts[0].kind else {
        unreachable!()
    };
    let remaining = generator.resolution.remaining().unwrap().get();
    generator.resolution.charge(remaining, SpanId(0)).unwrap();
    let before = generator.facts.len();
    assert_eq!(
        generator.consume(&mut path, &args[0]).unwrap_err().tag,
        "resolution-size"
    );
    assert_eq!(generator.facts.len(), before);
    assert!(path.moved.is_empty() && path.loans.is_empty() && path.resolved.is_empty());
    assert_eq!(generator.resolution.remaining().unwrap().get(), 0);
}

#[test]
fn last_variant_origin_requires_every_other_variant_to_be_excluded() {
    let mut source = source(0);
    source.adts[0].variants.push(VariantDecl {
        name: "Third".into(),
        fields: vec![],
    });
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let decl = &source.fns[1];
    let block = block();
    let mut generator = Gen::new(&ctx, &tables, decl);
    generator.resolution = resolution::analyze(&ctx, decl, &block, &generator.classifier).unwrap();
    generator.types = generator.fresh_types(decl).unwrap();
    let root_ty = &decl.locals[1].ty;
    let shape = ctx
        .shape(root_ty, generator.types.owner(), SpanId(0))
        .unwrap();
    let value = generator.fresh(&shape, "three_tags").unwrap();
    let mut path = Path {
        declared: [LocalId(1)].into_iter().collect(),
        env: [(LocalId(1), value.clone())].into_iter().collect(),
        live: true,
        ..Path::default()
    };
    let read = Expr::read(
        Place {
            local: LocalId(1),
            projections: vec![Projection::Field {
                variant: 0,
                field: 0,
            }],
        },
        Ty::Adt(id(), vec![Ty::Param(0)]),
        SpanId(0),
    );
    let Val::Leaf(second) = ctx
        .test_enum(root_ty, &generator.types, 1, value.clone(), SpanId(0))
        .unwrap()
    else {
        panic!()
    };
    let Val::Leaf(third) = ctx
        .test_enum(root_ty, &generator.types, 2, value, SpanId(0))
        .unwrap()
    else {
        panic!()
    };
    path.guard = vec![second.not()];
    assert!(
        generator.consume(&mut path, &read).is_err(),
        "one excluded tag leaves another possible tag"
    );
    path.guard.push(third.not());
    generator.consume(&mut path, &read).unwrap();
}

#[test]
fn old_enum_field_reads_keep_their_existing_pure_observation_semantics() {
    let mut source = source(0);
    let function = &mut source.fns[1];
    function.mode = Mode::Spec;
    function.locals[0].ty = Ty::Bool;
    for local in &mut function.locals {
        local.mode = Mode::Spec;
    }
    let old = Expr::new(Ty::Param(0), SpanId(0), ExprKind::Old(target()));
    function.body = Body::Spec(Expr::binary(
        BinOp::Eq,
        old.clone(),
        old,
        Ty::Bool,
        SpanId(0),
    ));
    assert!(
        crate::check_crate(&source).is_empty(),
        "old() remains a logical read of an actual parameter field"
    );
}

#[test]
fn inline_branch_condition_cannot_refill_the_original_resolution_budget() {
    fn condition(depth: usize) -> Expr {
        if depth == 0 {
            let value = Expr::read(Place::local(LocalId(1)), Ty::Param(0), SpanId(0));
            return Expr::binary(BinOp::Eq, value.clone(), value, Ty::Bool, SpanId(0));
        }
        Expr::binary(
            BinOp::And,
            condition(depth - 1),
            condition(depth - 1),
            Ty::Bool,
            SpanId(0),
        )
    }
    let mut source = source(0);
    source.fns[0].attrs.inline = true;
    source.fns[0].body = Body::Spec(condition(7));
    source.fns[1].locals[1].ty = Ty::Param(0);
    assert!(crate::check_crate(&source).is_empty());
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let decl = &source.fns[1];
    let block = block();
    let mut generator = Gen::new(&ctx, &tables, decl);
    generator.resolution = resolution::analyze(&ctx, decl, &block, &generator.classifier).unwrap();
    generator.types = generator.fresh_types(decl).unwrap();
    let shape = ctx
        .shape(&Ty::Param(0), generator.types.owner(), SpanId(0))
        .unwrap();
    let value = generator.fresh(&shape, "actual_owned_value").unwrap();
    let mut path = Path {
        declared: [LocalId(1)].into_iter().collect(),
        env: [(LocalId(1), value)].into_iter().collect(),
        live: true,
        ..Path::default()
    };
    let read = Expr::read(Place::local(LocalId(1)), Ty::Param(0), SpanId(0));
    let expression = Expr::new(
        Ty::Param(0),
        SpanId(0),
        ExprKind::If {
            cond: Box::new(Expr::new(
                Ty::Bool,
                SpanId(0),
                ExprKind::Call {
                    callee: source.fns[0].id,
                    type_args: vec![Ty::Param(0)],
                    args: vec![read.clone()],
                },
            )),
            then_expr: Box::new(read.clone()),
            else_expr: Box::new(read),
        },
    );
    generator.consume(&mut path, &expression).unwrap();
    let work = generator.resolution.shared_work().unwrap();
    assert!(std::ptr::eq(
        work.as_ref(),
        generator.resolution.remaining().unwrap()
    ));
    let remaining = work.get();
    assert!(remaining > 512);
    generator
        .resolution
        .charge(remaining - 512, SpanId(0))
        .unwrap();
    let before = generator.facts.len();
    let error = generator.consume(&mut path, &expression).unwrap_err();
    assert_eq!(
        error.tag, "inline-size",
        "the actual inline expansion spends the same exhausted ledger"
    );
    assert!(work.get() < 512);
    assert_eq!(generator.facts.len(), before);
}

#[test]
fn malformed_constructor_and_tuple_bases_cannot_bypass_origin_typing() {
    let mut source = source(0);
    source.fns[1].locals[1].ty = Ty::Param(0);
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let decl = &source.fns[1];
    let block = block();
    let mut generator = Gen::new(&ctx, &tables, decl);
    generator.resolution = resolution::analyze(&ctx, decl, &block, &generator.classifier).unwrap();
    generator.types = generator.fresh_types(decl).unwrap();
    let shape = ctx
        .shape(&Ty::Param(0), generator.types.owner(), SpanId(0))
        .unwrap();
    let value = generator.fresh(&shape, "owned_input").unwrap();
    let mut path = Path {
        declared: [LocalId(1)].into_iter().collect(),
        env: [(LocalId(1), value)].into_iter().collect(),
        live: true,
        ..Path::default()
    };
    let read = Expr::read(Place::local(LocalId(1)), Ty::Param(0), SpanId(0));
    let ctor = Expr::new(
        Ty::Unit,
        SpanId(0),
        ExprKind::Ctor {
            adt: id(),
            variant: 0,
            fields: vec![read.clone()],
        },
    );
    let selector = Expr::new(
        Ty::Param(0),
        SpanId(0),
        ExprKind::Field {
            base: Box::new(ctor),
            variant: 0,
            field: 0,
        },
    );
    assert_eq!(
        generator.consume(&mut path, &selector).unwrap_err().tag,
        "abstract-owned-origin"
    );
    let tuple = Expr::new(Ty::Unit, SpanId(0), ExprKind::Tuple(vec![read]));
    let selector = Expr::new(
        Ty::Param(0),
        SpanId(0),
        ExprKind::TupleField {
            base: Box::new(tuple),
            index: 0,
        },
    );
    assert_eq!(
        generator.consume(&mut path, &selector).unwrap_err().tag,
        "abstract-owned-origin"
    );
}

#[test]
fn abstract_emission_prices_the_actual_path_guards_before_copying_or_adding_a_fact() {
    let source = source(0);
    let ctx = Ctx::new(&source);
    let tables = Tables::build(&ctx, &source);
    let decl = &source.fns[1];
    let block = block();
    let mut generator = Gen::new(&ctx, &tables, decl);
    generator.resolution = resolution::analyze(&ctx, decl, &block, &generator.classifier).unwrap();
    generator.types = generator.fresh_types(decl).unwrap();
    let shape = ctx
        .shape(&decl.locals[1].ty, generator.types.owner(), SpanId(0))
        .unwrap();
    let value = generator.fresh(&shape, "source_under_large_guard").unwrap();
    let mut path = Path {
        declared: [LocalId(1)].into_iter().collect(),
        env: [(LocalId(1), value)].into_iter().collect(),
        live: true,
        guard: vec![Term::And(vec![
            Term::var("actual_guard_term", Sort::Bool);
            4096
        ])],
        ..Path::default()
    };
    let remaining = generator.resolution.remaining().unwrap().get();
    generator
        .resolution
        .charge(remaining - 2048, SpanId(0))
        .unwrap();
    let before = generator.facts.len();
    let error = generator
        .resolve_places(&mut path, &[target()], SpanId(0))
        .unwrap_err();
    assert_eq!(error.tag, "inline-size");
    assert_eq!(generator.facts.len(), before);
}
