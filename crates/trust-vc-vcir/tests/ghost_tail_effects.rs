//! Proof-block tails retain their original producer mode and raw prophecy.
use trust_vc_vcir::vcgen::{self, FnVcs};
use trust_vc_vcir::wf::{ghost_tail_modes, GhostTailModeClass as Class};
use trust_vc_vcir::*;

#[path = "ghost_tail_effects/helpers.rs"]
mod helpers;
use helpers::*;

#[test]
fn implicit_proof_unit_tail_is_checked_before_unit_consumption() {
    let k = call_tail(2);
    rejects_wrap(&k);
    let observations = ghost_tail_modes(&k);
    assert_eq!(observations.len(), 1);
    assert_eq!(observations[0].class, Some(Class::NonSpec));
}
#[test]
fn written_spec_unit_return_retains_its_raw_spec_mode() {
    let k = call_tail(3);
    accepted(&k);
    assert_eq!(ghost_tail_modes(&k)[0].class, Some(Class::Spec));
}
#[test]
fn a_semicolon_discards_the_proof_call_effect() {
    let mut f = client();
    let Body::Stmts(body) = &mut f.body else {
        panic!()
    };
    body.stmts
        .push(stmt(StmtKind::Ghost(Block::new(vec![invoke(2, None, 0)]))));
    let k = source(f);
    accepted(&k);
    assert!(ghost_tail_modes(&k).is_empty());
}
#[test]
fn unit_if_joins_arm_modes_without_promoting_the_guard_mode() {
    let mut f = client();
    tail(
        &mut f,
        vec![],
        Expr::new(
            Ty::Unit,
            sp(0),
            ExprKind::If {
                cond: Box::new(prophetic()),
                then_expr: Box::new(unit()),
                else_expr: Box::new(unit()),
            },
        ),
    );
    let k = source(f);
    rejects_wrap(&k);
    assert_eq!(ghost_tail_modes(&k)[0].class, Some(Class::NonSpec));
}
#[test]
fn mixed_proof_and_spec_branch_results_join_to_spec() {
    let mut f = client();
    let result = add_temp(&mut f);
    tail(
        &mut f,
        vec![
            declaration(result, None),
            stmt(StmtKind::If {
                cond: prophetic(),
                then_block: Block::new(vec![invoke(2, Some(result), 0)]),
                else_block: Block::new(vec![invoke(3, Some(result), 1)]),
            }),
        ],
        read(result),
    );
    let k = source(f);
    accepted(&k);
    assert_eq!(ghost_tail_modes(&k)[0].class, Some(Class::Spec));
}
#[test]
fn authored_unit_place_reads_receive_expected_spec_mode() {
    let mut f = client();
    let name = LocalId(f.locals.len() as u32);
    let mut decl = local(Ty::Unit, Mode::Spec, LocalKind::Let);
    decl.prophecy = DeclProphecy::Prophetic;
    f.locals.push(decl);
    tail(&mut f, vec![declaration(name, Some(unit()))], read(name));
    let k = source(f);
    accepted(&k);
    assert_eq!(ghost_tail_modes(&k)[0].class, Some(Class::Spec));
}
#[test]
fn a_unit_literal_is_non_spec_and_has_no_prophecy() {
    let mut f = client();
    tail(&mut f, vec![], unit());
    let k = source(f);
    accepted(&k);
    assert_eq!(ghost_tail_modes(&k)[0].class, Some(Class::NonSpec));
}
#[test]
fn uninitialized_temporary_never_defaults_to_spec() {
    let mut f = client();
    let value = add_temp(&mut f);
    tail(&mut f, vec![declaration(value, None)], read(value));
    malformed(&source(f));
}
#[test]
fn conflicting_sequential_producers_do_not_overwrite_a_raw_mode_origin() {
    let mut f = client();
    let value = add_temp(&mut f);
    tail(
        &mut f,
        vec![
            declaration(value, None),
            invoke(2, Some(value), 0),
            invoke(3, Some(value), 1),
        ],
        read(value),
    );
    malformed(&source(f));
}
#[test]
fn partial_branch_initialization_does_not_supply_a_spec_origin() {
    let mut f = client();
    let value = add_temp(&mut f);
    tail(
        &mut f,
        vec![
            declaration(value, None),
            stmt(StmtKind::If {
                cond: Expr::bool_lit(true, sp(0)),
                then_block: Block::new(vec![invoke(3, Some(value), 0)]),
                else_block: Block::default(),
            }),
        ],
        read(value),
    );
    malformed(&source(f));
}
#[test]
fn spec_temporary_storage_does_not_relabel_an_exec_literal_producer() {
    let mut f = client();
    let value = add_temp(&mut f);
    tail(&mut f, vec![declaration(value, Some(unit()))], read(value));
    let k = source(f);
    accepted(&k);
    assert_eq!(ghost_tail_modes(&k)[0].class, Some(Class::NonSpec));
}
#[test]
fn proof_tail_must_have_unit_type() {
    let mut f = client();
    tail(&mut f, vec![], Expr::bool_lit(false, sp(0)));
    let k = source(f);
    assert!(check_crate(&k)
        .iter()
        .any(|error| error.class == WfClass::Malformed));
    assert_eq!(ghost_tail_modes(&k)[0].class, None);
}
#[test]
fn retaining_a_pure_unit_tail_preserves_the_actual_prefix_vc_roster() {
    let mut f = client();
    tail(
        &mut f,
        vec![stmt(StmtKind::Assert {
            expr: Expr::bool_lit(true, sp(0)),
            site: SiteId(0),
            attrs: ClauseAttrs::default(),
        })],
        call(4, Ty::Unit),
    );
    let k = source(f);
    accepted(&k);
    let generated = vcgen::generate(&k);
    let Some(FnVcs::Checks(checks)) = generated.get(id(5)) else {
        panic!("{generated:?}")
    };
    assert_eq!(checks.len(), 1);
    assert_eq!(checks[0].site, SiteId(0));
}

#[test]
fn nested_semicolon_block_retains_the_exact_non_spec_wrapper_policy() {
    let mut f = client();
    tail(
        &mut f,
        vec![stmt(StmtKind::Block(Block::new(vec![invoke(2, None, 0)])))],
        unit(),
    );
    let k = source(f);
    accepted(&k);
    assert_eq!(ghost_tail_modes(&k)[0].class, Some(Class::NonSpec));
}
#[test]
fn a_pure_call_uses_its_real_return_binder_mode() {
    let mut f = client();
    tail(&mut f, vec![], call(4, Ty::Unit));
    let mut k = source(f);
    k.fns[3].locals[0].mode = Mode::Exec;
    rejects_wrap(&k);
    assert_eq!(ghost_tail_modes(&k)[0].class, Some(Class::NonSpec));
}
#[test]
fn computed_unit_field_reads_have_spec_mode_with_known_producer_origins() {
    let mut f = client();
    let value = add_temp(&mut f);
    let tuple = Expr::new(
        Ty::Tuple(vec![Ty::Unit]),
        sp(0),
        ExprKind::Tuple(vec![read(value)]),
    );
    let projection = Expr::new(
        Ty::Unit,
        sp(0),
        ExprKind::TupleField {
            base: Box::new(tuple),
            index: 0,
        },
    );
    tail(
        &mut f,
        vec![declaration(value, None), invoke(2, Some(value), 0)],
        projection,
    );
    let k = source(f);
    accepted(&k);
    assert_eq!(ghost_tail_modes(&k)[0].class, Some(Class::Spec));
}
#[test]
fn a_projection_cannot_license_an_unknown_saved_value() {
    let mut f = client();
    let value = add_temp(&mut f);
    let tuple = Expr::new(
        Ty::Tuple(vec![Ty::Unit]),
        sp(0),
        ExprKind::Tuple(vec![read(value)]),
    );
    let projection = Expr::new(
        Ty::Unit,
        sp(0),
        ExprKind::TupleField {
            base: Box::new(tuple),
            index: 0,
        },
    );
    tail(&mut f, vec![declaration(value, None)], projection);
    malformed(&source(f));
}

#[test]
fn a_computed_tuple_call_supplies_checked_unit_field_provenance() {
    let mut f = client();
    let tuple_ty = Ty::Tuple(vec![Ty::Unit]);
    let value = LocalId(f.locals.len() as u32);
    let mut decl = local(tuple_ty.clone(), Mode::Spec, LocalKind::Temp);
    decl.prophecy = DeclProphecy::DelayedInfer;
    f.locals.push(decl);
    let projection = Expr::new(
        Ty::Unit,
        sp(0),
        ExprKind::TupleField {
            base: Box::new(Expr::read(Place::local(value), tuple_ty.clone(), sp(0))),
            index: 0,
        },
    );
    tail(
        &mut f,
        vec![declaration(value, None), invoke(6, Some(value), 0)],
        projection,
    );
    let mut k = source(f);
    let mut producer = function(6, Mode::Proof, tuple_ty.clone(), Mode::Spec);
    producer
        .locals
        .push(local(Ty::Bool, Mode::Spec, LocalKind::Param));
    producer.params.push(LocalId(1));
    producer.body = Body::Stmts(Block::new(vec![stmt(StmtKind::Return {
        value: Some(Expr::new(tuple_ty, sp(0), ExprKind::Tuple(vec![unit()]))),
        site: SiteId(99),
    })]));
    k.fns.insert(4, producer);
    accepted(&k);
    assert_eq!(ghost_tail_modes(&k)[0].class, Some(Class::Spec));
}
#[test]
fn an_uninitialized_tuple_temporary_cannot_license_a_unit_field() {
    let mut f = client();
    let tuple_ty = Ty::Tuple(vec![Ty::Unit]);
    let value = LocalId(f.locals.len() as u32);
    let mut decl = local(tuple_ty.clone(), Mode::Spec, LocalKind::Temp);
    decl.prophecy = DeclProphecy::DelayedInfer;
    f.locals.push(decl);
    let projection = Expr::new(
        Ty::Unit,
        sp(0),
        ExprKind::TupleField {
            base: Box::new(Expr::read(Place::local(value), tuple_ty, sp(0))),
            index: 0,
        },
    );
    tail(&mut f, vec![declaration(value, None)], projection);
    malformed(&source(f));
}

#[test]
fn generic_spec_identity_unit_retains_its_spec_tail_mode() {
    let mut identity = function(6, Mode::Spec, Ty::Param(0), Mode::Spec);
    identity.type_params.push("T".into());
    identity
        .locals
        .push(local(Ty::Param(0), Mode::Spec, LocalKind::Param));
    identity.params.push(LocalId(1));
    identity.attrs.prophetic = true;
    identity.body = Body::Spec(Expr::read(Place::local(LocalId(1)), Ty::Param(0), sp(0)));
    let value = Expr::new(
        Ty::Unit,
        sp(0),
        ExprKind::Call {
            callee: id(6),
            type_args: vec![Ty::Unit],
            args: vec![unit()],
        },
    );
    let mut f = client();
    tail(&mut f, vec![], value);
    let mut k = source(f);
    k.fns.insert(4, identity);
    accepted(&k);
    assert_eq!(ghost_tail_modes(&k)[0].class, Some(Class::Spec));
}

#[test]
fn generic_tracked_return_instantiated_as_unit_keeps_signature_effect_policy() {
    let mut producer = function(6, Mode::Proof, Ty::Param(0), Mode::Proof);
    producer.type_params.push("T".into());
    producer.attrs.external_body = true;
    producer
        .locals
        .push(local(Ty::Bool, Mode::Spec, LocalKind::Param));
    producer.params.push(LocalId(1));
    let mut f = client();
    let value = add_temp(&mut f);
    let invocation = stmt(StmtKind::Call {
        callee: id(6),
        type_args: vec![Ty::Unit],
        args: vec![prophetic()],
        dest: Some(Place::local(value)),
        site: SiteId(0),
    });
    tail(
        &mut f,
        vec![declaration(value, None), invocation],
        read(value),
    );
    let mut k = source(f);
    k.fns.insert(4, producer);
    let errors = check_crate(&k);
    assert_eq!(errors.len(), 2, "{errors:?}");
    assert!(errors.iter().all(|error| error.class == WfClass::User));
    assert!(
        errors.iter().any(|error| error
            .message
            .contains("argument to proof-mode function with tracked parameters")),
        "{errors:?}"
    );
    rejects_wrap(&k);
    assert_eq!(ghost_tail_modes(&k)[0].class, Some(Class::NonSpec));
}

#[test]
fn a_generic_tuple_return_supplies_instantiated_unit_field_provenance() {
    let generic_tuple = Ty::Tuple(vec![Ty::Param(0)]);
    let mut producer = function(6, Mode::Proof, generic_tuple.clone(), Mode::Spec);
    producer.type_params.push("T".into());
    producer
        .locals
        .push(local(Ty::Bool, Mode::Spec, LocalKind::Param));
    producer
        .locals
        .push(local(Ty::Param(0), Mode::Spec, LocalKind::Param));
    producer.params = vec![LocalId(1), LocalId(2)];
    let field = Expr::read(Place::local(LocalId(2)), Ty::Param(0), sp(0));
    producer.body = Body::Stmts(Block::new(vec![stmt(StmtKind::Return {
        value: Some(Expr::new(
            generic_tuple,
            sp(0),
            ExprKind::Tuple(vec![field]),
        )),
        site: SiteId(99),
    })]));
    let mut f = client();
    let tuple_ty = Ty::Tuple(vec![Ty::Unit]);
    let value = LocalId(f.locals.len() as u32);
    let mut decl = local(tuple_ty.clone(), Mode::Spec, LocalKind::Temp);
    decl.prophecy = DeclProphecy::DelayedInfer;
    f.locals.push(decl);
    let invocation = stmt(StmtKind::Call {
        callee: id(6),
        type_args: vec![Ty::Unit],
        args: vec![prophetic(), unit()],
        dest: Some(Place::local(value)),
        site: SiteId(0),
    });
    let projection = Expr::new(
        Ty::Unit,
        sp(0),
        ExprKind::TupleField {
            base: Box::new(Expr::read(Place::local(value), tuple_ty, sp(0))),
            index: 0,
        },
    );
    tail(
        &mut f,
        vec![declaration(value, None), invocation],
        projection,
    );
    let mut k = source(f);
    k.fns.insert(4, producer);
    accepted(&k);
    assert_eq!(ghost_tail_modes(&k)[0].class, Some(Class::Spec));
}

#[test]
fn malformed_generic_return_origins_never_supply_spec_mode() {
    for (formal, type_args, diagnostic) in [
        (
            Ty::Param(1),
            vec![Ty::Unit],
            "type parameter 1 is not in scope",
        ),
        (
            Ty::Param(0),
            vec![Ty::Unit, Ty::Unit],
            "takes 1 type arguments, not 2",
        ),
    ] {
        let mut producer = function(6, Mode::Spec, formal, Mode::Spec);
        producer.type_params.push("T".into());
        producer.attrs.external_body = true;
        let value = Expr::new(
            Ty::Unit,
            sp(0),
            ExprKind::Call {
                callee: id(6),
                type_args,
                args: vec![],
            },
        );
        let mut f = client();
        tail(&mut f, vec![], value);
        let mut k = source(f);
        k.fns.insert(4, producer);
        malformed(&k);
        assert!(
            check_crate(&k)
                .iter()
                .any(|error| error.message.contains(diagnostic)),
            "{:?}",
            check_crate(&k)
        );
    }
}
