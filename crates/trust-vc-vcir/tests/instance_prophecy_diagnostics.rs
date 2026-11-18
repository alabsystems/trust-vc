//! Per-function effect diagnostics retain real generic-instance identities.
use trust_vc_vcir::wf::{function_prophecy_diagnostics, ghost_tail_modes, GhostTailModeClass};
use trust_vc_vcir::*;

fn id(value: u64) -> FnId {
    FnId(DefHash::new(157, value))
}

fn local(ty: Ty, mode: Mode, kind: LocalKind) -> LocalDecl {
    LocalDecl {
        name: "value".into(),
        ty,
        mode,
        prophecy: if kind == LocalKind::Temp {
            DeclProphecy::DelayedInfer
        } else {
            DeclProphecy::Default
        },
        mutable: kind == LocalKind::Temp,
        kind,
        span: SpanId(0),
    }
}

fn function(value: u64, mode: Mode, ty: Ty, return_mode: Mode) -> FnDecl {
    FnDecl {
        id: id(value),
        name: format!("function{value}"),
        span: SpanId(0),
        mode,
        role: FnRole::Item,
        kind: FnKind::Function,
        copy_premises: Vec::new(),
        type_params: vec![],
        locals: vec![local(ty, return_mode, LocalKind::Return)],
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
        body: Body::None,
    }
}

fn source(spec_return: bool) -> VcCrate {
    let mut prophetic = function(1, Mode::Spec, Ty::Bool, Mode::Spec);
    prophetic.attrs.prophetic = true;
    prophetic.body = Body::Spec(Expr::bool_lit(true, SpanId(0)));
    let mut lemma = function(
        2,
        Mode::Proof,
        Ty::Unit,
        if spec_return { Mode::Spec } else { Mode::Proof },
    );
    lemma
        .locals
        .push(local(Ty::Bool, Mode::Spec, LocalKind::Param));
    lemma.params.push(LocalId(1));
    let mut original = function(3, Mode::Exec, Ty::Unit, Mode::Exec);
    original.type_params.push("T".into());
    original
        .locals
        .push(local(Ty::Unit, Mode::Spec, LocalKind::Temp));
    let call = Stmt::new(
        SpanId(11),
        StmtKind::Call {
            callee: id(2),
            type_args: vec![],
            args: vec![Expr::new(
                Ty::Bool,
                SpanId(10),
                ExprKind::Call {
                    callee: id(1),
                    type_args: vec![],
                    args: vec![],
                },
            )],
            dest: Some(Place::local(LocalId(1))),
            site: SiteId(0),
        },
    );
    original.body = Body::Stmts(Block::new(vec![
        Stmt::new(
            SpanId(12),
            StmtKind::GhostTail {
                block: Block::new(vec![
                    Stmt::new(
                        SpanId(9),
                        StmtKind::Let {
                            local: LocalId(1),
                            init: None,
                        },
                    ),
                    call,
                ]),
                tail: Expr::read(Place::local(LocalId(1)), Ty::Unit, SpanId(11)),
            },
        ),
        Stmt::new(
            SpanId(13),
            StmtKind::Return {
                value: None,
                site: SiteId(1),
            },
        ),
    ]));
    let mut instance = original.clone();
    instance.id = id(4);
    instance.role = FnRole::Instance;
    instance.type_params.clear();
    instance.attrs.instance = Some(GenericInstance {
        declaration: original.id,
        type_args: vec![Ty::Unit],
    });
    let mut krate = VcCrate::new("instance effect diagnostics");
    krate.fns = vec![prophetic, lemma, original, instance];
    krate
}

#[test]
fn instance_effect_diagnostics_precede_source_attribution_without_relabeling() {
    let krate = source(false);
    let public = check_crate(&krate);
    assert_eq!(public.len(), 1, "{public:?}");
    assert_eq!(public[0].function, Some(id(3)));
    let instance = &krate.fns[3];
    assert_eq!(instance.role, FnRole::Instance);
    assert_eq!(instance.attrs.instance.as_ref().unwrap().declaration, id(3));
    assert!(matches!(instance.body, Body::Stmts(_)));
    let effects = function_prophecy_diagnostics(&krate, instance.id).unwrap();
    assert_eq!(effects.len(), 1, "{effects:?}");
    assert_eq!(effects[0].function, Some(instance.id));
    assert_eq!(effects[0].class, WfClass::User);
    assert_eq!(effects[0].span, SpanId(12));
    assert!(effects[0].message.contains("'Ghost' wrapper"));
    let rows = ghost_tail_modes(&krate);
    assert_eq!(rows.len(), 2);
    assert_eq!(rows[1].function, instance.id);
    assert_eq!(rows[1].class, Some(GhostTailModeClass::NonSpec));
    assert_eq!(function_prophecy_diagnostics(&krate, id(99)), None);
}

#[test]
fn an_empty_effect_view_does_not_certify_instance_well_formedness() {
    let mut krate = source(true);
    assert!(check_crate(&krate).is_empty(), "{:?}", check_crate(&krate));
    assert_eq!(function_prophecy_diagnostics(&krate, id(4)), Some(vec![]));
    krate.fns[3]
        .attrs
        .instance
        .as_mut()
        .unwrap()
        .type_args
        .clear();
    assert_eq!(function_prophecy_diagnostics(&krate, id(4)), Some(vec![]));
    assert!(check_crate(&krate)
        .iter()
        .any(|error| error.function == Some(id(4))
            && error.class == WfClass::Malformed
            && error.message.contains("invalid generic instance origin")));
}
