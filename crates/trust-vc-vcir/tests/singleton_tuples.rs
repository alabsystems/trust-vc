//! Canonical unary tuple types, constructors, projections and malformed twins.

use trust_vc_vcir::*;

fn singleton(value: Expr) -> Expr {
    Expr::new(
        Ty::Tuple(vec![value.ty.clone()]),
        SpanId(0),
        ExprKind::Tuple(vec![value]),
    )
}

fn specification(body: Expr) -> VcCrate {
    let mut krate = VcCrate::new("singleton tuple controls");
    krate.fns.push(FnDecl {
        id: FnId(DefHash::new(91, 1)),
        name: "value".into(),
        span: SpanId(0),
        mode: Mode::Spec,
        role: FnRole::Item,
        kind: FnKind::Function,
        type_params: vec![],
        locals: vec![LocalDecl {
            name: "result".into(),
            ty: body.ty.clone(),
            mode: Mode::Spec,
            mutable: false,
            kind: LocalKind::Return,
            span: SpanId(0),
        }],
        params: vec![],
        ret: LocalId(0),
        requires: vec![],
        ensures: vec![],
        recommends: vec![],
        decreases: vec![],
        decreases_when: None,
        decreases_by: None,
        attrs: FnAttrs::default(),
        body: Body::Spec(body),
    });
    krate
}

fn malformed(krate: &VcCrate) {
    assert!(check_crate(krate)
        .iter()
        .any(|error| error.class == WfClass::Malformed));
}

#[test]
fn singleton_constructor_and_projection_keep_the_exact_element_type() {
    let value = singleton(Expr::bool_lit(true, SpanId(0)));
    assert!(check_crate(&specification(value.clone())).is_empty());
    let projection = Expr::new(
        Ty::Bool,
        SpanId(0),
        ExprKind::TupleField {
            base: Box::new(value),
            index: 0,
        },
    );
    assert!(check_crate(&specification(projection.clone())).is_empty());

    let mut wrong_type = projection.clone();
    wrong_type.ty = Ty::Unit;
    malformed(&specification(wrong_type));
    let mut wrong_index = projection;
    let ExprKind::TupleField { index, .. } = &mut wrong_index.kind else {
        unreachable!()
    };
    *index = 1;
    malformed(&specification(wrong_index));
}

#[test]
fn unary_constructor_cannot_borrow_unit_or_another_arity() {
    let value = singleton(Expr::bool_lit(true, SpanId(0)));
    let mut unit = specification(value.clone());
    unit.fns[0].locals[0].ty = Ty::Unit;
    malformed(&unit);
    for fields in [
        vec![],
        vec![
            Expr::bool_lit(true, SpanId(0)),
            Expr::bool_lit(false, SpanId(0)),
        ],
    ] {
        let mut wrong = value.clone();
        wrong.kind = ExprKind::Tuple(fields);
        malformed(&specification(wrong));
    }
    let empty = Expr::new(Ty::Tuple(vec![]), SpanId(0), ExprKind::Tuple(vec![]));
    malformed(&specification(empty));
}

#[test]
fn nested_singletons_preserve_their_comma_and_shape() {
    let krate = specification(singleton(singleton(Expr::bool_lit(true, SpanId(0)))));
    assert!(check_crate(&krate).is_empty());
    let printed = pretty::crate_to_string(&krate);
    assert!(printed.contains("((bool,),)"), "{printed}");
    assert!(printed.contains("((true,),)"), "{printed}");
}
