use super::*;
use crate::{DefHash, FieldDecl, Mode, SpanId, VariantDecl};

fn copy(adts: &HashMap<AdtId, &AdtDecl>, premises: &[Ty], ty: &Ty) -> bool {
    is_copy_with(adts, premises, ty, None, |_| Ok::<_, ()>(())).unwrap()
}

#[test]
fn exact_premises_do_not_decompose_or_authorize_rigid_noncopy_types() {
    let adts = HashMap::new();
    let parameter = Ty::Param(0);
    let compound = Ty::Tuple(vec![parameter.clone(), Ty::Bool]);
    assert!(!copy(&adts, &[], &parameter));
    assert!(copy(&adts, std::slice::from_ref(&parameter), &parameter));
    assert!(copy(&adts, std::slice::from_ref(&parameter), &compound));
    assert!(copy(&adts, std::slice::from_ref(&compound), &compound));
    assert!(!copy(&adts, &[compound], &parameter));
    let shared = Ty::Ref {
        mutable: false,
        inner: Box::new(parameter.clone()),
    };
    assert!(copy(&adts, &[], &shared));
    for illegal in [
        Ty::MutRef(Box::new(parameter.clone())),
        Ty::Ref {
            mutable: true,
            inner: Box::new(parameter),
        },
        Ty::Int(crate::IntRange::U(7)),
        Ty::Tuple(vec![]),
    ] {
        assert!(!copy(&adts, std::slice::from_ref(&illegal), &illegal));
    }
}

#[test]
fn associated_types_gain_copy_only_from_exact_checked_premises() {
    let adts = HashMap::new();
    let first = Ty::Projection(crate::ProjectionId(DefHash::new(901, 20)), vec![Ty::Param(0)]);
    let other = Ty::Projection(crate::ProjectionId(DefHash::new(901, 21)), vec![Ty::Param(0)]);
    assert!(!copy(&adts, &[], &first));
    assert!(!copy(&adts, &[other], &first));
    assert!(copy(&adts, std::slice::from_ref(&first), &first));
    assert!(!copy(&adts, std::slice::from_ref(&first), &Ty::Param(0)));
    assert!(wellformed_with(&adts, &|_| None, &first, 1, |_| Ok::<_, ()>(())).unwrap() == false);
    let registered = |id| (id == crate::ProjectionId(DefHash::new(901, 20))).then_some(1);
    assert!(wellformed_with(&adts, &registered, &first, 1, |_| Ok::<_, ()>(())).unwrap());
}

fn wrapper(id: AdtId) -> AdtDecl {
    AdtDecl {
        id,
        name: "display only".into(),
        span: SpanId(0),
        type_params: vec!["T".into()],
        kind: AdtKind::Struct,
        variants: vec![VariantDecl {
            name: "display only".into(),
            fields: vec![FieldDecl {
                name: "field".into(),
                ty: Ty::Param(0),
                mode: Mode::Exec,
            }],
        }],
    }
}

#[test]
fn represented_finite_layouts_and_recursive_or_opaque_layouts_are_distinct() {
    let id = AdtId(DefHash::new(901, 1));
    let mut declaration = wrapper(id);
    let scalar = Ty::Adt(id, vec![Ty::Bool]);
    let nested = Ty::Adt(id, vec![scalar.clone()]);
    assert!(copy(
        &[(id, &declaration)].into_iter().collect(),
        &[],
        &nested
    ));
    declaration.variants[0].fields[0].ty = Ty::Adt(id, vec![Ty::Param(0)]);
    assert!(!copy(
        &[(id, &declaration)].into_iter().collect(),
        std::slice::from_ref(&scalar),
        &scalar
    ));
    declaration.kind = AdtKind::Opaque;
    declaration.variants.clear();
    assert!(!copy(
        &[(id, &declaration)].into_iter().collect(),
        std::slice::from_ref(&scalar),
        &scalar
    ));
    assert!(!copy(
        &HashMap::new(),
        std::slice::from_ref(&scalar),
        &scalar
    ));
}

#[test]
fn substitution_retains_the_callers_parameter_indices_and_shared_work_exhausts() {
    let adts = HashMap::new();
    let formal = Ty::Tuple(vec![Ty::Param(0), Ty::Param(1)]);
    let arguments = [Ty::Param(1), Ty::Bool];
    let actual = Ty::Tuple(vec![Ty::Param(1), Ty::Bool]);
    assert!(matches_substitution_with(&formal, &arguments, &actual, |_| Ok::<_, ()>(())).unwrap());
    assert!(!matches_substitution_with(
        &formal,
        &arguments,
        &Ty::Tuple(vec![Ty::Bool, Ty::Bool]),
        |_| Ok::<_, ()>(())
    )
    .unwrap());
    assert!(
        is_copy_with(&adts, &[Ty::Param(1)], &formal, Some(&arguments), |_| Ok::<
            _,
            (),
        >(
            ()
        ))
        .unwrap()
    );
    assert!(
        !is_copy_with(&adts, &[Ty::Param(0)], &formal, Some(&arguments), |_| Ok::<
            _,
            (),
        >(
            ()
        ))
        .unwrap()
    );
    let mut remaining = 10usize;
    let result = is_copy_with(
        &adts,
        &[Ty::Param(1)],
        &formal,
        Some(&arguments),
        |amount| {
            remaining = remaining.checked_sub(amount).ok_or(())?;
            Ok(())
        },
    );
    assert_eq!(
        result,
        Err(()),
        "exhaustion is not a successful partial classification"
    );
}
