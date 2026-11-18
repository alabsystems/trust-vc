// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Typed unwind contracts retain their formal parameters and instance origin.

use trust_vc_vcir::*;

#[path = "unwind_contracts/validation.rs"]
mod validation;

#[path = "unwind_contracts/dependencies.rs"]
mod dependencies;

#[cfg(feature = "solve")]
#[path = "unwind_contracts/solver.rs"]
mod solver;

#[cfg(feature = "solve")]
#[path = "unwind_contracts/isolated_loops.rs"]
mod isolated_loops;

#[cfg(feature = "solve")]
#[path = "unwind_contracts/generic_calls.rs"]
mod generic_calls;

fn id(number: u64) -> FnId {
    FnId(DefHash::new(173, number))
}

fn span() -> SpanId {
    SpanId(0)
}

fn local(ty: Ty, kind: LocalKind) -> LocalDecl {
    LocalDecl {
        name: "value".into(),
        ty,
        mode: Mode::Exec,
        kind,
        prophecy: DeclProphecy::Default,
        mutable: kind == LocalKind::Param,
        span: span(),
    }
}

fn function(number: u64) -> FnDecl {
    FnDecl {
        id: id(number),
        name: format!("function{number}"),
        span: span(),
        mode: Mode::Exec,
        role: FnRole::Item,
        kind: FnKind::Function,
        copy_premises: Vec::new(),
        type_params: vec![],
        locals: vec![
            local(Ty::Unit, LocalKind::Return),
            local(Ty::Bool, LocalKind::Param),
        ],
        params: vec![LocalId(1)],
        ret: LocalId(0),
        requires: vec![],
        ensures: vec![],
        recommends: vec![],
        unwind: None,
        decreases: vec![],
        decreases_when: None,
        decreases_by: None,
        attrs: FnAttrs::default(),
        body: Body::Stmts(Block::new(vec![statement(StmtKind::Return {
            value: None,
            site: SiteId(9),
        })])),
    }
}

fn statement(kind: StmtKind) -> Stmt {
    Stmt::new(span(), kind)
}

fn parameter() -> Expr {
    Expr::read(Place::local(LocalId(1)), Ty::Bool, span())
}

fn not(value: Expr) -> Expr {
    Expr::new(
        Ty::Bool,
        span(),
        ExprKind::Unary {
            op: UnOp::Not,
            arg: Box::new(value),
            check: None,
        },
    )
}

fn generic_condition(ty: Ty) -> Expr {
    let value = || Expr::read(Place::local(LocalId(2)), ty.clone(), span());
    let equality = Expr::binary(BinOp::Eq, value(), value(), Ty::Bool, span());
    Expr::binary(BinOp::And, equality, parameter(), Ty::Bool, span())
}

fn generic_source() -> VcCrate {
    let mut original = function(10);
    original.type_params = vec!["T".into()];
    original.locals.push(local(Ty::Param(0), LocalKind::Param));
    original.params.push(LocalId(2));
    original.unwind = Some(UnwindSpec::NoUnwindWhen(generic_condition(Ty::Param(0))));
    let mut instance = original.clone();
    instance.id = id(11);
    instance.name = "concrete_instance".into();
    instance.role = FnRole::Instance;
    instance.type_params.clear();
    instance.locals[2].ty = Ty::uint(32);
    instance.unwind = Some(UnwindSpec::NoUnwindWhen(generic_condition(Ty::uint(32))));
    instance.attrs.instance = Some(GenericInstance {
        declaration: original.id,
        type_args: vec![Ty::uint(32)],
    });
    let mut source = VcCrate::new("generic unwind contract");
    source.fns = vec![original, instance];
    source
}

#[test]
fn generic_unwind_contract_preserves_the_actual_instance_substitution() {
    let source = generic_source();
    assert!(
        check_crate(&source).is_empty(),
        "{:?}",
        check_crate(&source)
    );
    assert_eq!(source.fns[1].role, FnRole::Instance);
    assert_eq!(
        source.fns[1].attrs.instance.as_ref().unwrap().type_args,
        vec![Ty::uint(32)]
    );
    assert_eq!(
        (source.fns[0].id, source.fns[0].role),
        (id(10), FnRole::Item)
    );
    assert_eq!(source.fns[1].id, id(11));
    assert_eq!(
        source.fns[1].attrs.instance.as_ref().unwrap().declaration,
        id(10)
    );
    let generated = vcgen::generate(&source);
    assert_eq!(generated.fns.len(), 2);
    assert!(
        matches!(generated.get(id(10)), Some(vcgen::FnVcs::Checks(_))),
        "{generated:?}"
    );
    assert!(
        matches!(generated.get(id(11)), Some(vcgen::FnVcs::Instance)),
        "{generated:?}"
    );
}

#[test]
fn an_instance_cannot_change_or_drop_its_original_unwind_contract() {
    for replacement in [
        None,
        Some(UnwindSpec::MayUnwind),
        Some(UnwindSpec::NoUnwind),
        Some(UnwindSpec::NoUnwindWhen(not(parameter()))),
    ] {
        let mut source = generic_source();
        source.fns[1].unwind = replacement;
        let errors = check_crate(&source);
        assert!(
            errors
                .iter()
                .any(|error| error.function == Some(id(11)) && error.class == WfClass::Malformed),
            "{errors:?}"
        );
    }
}

#[test]
fn an_unsubstituted_generic_contract_is_not_an_instance_contract() {
    let mut source = generic_source();
    source.fns[1].unwind = Some(UnwindSpec::NoUnwindWhen(generic_condition(Ty::Param(0))));
    let errors = check_crate(&source);
    assert!(
        errors
            .iter()
            .any(|error| error.function == Some(id(11)) && error.class == WfClass::Malformed),
        "{errors:?}"
    );
}
