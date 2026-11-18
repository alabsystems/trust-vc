// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pure visitor/correspondence data. No fabricated native IDs or import token.

use super::*;
use trust_vc_vcir::{
    Block, Body, DeclProphecy, DefHash, Expr, ExprKind, FnAttrs, FnKind, Lit, LocalDecl, LocalId,
    LocalKind, Mode, Place, SiteId, SpanId, Stmt, StmtKind, Ty,
};

fn id(value: u64) -> FnId {
    FnId(DefHash::new(0, value))
}

fn function(id: FnId, role: FnRole, params: usize, output: Ty) -> FnDecl {
    let mut locals = (0..params)
        .map(|index| LocalDecl {
            name: format!("v{index}"),
            ty: Ty::Param(0),
            mode: Mode::Spec,
            prophecy: DeclProphecy::Default,
            mutable: false,
            kind: LocalKind::Param,
            span: SpanId(0),
        })
        .collect::<Vec<_>>();
    locals.push(LocalDecl {
        name: "ret".into(),
        ty: output,
        mode: Mode::Spec,
        prophecy: DeclProphecy::Default,
        mutable: false,
        kind: LocalKind::Return,
        span: SpanId(0),
    });
    FnDecl {
        id,
        name: "ordinary-observation-data".into(),
        span: SpanId(0),
        mode: if role == FnRole::Imported {
            Mode::Spec
        } else {
            Mode::Proof
        },
        role,
        kind: FnKind::Function,
        type_params: vec!["T".into()],
        copy_premises: Vec::new(),
        locals,
        params: (0..params as u32).map(LocalId).collect(),
        ret: LocalId(params as u32),
        requires: vec![],
        ensures: vec![],
        recommends: vec![],
        unwind: None,
        decreases: vec![],
        decreases_when: None,
        decreases_by: None,
        attrs: FnAttrs::default(),
        body: Body::None,
    }
}

fn call(callee: FnId, local: u32, span: u32) -> Expr {
    Expr::new(
        Ty::nat(),
        SpanId(span),
        ExprKind::Call {
            callee,
            type_args: vec![Ty::Param(0)],
            args: vec![Expr::read(
                Place::local(LocalId(local)),
                Ty::Param(0),
                SpanId(span),
            )],
        },
    )
}

#[test]
fn unwind_observations_preserve_kinds_and_refuse_conditional_scopes() {
    let mut declaration = function(FnId(DefHash::new(7, 9)), FnRole::Item, 0, Ty::Unit);
    declaration.mode = Mode::Exec;
    let value = vcir::signature(&declaration, &mut vcir::Budget::new()).unwrap();
    assert_eq!(
        value["unwind"],
        json!({"declared": false, "kind": "MayUnwind"})
    );
    declaration.unwind = Some(trust_vc_vcir::UnwindSpec::NoUnwind);
    let value = vcir::signature(&declaration, &mut vcir::Budget::new()).unwrap();
    assert_eq!(
        value["unwind"],
        json!({"declared": true, "kind": "NoUnwind"})
    );
    declaration.unwind = Some(trust_vc_vcir::UnwindSpec::NoUnwindWhen(Expr::new(
        Ty::Bool,
        SpanId(0),
        ExprKind::Lit(Lit::Bool(true)),
    )));
    assert!(vcir::signature(&declaration, &mut vcir::Budget::new())
        .unwrap_err()
        .contains("conditional unwind header scopes"));
    let declarations = BTreeMap::from([(declaration.id, &declaration)]);
    let mut walk = vcir::Walk::new(&declaration, &declarations);
    assert!(walk
        .body(&mut vcir::Budget::new())
        .unwrap_err()
        .contains("header scopes"));
}

#[test]
fn full_vectors_and_distinct_local_reads_survive_assertion_observation() {
    let imported = function(id(2), FnRole::Imported, 1, Ty::nat());
    let mut local = function(id(1), FnRole::Item, 2, Ty::Unit);
    local.body = Body::Stmts(Block::new(vec![Stmt::new(
        SpanId(20),
        StmtKind::Assert {
            expr: Expr::binary(
                trust_vc_vcir::BinOp::Eq,
                call(imported.id, 0, 10),
                call(imported.id, 1, 11),
                Ty::Bool,
                SpanId(12),
            ),
            site: SiteId(0),
            attrs: Default::default(),
        },
    )]));
    let declarations = BTreeMap::from([(local.id, &local), (imported.id, &imported)]);
    let mut walk = vcir::Walk::new(&local, &declarations);
    walk.body(&mut vcir::Budget::new()).unwrap();
    assert_eq!(walk.assertions.len(), 1);
    assert_eq!(walk.calls.len(), 2);
    assert_eq!(
        walk.assertions[0]["condition"]["expression"]["operator"],
        "Eq"
    );
    for (index, call) in walk.calls.iter().enumerate() {
        assert_eq!(call.value["assertion"], 0);
        assert_eq!(call.value["declaration_role"], "Imported");
        assert_eq!(
            call.value["type_arguments"],
            json!([{"kind": "Parameter", "index": 0}])
        );
        assert_eq!(
            call.value["value_arguments"][0]["expression"]["place"]["local"],
            index
        );
        assert_eq!(call.value["signature"]["return"]["type"]["range"], "Nat");
    }
}

#[test]
fn dead_branches_are_counted_and_different_declarations_are_never_merged() {
    let left = function(id(2), FnRole::Imported, 1, Ty::nat());
    let right = function(id(3), FnRole::Imported, 1, Ty::nat());
    let mut local = function(id(1), FnRole::Item, 1, Ty::nat());
    let returned = |callee| {
        Block::new(vec![Stmt::new(
            SpanId(1),
            StmtKind::Return {
                value: Some(call(callee, 0, 2)),
                site: SiteId(0),
            },
        )])
    };
    local.body = Body::Stmts(Block::new(vec![Stmt::new(
        SpanId(0),
        StmtKind::If {
            cond: Expr::bool_lit(false, SpanId(0)),
            then_block: returned(left.id),
            else_block: returned(right.id),
        },
    )]));
    let declarations = BTreeMap::from([(local.id, &local), (left.id, &left), (right.id, &right)]);
    let mut walk = vcir::Walk::new(&local, &declarations);
    walk.body(&mut vcir::Budget::new()).unwrap();
    assert_eq!(
        walk.calls
            .iter()
            .map(|call| call.callee)
            .collect::<Vec<_>>(),
        vec![left.id, right.id]
    );
    let mut missing = call(left.id, 0, 2);
    if let ExprKind::Call { type_args, .. } = &mut missing.kind {
        type_args.clear();
    }
    local.body = Body::Spec(missing);
    let declarations = BTreeMap::from([(local.id, &local), (left.id, &left)]);
    assert!(vcir::Walk::new(&local, &declarations)
        .body(&mut vcir::Budget::new())
        .is_err());
}

#[test]
fn ambiguous_reused_missing_unrepresented_and_overbudget_observations_refuse() {
    let mut used = BTreeSet::new();
    let mut budget = vcir::Budget::new();
    assert_eq!(
        unique_match(&[(1u32, 2u32)], &(1, 2), &mut used, &mut budget).unwrap(),
        0
    );
    assert!(unique_match(&[(1, 2)], &(1, 2), &mut used, &mut budget).is_err());
    assert!(unique_match(
        &[(1, 2), (1, 2)],
        &(1, 2),
        &mut BTreeSet::new(),
        &mut budget
    )
    .is_err());
    assert!(unique_match(&[(1, 2)], &(2, 1), &mut BTreeSet::new(), &mut budget).is_err());
    let mut local = function(id(1), FnRole::Item, 0, Ty::Unit);
    local.body = Body::Spec(Expr::new(
        Ty::Unit,
        SpanId(0),
        ExprKind::ProofInSpec(Block::default()),
    ));
    let declarations = BTreeMap::from([(local.id, &local)]);
    assert!(vcir::Walk::new(&local, &declarations)
        .body(&mut budget)
        .is_err());
    let mut exhausted = vcir::Budget::new();
    exhausted.charge(16_384, 0, 0).unwrap();
    assert!(vcir::Walk::new(&local, &declarations)
        .body(&mut exhausted)
        .is_err());
}

#[test]
fn changing_a_variant_test_keeps_its_nested_call_and_changes_the_observation() {
    fn observe(variant: u32) -> (Value, Vec<Value>) {
        let sum = Ty::Adt(
            trust_vc_vcir::AdtId(DefHash::new(0, 10)),
            vec![Ty::Param(0)],
        );
        let imported = function(id(2), FnRole::Imported, 1, sum.clone());
        let mut local = function(id(1), FnRole::Item, 1, Ty::Unit);
        let receiver = Expr::new(
            sum,
            SpanId(11),
            ExprKind::Call {
                callee: imported.id,
                type_args: vec![Ty::Param(0)],
                args: vec![Expr::read(
                    Place::local(LocalId(0)),
                    Ty::Param(0),
                    SpanId(12),
                )],
            },
        );
        local.body = Body::Stmts(Block::new(vec![Stmt::new(
            SpanId(20),
            StmtKind::Assert {
                expr: Expr::new(
                    Ty::Bool,
                    SpanId(10),
                    ExprKind::IsVariant {
                        base: Box::new(receiver),
                        variant,
                    },
                ),
                site: SiteId(0),
                attrs: Default::default(),
            },
        )]));
        let declarations = BTreeMap::from([(local.id, &local), (imported.id, &imported)]);
        let mut walk = vcir::Walk::new(&local, &declarations);
        walk.body(&mut vcir::Budget::new()).unwrap();
        assert_eq!(walk.assertions.len(), 1);
        assert_eq!(walk.calls.len(), 1);
        assert_eq!(walk.calls[0].callee, imported.id);
        (
            walk.assertions[0].clone(),
            walk.calls.iter().map(|call| call.value.clone()).collect(),
        )
    }
    let (first, first_calls) = observe(0);
    let (changed, changed_calls) = observe(1);
    assert_ne!(first, changed);
    assert_eq!(first_calls, changed_calls);
}
