// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Real AY obligations distinguish affine fields from retained logical snapshots.
use super::*;
#[path = "field_mode_ownership/harness.rs"]
mod harness;
use harness::require;

fn adt_id() -> AdtId {
    AdtId(DefHash::new(133, 701))
}
fn aggregate_type() -> Ty {
    Ty::Adt(adt_id(), vec![])
}
fn aggregate(owned: Ty, snapshot: Ty) -> AdtDecl {
    AdtDecl {
        id: adt_id(),
        name: "MixedFieldModes".into(),
        type_params: vec![],
        span: span(),
        kind: AdtKind::Struct,
        variants: vec![VariantDecl {
            name: "MixedFieldModes".into(),
            fields: vec![
                FieldDecl {
                    name: "owned".into(),
                    ty: owned,
                    mode: Mode::Exec,
                },
                FieldDecl {
                    name: "snapshot".into(),
                    ty: snapshot,
                    mode: Mode::Spec,
                },
            ],
        }],
    }
}
fn projected(local: LocalId, field: u32, ty: Ty) -> Expr {
    Expr::read(
        Place {
            local,
            projections: vec![Projection::Field { variant: 0, field }],
        },
        ty,
        span(),
    )
}
fn construct(first: Expr, second: Expr) -> Expr {
    Expr::new(
        aggregate_type(),
        span(),
        ExprKind::Ctor {
            adt: adt_id(),
            variant: 0,
            fields: vec![first, second],
        },
    )
}
fn resolved(value: Expr) -> Expr {
    Expr::new(Ty::Bool, span(), ExprKind::HasResolved(Box::new(value)))
}
fn let_value(local: LocalId, value: Option<Expr>) -> Stmt {
    stmt(StmtKind::Let { local, init: value })
}
fn borrow(dest: LocalId, place: Place) -> Stmt {
    stmt(StmtKind::BorrowMut { dest, place })
}
fn write(place: Place, value: i128) -> Stmt {
    stmt(StmtKind::Assign {
        place,
        value: integer(value),
    })
}

fn proof_borrow(reborrow: bool, expected: i128) -> VcCrate {
    let mut f = function(Ty::Unit);
    let value = add(&mut f, scalar(), Mode::Exec, LocalKind::Let);
    let r = add(&mut f, reference(scalar()), Mode::Proof, LocalKind::Let);
    let p = add(&mut f, reference(scalar()), Mode::Proof, LocalKind::Let);
    let mut ghost = vec![let_value(r, None), borrow(r, Place::local(value))];
    if reborrow {
        ghost.extend([let_value(p, None), borrow(p, Place::deref(r))]);
    }
    f.body = Body::Stmts(Block::new(vec![
        let_value(value, Some(integer(7))),
        stmt(StmtKind::Ghost(Block::new(ghost))),
        assertion(eq(read(value, scalar()), integer(expected)), 0),
        ret(None),
    ]));
    krate(f)
}

fn snapshot_write(expected: i128) -> VcCrate {
    let mut f = function(Ty::Unit);
    let owned = add(&mut f, scalar(), Mode::Exec, LocalKind::Param);
    let replacement = add(&mut f, scalar(), Mode::Spec, LocalKind::Param);
    f.requires = vec![
        clause(eq(read(owned, scalar()), integer(7))),
        clause(eq(read(replacement, scalar()), integer(8))),
    ];
    let mixed = add(&mut f, aggregate_type(), Mode::Exec, LocalKind::Let);
    let snapshot = Place {
        local: mixed,
        projections: vec![Projection::Field {
            variant: 0,
            field: 1,
        }],
    };
    f.body = Body::Stmts(Block::new(vec![
        let_value(mixed, Some(construct(read(owned, scalar()), integer(0)))),
        stmt(StmtKind::Ghost(Block::new(vec![stmt(StmtKind::Assign {
            place: snapshot,
            value: read(replacement, scalar()),
        })]))),
        assertion(eq(projected(mixed, 0, scalar()), integer(expected)), 0),
        assertion(eq(projected(mixed, 1, scalar()), integer(8)), 1),
        ret(None),
    ]));
    let mut source = krate(f);
    source.adts.push(aggregate(scalar(), scalar()));
    source
}

#[derive(Clone, Copy)]
enum Goal {
    Scalar(i128),
    SnapshotResolved,
    CurrentAfterWrite,
}

fn independent_goals() -> [(Goal, bool); 4] {
    [
        (Goal::Scalar(7), true),
        (Goal::Scalar(8), false),
        (Goal::SnapshotResolved, false),
        (Goal::CurrentAfterWrite, true),
    ]
}

fn require_mixed(call: Option<bool>) {
    for (goal, proved) in independent_goals() {
        require(mixed(call, goal), &[proved]);
    }
}

fn copied_twice(spec_only: bool, goal: Goal) -> VcCrate {
    let mut source = mixed(None, goal);
    if spec_only {
        source.adts[0].variants[0].fields[0].mode = Mode::Spec;
    }
    let f = &mut source.fns[0];
    let copied = add(f, aggregate_type(), Mode::Exec, LocalKind::Let);
    let Body::Stmts(body) = &mut f.body else {
        panic!("statement body");
    };
    let (index, expression) = body
        .stmts
        .iter()
        .enumerate()
        .find_map(|(index, statement)| {
            let StmtKind::Let {
                init: Some(expression),
                ..
            } = &statement.kind
            else {
                return None;
            };
            (expression.ty == aggregate_type() && matches!(expression.kind, ExprKind::Read(_)))
                .then(|| (index, expression.clone()))
        })
        .expect("the authored whole-product move");
    body.stmts
        .insert(index + 1, let_value(copied, Some(expression)));
    source
}

fn initial(value: LocalId, loan: LocalId) -> Vec<Stmt> {
    vec![
        let_value(value, Some(integer(0))),
        let_value(loan, None),
        borrow(loan, Place::local(value)),
        write(Place::deref(loan), 7),
    ]
}
fn identity() -> FnDecl {
    let mut f = function(aggregate_type());
    f.id = FnId(DefHash::new(133, 702));
    f.name = "real_mixed_product_identity".into();
    let input = add(&mut f, aggregate_type(), Mode::Exec, LocalKind::Param);
    f.ensures.push(clause(eq(
        read(f.ret, aggregate_type()),
        read(input, aggregate_type()),
    )));
    f.body = Body::Stmts(Block::new(vec![ret(Some(read(input, aggregate_type())))]));
    f
}
fn mixed(call: Option<bool>, goal: Goal) -> VcCrate {
    let mut f = function(Ty::Unit);
    let x = add(&mut f, scalar(), Mode::Exec, LocalKind::Let);
    let y = add(&mut f, scalar(), Mode::Exec, LocalKind::Let);
    let r = add(&mut f, reference(scalar()), Mode::Exec, LocalKind::Let);
    let s = add(&mut f, reference(scalar()), Mode::Exec, LocalKind::Let);
    let product = add(&mut f, aggregate_type(), Mode::Exec, LocalKind::Let);
    let moved = add(&mut f, aggregate_type(), Mode::Exec, LocalKind::Let);
    let first = add(&mut f, reference(scalar()), Mode::Spec, LocalKind::Let);
    let second = add(&mut f, reference(scalar()), Mode::Spec, LocalKind::Let);
    let mut body = initial(x, r);
    body.extend(initial(y, s));
    body.push(let_value(
        product,
        Some(construct(
            read(r, reference(scalar())),
            read(s, reference(scalar())),
        )),
    ));
    let snapshot_owner = match call {
        None => {
            body.push(let_value(moved, Some(read(product, aggregate_type()))));
            product
        }
        Some(discard) => {
            if !discard {
                body.push(let_value(moved, None));
            }
            body.push(stmt(StmtKind::Call {
                callee: identity().id,
                type_args: vec![],
                args: vec![read(product, aggregate_type())],
                dest: (!discard).then_some(Place::local(moved)),
                site: SiteId(5),
            }));
            if discard {
                product
            } else {
                moved
            }
        }
    };
    body.push(stmt(StmtKind::Ghost(Block::new(vec![
        let_value(
            first,
            Some(projected(snapshot_owner, 1, reference(scalar()))),
        ),
        let_value(
            second,
            Some(projected(snapshot_owner, 1, reference(scalar()))),
        ),
    ]))));
    // Each property has its own program. A failed assertion is assumed for
    // later checks, so it cannot precede another oracle in this component.
    match goal {
        Goal::Scalar(expected) => body.push(assertion(eq(read(x, scalar()), integer(expected)), 0)),
        Goal::SnapshotResolved => body.push(assertion(
            resolved(projected(snapshot_owner, 1, reference(scalar()))),
            0,
        )),
        Goal::CurrentAfterWrite => {}
    }
    // This real later write keeps s live for the early resolution question.
    body.push(write(Place::deref(s), 8));
    if matches!(goal, Goal::CurrentAfterWrite) {
        body.push(assertion(
            eq(current(read(s, reference(scalar()))), integer(8)),
            0,
        ));
    }
    body.push(ret(None));
    f.body = Body::Stmts(Block::new(body));
    let mut source = krate(f);
    source
        .adts
        .push(aggregate(reference(scalar()), reference(scalar())));
    if call.is_some() {
        source.fns.push(identity());
    }
    source
}

#[test]
fn proof_carrier_borrows_exec_storage_without_losing_resolution() {
    require(proof_borrow(false, 7), &[true]);
    require(proof_borrow(false, 8), &[false]);
}
#[test]
fn proof_reborrow_keeps_exec_pointee_and_owned_resolution() {
    require(proof_borrow(true, 7), &[true]);
    require(proof_borrow(true, 8), &[false]);
}
#[test]
fn spec_field_mutation_preserves_the_exec_sibling() {
    require(snapshot_write(7), &[true, true]);
    require(snapshot_write(8), &[false, true]);
}
#[test]
fn mixed_product_move_never_consumes_or_resolves_spec_reference_snapshots() {
    require_mixed(None);
}
#[test]
fn mixed_product_call_returns_only_affine_slots() {
    require_mixed(Some(false));
}
#[test]
fn discarded_mixed_call_result_never_resolves_spec_reference_snapshots() {
    require_mixed(Some(true));
}
#[test]
fn a_mixed_product_affine_field_still_rejects_a_second_move() {
    refusal(copied_twice(false, Goal::Scalar(7)), "mut-ref-moved");
}
#[test]
fn products_containing_only_spec_reference_snapshots_remain_copyable() {
    for (goal, proved) in independent_goals() {
        require(copied_twice(true, goal), &[proved]);
    }
}
