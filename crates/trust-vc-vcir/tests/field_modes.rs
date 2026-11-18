// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Field declarations and typed reference paths determine storage authority.
use trust_vc_vcir::*;

#[path = "field_modes/helpers.rs"]
mod helpers;
use helpers::*;
#[path = "field_modes/paths.rs"]
mod paths;
#[cfg(feature = "solve")]
#[path = "field_modes/solver.rs"]
mod solver;
#[path = "field_modes/transport.rs"]
mod transport;
#[path = "field_modes/transport_calls.rs"]
mod transport_calls;

fn borrowed_from_proof(write: bool, expected: i128) -> VcCrate {
    let mut f = function(1, Mode::Exec, Ty::Unit, Mode::Exec);
    let value = add(&mut f, scalar(), Mode::Exec, LocalKind::Let);
    let loan = add(&mut f, reference(), Mode::Proof, LocalKind::Let);
    let mut ghost = vec![
        statement(StmtKind::Let {
            local: loan,
            init: None,
        }),
        statement(StmtKind::BorrowMut {
            dest: loan,
            place: Place::local(value),
        }),
        statement(StmtKind::Assert {
            expr: equality(
                Expr::read(Place::deref(loan), scalar(), span()),
                integer(expected),
            ),
            site: SiteId(0),
            attrs: ClauseAttrs::default(),
        }),
    ];
    if write {
        ghost.push(statement(StmtKind::Assign {
            place: Place::deref(loan),
            value: integer(7),
        }));
    }
    f.body = Body::Stmts(Block::new(vec![
        statement(StmtKind::Let {
            local: value,
            init: Some(integer(7)),
        }),
        statement(StmtKind::Ghost(Block::new(ghost))),
        returned(None),
    ]));
    source(f)
}

#[test]
fn proof_borrow_of_exec_storage_has_a_proof_carrier() {
    clean(&borrowed_from_proof(false, 7));
}

#[test]
fn proof_carrier_does_not_grant_ghost_mutation_of_exec_storage() {
    user_error(
        &borrowed_from_proof(true, 7),
        "cannot assign to exec variable from proof mode",
    );
}

#[test]
fn call_destination_uses_pointee_mode_instead_of_reference_carrier_mode() {
    let mut f = function(1, Mode::Exec, Ty::Unit, Mode::Exec);
    let pointer = add(&mut f, reference(), Mode::Proof, LocalKind::Param);
    f.body = Body::Stmts(Block::new(vec![
        statement(StmtKind::Ghost(Block::new(vec![statement(
            StmtKind::Call {
                callee: id(2),
                type_args: vec![],
                args: vec![],
                dest: Some(Place::deref(pointer)),
                site: SiteId(1),
            },
        )]))),
        returned(None),
    ]));
    let mut krate = source(f);
    krate.fns.push(proof_seven());
    user_error(&krate, "cannot assign to exec variable from proof mode");
}

#[test]
fn executable_borrow_cannot_access_a_proof_carrier_prefix() {
    let mut f = function(1, Mode::Exec, Ty::Unit, Mode::Exec);
    let pointer = add(&mut f, reference(), Mode::Proof, LocalKind::Param);
    let loan = add(&mut f, reference(), Mode::Exec, LocalKind::Let);
    f.body = Body::Stmts(Block::new(vec![
        statement(StmtKind::Let {
            local: loan,
            init: None,
        }),
        statement(StmtKind::BorrowMut {
            dest: loan,
            place: Place::deref(pointer),
        }),
        returned(None),
    ]));
    user_error(
        &source(f),
        "cannot access non-exec place in executable code",
    );
}

#[test]
fn executable_read_cannot_access_a_proof_carrier_prefix() {
    let mut f = function(1, Mode::Exec, Ty::Unit, Mode::Exec);
    let pointer = add(&mut f, reference(), Mode::Proof, LocalKind::Param);
    let value = add(&mut f, scalar(), Mode::Exec, LocalKind::Let);
    f.body = Body::Stmts(Block::new(vec![
        statement(StmtKind::Let {
            local: value,
            init: Some(Expr::read(Place::deref(pointer), scalar(), span())),
        }),
        returned(None),
    ]));
    user_error(&source(f), "expression has mode proof, expected mode exec");
}

#[test]
fn spec_reference_remains_read_only_through_further_projections() {
    let mut f = function(1, Mode::Proof, Ty::Unit, Mode::Proof);
    let pointer = add(
        &mut f,
        Ty::MutRef(Box::new(Ty::Tuple(vec![scalar()]))),
        Mode::Spec,
        LocalKind::Param,
    );
    f.body = Body::Stmts(Block::new(vec![
        statement(StmtKind::Assign {
            place: Place {
                local: pointer,
                projections: vec![Projection::Deref, Projection::TupleField(0)],
            },
            value: integer(7),
        }),
        returned(None),
    ]));
    user_error(
        &source(f),
        "cannot mutate through a spec-mode mutable reference",
    );
}

fn field_read(target: Mode, field: Mode) -> VcCrate {
    let mut f = function(1, Mode::Exec, Ty::Unit, Mode::Exec);
    let record = add(&mut f, record_type(), Mode::Exec, LocalKind::Param);
    let value = add(&mut f, scalar(), target, LocalKind::Let);
    let binding = statement(StmtKind::Let {
        local: value,
        init: Some(project(read(record, record_type()), 0)),
    });
    let binding = if target == Mode::Proof {
        statement(StmtKind::Ghost(Block::new(vec![binding])))
    } else {
        binding
    };
    f.body = Body::Stmts(Block::new(vec![binding, returned(None)]));
    let mut krate = source(f);
    krate.adts.push(record_decl(field));
    krate
}

#[test]
fn spec_field_read_is_not_an_executable_value() {
    user_error(
        &field_read(Mode::Exec, Mode::Spec),
        "expression has mode spec, expected mode exec",
    );
}

#[test]
fn spec_field_read_is_not_a_tracked_value() {
    user_error(
        &field_read(Mode::Proof, Mode::Spec),
        "expression has mode spec, expected mode proof",
    );
}

#[test]
fn proof_field_read_is_not_an_executable_value() {
    user_error(
        &field_read(Mode::Exec, Mode::Proof),
        "expression has mode proof, expected mode exec",
    );
}

#[test]
fn field_metadata_survives_pretty_rendering() {
    let krate = field_read(Mode::Spec, Mode::Spec);
    clean(&krate);
    assert!(pretty::crate_to_string(&krate).contains("spec selected:"));
    assert_eq!(SCHEMA, "trust-vc.vcir@16");
}

#[test]
fn constructor_checks_each_declared_field_context_separately() {
    let mut f = function(1, Mode::Exec, Ty::Unit, Mode::Exec);
    let snapshot = add(&mut f, scalar(), Mode::Spec, LocalKind::Param);
    let record = add(&mut f, record_type(), Mode::Exec, LocalKind::Let);
    f.body = Body::Stmts(Block::new(vec![
        statement(StmtKind::Let {
            local: record,
            init: Some(Expr::new(
                record_type(),
                span(),
                ExprKind::Ctor {
                    adt: adt_id(),
                    variant: 0,
                    fields: vec![read(snapshot, scalar()), integer(0)],
                },
            )),
        }),
        returned(None),
    ]));
    let mut krate = source(f);
    krate.adts.push(record_decl(Mode::Spec));
    clean(&krate);
    krate.adts[0].variants[0].fields[0].mode = Mode::Exec;
    user_error(&krate, "expression has mode spec, expected mode exec");
}

#[test]
fn call_arguments_use_formal_modes_instead_of_one_call_wide_flag() {
    let mut target = function(2, Mode::Exec, Ty::Unit, Mode::Exec);
    add(&mut target, scalar(), Mode::Spec, LocalKind::Param);
    let mut caller = function(1, Mode::Exec, Ty::Unit, Mode::Exec);
    let record = add(&mut caller, record_type(), Mode::Exec, LocalKind::Param);
    caller.body = Body::Stmts(Block::new(vec![
        statement(StmtKind::Call {
            callee: target.id,
            type_args: vec![],
            args: vec![project(read(record, record_type()), 0)],
            dest: None,
            site: SiteId(1),
        }),
        returned(None),
    ]));
    let mut krate = source(caller);
    krate.adts.push(record_decl(Mode::Spec));
    krate.fns.push(target);
    clean(&krate);
    krate.fns[1].locals[1].mode = Mode::Exec;
    user_error(&krate, "expression has mode spec, expected mode exec");
}

#[test]
fn legacy_mutable_reference_mode_policy_is_preserved() {
    let mut f = function(1, Mode::Proof, Ty::Unit, Mode::Proof);
    let pointer = add(
        &mut f,
        Ty::Ref {
            mutable: true,
            inner: Box::new(scalar()),
        },
        Mode::Proof,
        LocalKind::Param,
    );
    f.body = Body::Stmts(Block::new(vec![
        statement(StmtKind::Assign {
            place: Place::deref(pointer),
            value: integer(7),
        }),
        returned(None),
    ]));
    clean(&source(f));
}

#[test]
fn unit_consumption_does_not_reclassify_its_raw_spec_producer() {
    let mut target = function(2, Mode::Spec, Ty::Unit, Mode::Spec);
    target.body = Body::Spec(Expr::new(Ty::Unit, span(), ExprKind::Lit(Lit::Unit)));
    let mut caller = function(1, Mode::Proof, Ty::Unit, Mode::Proof);
    caller.body = Body::Stmts(Block::new(vec![returned(Some(Expr::new(
        Ty::Unit,
        span(),
        ExprKind::Call {
            callee: target.id,
            type_args: vec![],
            args: vec![],
        },
    )))]));
    let mut krate = source(caller);
    krate.fns.push(target);
    clean(&krate);
}
