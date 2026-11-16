// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn generic_nested_field_modes_survive_type_substitution() {
    let inner = adt_id();
    let outer = AdtId(DefHash::new(191, 101));
    let mut inner_decl = record_decl(Mode::Spec);
    inner_decl.type_params.push("T".into());
    inner_decl.variants[0].fields[0].ty = Ty::Param(0);
    let outer_decl = AdtDecl {
        id: outer,
        name: "Outer".into(),
        type_params: vec!["T".into()],
        span: span(),
        kind: AdtKind::Struct,
        variants: vec![VariantDecl {
            name: "Outer".into(),
            fields: vec![FieldDecl {
                name: "nested".into(),
                ty: Ty::Adt(inner, vec![Ty::Param(0)]),
                mode: Mode::Exec,
            }],
        }],
    };
    let mut f = function(1, Mode::Exec, Ty::Unit, Mode::Exec);
    let record = add(
        &mut f,
        Ty::Adt(outer, vec![scalar()]),
        Mode::Exec,
        LocalKind::Param,
    );
    let snapshot = add(&mut f, scalar(), Mode::Spec, LocalKind::Let);
    let value = Expr::read(
        Place {
            local: record,
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
        },
        scalar(),
        span(),
    );
    f.body = Body::Stmts(Block::new(vec![
        statement(StmtKind::Let {
            local: snapshot,
            init: Some(value),
        }),
        returned(None),
    ]));
    let mut krate = source(f);
    krate.adts = vec![inner_decl, outer_decl];
    clean(&krate);
    krate.fns[0].locals[snapshot.index()].mode = Mode::Exec;
    user_error(&krate, "expression has mode spec, expected mode exec");
}

#[test]
fn a_proof_field_prefix_cannot_become_executable_by_dereferencing_it() {
    for borrow in [false, true] {
        let mut f = function(1, Mode::Exec, Ty::Unit, Mode::Exec);
        let record = add(&mut f, record_type(), Mode::Exec, LocalKind::Param);
        let place = Place {
            local: record,
            projections: vec![
                Projection::Field {
                    variant: 0,
                    field: 0,
                },
                Projection::Deref,
            ],
        };
        let dest = add(
            &mut f,
            if borrow { reference() } else { scalar() },
            Mode::Exec,
            LocalKind::Let,
        );
        let mut stmts = if borrow {
            vec![
                statement(StmtKind::Let {
                    local: dest,
                    init: None,
                }),
                statement(StmtKind::BorrowMut { dest, place }),
            ]
        } else {
            vec![statement(StmtKind::Let {
                local: dest,
                init: Some(Expr::read(place, scalar(), span())),
            })]
        };
        stmts.push(returned(None));
        f.body = Body::Stmts(Block::new(stmts));
        let mut krate = source(f);
        let mut record = record_decl(Mode::Proof);
        record.variants[0].fields[0].ty = reference();
        krate.adts.push(record);
        user_error(
            &krate,
            if borrow {
                "cannot access non-exec place in executable code"
            } else {
                "expression has mode proof, expected mode exec"
            },
        );
    }
}
