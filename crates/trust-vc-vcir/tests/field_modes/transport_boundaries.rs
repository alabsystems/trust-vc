// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn nonowned_layout_dags_do_not_require_exponential_mode_expansion() {
    let ids = (0..60)
        .map(|n| AdtId(DefHash::new(193, n)))
        .collect::<Vec<_>>();
    let ty = Ty::Adt(ids[59], vec![]);
    let input = LocalId(2);
    let mut krate = fixture(
        ty.clone(),
        vec![statement(StmtKind::Call {
            callee: id(3),
            type_args: vec![],
            args: vec![read(input, ty.clone())],
            dest: Some(Place::local(RESULT)),
            site: SiteId(2),
        })],
        Mode::Proof,
    );
    assert_eq!(
        add(&mut krate.fns[0], ty.clone(), Mode::Proof, LocalKind::Param),
        input
    );
    let mut target = function(3, Mode::Proof, ty.clone(), Mode::Proof);
    let parameter = add(&mut target, ty.clone(), Mode::Proof, LocalKind::Param);
    target.body = Body::Stmts(Block::new(vec![returned(Some(read(parameter, ty)))]));
    krate.fns.push(target);
    for (index, id) in ids.iter().enumerate() {
        let field = if index == 0 {
            scalar()
        } else {
            Ty::Adt(ids[index - 1], vec![])
        };
        let fields = (0..if index == 0 { 1 } else { 2 })
            .map(|n| FieldDecl {
                name: format!("field{n}"),
                ty: field.clone(),
                mode: Mode::Exec,
            })
            .collect();
        krate.adts.push(AdtDecl {
            id: *id,
            name: format!("Dag{index}"),
            type_params: vec![],
            span: span(),
            kind: AdtKind::Struct,
            variants: vec![VariantDecl {
                name: "Node".into(),
                fields,
            }],
        });
    }
    // This asks WF for value modes, not the VC generator for a huge value.
    clean(&krate);
}

#[test]
fn owned_reference_snapshots_and_unknown_generic_values_remain_spec() {
    for ty in [reference(), Ty::Param(0)] {
        let original = LocalId(2);
        let mut krate = fixture(
            ty.clone(),
            vec![assign(read(original, ty.clone()))],
            Mode::Proof,
        );
        if ty == Ty::Param(0) {
            krate.fns[0].type_params.push("T".into());
            krate.fns[1].type_params.push("T".into());
            let Body::Stmts(block) = &mut krate.fns[0].body else {
                panic!("statement body");
            };
            let StmtKind::Call { type_args, .. } = &mut block.stmts[2].kind else {
                panic!("consumer call");
            };
            type_args.push(Ty::Param(0));
        }
        assert_eq!(
            add(&mut krate.fns[0], ty, Mode::Proof, LocalKind::Param),
            original
        );
        mode_error(&krate);
    }
}

#[test]
fn a_proof_carrier_prefix_cannot_be_laundered_through_a_scalar_temp() {
    let mut target = function(2, Mode::Exec, Ty::Unit, Mode::Exec);
    add(&mut target, scalar(), Mode::Exec, LocalKind::Param);
    let mut caller = function(1, Mode::Exec, Ty::Unit, Mode::Exec);
    let temp = add(&mut caller, scalar(), Mode::Spec, LocalKind::Temp);
    caller.locals[temp.index()].prophecy = DeclProphecy::DelayedInfer;
    let pointer = add(&mut caller, reference(), Mode::Proof, LocalKind::Param);
    caller.body = Body::Stmts(Block::new(vec![
        statement(StmtKind::Let {
            local: temp,
            init: None,
        }),
        statement(StmtKind::Ghost(Block::new(vec![statement(
            StmtKind::Assign {
                place: Place::local(temp),
                value: Expr::read(Place::deref(pointer), scalar(), span()),
            },
        )]))),
        statement(StmtKind::Call {
            callee: target.id,
            type_args: vec![],
            args: vec![read(temp, scalar())],
            dest: None,
            site: SiteId(1),
        }),
        returned(None),
    ]));
    let mut krate = source(caller);
    krate.fns.push(target);
    user_error(&krate, "expression has mode proof, expected mode exec");
}

#[test]
fn a_ghost_producer_cannot_export_exec_authority_through_an_outer_temp() {
    for ghost in [false, true] {
        let mut target = function(2, Mode::Exec, Ty::Unit, Mode::Exec);
        add(&mut target, Ty::Bool, Mode::Exec, LocalKind::Param);
        let mut caller = function(1, Mode::Exec, Ty::Unit, Mode::Exec);
        let temp = add(&mut caller, Ty::Bool, Mode::Spec, LocalKind::Temp);
        caller.locals[temp.index()].prophecy = DeclProphecy::DelayedInfer;
        let choice = add(&mut caller, Ty::Bool, Mode::Spec, LocalKind::Param);
        let condition = if ghost {
            read(choice, Ty::Bool)
        } else {
            boolean(false)
        };
        let producer = Block::new(vec![branch(
            condition,
            vec![assign(boolean(false))],
            vec![assign(boolean(true))],
        )]);
        let producer = if ghost {
            StmtKind::Ghost(producer)
        } else {
            StmtKind::Block(producer)
        };
        caller.body = Body::Stmts(Block::new(vec![
            statement(StmtKind::Let {
                local: temp,
                init: None,
            }),
            statement(producer),
            statement(StmtKind::Call {
                callee: target.id,
                type_args: vec![],
                args: vec![read(temp, Ty::Bool)],
                dest: None,
                site: SiteId(1),
            }),
            returned(None),
        ]));
        assert_eq!(temp, RESULT);
        let mut krate = source(caller);
        krate.fns.push(target);
        if ghost {
            user_error(&krate, "expression has mode proof, expected mode exec");
        } else {
            clean(&krate);
        }
    }
}
