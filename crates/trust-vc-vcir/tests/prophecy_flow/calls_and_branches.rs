//! Prophecy-flow regression cases. Root wrappers preserve the test roster.

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

pub(super) fn non_ghost_declarations_and_exec_arguments_reject_prophetic_data() {
    let mut sink = function(2, Mode::Exec, Ty::Unit);
    add(
        &mut sink,
        Ty::Bool,
        Mode::Exec,
        LocalKind::Param,
        DeclProphecy::Default,
    );
    let mut caller = function(3, Mode::Exec, Ty::Unit);
    let target = add(
        &mut caller,
        Ty::Bool,
        Mode::Exec,
        LocalKind::Let,
        DeclProphecy::Default,
    );
    caller.body = Body::Stmts(Block::new(vec![
        let_stmt(target, Some(call(1, Ty::Bool, vec![]))),
        invoke(2, vec![call(1, Ty::Bool, vec![])], None, 1),
    ]));
    let krate = source(vec![sink, caller]);
    rejected(&krate, 3, "declaration of non-ghost variables");
    rejected(&krate, 3, "argument to exec-mode function");
}

pub(super) fn exec_calls_and_returns_cannot_be_prophecy_conditional() {
    let sink = function(2, Mode::Exec, Ty::Unit);
    let mut caller = function(3, Mode::Exec, Ty::Unit);
    caller.body = Body::Stmts(Block::new(vec![branch(
        call(1, Ty::Bool, vec![]),
        vec![
            invoke(2, vec![], None, 1),
            stmt(StmtKind::Return {
                value: None,
                site: SiteId(2),
            }),
        ],
    )]));
    let krate = source(vec![sink, caller]);
    rejected(
        &krate,
        3,
        "call to exec-mode function cannot occur in prophecy-conditional context",
    );
    rejected(
        &krate,
        3,
        "return cannot occur in prophecy-conditional context",
    );
}

pub(super) fn proof_calls_allow_only_spec_parameters_and_spec_or_unit_results() {
    for (parameter_mode, return_mode, result, allowed) in [
        (Mode::Spec, Mode::Spec, Ty::Bool, true),
        (Mode::Spec, Mode::Proof, Ty::Unit, true),
        (Mode::Proof, Mode::Spec, Ty::Bool, false),
        (Mode::Spec, Mode::Proof, Ty::Bool, false),
    ] {
        let mut lemma = function(2, Mode::Proof, result);
        lemma.locals[0].mode = return_mode;
        add(
            &mut lemma,
            Ty::Bool,
            parameter_mode,
            LocalKind::Param,
            DeclProphecy::Default,
        );
        let mut caller = function(3, Mode::Proof, Ty::Unit);
        caller.body = Body::Stmts(Block::new(vec![branch(
            call(1, Ty::Bool, vec![]),
            vec![invoke(2, vec![call(1, Ty::Bool, vec![])], None, 1)],
        )]));
        let krate = source(vec![lemma, caller]);
        if allowed {
            accepted(&krate);
        } else {
            rejected(
                &krate,
                3,
                "argument to proof-mode function with tracked parameters",
            );
            rejected(
                &krate,
                3,
                "call to proof-mode function with tracked parameters cannot occur",
            );
        }
    }
}

pub(super) fn pure_spec_result_proof_call_preserves_argument_taint_at_its_destination() {
    let mut lemma = function(2, Mode::Proof, Ty::Bool);
    let param = add(
        &mut lemma,
        Ty::Bool,
        Mode::Spec,
        LocalKind::Param,
        DeclProphecy::Default,
    );
    lemma.body = Body::Stmts(Block::new(vec![stmt(StmtKind::Return {
        value: Some(read(param, Ty::Bool)),
        site: SiteId(1),
    })]));
    let mut caller = function(3, Mode::Proof, Ty::Bool);
    let target = add(
        &mut caller,
        Ty::Bool,
        Mode::Spec,
        LocalKind::Let,
        DeclProphecy::DelayedInfer,
    );
    caller.body = Body::Stmts(Block::new(vec![
        let_stmt(target, None),
        invoke(2, vec![call(1, Ty::Bool, vec![])], Some(target), 1),
        stmt(StmtKind::Return {
            value: Some(read(target, Ty::Bool)),
            site: SiteId(2),
        }),
    ]));
    rejected(&source(vec![lemma, caller]), 3, "return value");
}

pub(super) fn generated_conditional_results_join_both_branches_independently() {
    // This is the actual native lowering of an effectful expression result:
    // a generated Spec Temp, no initializer, and whole-temp writes per arm.
    for (yes, no, tainted) in [
        (boolean(false), boolean(true), false),
        (boolean(false), call(1, Ty::Bool, vec![]), true),
        (call(1, Ty::Bool, vec![]), boolean(false), true),
    ] {
        let mut consumer = function(2, Mode::Proof, Ty::Unit);
        add(
            &mut consumer,
            Ty::Bool,
            Mode::Spec,
            LocalKind::Param,
            DeclProphecy::Default,
        );
        let mut caller = function(3, Mode::Proof, Ty::Unit);
        let result = add(
            &mut caller,
            Ty::Bool,
            Mode::Spec,
            LocalKind::Temp,
            DeclProphecy::DelayedInfer,
        );
        caller.body = Body::Stmts(Block::new(vec![
            let_stmt(result, None),
            stmt(StmtKind::If {
                cond: boolean(false),
                then_block: Block::new(vec![assign(result, yes)]),
                else_block: Block::new(vec![assign(result, no)]),
            }),
            invoke(2, vec![read(result, Ty::Bool)], None, 1),
        ]));
        let mut krate = source(vec![consumer, caller]);
        accepted(&krate); // A purely spec proof consumer accepts either result.
        krate.fns[1].locals[1].mode = Mode::Proof;
        if tainted {
            rejected(
                &krate,
                3,
                "argument to proof-mode function with tracked parameters",
            );
        } else {
            accepted(&krate);
        }
    }
}

pub(super) fn generated_short_circuit_results_include_condition_and_require_both_initializations() {
    let mut consumer = function(2, Mode::Proof, Ty::Unit);
    add(
        &mut consumer,
        Ty::Bool,
        Mode::Proof,
        LocalKind::Param,
        DeclProphecy::Default,
    );
    let mut caller = function(3, Mode::Proof, Ty::Unit);
    let result = add(
        &mut caller,
        Ty::Bool,
        Mode::Spec,
        LocalKind::Temp,
        DeclProphecy::DelayedInfer,
    );
    caller.body = Body::Stmts(Block::new(vec![
        let_stmt(result, None),
        stmt(StmtKind::If {
            cond: call(1, Ty::Bool, vec![]),
            then_block: Block::new(vec![assign(result, boolean(true))]),
            else_block: Block::new(vec![assign(result, boolean(false))]),
        }),
        invoke(2, vec![read(result, Ty::Bool)], None, 1),
    ]));
    rejected(
        &source(vec![consumer.clone(), caller.clone()]),
        3,
        "argument to proof-mode function with tracked parameters",
    );
    caller.body = Body::Stmts(Block::new(vec![
        let_stmt(result, None),
        branch(boolean(false), vec![assign(result, boolean(true))]),
        invoke(2, vec![read(result, Ty::Bool)], None, 1),
    ]));
    rejected(
        &source(vec![consumer, caller]),
        3,
        "uninitialized infer-mode variable",
    );
}
