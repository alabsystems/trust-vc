//! Prophecy-flow regression cases. Root wrappers preserve the test roster.

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

pub(super) fn prophetic_functions_still_cannot_use_prophecy_for_termination_measures() {
    let mut seed = function(2, Mode::Spec, Ty::int());
    seed.attrs.prophetic = true;
    seed.body = Body::Spec(integer(0));
    let mut caller = function(3, Mode::Spec, Ty::Bool);
    caller.attrs.prophetic = true;
    caller.decreases.push(call(2, Ty::int(), vec![]));
    caller.body = Body::Spec(boolean(true));
    rejected(&source(vec![seed, caller]), 3, "'decreases' clause");
}

pub(super) fn loop_condition_retains_taint_from_its_computation_block() {
    let mut caller = function(2, Mode::Exec, Ty::Unit);
    let temp = add(
        &mut caller,
        Ty::Bool,
        Mode::Spec,
        LocalKind::Temp,
        DeclProphecy::Default,
    );
    caller.body = Body::Stmts(Block::new(vec![loop_stmt(
        Some(LoopCond {
            block: Block::new(vec![let_stmt(temp, Some(call(1, Ty::Bool, vec![])))]),
            expr: read(temp, Ty::Bool),
        }),
        vec![],
        vec![],
    )]));
    rejected(&source(vec![caller]), 2, "loop condition");
}

pub(super) fn loop_decreases_reject_prophetic_values() {
    let mut seed = function(2, Mode::Spec, Ty::int());
    seed.attrs.prophetic = true;
    seed.body = Body::Spec(integer(0));
    let mut caller = function(3, Mode::Exec, Ty::Unit);
    caller.body = Body::Stmts(Block::new(vec![loop_stmt(
        None,
        vec![],
        vec![call(2, Ty::int(), vec![])],
    )]));
    rejected(&source(vec![seed, caller]), 3, "'decreases' clause");
}

pub(super) fn loop_and_loop_control_cannot_depend_on_prophetic_conditions() {
    let mut caller = function(2, Mode::Exec, Ty::Unit);
    caller.body = Body::Stmts(Block::new(vec![branch(
        call(1, Ty::Bool, vec![]),
        vec![loop_stmt(None, vec![], vec![])],
    )]));
    rejected(
        &source(vec![caller.clone()]),
        2,
        "loop cannot occur in prophecy-conditional context",
    );
    caller.body = Body::Stmts(Block::new(vec![loop_stmt(
        None,
        vec![branch(
            call(1, Ty::Bool, vec![]),
            vec![
                stmt(StmtKind::Break {
                    target: LoopId(1),
                    site: SiteId(20),
                }),
                stmt(StmtKind::Continue {
                    target: LoopId(1),
                    site: SiteId(21),
                }),
            ],
        )],
        vec![],
    )]));
    let krate = source(vec![caller]);
    rejected(
        &krate,
        2,
        "break cannot occur in prophecy-conditional context",
    );
    rejected(
        &krate,
        2,
        "continue cannot occur in prophecy-conditional context",
    );
}
