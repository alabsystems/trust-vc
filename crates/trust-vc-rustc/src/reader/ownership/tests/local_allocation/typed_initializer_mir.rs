// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The actual built MIR contains a typed helper call and a normal successor.
use super::*;
use rustc_middle::{mir, ty};

pub(super) fn call(tcx: TyCtxt<'_>, owner: LocalDefId, helper: DefId) {
    let built = tcx.mir_built(owner);
    assert!(!built.is_stolen());
    let body = built.borrow();
    let mut calls = 0;
    for block in body.basic_blocks.iter() {
        let mir::TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } = &block.terminator().kind
        else {
            continue;
        };
        let ty::FnDef(definition, parameters) = func.ty(&body.local_decls, tcx).kind() else {
            continue;
        };
        if *definition != helper {
            continue;
        }
        calls += 1;
        let parameters = parameters.no_bound_vars().unwrap();
        assert_eq!(parameters.len(), 1);
        assert!(args.is_empty());
        let result = destination.ty(&body.local_decls, tcx).ty;
        assert_eq!(parameters[0].as_type(), Some(result));
        assert!(!result.is_never());
        let normal = target.expect("the helper must preserve a real normal continuation");
        assert!(!matches!(
            body.basic_blocks[normal].terminator().kind,
            mir::TerminatorKind::Unreachable
        ));
    }
    assert_eq!(
        calls, 1,
        "the actual target MIR must contain exactly one selected helper call"
    );
    // This borrow guard is dropped before mir_borrowck may steal built MIR.
}
