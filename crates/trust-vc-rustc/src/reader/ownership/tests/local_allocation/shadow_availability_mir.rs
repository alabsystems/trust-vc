// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Actual built MIR retains typed helper calls and real normal continuations.
use super::*;
use rustc_middle::mir;

pub(super) fn calls(tcx: TyCtxt<'_>, owner: LocalDefId, helpers: Helpers, expected: Counts) {
    let built = tcx.mir_built(owner);
    assert!(!built.is_stolen());
    let body = built.borrow();
    let mut erased = 0;
    let mut shadow = 0;
    let mut tie = 0;
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
        let function = func.ty(&body.local_decls, tcx);
        let ty::FnDef(definition, parameters) = function.kind() else {
            continue;
        };
        if ![helpers.erased, helpers.shadow, helpers.tie].contains(definition) {
            continue;
        }
        let parameters = parameters.no_bound_vars().unwrap();
        assert_eq!(parameters.len(), 2);
        let first = parameters[0].as_type().unwrap();
        let second = parameters[1].as_type().unwrap();
        let result = destination.ty(&body.local_decls, tcx).ty;
        assert!(!result.is_never());
        let normal = target.expect("a shadow helper must not erase the normal continuation");
        assert!(!matches!(
            body.basic_blocks[normal].terminator().kind,
            mir::TerminatorKind::Unreachable
        ));
        if *definition == helpers.tie {
            tie += 1;
            assert_eq!(args.len(), 2);
            let ty::Ref(_, inner, ast::Mutability::Mut) = result.kind() else {
                panic!("actual tied mutable reference result");
            };
            assert_eq!(*inner, first);
            assert!(function.fn_sig(tcx).bound_vars().len() == 1);
        } else {
            assert_eq!(args.len(), 1);
            assert_eq!(result, second);
            if *definition == helpers.erased {
                erased += 1;
            } else {
                shadow += 1;
                let ty::Tuple(fields) = first.kind() else {
                    panic!("shadow read tuple argument");
                };
                assert_eq!(fields.len(), 1);
                assert!(
                    matches!(fields[0].kind(),ty::Ref(_,inner,ast::Mutability::Not) if *inner==result)
                );
            }
        }
    }
    assert_eq!(
        (erased, shadow, tie),
        (
            expected.seeds + expected.erased_reads + 2 * expected.resets,
            expected.reads,
            expected.ties
        )
    );
}
