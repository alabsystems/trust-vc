// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The original generic body checks unwind promises with an unused owned T.

use super::*;
use trust_vc_vcir::solve::{check_detailed, Limits, Verdict};
use trust_vc_vcir::vcgen::term::Term;
use trust_vc_vcir::vcgen::{CheckKind, FnVcs, QueryGroup};

fn source(negate_argument: bool) -> VcCrate {
    let mut caller = function(1);
    caller.name = "generic_caller".into();
    caller.type_params = vec!["T".into()];
    caller.locals[1].name = "enabled".into();
    let mut owned = local(Ty::Param(0), LocalKind::Param);
    owned.name = "_value".into();
    caller.locals.push(owned);
    caller.params = vec![LocalId(2), LocalId(1)];
    caller.unwind = Some(UnwindSpec::NoUnwindWhen(parameter()));

    let mut callee = function(2);
    callee.name = "conditional".into();
    callee.unwind = Some(UnwindSpec::NoUnwindWhen(parameter()));
    caller.body = Body::Stmts(Block::new(vec![
        Stmt::new(
            SpanId(50),
            StmtKind::Call {
                callee: callee.id,
                type_args: vec![],
                args: vec![if negate_argument {
                    not(parameter())
                } else {
                    parameter()
                }],
                dest: None,
                site: SiteId(3),
            },
        ),
        statement(StmtKind::Return {
            value: None,
            site: SiteId(9),
        }),
    ]));
    let mut source = VcCrate::new("unbounded generic caller unwind implication");
    source.fns = vec![caller, callee];
    source
}

fn require(negate_argument: bool, proved: bool) {
    let source = source(negate_argument);
    let caller = &source.fns[0];
    assert_eq!((caller.id, caller.role), (id(1), FnRole::Item));
    assert_eq!(caller.type_params, vec!["T"]);
    assert!(caller.attrs.instance.is_none());
    assert!(!caller.attrs.external_body);
    assert_eq!(caller.params, vec![LocalId(2), LocalId(1)]);
    let owned = caller.local(LocalId(2)).unwrap();
    assert_eq!((owned.kind, owned.mode), (LocalKind::Param, Mode::Exec));
    assert_eq!(owned.ty, Ty::Param(0));
    assert_eq!(owned.name, "_value");
    let errors = check_crate(&source);
    assert!(errors.is_empty(), "{errors:?}");
    let generated = vcgen::generate(&source);
    assert_eq!(generated.fns.len(), 2);
    for declaration in &source.fns {
        assert!(
            matches!(generated.get(declaration.id), Some(FnVcs::Checks(_))),
            "{generated:?}"
        );
    }
    let Some(FnVcs::Checks(checks)) = generated.get(caller.id) else {
        unreachable!()
    };
    assert_eq!(checks.len(), 1, "{checks:?}");
    let check = &checks[0];
    assert_eq!(check.site, SiteId(3));
    assert_eq!(check.group, QueryGroup::Body);
    assert_eq!(
        check.kind,
        CheckKind::Unwind {
            call: SpanId(50),
            callee: id(2)
        }
    );
    assert!(!check.approximate && !check.order_unknown);
    assert!(check.query.architectures.is_none());
    assert!(check.query.bitvector.is_none());
    // Both verdicts must pass through Core and AY, not the literal-true
    // shortcut in the ordinary scalar dispatcher.
    assert_ne!(check.query.goal, Term::Bool(true));
    let answer = check_detailed(
        &check.query,
        "original generic caller unwind implication",
        &Limits::default(),
    );
    assert!(
        if proved {
            matches!(answer.verdict, Verdict::Proved { .. })
        } else {
            matches!(answer.verdict, Verdict::Refuted { .. })
        },
        "expected proved={proved}: {answer:?}; check={check:?}"
    );
}

#[test]
fn generic_caller_proves_matching_condition_with_unused_owned_parameter() {
    require(false, true);
}

#[test]
fn generic_caller_refutes_opposite_condition_with_unused_owned_parameter() {
    require(true, false);
}
