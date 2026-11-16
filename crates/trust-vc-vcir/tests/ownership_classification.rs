// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Unused nominal inventory needs ownership classification, not a value layout.
use trust_vc_vcir::vcgen::{self, FnVcs};
use trust_vc_vcir::*;

#[path = "ownership_classification/effects.rs"]
mod effects;
#[path = "ownership_classification/helpers.rs"]
mod helpers;
#[path = "ownership_classification/layouts.rs"]
mod layouts;
#[cfg(feature = "solve")]
#[path = "ownership_classification/semantics.rs"]
mod semantics;

fn adt(index: u32) -> AdtId {
    AdtId(DefHash::new(149, u64::from(index)))
}

fn nonowned_dag(depth: u32) -> VcCrate {
    let span = SpanId(0);
    let mut source = VcCrate::new("unused nonowned nominal DAG");
    for index in 0..=depth {
        let fields = if index == 0 {
            vec![FieldDecl {
                name: "scalar".into(),
                ty: Ty::uint(32),
                mode: Mode::Exec,
            }]
        } else {
            let child = Ty::Adt(adt(index - 1), vec![]);
            vec![
                FieldDecl {
                    name: "left".into(),
                    ty: child.clone(),
                    mode: Mode::Exec,
                },
                FieldDecl {
                    name: "right".into(),
                    ty: child,
                    mode: Mode::Exec,
                },
            ]
        };
        source.adts.push(AdtDecl {
            id: adt(index),
            name: format!("Nonowned{index}"),
            type_params: vec![],
            span,
            kind: AdtKind::Struct,
            variants: vec![VariantDecl {
                name: format!("Nonowned{index}"),
                fields,
            }],
        });
    }
    source.fns.push(FnDecl {
        id: FnId(DefHash::new(149, 1001)),
        name: "return_without_materializing_unused_inventory".into(),
        span,
        mode: Mode::Exec,
        role: FnRole::Item,
        kind: FnKind::Function,
        type_params: vec![],
        locals: vec![
            LocalDecl {
                name: "return".into(),
                ty: Ty::Unit,
                mode: Mode::Exec,
                kind: LocalKind::Return,
                prophecy: DeclProphecy::Default,
                mutable: false,
                span,
            },
            LocalDecl {
                name: "unused".into(),
                ty: Ty::Adt(adt(depth), vec![]),
                mode: Mode::Exec,
                kind: LocalKind::Let,
                prophecy: DeclProphecy::Default,
                mutable: false,
                span,
            },
        ],
        params: vec![],
        ret: LocalId(0),
        requires: vec![],
        ensures: vec![],
        recommends: vec![],
        decreases: vec![],
        decreases_when: None,
        decreases_by: None,
        unwind: None,
        attrs: FnAttrs::default(),
        body: Body::Stmts(Block::new(vec![Stmt::new(
            span,
            StmtKind::Return {
                value: None,
                site: SiteId(0),
            },
        )])),
    });
    source
}

#[test]
fn unused_nonowned_nominal_dag_needs_no_affine_resolution() {
    // This is intentionally deeper than the old recursive holds guard. Its
    // first depth-65 path returns conservative true, so the old implementation
    // reaches the candidate-depth refusal in bounded work instead of exploring
    // billions of duplicated nonowned leaves. No value is ever constructed.
    let source = nonowned_dag(70);
    let errors = check_crate(&source);
    assert!(errors.is_empty(), "{errors:?}");
    let function = &source.fns[0];
    assert_eq!(function.role, FnRole::Item);
    assert!(function.params.is_empty() && function.attrs.instance.is_none());
    assert!(!function.attrs.external_body && function.type_params.is_empty());
    let Body::Stmts(body) = &function.body else {
        panic!("actual statement body");
    };
    assert_eq!(body.stmts.len(), 1);
    assert!(matches!(
        body.stmts[0].kind,
        StmtKind::Return { value: None, .. }
    ));
    let generated = vcgen::generate(&source);
    assert_eq!(generated.fns.len(), 1);
    let Some(FnVcs::Checks(checks)) = generated.get(function.id) else {
        panic!("a nonowned unused DAG must not require affine layout: {generated:?}");
    };
    assert!(checks.is_empty(), "{checks:?}");
}
