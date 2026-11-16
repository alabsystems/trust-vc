// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The classifier and CFG spend one original ledger, including refusal paths.
use super::*;
use crate::{AdtDecl, AdtId, DefHash, FieldDecl, SpanId, VariantDecl, VcCrate};

fn id() -> AdtId {
    AdtId(DefHash::new(149, 5001))
}
fn wrapped(argument: Ty) -> Ty {
    Ty::Adt(id(), vec![argument])
}
fn source() -> VcCrate {
    let mut source = crate::vcgen::closed_templates::tests::source();
    source.adts.push(AdtDecl {
        id: id(),
        name: "LedgerWrapper".into(),
        type_params: vec!["T".into()],
        span: SpanId(0),
        kind: AdtKind::Struct,
        variants: vec![VariantDecl {
            name: "LedgerWrapper".into(),
            fields: vec![FieldDecl {
                name: "value".into(),
                ty: Ty::Param(0),
                mode: Mode::Exec,
            }],
        }],
    });
    source
}

#[test]
fn classifier_and_cfg_spend_the_same_original_work_cell() {
    let source = source();
    let ctx = Ctx::new(&source);
    let decl = &source.fns[1];
    let classifier = Classifier::new(&ctx, decl);
    let before = classifier.work.remaining().get();
    assert!(classifier
        .contains(&wrapped(Ty::MutRef(Box::new(Ty::uint(32)))), SpanId(0))
        .unwrap());
    let classified = classifier.work.remaining().get();
    assert!(classified < before);
    let builder = Builder::new(&ctx, decl, &classifier).unwrap();
    assert!(std::ptr::eq(
        builder.work.remaining(),
        classifier.work.remaining()
    ));
    builder.charge(1).unwrap();
    assert_eq!(classifier.work.remaining().get(), classified - 1);
}

#[test]
fn one_short_classification_never_refills_or_returns_false_on_exhaustion() {
    let source = source();
    let ctx = Ctx::new(&source);
    let decl = &source.fns[1];
    let ty = wrapped(Ty::MutRef(Box::new(Ty::uint(32))));
    let probe = Classifier::new(&ctx, decl);
    let original = probe.work.remaining().get();
    assert!(probe.contains(&ty, SpanId(0)).unwrap());
    let cost = original - probe.work.remaining().get();
    assert!(cost > 1 && cost < original);

    // Preconsume the real original ledger. No substitute cap or refill API.
    let limited = Classifier::new(&ctx, decl);
    limited
        .work
        .charge(original - (cost - 1), SpanId(0))
        .unwrap();
    let problem = limited.contains(&ty, SpanId(0)).unwrap_err();
    assert_eq!(problem.tag, "resolution-size");
    let remaining = limited.work.remaining().get();
    assert!(limited.contains(&ty, SpanId(0)).is_err());
    assert!(limited.work.remaining().get() <= remaining);
}

#[test]
fn a_nominal_cycle_cannot_be_cached_as_nonowned() {
    let mut source = source();
    source.adts[0].variants[0].fields[0].ty = wrapped(Ty::Param(0));
    let ctx = Ctx::new(&source);
    let classifier = Classifier::new(&ctx, &source.fns[1]);
    for _ in 0..2 {
        let problem = classifier
            .contains(&wrapped(Ty::uint(32)), SpanId(0))
            .unwrap_err();
        assert_eq!(problem.tag, "resolution-type");
        assert_eq!(problem.detail, "cyclic ownership datatype");
    }
}

#[test]
fn classifier_reuse_requires_the_same_declaration_and_context() {
    let source = source();
    let ctx = Ctx::new(&source);
    let other = Ctx::new(&source);
    let decl = &source.fns[1];
    let copied = (*decl).clone();
    let classifier = Classifier::new(&ctx, decl);
    assert!(classifier.validate(&ctx, decl).is_ok());
    assert!(classifier.validate(&other, decl).is_err());
    assert!(classifier.validate(&ctx, &copied).is_err());
}
