// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::SourceLocation;
use proc_macro2::Span;
use syn::spanned::Spanned;

#[test]
fn a_synthesized_span_yields_no_location() {
    // `Span::call_site()` is what every token rebuilt by a normalization pass
    // carries, and what `syn`'s `Spanned` falls back to when a join fails.
    assert_eq!(SourceLocation::from_span(Span::call_site()), None);
}

/// The measurement this rejection rests on: a synthesized span does NOT say
/// "no line" — it says LINE 1, which would be reported as the top of whatever
/// file the obligation was attributed to.
#[test]
fn a_synthesized_span_would_otherwise_have_claimed_line_one() {
    let span = Span::call_site();
    assert_eq!(span.start().line, 1, "call_site claims line 1, not line 0");
    assert!(
        span.byte_range().is_empty(),
        "and the empty byte range is what tells it apart"
    );
}

#[test]
fn a_parsed_span_yields_one_based_line_and_column() {
    let source = "fn f() {\n    assert!(true);\n}\n";
    let file: syn::File = syn::parse_str(source).expect("parses");
    let syn::Item::Fn(item) = &file.items[0] else {
        panic!("expected fn");
    };
    let stmt = &item.block.stmts[0];
    let location = SourceLocation::from_span(stmt.span()).expect("parsed span has a position");
    assert_eq!(location.line(), 2);
    // Four spaces of indent: rustc would say column 5, not proc-macro2's 4.
    assert_eq!(location.column(), 5);
    assert_eq!(location.render(), "2:5");
    assert_eq!(
        location.with_file("evals/verus/ported/choose.rs").render(),
        "evals/verus/ported/choose.rs:2:5"
    );
}

#[test]
fn or_file_never_overwrites_an_attached_file() {
    let location = SourceLocation::new(7, 3).with_file("a.rs");
    assert_eq!(location.or_file("b.rs").render(), "a.rs:7:3");
    assert_eq!(
        SourceLocation::new(7, 3).or_file("b.rs").render(),
        "b.rs:7:3"
    );
}

#[test]
fn untyped_obligation_location_setters_keep_both_channels_consistent() {
    use crate::vc::ProofObligation;

    let source = SourceLocation::new(2, 3).with_file("source:unit.rs");
    let rendered = source.render();
    let same = ProofObligation::ensures("post", "true")
        .with_source_location(source.clone())
        .with_location(rendered.clone());
    assert_eq!(same.location(), Some(rendered.as_str()));
    assert_eq!(same.source_location(), Some(&source));

    let replaced = same
        .with_location("other:unit.rs:99:1")
        .or_source_location(SourceLocation::new(7, 8));
    assert_eq!(replaced.location(), Some("other:unit.rs:99:1"));
    assert_eq!(replaced.source_location(), None);

    let restored = replaced.with_source_location(source.clone());
    assert_eq!(restored.location(), Some(rendered.as_str()));
    assert_eq!(restored.source_location(), Some(&source));
}

#[test]
fn typed_obligation_location_overrides_survive_conversion() {
    use crate::ir::TrustVcExpr;
    use crate::vc::TypedProofObligation;

    let source = SourceLocation::new(2, 3).with_file("source:unit.rs");
    let rendered = source.render();
    let same = TypedProofObligation::ensures("post", TrustVcExpr::BoolLit(true))
        .with_source_location(source.clone())
        .with_location(rendered.clone())
        .into_proof_obligation();
    assert_eq!(same.location(), Some(rendered.as_str()));
    assert_eq!(same.source_location(), Some(&source));

    let replaced = TypedProofObligation::ensures("post", TrustVcExpr::BoolLit(true))
        .with_source_location(source.clone())
        .with_location("other:unit.rs:99:1");
    assert_eq!(replaced.location(), Some("other:unit.rs:99:1"));
    let replaced = replaced.into_proof_obligation();
    assert_eq!(replaced.location(), Some("other:unit.rs:99:1"));
    assert_eq!(replaced.source_location(), None);

    let restored = TypedProofObligation::ensures("post", TrustVcExpr::BoolLit(true))
        .with_location("other:unit.rs:99:1")
        .with_source_location(source.clone())
        .into_proof_obligation();
    assert_eq!(restored.location(), Some(rendered.as_str()));
    assert_eq!(restored.source_location(), Some(&source));
}
