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
