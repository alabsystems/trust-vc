// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{parse_function_by_name, parse_functions, try_parse_functions};

#[test]
fn parses_free_functions_methods_and_trait_items() {
    let source = r#"
fn free(x: i32) -> i32 { x + 1 }

struct Counter {
    value: u32,
}

impl Counter {
    fn get(&self) -> u32 {
        self.value
    }
}

trait Named {
    fn name(&self) -> &'static str;
}
"#;

    let signatures = parse_functions(source);
    let names: Vec<_> = signatures
        .iter()
        .map(|signature| signature.name.as_str())
        .collect();

    assert_eq!(signatures.len(), 3);
    assert_eq!(names, vec!["free", "get", "name"]);
}

#[test]
fn parses_functions_in_inline_modules() {
    let source = r#"
mod outer {
    mod inner {
        fn nested(value: u64) -> u64 {
            value
        }
    }
}
"#;

    let nested = parse_function_by_name(source, "nested").expect("nested function should exist");

    assert_eq!(nested.params, vec![("value".to_owned(), "u64".to_owned())]);
    assert_eq!(nested.return_type.as_deref(), Some("u64"));
    assert_eq!(
        nested.source.trim(),
        "fn nested(value: u64) -> u64 {\n            value\n        }"
    );
}

#[test]
fn extracts_exact_function_source_instead_of_entire_file() {
    let source = r#"
fn helper() {}

fn target(x: i32) -> i32 {
    x + 1
}

fn trailing() {}
"#;

    let target = parse_function_by_name(source, "target").expect("target should exist");

    assert_eq!(target.source, "fn target(x: i32) -> i32 {\n    x + 1\n}");
    assert!(!target.source.contains("helper"));
    assert!(!target.source.contains("trailing"));
}

#[test]
fn preserves_generics_lifetimes_and_self_receivers() {
    let source = r#"
struct Reader;

impl Reader {
    async fn borrow<'a, T>(&'a mut self, value: T) -> &'a T
    where
        T: Clone,
    {
        todo!()
    }
}
"#;

    let signature = parse_function_by_name(source, "borrow").expect("method should exist");

    assert!(signature.is_async);
    assert_eq!(
        signature.params[0],
        ("self".to_owned(), "&'a mut self".to_owned())
    );
    assert_eq!(signature.params[1], ("value".to_owned(), "T".to_owned()));
    assert_eq!(signature.return_type.as_deref(), Some("&'a T"));
    assert_eq!(signature.generics, vec!["'a".to_owned(), "T".to_owned()]);
    assert_eq!(signature.where_clause, vec!["T: Clone".to_owned()]);
}

#[test]
fn preserves_receiver_forms() {
    let source = r#"
struct Example;

impl Example {
    fn by_ref(&self) {}
    fn by_mut(&mut self) {}
    fn by_value(self) {}
}
"#;

    let signatures = parse_functions(source);

    assert_eq!(signatures[0].params[0].1, "&self");
    assert_eq!(signatures[1].params[0].1, "&mut self");
    assert_eq!(signatures[2].params[0].1, "self");
}

#[test]
fn reports_signature_start_and_item_length() {
    let source = r#"
#[inline]
fn marked() {}
"#;

    let signature = parse_function_by_name(source, "marked").expect("marked should exist");
    let start = signature.span_start.expect("signature start should exist");
    let length = signature.span_len.expect("item length should exist");

    assert!(source[start..].starts_with("fn marked"));
    assert_eq!(length, signature.source.len());
    assert_eq!(signature.source, "#[inline]\nfn marked() {}");
}

#[test]
fn parse_functions_returns_empty_on_invalid_source() {
    assert!(parse_functions("fn broken(").is_empty());
}

#[test]
fn try_parse_functions_returns_source_parse_error() {
    let error = try_parse_functions("fn broken(").expect_err("invalid source should fail");
    let message = error.to_string();

    assert!(message.contains("source parse error"));
}
