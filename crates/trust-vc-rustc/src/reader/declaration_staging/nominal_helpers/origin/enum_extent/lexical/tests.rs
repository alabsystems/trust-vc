// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Syntax components only; these cannot construct a native helper fact.

use super::*;

fn one(source: &str, kind: Kind) -> Result<(), &'static str> {
    partition(
        source,
        &[Part {
            start: 0,
            end: source.len(),
            kind,
        }],
    )
}

#[test]
fn outer_docs_match_original_syntax_independently_of_macro_reemission() {
    for text in [
        "/// a source doc",
        "/** a source doc */",
        "#[doc = \"source doc\"]",
        "#[doc = r#\"source #[tool] text\"#]",
    ] {
        assert!(one(text, Kind::Document).is_ok(), "{text}");
    }
    for text in [
        "//! inner",
        "/*! inner */",
        "//// ordinary",
        "/* ordinary */",
        "#[other = \"doc\"]",
        "#[doc(other)]",
        "#[doc = include_str!(\"x\")]",
    ] {
        assert!(one(text, Kind::Document).is_err(), "{text}");
    }
}

#[test]
fn attached_prefix_partition_allows_only_complete_attributes_and_ordinary_trivia() {
    let first = "/// Represents (typed) contents of memory.";
    let gap = "\n// ordinary explanation\n/* ordinary /* nested */ explanation */\n";
    let last = "#[verifier::accept_recursive_types(T)]";
    let source = format!("{first}{gap}{last}\n");
    let start = first.len() + gap.len();
    assert!(partition(
        &source,
        &[
            Part {
                start: 0,
                end: first.len(),
                kind: Kind::Document
            },
            Part {
                start,
                end: start + last.len(),
                kind: Kind::Attribute
            }
        ]
    )
    .is_ok());
}

#[test]
fn delimiters_in_strings_and_nested_token_groups_do_not_end_an_attribute() {
    for source in [
        r###"#[tool(value = r#"] /* not a comment */"#, [x], { nested: (x) })]"###,
        r#"#[r#tool::attribute("escaped \" ]", b']', /* ] */ (value))]"#,
        "#[bare::path]",
        "#[tool = true]",
        "#[tool = 17]",
    ] {
        assert!(one(source, Kind::Attribute).is_ok(), "{source}");
    }
}

#[test]
fn uncovered_docs_attributes_inner_syntax_and_code_are_not_trivia() {
    for gap in [
        "\n/// missing native slot\n",
        "\n#[tool]\n",
        "\nfn unrelated() {}\n",
        "\n//! inner\n",
        "\n/* unterminated\n",
    ] {
        let first = "#[first]";
        let last = "#[last]";
        let source = format!("{first}{gap}{last}");
        let start = first.len() + gap.len();
        assert!(
            partition(
                &source,
                &[
                    Part {
                        start: 0,
                        end: first.len(),
                        kind: Kind::Attribute
                    },
                    Part {
                        start,
                        end: source.len(),
                        kind: Kind::Attribute
                    }
                ]
            )
            .is_err(),
            "{gap}"
        );
    }
}

#[test]
fn duplicate_overlap_and_nonboundary_coordinates_are_refused() {
    let source = "#[first] #[last]";
    assert!(partition(
        source,
        &[
            Part {
                start: 0,
                end: 8,
                kind: Kind::Attribute
            },
            Part {
                start: 0,
                end: 8,
                kind: Kind::Attribute
            }
        ]
    )
    .is_err());
    assert!(partition(
        source,
        &[
            Part {
                start: 0,
                end: 8,
                kind: Kind::Attribute
            },
            Part {
                start: 7,
                end: source.len(),
                kind: Kind::Attribute
            }
        ]
    )
    .is_err());
    assert!(partition(
        source,
        &[Part {
            start: 8,
            end: 7,
            kind: Kind::Attribute
        }]
    )
    .is_err());
    assert!(partition(
        "#[é]",
        &[Part {
            start: 0,
            end: 3,
            kind: Kind::Attribute
        }]
    )
    .is_err());
}

#[test]
fn malformed_inner_multiple_and_unrepresented_attribute_forms_refuse() {
    for source in [
        "#![tool]",
        "#[tool] #[other]",
        "#[tool(x) other]",
        "#[= x]",
        "#[tool::]",
        "#[tool(]]",
        "#[tool(\"unterminated)]",
        "#[tool(r#\"unterminated)]",
        "#[tool] fn unrelated() {}",
        "#[tool = value + computation()]",
    ] {
        assert!(one(source, Kind::Attribute).is_err(), "{source}");
    }
}

#[test]
fn token_and_delimiter_inventories_are_bounded() {
    let tokens = format!("#[tool({})]", "x ".repeat(TOKENS));
    assert!(one(&tokens, Kind::Attribute).is_err());
    let depth = format!("#[tool({}x{})]", "(".repeat(DEPTH), ")".repeat(DEPTH));
    assert!(one(&depth, Kind::Attribute).is_err());
    assert!(one("#[tool(([x], { y }))]", Kind::Attribute).is_ok());
}
