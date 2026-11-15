// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Refuses a `Verified` answer for a function whose file spells an identifier
//! outside ASCII.
//!
//! rustc reads every identifier in Unicode normalization form C, so spellings
//! that normalize to one string name one item: U+212A KELVIN SIGN and `K`, and
//! `e` followed by U+0301 COMBINING ACUTE ACCENT and U+00E9. The lane compares
//! the strings `syn` gives it as written, and reads such spellings as
//! different names. Beside `mod a { pub type K = u64; }`, with `mod z { pub
//! type K = u8; }` spelled with the Kelvin sign and `use z::*;`, it read the
//! `K` of `fn u1(v: K)` as `a::K`, the one declaration spelled that way,
//! while rustc binds it through the glob to `z`'s byte.
//!
//! An ASCII string is its own normal form, so a file whose identifiers are
//! all ASCII compares them as rustc does. A file that spells one outside
//! ASCII is refused, wherever the identifier is: in an item, a body, an
//! attribute or the arguments of a macro. So is a string in an attribute that
//! the lane can read as code: any string in an attribute other than a doc
//! comment, and a doc comment that carries the lane's own `trust_vc:`
//! metadata. The crate lane applies the same rule to every file of the crate
//! (`type_name_rebinding::crate_siblings`), and the path-dependency import to
//! every file it reads.
//!
//! A refutation and an earlier refusal are kept unchanged: neither can be a
//! false `Verified`.

use proc_macro2::{Delimiter, TokenStream, TokenTree};
use quote::ToTokens;
use syn::{File, ItemFn};

/// The tag every refusal from this module starts with.
pub(super) const IDENTIFIER_SPELLING_TAG: &str = "identifier spelling";

/// The refusal message for a `Verified` answer of `func`, or `None` when the
/// file, and `func` (which may be a transformed copy of its file node), spell
/// every identifier in ASCII. See the module documentation.
pub(super) fn verified_refusal(file: Option<&File>, func: &ItemFn) -> Option<String> {
    let hazard = file
        .and_then(file_hazard)
        .or_else(|| stream_hazard(func.to_token_stream()))?;
    Some(format!(
        "{IDENTIFIER_SPELLING_TAG}: {hazard}, so two spellings this lane reads as different \
         names can be one name to rustc. A `Verified` answer is refused; a refutation would be \
         kept"
    ))
}

/// Why `file` can spell one name in two ways the lane tells apart, or `None`
/// when every identifier it spells, and every string of an attribute the
/// lane can read as code, is ASCII.
pub(crate) fn file_hazard(file: &File) -> Option<String> {
    stream_hazard(file.to_token_stream())
}

fn stream_hazard(stream: TokenStream) -> Option<String> {
    let trees: Vec<TokenTree> = stream.into_iter().collect();
    for (index, tree) in trees.iter().enumerate() {
        match tree {
            TokenTree::Ident(ident) => {
                let spelled = ident.to_string();
                if let Some(ch) = spelled.chars().find(|ch| !ch.is_ascii()) {
                    return Some(format!(
                        "the file spells the identifier `{spelled}`, whose character U+{:04X} \
                         is outside ASCII, and rustc reads an identifier in Unicode \
                         normalization form C",
                        u32::from(ch)
                    ));
                }
            }
            TokenTree::Group(group) => {
                let attribute =
                    group.delimiter() == Delimiter::Bracket && attribute_bracket(&trees[..index]);
                let hazard = if attribute {
                    attribute_string_hazard(group.stream())
                        .or_else(|| stream_hazard(group.stream()))
                } else {
                    stream_hazard(group.stream())
                };
                if hazard.is_some() {
                    return hazard;
                }
            }
            TokenTree::Punct(_) | TokenTree::Literal(_) => {}
        }
    }
    None
}

/// True when a bracket group that follows `before` is an attribute's: `#[..]`
/// or `#![..]`.
fn attribute_bracket(before: &[TokenTree]) -> bool {
    match before {
        [.., hash, bang] if is_punct(bang, '!') => is_punct(hash, '#'),
        [.., hash] => is_punct(hash, '#'),
        [] => false,
    }
}

fn is_punct(tree: &TokenTree, ch: char) -> bool {
    matches!(tree, TokenTree::Punct(punct) if punct.as_char() == ch)
}

/// A string outside ASCII in the attribute whose tokens inside the brackets
/// are `attribute`, which the lane can read as code. A doc comment
/// (`#[doc = ".."]`) is read as code only when it carries `trust_vc:`
/// metadata.
fn attribute_string_hazard(attribute: TokenStream) -> Option<String> {
    let trees: Vec<TokenTree> = attribute.into_iter().collect();
    if let [TokenTree::Ident(name), TokenTree::Punct(eq), TokenTree::Literal(text)] =
        trees.as_slice()
    {
        if name == "doc" && eq.as_char() == '=' {
            let text = text.to_string();
            let body = text.trim_start_matches('r').trim_start_matches(['#', '"']);
            if !body.trim_start().starts_with("trust_vc") {
                return None;
            }
        }
    }
    literal_hazard(trees)
}

fn literal_hazard(trees: Vec<TokenTree>) -> Option<String> {
    for tree in trees {
        match tree {
            TokenTree::Literal(literal) => {
                let text = literal.to_string();
                if let Some(ch) = text.chars().find(|ch| !ch.is_ascii()) {
                    return Some(format!(
                        "an attribute of the file holds the string {text}, whose character \
                         U+{:04X} is outside ASCII, which the lane can read as an identifier \
                         that rustc reads in Unicode normalization form C",
                        u32::from(ch)
                    ));
                }
            }
            TokenTree::Group(group) => {
                if let Some(hazard) = literal_hazard(group.stream().into_iter().collect()) {
                    return Some(hazard);
                }
            }
            TokenTree::Ident(_) | TokenTree::Punct(_) => {}
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn refusal(src: &str) -> Option<String> {
        let file: File = syn::parse_str(src).expect("fixture parses");
        let func = file
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) => Some(func.clone()),
                _ => None,
            })
            .unwrap_or_else(|| syn::parse_quote! { fn __probe() {} });
        verified_refusal(Some(&file), &func)
    }

    #[test]
    fn an_identifier_outside_ascii_refuses_the_file() {
        for (src, spelled) in [
            ("mod z { pub type \u{212A} = u8; } fn f() {}", "\u{212A}"),
            ("fn f() { let caf\u{e9} = 1u8; }", "caf\u{e9}"),
            ("fn f() { let We\u{301} = 1u8; }", "We\u{301}"),
            ("fn f<'\u{212A}>(x: &'\u{212A} u8) {}", "\u{212A}"),
            (
                "#[trust_vc::ensures(\u{212A} > 0)] fn f(x: u8) {}",
                "\u{212A}",
            ),
            ("fn f() { m!(\u{212A}); }", "\u{212A}"),
            ("fn f() { let r#\u{212A} = 1u8; }", "\u{212A}"),
        ] {
            let why = refusal(src).unwrap_or_else(|| panic!("refused: {src}"));
            assert!(why.starts_with(IDENTIFIER_SPELLING_TAG), "{why}");
            assert!(why.contains(spelled), "{why}");
        }
    }

    #[test]
    fn a_string_an_attribute_can_read_as_code_refuses_the_file() {
        let why = refusal("#[trust_vc::marker(\"\u{212A}\")] fn f() {}").expect("refused");
        assert!(why.contains("U+212A"), "{why}");
        let why =
            refusal("#[doc = \"trust_vc:decreases:entry=\u{212A}\"] fn f() {}").expect("refused");
        assert!(why.contains("U+212A"), "{why}");
    }

    #[test]
    fn ascii_identifiers_and_plain_text_are_read() {
        for src in [
            "mod z { pub type K = u8; } fn f(v: z::K) {}",
            "/// caf\u{e9} \u{2014} a note\nfn f() { let s = \"\u{212A}\"; let c = '\u{e9}'; }",
            "//! \u{2014} module note\nfn f() {}",
            "fn f() { // \u{212A}\n }",
            "#[doc = \"\u{e9}\"] fn f() {}",
            "fn f() { assert!(true, \"\u{e9}\"); }",
        ] {
            assert_eq!(refusal(src), None, "{src}");
        }
    }
}
