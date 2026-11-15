//! Field get_mode semantics, including its explicit parse-error default.

use rustc_ast::token::TokenKind;
use rustc_ast::tokenstream::TokenTree;
use rustc_attr_ir::{AttrArgs, Attribute};
use trust_vc_vcir::Mode;

use super::super::attrs::{self, AttrProblem, VerusAttr};

const MAX_ATTRIBUTES: usize = 2_048;
const MAX_ATTRIBUTE_WORK: usize = 4_096;

fn ident(tree: &TokenTree, expected: &str) -> bool {
    matches!(tree, TokenTree::Token(token, _) if matches!(token.kind,
        TokenKind::Ident(name, _) if name.as_str() == expected))
}

// Called only after the complete attribute list passed verus_parse. For the
// spec keyword, that parser permits only bare spec or spec(checked), and drops
// commas and delimiter spelling in the same way as the pinned Verus parser.
fn spec_checked(attribute: &Attribute) -> bool {
    let Attribute::Unparsed(item) = attribute else {
        return false;
    };
    let AttrArgs::Delimited(args) = &item.args else {
        return false;
    };
    let path = item
        .path
        .segments
        .iter()
        .map(|name| name.as_str())
        .collect::<Vec<_>>();
    match path.as_slice() {
        ["verifier", "spec"] => true,
        ["verus", "internal"] => args
            .tokens
            .iter()
            .find(|tree| {
                !matches!(tree,
                TokenTree::Token(token, _) if token.kind == TokenKind::Comma)
            })
            .is_some_and(|tree| ident(tree, "spec")),
        _ => false,
    }
}

fn bounded(attributes: &[Attribute]) -> Result<(), String> {
    if attributes.len() > MAX_ATTRIBUTES {
        return Err("field attribute inventory exceeds its bound".into());
    }
    let mut remaining = MAX_ATTRIBUTE_WORK;
    for attribute in attributes {
        let Attribute::Unparsed(item) = attribute else {
            continue;
        };
        let AttrArgs::Delimited(args) = &item.args else {
            continue;
        };
        let mut pending = vec![(&args.tokens, 0)];
        while let Some((tokens, depth)) = pending.pop() {
            if depth > 64 {
                return Err("field attribute nesting exceeds its bound".into());
            }
            for tree in tokens.iter() {
                remaining = remaining
                    .checked_sub(1)
                    .ok_or("field attribute token work exceeds its bound")?;
                if let TokenTree::Delimited(_, _, _, inner) = tree {
                    pending.push((inner, depth + 1));
                }
            }
        }
    }
    Ok(())
}

/// Pinned attributes::get_mode calls parse_attrs_opt, which discards the entire
/// parsed list on an ordinary parse error, then takes the first Mode or Exec.
/// Unmodelled parser behavior stays Unknown rather than becoming a default.
pub(super) fn mode(attributes: &[Attribute]) -> Result<Mode, String> {
    bounded(attributes)?;
    match attrs::verus_parse(attributes) {
        Err(AttrProblem::Error(_, _)) => return Ok(Mode::Exec),
        Err(AttrProblem::Unmodelled(_, reason)) => {
            return Err(format!("unmodelled field attribute: {reason}"))
        }
        Ok(_) => {}
    }
    for attribute in attributes {
        if spec_checked(attribute) {
            return Ok(Mode::Spec);
        }
        for (attribute, _) in attrs::verus_attrs(std::slice::from_ref(attribute)) {
            if let VerusAttr::Mode(mode) = attribute {
                return Ok(mode);
            }
        }
    }
    Ok(Mode::Exec)
}

pub(super) fn empty_verifier(attribute: &Attribute, expected: &str) -> bool {
    let Attribute::Unparsed(item) = attribute else {
        return false;
    };
    let path = item
        .path
        .segments
        .iter()
        .map(|name| name.as_str())
        .collect::<Vec<_>>();
    matches!(path.as_slice(), ["verifier", name] if *name == expected)
        && matches!(item.args, AttrArgs::Empty)
}

pub(super) fn verifier_named(attribute: &Attribute, expected: &str) -> bool {
    let Attribute::Unparsed(item) = attribute else {
        return false;
    };
    let path = item
        .path
        .segments
        .iter()
        .map(|name| name.as_str())
        .collect::<Vec<_>>();
    matches!(path.as_slice(), ["verifier", name] if *name == expected)
}
