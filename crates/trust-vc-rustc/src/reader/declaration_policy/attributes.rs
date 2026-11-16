//! Bounded grammar for the policy directives used by this native slice.

use rustc_ast::token::{Delimiter, TokenKind};
use rustc_ast::tokenstream::{TokenStream, TokenTree};
use rustc_attr_ir::{AttrArgs, Attribute};
use trust_vc_vcir::Mode;

use super::Recursion;

const MAX_ATTRIBUTES: usize = 2_048;
const MAX_TOKENS: usize = 64;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Context {
    Function,
    Implementation,
    Nominal,
    Parameter,
}

#[derive(Default)]
pub(super) struct Directives {
    pub(super) verus_macro: bool,
    pub(super) external_body: bool,
    pub(super) ext_equal: bool,
    pub(super) nominal_mode: Option<Mode>,
    pub(super) named: Vec<(String, Recursion)>,
    bare: Vec<Recursion>,
}

impl Directives {
    /// Pinned Verus gives parameter-level flags this precedence. Named item
    /// directives are processed separately and duplicate a parameter flag.
    pub(super) fn bare_policy(&self) -> Option<Recursion> {
        [
            Recursion::Reject,
            Recursion::RejectInGround,
            Recursion::Accept,
        ]
        .into_iter()
        .find(|policy| self.bare.contains(policy))
    }

    pub(super) fn has_recursion(&self) -> bool {
        !self.bare.is_empty() || !self.named.is_empty()
    }
}

fn ident(tree: &TokenTree) -> Option<String> {
    let TokenTree::Token(token, _) = tree else {
        return None;
    };
    let TokenKind::Ident(name, _) = token.kind else {
        return None;
    };
    Some(name.as_str().to_string())
}

fn tokens(stream: &TokenStream) -> Result<Vec<&TokenTree>, String> {
    let tokens = stream.iter().take(MAX_TOKENS + 1).collect::<Vec<_>>();
    if tokens.len() > MAX_TOKENS {
        return Err("policy attribute token inventory exceeds its bound".into());
    }
    Ok(tokens)
}

fn one_identifier(stream: &TokenStream) -> Result<String, String> {
    let tokens = tokens(stream)?;
    // Verus's AttrTree drops commas; preserve its trailing-comma spelling.
    let mut names = Vec::new();
    for token in tokens {
        if let TokenTree::Token(token, _) = token {
            if token.kind == TokenKind::Comma {
                continue;
            }
        }
        names.push(ident(token).ok_or("a policy argument is not an identifier")?);
    }
    match names.as_slice() {
        [name] => Ok(name.clone()),
        _ => Err("a policy directive needs exactly one native parameter name".into()),
    }
}

fn arguments(args: &AttrArgs) -> Result<Option<String>, String> {
    match args {
        AttrArgs::Empty => Ok(None),
        AttrArgs::Delimited(delimited) if delimited.delim == Delimiter::Parenthesis => {
            one_identifier(&delimited.tokens).map(Some)
        }
        _ => Err("an unsupported policy directive argument form".into()),
    }
}

fn policy(name: &str, argument: Option<&str>) -> Option<Recursion> {
    match name {
        "reject_recursive_types" => Some(Recursion::Reject),
        "reject_recursive_types_in_ground_variants" => Some(Recursion::RejectInGround),
        "accept_recursive_types" => Some(Recursion::Accept),
        "maybe_negative" if argument.is_none() => Some(Recursion::Reject),
        "strictly_positive" if argument.is_none() => Some(Recursion::Accept),
        _ => None,
    }
}

fn directive(
    out: &mut Directives,
    context: Context,
    name: &str,
    argument: Option<String>,
    internal: bool,
    bodyless_spec: bool,
) -> Result<(), String> {
    if let Some(policy) = policy(name, argument.as_deref()) {
        match (context, argument) {
            (Context::Nominal, Some(parameter)) => out.named.push((parameter, policy)),
            (Context::Parameter, None) => out.bare.push(policy),
            _ => {
                return Err(
                    "a recursion directive is outside its supported item/parameter position".into(),
                )
            }
        }
        return Ok(());
    }
    if internal && argument.is_none() {
        // These affect body interpretation, not binders. Admit them only as
        // the complete parsed Spec/uninterp/external_body combination; the
        // separate factory still checks modes and traverses every header.
        if context == Context::Function
            && bodyless_spec
            && matches!(name, "uninterp" | "external_body")
        {
            return Ok(());
        }
        match name {
            "verus_macro" if context != Context::Parameter => {
                out.verus_macro = true;
                return Ok(());
            }
            "spec" | "proof" | "exec" if context == Context::Nominal => {
                // Same first-mode rule as the declaration/field parser.
                out.nominal_mode.get_or_insert(match name {
                    "spec" => Mode::Spec,
                    "proof" => Mode::Proof,
                    _ => Mode::Exec,
                });
                return Ok(());
            }
            "spec" | "proof" | "exec" | "open" | "closed"
                if matches!(context, Context::Function | Context::Nominal) =>
            {
                return Ok(())
            }
            _ => {}
        }
    }
    if internal
        && context == Context::Function
        && name == "returns"
        && argument
            .as_deref()
            .is_some_and(|mode| matches!(mode, "spec" | "proof" | "exec"))
    {
        return Ok(());
    }
    if argument.is_none() && context == Context::Nominal {
        match name {
            "external_body" => {
                out.external_body = true;
                return Ok(());
            }
            "ext_equal" => {
                out.ext_equal = true;
                return Ok(());
            }
            _ => {}
        }
    }
    // Policy facts describe binders, never body unfolding. Actual inline
    // semantics remain unsupported by the ordinary reader. This canonical
    // function directive is neutral only after the full language parse below.
    if !internal && argument.is_none() && context == Context::Function && name == "inline" {
        return Ok(());
    }
    Err(format!("an unsupported generic policy directive: {name}"))
}

pub(super) fn read(attributes: &[Attribute], context: Context) -> Result<Directives, String> {
    if attributes.len() > MAX_ATTRIBUTES {
        return Err("native attribute inventory exceeds its bound".into());
    }
    let parsed = super::super::attrs::item_attrs(attributes);
    let bodyless_spec = context == Context::Function
        && parsed.mode == Some(Mode::Spec)
        && parsed.uninterp
        && parsed.external_body
        && super::super::attrs::verus_parse(attributes).is_ok();
    if attributes.iter().any(|attribute| {
        matches!(attribute, Attribute::Tool(item)
        if item.path.segments.iter().map(|name| name.as_str()).eq(["verifier", "inline"]))
    }) {
        super::super::attrs::verus_parse(attributes).map_err(|problem| {
            format!("the original inline attribute language is unavailable: {problem:?}")
        })?;
    }
    let mut result = Directives::default();
    for attribute in attributes {
        let item = match attribute {
            Attribute::Tool(item) => item,
            Attribute::DeriveHelper(item) if item.path.segments.len() == 1 => item,
            _ => continue,
        };
        let path = item
            .path
            .segments
            .iter()
            .map(|name| name.as_str())
            .collect::<Vec<_>>();
        match path.as_slice() {
            ["verifier", name] => directive(
                &mut result,
                context,
                name,
                arguments(&item.args)?,
                false,
                bodyless_spec,
            )?,
            ["verus", "internal"] => {
                let AttrArgs::Delimited(delimited) = &item.args else {
                    return Err("a Verus internal policy attribute has no token list".into());
                };
                if delimited.delim != Delimiter::Parenthesis {
                    return Err("an internal policy attribute has the wrong delimiter".into());
                }
                let tokens = tokens(&delimited.tokens)?;
                let (name, argument) = match tokens.as_slice() {
                    [name] => (
                        ident(name).ok_or("an internal directive is not an identifier")?,
                        None,
                    ),
                    [name, TokenTree::Delimited(_, _, Delimiter::Parenthesis, args)] => (
                        ident(name).ok_or("an internal directive is not an identifier")?,
                        Some(one_identifier(args)?),
                    ),
                    _ => return Err("an unsupported internal policy token shape".into()),
                };
                directive(&mut result, context, &name, argument, true, bodyless_spec)?;
            }
            ["verus", ..] | ["verifier", ..] => {
                return Err("an unsupported verifier policy attribute path".into())
            }
            _ => {}
        }
    }
    Ok(result)
}
