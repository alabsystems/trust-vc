//! Verus attributes on HIR nodes.
//!
//! Verus code carries two attribute syntaxes after expansion:
//!
//! * `#[verus::internal(<keyword>)]`, emitted by the `verus!` macro (mode,
//!   `verus_macro`, `uninterp`, `reveal_fn`, ...);
//! * `#[verifier::<keyword>(<args>)]`, written by users or emitted by the
//!   macro (`proof_block`, `opaque`, `rlimit(20)`, `proof_note("..")`).
//!
//! rustc keeps both as tool attributes: a path plus a token stream.
//! [`verus_attrs`] turns them into [`VerusAttr`] values. Every other
//! attribute (lint levels, `doc`, `derive`, ...) is ignored, as Verus ignores
//! it. A Verus keyword the reader does not know becomes
//! [`VerusAttr::Unknown`], so callers can refuse the item rather than drop a
//! directive silently.

use rustc_ast::token::{LitKind, TokenKind};
use rustc_ast::tokenstream::{TokenStream, TokenTree};
use rustc_attr_ir::{AttrArgs, Attribute};
use rustc_span::Span;

use trust_vc_vcir::{DeclProphecy, Mode, Rlimit};

/// One recognized Verus attribute.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerusAttr {
    /// `#[verus::internal(verus_macro)]`: the item came from `verus!`.
    VerusMacro,
    /// `#[verus::internal(spec|proof|exec)]`.
    Mode(Mode),
    /// `#[verus::internal(returns(spec|proof|exec))]`: the mode of a
    /// function's return value (`-> (tracked r: T)`).
    ReturnMode(Mode),
    /// `#[verus::internal(infer_mode)]`: a `let` whose mode its first
    /// assignment decides (from `let tracked x = ..`).
    InferMode,
    /// `#[verus::internal(unwrapped_binding)]` and
    /// `#[verus::internal(infer_proph)]`: on the `let`s of `let ghost` and
    /// `let tracked`; they only change warnings and prophecy inference.
    LetMarker(&'static str),
    /// `#[verus::internal(open)]` / `closed`: visibility of a spec
    /// function's body outside its module.
    Visibility { open: bool },
    /// `#[verus::internal(open_visibility_qualifier)]`, which `open(in
    /// path)` puts on a `use` statement in the function's body.
    OpenVisibilityQualifier,
    /// `#[verus::internal(uninterp)]`: a spec function without a body.
    Uninterp,
    /// `#[verus::internal(external_body)]` or `#[verifier::external_body]`.
    ExternalBody,
    /// `#[verifier::external]`: not a verification target.
    External,
    /// `#[verifier::opaque]`.
    Opaque,
    /// `#[verifier::prophetic]`: a Spec function effect or an explicit
    /// prophetic local declaration. This grants no proof authority.
    Prophetic,
    /// `#[verifier::inline]`, with no arguments. Body/mode/visibility rules
    /// are checked by the function reader before its IR is usable.
    Inline,
    /// The macro's external, deliberately uncallable ambiguous-field stub.
    /// Admission requires the separate original local-enum checker.
    GetFieldManyVariants,
    /// `#[verifier::rlimit(n)]` or `rlimit(infinity)`.
    Rlimit(Rlimit),
    /// `#[verifier::proof_block]` or `#[verus::internal(proof_block)]`: a
    /// ghost block in exec code.
    ProofBlock,
    /// Another of Verus's ghost-block attributes (`attributes.rs`,
    /// `GhostBlockAttr`, and `proof_in_spec`): `tracked_block`, the block and
    /// wrapper of `Ghost(..)` and `Tracked(..)`, and a proof block inside
    /// ghost code. Holds its keyword.
    OtherGhostBlock(String),
    /// `#[verifier::proof_note("text")]`.
    ProofNote(String),
    /// `#[verifier::custom_err("text")]`.
    CustomErr(String),
    /// `#[verus::internal(reveal_fn)]`: the helper function inside a reveal.
    RevealFn,
    /// `#[verus::internal(broadcast_use_reveal)]`: on the last expression of
    /// a reveal's target block, marks the reveal as a `broadcast use`.
    BroadcastUseReveal,
    /// A macro-marked broadcast proof declaration.
    BroadcastForall,
    /// `#[verifier::loop_isolation]` (true), `loop_isolation(true)` or
    /// `loop_isolation(false)`: on a loop, or inherited by the loops of a
    /// function from it and the items around it.
    LoopIsolation(bool),
    /// `#[verifier::allow_complex_invariants]`, likewise.
    AllowComplexInvariants,
    /// `#[verifier::exec_allows_no_decreases_clause]`, inherited from a
    /// function and the items around it: its loops need no `decreases`.
    ExecAllowsNoDecreasesClause,
    /// `#[verifier::decreases_by]`, `#[verifier::recommends_by]` or
    /// `#[verus::internal(via)]` (`#[via_fn]`): a proof function that serves
    /// as a spec function's `decreases_by` or `recommends_by`.
    DecreasesBy,
    /// `#[verifier::assume_termination]`: an exec function whose
    /// termination is assumed.
    AssumeTermination,
    /// `#[verifier::spinoff_prover]`: the function's queries run in a
    /// solver process of their own, which changes no verdict.
    SpinoffProver,
    /// `#[trigger]` (`None`) or `#[trigger(g, ..)]` on a term of a
    /// quantifier's body (`verus::internal` or `verifier`).
    Trigger(Option<Vec<u64>>),
    /// `#![auto]` on a quantifier (`auto_trigger`).
    AutoTrigger,
    /// `#![all_triggers]` on a quantifier.
    AllTriggers,
    /// A Verus attribute the reader does not handle. Holds its keyword.
    Unknown(String),
}

/// A parsed attribute argument tree: `name`, `name(args..)` or a literal.
#[derive(Debug, Clone)]
enum Tree {
    Fun(String, Option<Vec<Tree>>),
    Lit(LitKind, String),
}

/// The Verus attributes among `attrs`, with their spans.
pub fn verus_attrs(attrs: &[Attribute]) -> Vec<(VerusAttr, Span)> {
    let mut out = Vec::new();
    for attr in attrs {
        let item = match attr {
            Attribute::Tool(item) => item,
            Attribute::DeriveHelper(item) if item.path.segments.len() == 1 => item,
            _ => continue,
        };
        let segments: Vec<&str> = item.path.segments.iter().map(|s| s.as_str()).collect();
        let parsed = match segments.as_slice() {
            ["verus", "internal"] => match &item.args {
                AttrArgs::Delimited(delim) => match token_trees(&delim.tokens) {
                    Some(trees) if trees.len() == 1 => internal_attr(&trees[0]),
                    _ => VerusAttr::Unknown("verus::internal".to_string()),
                },
                _ => VerusAttr::Unknown("verus::internal".to_string()),
            },
            ["verifier", keyword] => {
                let args = match &item.args {
                    AttrArgs::Empty => Some(None),
                    AttrArgs::Delimited(delim) => token_trees(&delim.tokens).map(Some),
                    AttrArgs::Eq { .. } => None,
                };
                match args {
                    Some(args) => verifier_attr(keyword, args.as_deref()),
                    None => VerusAttr::Unknown(format!("verifier::{keyword}")),
                }
            }
            ["verus", other] => VerusAttr::Unknown(format!("verus::{other}")),
            ["verifier"] => VerusAttr::Unknown("verifier".to_string()),
            _ => continue,
        };
        out.push((parsed, item.span));
    }
    out
}

/// What Verus's attribute parser finds wrong with a node's attributes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AttrProblem {
    /// Verus's error: its message, at its span.
    Error(Span, String),
    /// Something Verus does that the reader does not reproduce: it panics,
    /// prints its own data structures, or only warns. Refused, with what it
    /// was.
    Unmodelled(Span, String),
}

/// What Verus's parser (`attributes.rs`, `parse_attrs`) makes of the
/// attributes of one node, as far as the checks that follow the parse need.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct VerusParse {
    /// The spans of the proof notes and custom errors, in order.
    pub notes: Vec<Span>,
    /// A trigger group (`trigger`, `trigger(..)`, `auto_trigger`,
    /// `all_triggers`) or a proof note: `expr_to_vir` wraps the expression
    /// in it (`get_trigger`, `get_proof_note_annotation`), so a place
    /// becomes a temporary.
    pub wraps: bool,
    /// `verifier::truncate`.
    pub truncate: bool,
    /// The last `rustc_*` attribute Verus does not ignore, which
    /// `get_verifier_attrs` rejects after the parse.
    pub rustc: Option<(String, Span)>,
    /// A deprecated attribute Verus warns about.
    pub deprecated: Option<Span>,
}

/// `attributes.rs`, `RUSTC_ATTRS_OK_TO_IGNORE`.
const RUSTC_ATTRS_OK_TO_IGNORE: &[&str] = &[
    "rustc_allow_const_fn_unstable",
    "rustc_const_stable",
    "rustc_const_unstable",
    "rustc_allowed_through_unstable_modules",
    "rustc_builtin_macro",
    "rustc_macro_transparency",
    "rustc_coherence_is_core",
    "rustc_diagnostic_item",
    "rustc_on_unimplemented",
    "rustc_trivial_field_reads",
    "rustc_doc_primitive",
    "rustc_paren_sugar",
    "rustc_insignificant_dtor",
    "rustc_box",
];

/// Parse `attrs` the way Verus does (`attributes.rs`, `attr_to_tree` and
/// `parse_attrs`): attributes in order, the first one Verus cannot parse
/// ends the parse with its error, at the attribute's span. Attributes that
/// are neither `verifier::` nor `verus::` (nor Verus's old bare mode names,
/// nor `rustc_*`) are ignored, as Verus ignores them.
pub fn verus_parse(attrs: &[Attribute]) -> Result<VerusParse, AttrProblem> {
    use crate::messages::attr as msg;
    let mut out = VerusParse::default();
    for attr in attrs {
        let item = match attr {
            Attribute::Tool(item) => item,
            Attribute::DeriveHelper(item) if item.path.segments.len() == 1 => item,
            _ => continue,
        };
        let span = item.span;
        let error = |message: &str| Err(AttrProblem::Error(span, message.to_string()));
        let segments: Vec<&str> = item.path.segments.iter().map(|s| s.as_str()).collect();
        match segments.as_slice() {
            ["verifier"] => return error(msg::INVALID_VERIFIER),
            ["verifier", name] => {
                let args = match &item.args {
                    AttrArgs::Empty => None,
                    AttrArgs::Delimited(delim) => match token_trees(&delim.tokens) {
                        Some(trees) => Some(trees),
                        None => return error(msg::INVALID_VERIFIER),
                    },
                    AttrArgs::Eq { .. } => return Err(eq_args(span, &segments)),
                };
                verifier_keyword(name, args.as_deref(), span, &mut out)?;
            }
            ["verus", "internal"] => {
                let AttrArgs::Delimited(delim) = &item.args else {
                    return error(msg::INVALID_VERUS);
                };
                let Some(trees) = token_trees(&delim.tokens) else {
                    return error(msg::INVALID_VERUS);
                };
                let [tree] = trees.as_slice() else {
                    return error(msg::INVALID_VERUS);
                };
                internal_keyword(tree, span, &mut out)?;
            }
            ["verus", name] => {
                let args = match &item.args {
                    AttrArgs::Empty => None,
                    AttrArgs::Delimited(delim) => match token_trees(&delim.tokens) {
                        Some(trees) => Some(trees),
                        None => return error(msg::INVALID_VERIFIER),
                    },
                    AttrArgs::Eq { .. } => return Err(eq_args(span, &segments)),
                };
                // `VerusPrefix::None`: only `verus::trusted`.
                if !(*name == "trusted" && args.is_none()) {
                    return error(msg::UNRECOGNIZED_INTERNAL);
                }
            }
            ["spec" | "proof" | "exec"] => return error(msg::OLD_MODE_ATTRIBUTE),
            [name] if name.starts_with("rustc_") && !RUSTC_ATTRS_OK_TO_IGNORE.contains(name) => {
                out.rustc = Some(((*name).to_string(), span));
            }
            _ => {}
        }
    }
    Ok(out)
}

/// `#[verifier::name = ..]` or `#[verus::name = ..]`: Verus reaches a
/// `todo!()` on it.
fn eq_args(span: Span, segments: &[&str]) -> AttrProblem {
    AttrProblem::Unmodelled(
        span,
        format!("`#[{} = ..]`, on which Verus panics", segments.join("::")),
    )
}

/// A `verifier::` attribute, as `parse_attrs` reads it under
/// `AttrPrefix::Verifier`: a keyword with the argument shapes Verus accepts,
/// or Verus's error.
fn verifier_keyword(
    name: &str,
    args: Option<&[Tree]>,
    span: Span,
    out: &mut VerusParse,
) -> Result<(), AttrProblem> {
    use crate::messages::attr as msg;
    let error = |message: &str| Err(AttrProblem::Error(span, message.to_string()));
    let one_ident = |args: Option<&[Tree]>| matches!(args, Some([Tree::Fun(_, None)]));
    let accepted = match (name, args) {
        ("spec" | "proof" | "exec", None) => true,
        ("spec", Some([Tree::Fun(arg, None)])) => arg == "checked",
        ("proof_note" | "custom_err", args) => {
            if !matches!(args, Some([Tree::Lit(LitKind::Str, _)])) {
                return error(msg::EXPECTED_STRING);
            }
            out.notes.push(span);
            out.wraps = true;
            true
        }
        ("trigger" | "auto_trigger" | "all_triggers", None) => {
            out.wraps = true;
            true
        }
        ("trigger", Some(args)) => {
            trigger_groups(args, span)?;
            out.wraps = true;
            true
        }
        (
            "verus_macro"
            | "external_body"
            | "external"
            | "verify"
            | "opaque"
            | "opaque_outside_module"
            | "inline"
            | "ext_equal"
            | "proof_block"
            | "ghost_block_wrapped"
            | "tracked_block_wrapped"
            | "tracked_block"
            | "ghost_wrapper"
            | "proof_in_spec"
            | "maybe_negative"
            | "reject_recursive_types"
            | "reject_recursive_types_in_ground_variants"
            | "strictly_positive"
            | "accept_recursive_types"
            | "broadcast_use_by_default_when_this_crate_is_imported"
            | "no_auto_trigger"
            | "allow_in_spec"
            | "atomic"
            | "invariant_block"
            | "bit_vector"
            | "decreases_by"
            | "recommends_by"
            | "integer_ring"
            | "nonlinear"
            | "spinoff_prover"
            | "loop_isolation"
            | "allow_complex_invariants"
            | "memoize"
            | "external_fn_specification"
            | "external_type_specification"
            | "external_derive"
            | "external_trait_specification"
            | "sealed"
            | "prophetic"
            | "ignore_outside_new_mut_ref_experiment"
            | "type_invariant"
            | "assume_termination"
            | "exec_allows_no_decreases_clause"
            | "tracked_swap_primitive"
            | "tracked_take_option_primitive",
            None,
        ) => true,
        ("truncate", None) => {
            out.truncate = true;
            true
        }
        ("broadcast_forall" | "prune_unless_this_module_is_used", None) => {
            out.deprecated = Some(span);
            true
        }
        (
            "reject_recursive_types"
            | "reject_recursive_types_in_ground_variants"
            | "accept_recursive_types"
            | "when_used_as_spec"
            | "external_derive"
            | "external_trait_specification",
            args,
        ) if one_ident(args) => true,
        ("returns", Some([Tree::Fun(mode, None)])) => {
            matches!(mode.as_str(), "spec" | "proof" | "exec")
        }
        ("loop_isolation", Some([Tree::Fun(value, None)])) => {
            matches!(value.as_str(), "true" | "false")
        }
        ("deprecated_postcondition_mut_ref_style", _) => true,
        ("auto_ext_equal", Some(places)) => {
            for place in places {
                let known = matches!(place, Tree::Fun(p, None)
                    if matches!(p.as_str(), "assert" | "assert_by" | "ensures" | "invariant"));
                if !known {
                    return error(msg::AUTO_EXT_EQUAL_PLACES);
                }
            }
            true
        }
        ("rlimit", args) => {
            let number = match args {
                Some([Tree::Lit(LitKind::Float | LitKind::Integer, text)]) => {
                    text.parse::<f32>().is_ok()
                }
                Some([Tree::Fun(word, None)]) => word == "infinity",
                _ => false,
            };
            if !number {
                return error(msg::RLIMIT_NUMBER);
            }
            true
        }
        (
            "external_trait_extension",
            Some([Tree::Fun(_, None), Tree::Fun(via, None), Tree::Fun(_, None)]),
        ) => via == "via",
        ("invalid_trigger_attribute", None) => return error(msg::INVALID_TRIGGER_ATTRIBUTE),
        _ => false,
    };
    if accepted {
        Ok(())
    } else {
        error(msg::UNRECOGNIZED_VERIFIER)
    }
}

/// `#[verus::internal(tree)]`, as `parse_attrs` reads it under
/// `VerusPrefix::Internal`.
fn internal_keyword(tree: &Tree, span: Span, out: &mut VerusParse) -> Result<(), AttrProblem> {
    use crate::messages::attr as msg;
    let accepted = match tree {
        Tree::Fun(name, None)
            if matches!(name.as_str(), "trigger" | "auto_trigger" | "all_triggers") =>
        {
            out.wraps = true;
            true
        }
        Tree::Fun(name, None) => matches!(
            name.as_str(),
            "spec"
                | "proof"
                | "exec"
                | "infer_mode"
                | "infer_proph"
                | "trigger"
                | "auto_trigger"
                | "all_triggers"
                | "verus_macro"
                | "proof_block"
                | "external_body"
                | "external_trait_blanket"
                | "open"
                | "closed"
                | "uninterp"
                | "reveal_group"
                | "header_unwrap_parameter"
                | "reveal_fn"
                | "const_body"
                | "broadcast_use_reveal"
                | "broadcast_forall"
                | "for_loop"
                | "auto_decreases"
                | "via"
                | "unwrapped_binding"
                | "size_of"
                | "item_broadcast_use"
                | "get_field_many_variants"
                | "size_of_broadcast_proof"
                | "external_fn_specification"
                | "open_visibility_qualifier"
                | "unerased_proxy"
                | "uses_unerased_proxy"
                | "encoded_const"
                | "encoded_static"
                | "structural_const_wrapper"
        ),
        Tree::Fun(name, Some(args)) => match (name.as_str(), args.as_slice()) {
            ("spec", [Tree::Fun(arg, None)]) => arg == "checked",
            ("trigger", args) => {
                trigger_groups(args, span)?;
                out.wraps = true;
                true
            }
            ("returns", [Tree::Fun(mode, None)]) => {
                matches!(mode.as_str(), "spec" | "proof" | "exec")
            }
            ("prover", [Tree::Fun(prover, None)]) => {
                if !matches!(
                    prover.as_str(),
                    "nonlinear_arith" | "bit_vector" | "integer_ring"
                ) {
                    return Err(AttrProblem::Error(span, msg::INVALID_PROVER.to_string()));
                }
                true
            }
            _ => false,
        },
        Tree::Lit(..) => false,
    };
    if accepted {
        Ok(())
    } else {
        Err(AttrProblem::Error(
            span,
            msg::UNRECOGNIZED_INTERNAL.to_string(),
        ))
    }
}

/// The groups of `trigger(g1, g2, ..)` (`get_trigger_arg`): each an integer
/// literal that fits in `u64`, and at least one.
fn trigger_groups(args: &[Tree], span: Span) -> Result<(), AttrProblem> {
    use crate::messages::attr as msg;
    for arg in args {
        match arg {
            Tree::Lit(LitKind::Integer, digits) if digits.parse::<u64>().is_ok() => {}
            // Verus prints the argument with `{:?}`; for a literal that is
            // its kind and its text.
            Tree::Lit(kind, text) => {
                return Err(AttrProblem::Error(
                    span,
                    msg::trigger_not_integer(&format!("Lit({kind:?}, {text:?})")),
                ))
            }
            // For a name, `{:?}` prints Verus's span, a path on the
            // machine that ran it.
            Tree::Fun(..) => {
                return Err(AttrProblem::Unmodelled(
                    span,
                    "a trigger group that is not an integer literal".to_string(),
                ))
            }
        }
    }
    if args.is_empty() {
        return Err(AttrProblem::Error(span, msg::EMPTY_TRIGGER.to_string()));
    }
    Ok(())
}

/// `trigger(g1, g2, ..)`: its groups, when each is an integer literal and
/// there is one at least ([`trigger_groups`] has Verus's errors).
fn trigger_attr(args: &[Tree]) -> VerusAttr {
    let groups: Option<Vec<u64>> = args
        .iter()
        .map(|arg| match arg {
            Tree::Lit(LitKind::Integer, digits) => digits.parse::<u64>().ok(),
            _ => None,
        })
        .collect();
    match groups {
        Some(groups) if !groups.is_empty() => VerusAttr::Trigger(Some(groups)),
        _ => VerusAttr::Unknown("trigger(..)".to_string()),
    }
}

/// `#[verus::internal(tree)]`.
fn internal_attr(tree: &Tree) -> VerusAttr {
    match tree {
        Tree::Fun(name, None) => match name.as_str() {
            "verus_macro" => VerusAttr::VerusMacro,
            "spec" => VerusAttr::Mode(Mode::Spec),
            "proof" => VerusAttr::Mode(Mode::Proof),
            "exec" => VerusAttr::Mode(Mode::Exec),
            "open" => VerusAttr::Visibility { open: true },
            "closed" => VerusAttr::Visibility { open: false },
            "open_visibility_qualifier" => VerusAttr::OpenVisibilityQualifier,
            "uninterp" => VerusAttr::Uninterp,
            "get_field_many_variants" => VerusAttr::GetFieldManyVariants,
            "external_body" => VerusAttr::ExternalBody,
            "reveal_fn" => VerusAttr::RevealFn,
            "broadcast_use_reveal" => VerusAttr::BroadcastUseReveal,
            "broadcast_forall" => VerusAttr::BroadcastForall,
            "proof_block" => VerusAttr::ProofBlock,
            "infer_mode" => VerusAttr::InferMode,
            "unwrapped_binding" => VerusAttr::LetMarker("unwrapped_binding"),
            "infer_proph" => VerusAttr::LetMarker("infer_proph"),
            "via" => VerusAttr::DecreasesBy,
            "trigger" => VerusAttr::Trigger(None),
            "auto_trigger" => VerusAttr::AutoTrigger,
            "all_triggers" => VerusAttr::AllTriggers,
            other => VerusAttr::Unknown(format!("verus::internal({other})")),
        },
        Tree::Fun(name, Some(args)) if name == "trigger" => trigger_attr(args),
        Tree::Fun(name, Some(args)) if name == "returns" => match args.as_slice() {
            [Tree::Fun(mode, None)] => match mode.as_str() {
                "spec" => VerusAttr::ReturnMode(Mode::Spec),
                "proof" => VerusAttr::ReturnMode(Mode::Proof),
                "exec" => VerusAttr::ReturnMode(Mode::Exec),
                _ => VerusAttr::Unknown("verus::internal(returns(..))".to_string()),
            },
            _ => VerusAttr::Unknown("verus::internal(returns(..))".to_string()),
        },
        Tree::Fun(name, Some(_)) => VerusAttr::Unknown(format!("verus::internal({name}(..))")),
        Tree::Lit(..) => VerusAttr::Unknown("verus::internal(literal)".to_string()),
    }
}

/// `#[verifier::keyword(args)]`.
fn verifier_attr(keyword: &str, args: Option<&[Tree]>) -> VerusAttr {
    match (keyword, args) {
        ("proof_block", None) => VerusAttr::ProofBlock,
        (
            "tracked_block"
            | "ghost_block_wrapped"
            | "tracked_block_wrapped"
            | "ghost_wrapper"
            | "proof_in_spec",
            None,
        ) => VerusAttr::OtherGhostBlock(format!("verifier::{keyword}")),
        ("spec", None) => VerusAttr::Mode(Mode::Spec),
        ("proof", None) => VerusAttr::Mode(Mode::Proof),
        ("exec", None) => VerusAttr::Mode(Mode::Exec),
        ("returns", Some([Tree::Fun(mode, None)])) => match mode.as_str() {
            "spec" => VerusAttr::ReturnMode(Mode::Spec),
            "proof" => VerusAttr::ReturnMode(Mode::Proof),
            "exec" => VerusAttr::ReturnMode(Mode::Exec),
            _ => VerusAttr::Unknown("verifier::returns(..)".to_string()),
        },
        ("opaque", None) => VerusAttr::Opaque,
        ("inline", None) => VerusAttr::Inline,
        ("prophetic", None) => VerusAttr::Prophetic,
        ("external_body", None) => VerusAttr::ExternalBody,
        ("external", None) => VerusAttr::External,
        ("proof_note", Some([Tree::Lit(LitKind::Str, text)])) => VerusAttr::ProofNote(text.clone()),
        ("custom_err", Some([Tree::Lit(LitKind::Str, text)])) => VerusAttr::CustomErr(text.clone()),
        ("rlimit", Some([Tree::Lit(LitKind::Integer, digits)])) => match digits.parse::<u64>() {
            Ok(n) => VerusAttr::Rlimit(Rlimit::Finite(n)),
            Err(_) => VerusAttr::Unknown("verifier::rlimit".to_string()),
        },
        ("rlimit", Some([Tree::Fun(word, None)])) if word == "infinity" => {
            VerusAttr::Rlimit(Rlimit::Infinite)
        }
        ("loop_isolation", None) => VerusAttr::LoopIsolation(true),
        ("loop_isolation", Some([Tree::Fun(value, None)])) if value == "true" => {
            VerusAttr::LoopIsolation(true)
        }
        ("loop_isolation", Some([Tree::Fun(value, None)])) if value == "false" => {
            VerusAttr::LoopIsolation(false)
        }
        ("allow_complex_invariants", None) => VerusAttr::AllowComplexInvariants,
        ("exec_allows_no_decreases_clause", None) => VerusAttr::ExecAllowsNoDecreasesClause,
        ("decreases_by" | "recommends_by", None) => VerusAttr::DecreasesBy,
        ("assume_termination", None) => VerusAttr::AssumeTermination,
        ("spinoff_prover", None) => VerusAttr::SpinoffProver,
        ("trigger", None) => VerusAttr::Trigger(None),
        ("trigger", Some(args)) => trigger_attr(args),
        ("auto_trigger", None) => VerusAttr::AutoTrigger,
        ("all_triggers", None) => VerusAttr::AllTriggers,
        _ => VerusAttr::Unknown(format!("verifier::{keyword}")),
    }
}

/// Is `attr` one of the loop settings a function inherits from the items
/// around it ([`loop_settings`])? Verus reads them there and nowhere else.
#[must_use]
pub const fn is_loop_setting(attr: &VerusAttr) -> bool {
    matches!(
        attr,
        VerusAttr::LoopIsolation(_)
            | VerusAttr::AllowComplexInvariants
            | VerusAttr::ExecAllowsNoDecreasesClause
    )
}

/// The loop settings of a function, from its own attributes and those of
/// the items around it up to the crate root (`attributes.rs`,
/// `get_loop_isolation_walk_parents` and its siblings).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct LoopSettings {
    /// The innermost `loop_isolation`, if any.
    pub isolation: Option<bool>,
    /// `allow_complex_invariants` anywhere.
    pub allow_complex_invariants: bool,
    /// `exec_allows_no_decreases_clause` anywhere.
    pub allow_no_decreases: bool,
}

/// [`LoopSettings`] of `def_id`: its attributes, then its parent's, up to
/// the crate root; the first `loop_isolation` met wins.
pub fn loop_settings(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    def_id: rustc_hir::def_id::DefId,
) -> LoopSettings {
    let mut out = LoopSettings::default();
    let mut current = Some(def_id);
    while let Some(id) = current {
        if let Some(local) = id.as_local() {
            let hir_id = tcx.local_def_id_to_hir_id(local);
            for (attr, _) in verus_attrs(tcx.hir_attrs(hir_id)) {
                match attr {
                    VerusAttr::LoopIsolation(flag) if out.isolation.is_none() => {
                        out.isolation = Some(flag);
                    }
                    VerusAttr::AllowComplexInvariants => out.allow_complex_invariants = true,
                    VerusAttr::ExecAllowsNoDecreasesClause => out.allow_no_decreases = true,
                    _ => {}
                }
            }
        }
        current = tcx.opt_parent(id);
    }
    out
}

/// Parse the tokens of an attribute's arguments: comma-separated identifiers
/// (each optionally followed by a delimited argument list) and literals.
/// Returns `None` for any other token.
fn token_trees(stream: &TokenStream) -> Option<Vec<Tree>> {
    let tokens: Vec<&TokenTree> = stream.iter().collect();
    let mut trees = Vec::new();
    let mut i = 0;
    while i < tokens.len() {
        let TokenTree::Token(token, _) = tokens[i] else {
            return None;
        };
        match token.kind {
            TokenKind::Literal(lit) => {
                trees.push(Tree::Lit(lit.kind, lit.symbol.as_str().to_string()))
            }
            TokenKind::Ident(symbol, _) => {
                let args = match tokens.get(i + 1) {
                    Some(TokenTree::Delimited(_, _, _, inner)) => {
                        i += 1;
                        Some(token_trees(inner)?)
                    }
                    _ => None,
                };
                trees.push(Tree::Fun(symbol.as_str().to_string(), args));
            }
            TokenKind::Comma => {}
            _ => return None,
        }
        i += 1;
    }
    Some(trees)
}

/// The item-level facts the reader needs, gathered from an item's attributes.
#[derive(Debug, Clone, Default)]
pub struct ItemAttrs {
    /// The unique directive's effect; full attribute syntax is still parsed.
    pub inline: bool,
    /// `prophetic`: the function result may depend on prophecy.
    pub prophetic: bool,
    /// Came from `verus!`.
    pub verus_macro: bool,
    /// Declared mode, from the first mode attribute; `None` means exec.
    pub mode: Option<Mode>,
    /// Declared mode of the return value (`returns(..)`); `None` means the
    /// default for the function's mode.
    pub ret_mode: Option<Mode>,
    /// `uninterp`, the last of `open`, `closed` and `uninterp`.
    pub uninterp: bool,
    /// `external_body`.
    pub external_body: bool,
    /// Macro-marked broadcast proof function (distinct from deprecated syntax).
    pub broadcast_forall: bool,
    /// `external`.
    pub external: bool,
    /// `opaque`.
    pub opaque: bool,
    /// `rlimit`.
    pub rlimit: Option<Rlimit>,
    /// `reveal_fn`.
    pub reveal_fn: bool,
    /// `open`, the last of `open`, `closed` and `uninterp`: a spec
    /// function's body is visible wherever the function is.
    pub open: bool,
    /// `closed`, the last of `open`, `closed` and `uninterp`: a spec
    /// function's body is visible only in its module.
    pub closed: bool,
    /// `decreases_by`, `recommends_by` or `via`.
    pub decreases_by: bool,
    /// `assume_termination`.
    pub assume_termination: bool,
    /// Verus attributes the reader cannot honour on an item, with spans.
    pub unsupported: Vec<(String, Span)>,
}

/// Collect the item-level Verus attributes of an item, the way Verus reads
/// them (`attributes.rs`): the first mode attribute gives the mode
/// (`get_mode_opt`), and the last of `open`, `closed` and `uninterp` gives
/// the body's visibility (`get_verifier_attrs`, `publish`), so an attribute
/// written before the ones `verus!` adds decides the mode and loses the
/// visibility. The last return mode counts (`get_ret_mode`).
pub fn item_attrs(attrs: &[Attribute]) -> ItemAttrs {
    let mut out = ItemAttrs::default();
    for (attr, span) in verus_attrs(attrs) {
        match attr {
            VerusAttr::VerusMacro => out.verus_macro = true,
            VerusAttr::Mode(mode) => {
                out.mode.get_or_insert(mode);
            }
            VerusAttr::ReturnMode(mode) => out.ret_mode = Some(mode),
            VerusAttr::Visibility { open } => {
                out.open = open;
                out.closed = !open;
                out.uninterp = false;
            }
            VerusAttr::Uninterp => {
                out.uninterp = true;
                out.open = false;
                out.closed = false;
            }
            // Verus reads it only on the `use` statement that `open(in
            // path)` puts in a function's body; on an item it does nothing.
            VerusAttr::OpenVisibilityQualifier => {}
            VerusAttr::ExternalBody => out.external_body = true,
            VerusAttr::BroadcastForall => out.broadcast_forall = true,
            VerusAttr::External => out.external = true,
            VerusAttr::Opaque => out.opaque = true,
            VerusAttr::Inline => out.inline = true,
            VerusAttr::Prophetic => out.prophetic = true,
            VerusAttr::Rlimit(r) => out.rlimit = Some(r),
            VerusAttr::RevealFn => out.reveal_fn = true,
            VerusAttr::ProofBlock => out
                .unsupported
                .push(("verifier::proof_block".to_string(), span)),
            VerusAttr::BroadcastUseReveal => out
                .unsupported
                .push(("verus::internal(broadcast_use_reveal)".to_string(), span)),
            VerusAttr::ProofNote(_) => out
                .unsupported
                .push(("verifier::proof_note".to_string(), span)),
            VerusAttr::CustomErr(_) => out
                .unsupported
                .push(("verifier::custom_err".to_string(), span)),
            VerusAttr::InferMode => out
                .unsupported
                .push(("verus::internal(infer_mode)".to_string(), span)),
            VerusAttr::LetMarker(name) => out
                .unsupported
                .push((format!("verus::internal({name})"), span)),
            VerusAttr::OtherGhostBlock(name) | VerusAttr::Unknown(name) => {
                out.unsupported.push((name, span))
            }
            VerusAttr::Trigger(_) | VerusAttr::AutoTrigger | VerusAttr::AllTriggers => out
                .unsupported
                .push(("verus::internal(trigger)".to_string(), span)),
            VerusAttr::DecreasesBy => out.decreases_by = true,
            VerusAttr::AssumeTermination => out.assume_termination = true,
            VerusAttr::SpinoffProver | VerusAttr::GetFieldManyVariants => {}
            // Read where a loop needs them ([`loop_settings`]).
            VerusAttr::LoopIsolation(_)
            | VerusAttr::AllowComplexInvariants
            | VerusAttr::ExecAllowsNoDecreasesClause => {}
        }
    }
    out
}

/// Declaration markers are read before the ghost-block mode promotion, as in
/// upstream `let_stmt_to_vir`. `unwrapped_binding` only controls a warning.
pub(crate) fn local_prophecy(attrs: &[Attribute], declared_mode: Mode) -> DeclProphecy {
    let parsed = verus_attrs(attrs);
    declaration_prophecy(
        parsed.iter().any(|(attr, _)| *attr == VerusAttr::Prophetic),
        parsed
            .iter()
            .any(|(attr, _)| *attr == VerusAttr::LetMarker("infer_proph")),
        declared_mode,
    )
}

fn declaration_prophecy(prophetic: bool, infer_proph: bool, mode: Mode) -> DeclProphecy {
    if prophetic {
        DeclProphecy::Prophetic
    } else if infer_proph && mode == Mode::Spec {
        DeclProphecy::DelayedInfer
    } else {
        DeclProphecy::Default
    }
}

#[cfg(test)]
mod prophecy_tests {
    use super::*;

    #[test]
    fn explicit_prophetic_is_semantic_and_requires_no_arguments() {
        assert_eq!(verifier_attr("prophetic", None), VerusAttr::Prophetic);
        assert!(matches!(
            verifier_attr("prophetic", Some(&[])),
            VerusAttr::Unknown(_)
        ));
        assert!(matches!(
            verifier_attr("prophetic", Some(&[Tree::Fun("true".into(), None)])),
            VerusAttr::Unknown(_)
        ));
    }

    #[test]
    fn declaration_markers_match_original_mode_and_explicit_precedence() {
        assert_eq!(
            declaration_prophecy(false, false, Mode::Spec),
            DeclProphecy::Default
        );
        assert_eq!(
            declaration_prophecy(false, true, Mode::Spec),
            DeclProphecy::DelayedInfer
        );
        for mode in [Mode::Exec, Mode::Proof] {
            assert_eq!(
                declaration_prophecy(false, true, mode),
                DeclProphecy::Default
            );
        }
        for mode in [Mode::Spec, Mode::Proof, Mode::Exec] {
            // Mode validation rejects the latter two; parsing preserves the marker.
            assert_eq!(
                declaration_prophecy(true, true, mode),
                DeclProphecy::Prophetic
            );
        }
        assert_eq!(
            internal_attr(&Tree::Fun("unwrapped_binding".into(), None)),
            VerusAttr::LetMarker("unwrapped_binding")
        );
    }
}
