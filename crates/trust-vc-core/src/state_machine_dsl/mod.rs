//! D1a: item-position `trust_vc::state_machine!` (non-tokenized).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! # What this is
//!
//! A native expansion of Verus's non-tokenized `state_machine!` DSL (pinned
//! upstream: `source/state_machines_macros` at Verus `a40d57c7`). It runs at
//! the SHARED parse entry ([`crate::parse_file_allow_tracked`]) before any
//! other rewrite, so every lane that parses a file — the function lane,
//! conformance, the CLI scan, evidence, dependency specs, source trees, mode
//! scans — sees the same generated items. For a file with no item-position
//! `state_machine!` / `tokenized_state_machine!` invocation it is an exact
//! no-op.
//!
//! # What an admitted machine `X` becomes (file lane)
//!
//! All at the FILE ROOT, with machine-unique names (the engine's inherent-
//! method registries are keyed by bare type name, so a generated `X::State`
//! per machine would collide):
//!
//! * `pub struct __TvcSm_X_State { pub f: T, .. }`;
//! * one inherent impl holding every user `#[invariant]` as a
//!   `#[trust_vc::spec]` `&self` method and `invariant(&self)`, the
//!   conjunction of the user invariant BODIES (inlined, not called);
//! * free `#[trust_vc::spec]` relations `__TvcSm_X__{c, c_enabled}` per
//!   `init!`, `__TvcSm_X__{t, t_strong, t_enabled}` per `transition!` /
//!   `readonly!`, and `__TvcSm_X__{init, next, next_strong}`;
//! * one free `#[trust_vc::proof]` fn per `#[inductive(..)]` lemma, keeping
//!   the user's ident, span and body, with the generated contract
//!   (`requires c(post, p̄)` / `requires pre.invariant() && t_strong(..)`,
//!   `ensures post.invariant()`).
//!
//! Every generated item carries `#[doc = "trust_vc:state_machine_generated"]`.
//! There are no axioms, no `external_body`, no `assume`, no trusted contracts:
//! every relation is a definitional spec fn, and the engine REFUSES (rather
//! than silently uninterprets) a generated definition whose axiom it would
//! drop.
//!
//! References `X::State`, `X::State::g`, `X::State::lemma` anywhere in the
//! file are rewritten at token level to the generated names. Everything else
//! under `X::` is POISON: a reserved ident `__trust_vc_sm_poison_<k>` paired
//! with a root marker item `__trust_vc_state_machine_refused!{ k line "msg" }`.
//! A refused machine is replaced by such a marker, and every `X::…` reference
//! to it is poisoned; the parse itself never fails. Any function whose tokens
//! carry a poison ident fails closed with the recorded message.
//!
//! # Binding rule for slice 1c (CHC)
//!
//! [`LemmaStrategy`] has exactly one variant. A CHC/PDR result proves an
//! invariant of REACHABLE states; it does not prove a lemma's contract
//! (`inv(pre) && t(pre, post) ==> inv(post)`), which clients assume at every
//! call. A CHC result may therefore NEVER discharge a user lemma contract. It
//! may only propose a separately generated invariant with its own generated
//! lemmas (checked by the ordinary pipeline), or supply hints.

mod expand;
mod parse;
mod relation;
mod wf;

#[cfg(test)]
mod tests;

use proc_macro2::TokenStream;
use syn::{File, Item};

/// Doc-attribute text on every generated item.
pub const GENERATED_MARKER: &str = "trust_vc:state_machine_generated";
/// Reserved prefix of generated root items.
pub(crate) const GENERATED_PREFIX: &str = "__TvcSm_";
/// Reserved prefix of poison idents.
pub(crate) const POISON_PREFIX: &str = "__trust_vc_sm_poison_";
/// Name of the root refusal marker item macro.
pub(crate) const REFUSED_MARKER_MACRO: &str = "__trust_vc_state_machine_refused";
/// The fourth token of a refusal marker that stands for items this lane does
/// not read: an invocation of a macro that is not trust_vc's own
/// `state_machine!`, or a rewritten item that did not parse back and was
/// dropped. A marker for trust_vc's own refused machine, or for a reference
/// site, carries only its three parts.
pub(crate) const UNREAD_MARKER_FLAG: &str = "unread";

/// How an inductiveness lemma is discharged. See the module docs for the
/// binding rule that keeps this a single variant until slice 1c.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LemmaStrategy {
    /// The user's lemma body, checked by the ordinary proof-fn pipeline.
    UserBody,
}

/// Expand every item-position `state_machine!` in `file` (file lane). Never
/// fails; refusals become poison markers. Exact no-op for files without an
/// item-position invocation.
pub fn expand_file(file: &mut File) {
    expand::expand_file(file);
}

/// Proc-macro lane: expand one `state_machine!` invocation body.
pub fn expand_tokens(input: TokenStream) -> TokenStream {
    expand::expand_tokens(input)
}

fn marker_parts(item: &Item) -> Option<(usize, usize, String)> {
    let Item::Macro(m) = item else { return None };
    if m.ident.is_some() || !m.mac.path.is_ident(REFUSED_MARKER_MACRO) {
        return None;
    }
    let mut iter = m.mac.tokens.clone().into_iter();
    let k = iter.next()?.to_string().parse().ok()?;
    let line = iter.next()?.to_string().parse().ok()?;
    let lit: syn::LitStr = syn::parse2(iter.next()?.into()).ok()?;
    Some((k, line, lit.value()))
}

fn walk_markers(items: &[Item], out: &mut Vec<(usize, usize, String)>) {
    for item in items {
        if let Some(parts) = marker_parts(item) {
            out.push(parts);
        }
        if let Item::Mod(m) = item {
            if let Some((_, inner)) = &m.content {
                walk_markers(inner, out);
            }
        }
    }
}

/// Every refusal / poison marker in an EXPANDED file, as `(line, message)`.
pub fn refusals(file: &File) -> Vec<(usize, String)> {
    let mut out = Vec::new();
    walk_markers(&file.items, &mut out);
    out.into_iter().map(|(_, line, msg)| (line, msg)).collect()
}

/// The message recorded for a poison ident in an EXPANDED file.
pub fn poison_message(file: &File, ident: &proc_macro2::Ident) -> Option<String> {
    let k: usize = ident
        .to_string()
        .strip_prefix(POISON_PREFIX)?
        .parse()
        .ok()?;
    let mut out = Vec::new();
    walk_markers(&file.items, &mut out);
    out.into_iter()
        .find(|(kk, _, _)| *kk == k)
        .map(|(_, _, msg)| msg)
}

/// The first poison ident in `tokens`, if any.
pub(crate) fn first_poison_ident(tokens: TokenStream) -> Option<proc_macro2::Ident> {
    for tree in tokens {
        match tree {
            proc_macro2::TokenTree::Ident(ident)
                if ident.to_string().starts_with(POISON_PREFIX) =>
            {
                return Some(ident)
            }
            proc_macro2::TokenTree::Group(g) => {
                if let Some(found) = first_poison_ident(g.stream()) {
                    return Some(found);
                }
            }
            _ => {}
        }
    }
    None
}

/// Every `(machine, lemma, kind)` of every admitted root machine in a RAW
/// (unexpanded, plain `syn::parse_file`) file. `kind` is `"init"` or
/// `"transition"`.
pub fn machine_lemmas(file: &File) -> Vec<(String, String, &'static str)> {
    let facts = wf::FileFacts::collect(&file.items);
    let mut out = Vec::new();
    for (index, item) in file.items.iter().enumerate() {
        let Item::Macro(m) = item else { continue };
        if !expand::is_sm_invocation(item)
            || crate::macro_scope::resolve_item_macro(file, &[index])
                != crate::macro_scope::ItemMacroResolution::TrustVc
            || !m
                .mac
                .path
                .segments
                .last()
                .is_some_and(|s| s.ident == "state_machine")
        {
            continue;
        }
        if let Ok(machine) = wf::check_machine(m.mac.tokens.clone(), Some(&facts)) {
            for lemma in &machine.lemmas {
                out.push((
                    machine.name.to_string(),
                    lemma.func.sig.ident.to_string(),
                    lemma.kind.label(),
                ));
            }
        }
    }
    out
}

/// True when `file` holds an item-position `state_machine!` or
/// `tokenized_state_machine!` invocation anywhere (raw file).
pub fn has_item_position_invocation(file: &File) -> bool {
    expand::has_invocations(&file.items)
}

/// True when `attrs` carries the generated-item doc marker.
pub(crate) fn is_generated(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| match &attr.meta {
        syn::Meta::NameValue(nv) if nv.path.is_ident("doc") => match &nv.value {
            syn::Expr::Lit(syn::ExprLit {
                lit: syn::Lit::Str(s),
                ..
            }) => s.value() == GENERATED_MARKER,
            _ => false,
        },
        _ => false,
    })
}

/// Item labels of the file-lane expansion of the machine in `input` and of
/// the proc-macro-lane expansion, for the compile-lane parity test.
#[doc(hidden)]
pub fn lane_item_labels(input: TokenStream) -> (Vec<String>, Vec<String>) {
    let file_lane = match wf::check_machine(input.clone(), None) {
        Ok(machine) => expand::file_lane_item_names(&machine),
        Err(errors) => vec![format!("error: {}", errors.join("; "))],
    };
    let proc_lane = match syn::parse2::<File>(expand::expand_tokens(input)) {
        Ok(file) => file.items.iter().map(expand::item_label).collect(),
        Err(err) => vec![format!("error: {err}")],
    };
    (file_lane, proc_lane)
}
