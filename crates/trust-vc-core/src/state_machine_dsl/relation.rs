//! The D1a relation compiler: an admitted transition body -> the definitional
//! relation `pre, post, params -> bool` and its enabling condition.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Mirrors the pinned upstream pipeline (`simplification.rs` then
//! `to_relation.rs`) for the statement subset D1a admits (`require`, `let`,
//! `update`, `init`, `if`), without enumerating paths:
//!
//! * `require E` conjoins `E` (upstream `prepend_conjunct`);
//! * `let x = E` is a pure substitution (admitted expressions contain no
//!   binders, and let names are unique across the whole transition, so no
//!   capture is possible);
//! * `update f = E` / `init f = E` rebind the field's POST value; `pre.f`
//!   always denotes the PRE field, exactly as upstream's `update_tmp_f`
//!   prologue (`simplification.rs`) never rebinds `pre`;
//! * `if C {A} else {B}` conjoins `imply(C, RA)` / `imply(!C, RB)` (upstream
//!   emits `if C {RA} else {RB}` when both sides are nonempty — the same
//!   proposition) and extracts every field value assigned on either side as
//!   `if C { a } else { b }` (upstream `get_extraction_decl_stmt`);
//! * the end of the body conjoins `post.f == cur(f)` for EVERY field — the
//!   frame is part of the relation, and an untouched field yields
//!   `post.f == pre.f`.
//!
//! The enabling condition is the relation with the postconditions removed
//! (upstream `to_is_enabled_condition_weak`).

use std::collections::BTreeMap;

use proc_macro2::TokenStream;
use quote::{quote, quote_spanned};
use syn::visit_mut::VisitMut;
use syn::{Expr, Ident, Pat};

use super::parse::{TStmt, TransitionAst, TransitionKind};
use super::wf::FieldDef;

/// Upper bound on the rendered relation, in bytes of token text.
pub(crate) const RELATION_SIZE_BOUND: usize = 64 * 1024;

struct Substituter<'a> {
    env: &'a BTreeMap<String, TokenStream>,
}

impl VisitMut for Substituter<'_> {
    fn visit_expr_mut(&mut self, node: &mut Expr) {
        if let Expr::Path(p) = node {
            if p.qself.is_none() {
                if let Some(ident) = p.path.get_ident() {
                    if let Some(replacement) = self.env.get(&ident.to_string()) {
                        let span = ident.span();
                        let tokens = quote_spanned!(span=> (#replacement));
                        *node = syn::parse2(tokens).expect("parenthesized expression re-parses");
                        return;
                    }
                }
            }
        }
        syn::visit_mut::visit_expr_mut(self, node);
    }

    fn visit_field_value_mut(&mut self, node: &mut syn::FieldValue) {
        // A shorthand `S { x }` must be expanded before its value is replaced.
        if node.colon_token.is_none() {
            node.colon_token = Some(Default::default());
        }
        syn::visit_mut::visit_field_value_mut(self, node);
    }
}

fn subst(e: &Expr, env: &BTreeMap<String, TokenStream>) -> TokenStream {
    let mut e = e.clone();
    Substituter { env }.visit_expr_mut(&mut e);
    quote!((#e))
}

type Cur = BTreeMap<String, Option<TokenStream>>;

fn conj(parts: &[TokenStream]) -> Option<TokenStream> {
    match parts {
        [] => None,
        [one] => Some(one.clone()),
        many => {
            let mut iter = many.iter();
            let first = iter.next().expect("nonempty");
            let mut acc = quote!(#first);
            for part in iter {
                acc = quote!(#acc && #part);
            }
            Some(quote!((#acc)))
        }
    }
}

fn compile(
    ts: &TStmt,
    env: &BTreeMap<String, TokenStream>,
    cur: &mut Cur,
    req: &mut Vec<TokenStream>,
) -> Result<(), String> {
    match ts {
        TStmt::Block(_, stmts) => {
            for s in stmts {
                compile(s, env, cur, req)?;
            }
            Ok(())
        }
        TStmt::Let {
            pat, expr, body, ..
        } => {
            let Pat::Ident(pi) = pat else {
                return Err("internal: let pattern reached the relation compiler".to_string());
            };
            let mut inner = env.clone();
            inner.insert(pi.ident.to_string(), subst(expr, env));
            compile(body, &inner, cur, req)
        }
        TStmt::Require(_, e) => {
            req.push(subst(e, env));
            Ok(())
        }
        TStmt::Update(_, f, e) | TStmt::Init(_, f, e) => {
            cur.insert(f.to_string(), Some(subst(e, env)));
            Ok(())
        }
        TStmt::If { cond, thn, els, .. } => {
            let c = subst(cond, env);
            let mut cur_a = cur.clone();
            let mut req_a = Vec::new();
            compile(thn, env, &mut cur_a, &mut req_a)?;
            let mut cur_b = cur.clone();
            let mut req_b = Vec::new();
            compile(els, env, &mut cur_b, &mut req_b)?;
            if let Some(ra) = conj(&req_a) {
                req.push(quote!((!#c || #ra)));
            }
            if let Some(rb) = conj(&req_b) {
                req.push(quote!((#c || #rb)));
            }
            let keys: Vec<String> = cur.keys().cloned().collect();
            for key in keys {
                let a = cur_a.get(&key).cloned().flatten();
                let b = cur_b.get(&key).cloned().flatten();
                let merged = match (a, b) {
                    (None, None) => None,
                    (Some(a), Some(b)) if a.to_string() == b.to_string() => Some(a),
                    (Some(a), Some(b)) => Some(quote!((if #c { #a } else { #b }))),
                    // wf guarantees both branches initialize the same fields.
                    _ => {
                        return Err(format!(
                            "internal: branches disagree on field '{key}' in the relation compiler"
                        ))
                    }
                };
                cur.insert(key, merged);
            }
            Ok(())
        }
        TStmt::Assert(..) | TStmt::Match { .. } | TStmt::SubUpdate(..) | TStmt::Special { .. } => {
            Err("internal: a refused statement reached the relation compiler".to_string())
        }
    }
}

/// The compiled relation and enabling condition bodies.
pub(crate) struct CompiledRelation {
    pub(crate) relation: TokenStream,
    pub(crate) enabled: TokenStream,
}

pub(crate) fn compile_transition(
    tr: &TransitionAst,
    fields: &[FieldDef],
    pre: &Ident,
    post: &Ident,
) -> Result<CompiledRelation, String> {
    let mut cur: Cur = BTreeMap::new();
    for f in fields {
        let name = &f.name;
        let initial = if tr.kind == TransitionKind::Init {
            None
        } else {
            Some(quote!(#pre.#name))
        };
        cur.insert(name.to_string(), initial);
    }
    let mut req = Vec::new();
    compile(&tr.body, &BTreeMap::new(), &mut cur, &mut req)?;
    let enabled = conj(&req).unwrap_or_else(|| quote!(true));
    let mut all = req;
    for f in fields {
        let name = &f.name;
        let value = cur
            .get(&name.to_string())
            .cloned()
            .flatten()
            .ok_or_else(|| format!("itialization procedure does not initialize field '{name}'"))?;
        all.push(quote!((#post.#name == #value)));
    }
    let relation = conj(&all).unwrap_or_else(|| quote!(true));
    let size = relation.to_string().len();
    if size > RELATION_SIZE_BOUND {
        return Err(format!(
            "relation for `{}` exceeds the D1a size bound",
            tr.name
        ));
    }
    Ok(CompiledRelation { relation, enabled })
}
