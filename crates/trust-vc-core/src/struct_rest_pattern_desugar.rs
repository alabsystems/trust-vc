//! Source-level desugaring of a `let` binding whose pattern the extractor does
//! not lower into per-element `let` bindings:
//!   · a struct pattern with a rest — `let S { a, b, .. } = obj;`
//!     → `let a = obj.a; let b = obj.b;`
//!   · a fixed-array pattern — `let [a, _, c] = arr;`
//!     → `let a = arr[0]; let c = arr[2];`
//!   · a tuple-struct pattern — `let TS(a, _) = t;`
//!     → `let a = t.0;`
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `let S { a, b, .. } = obj;` binds `a`/`b` to `obj.a`/`obj.b` and ignores the
//! rest. The extractor otherwise fail-closes such a `let` ("Failed to lower
//! obligation"). Rewriting it to the equivalent sequence of field-access lets —
//! `let a = obj.a; let b = obj.b;` — reuses the field-projection path the
//! extractor already handles soundly (a plain `let x = obj.field;`).
//!
//! SCOPE (everything else left untouched, fail-closed): the rewrite fires ONLY
//! when
//!   · the pattern is `Pat::Struct` WITH a rest `..` (a full struct pattern with
//!     no rest already lowers), every field binds a plain `Pat::Ident` (no
//!     `ref`/`mut`/nested subpattern), and no field carries a binding-`@`
//!     subpattern; and
//!   · the initializer is a bare identifier (or `self`), so re-projecting each
//!     field cannot re-run a side effect (an initializer that is a call, index,
//!     etc. is left alone — re-evaluating it per field would be UNSOUND).
//! A binding name equal to a field is Rust's shorthand (`a` ⇒ `obj.a`); a
//! renamed field (`a: x`) binds `x` ⇒ `obj.a`. The rewrite reproduces exactly
//! that mapping, so it can only turn a fail-closed `let` into a soundly modeled
//! one — never a false verify.

use syn::visit_mut::VisitMut;
use syn::{Block, Expr, Ident, ItemFn, Local, Pat, Stmt};

/// The single identifier an initializer projects from, if it is side-effect-free
/// to re-project (a bare identifier / `self`). Anything else returns `None`.
fn simple_receiver(expr: &Expr) -> Option<Ident> {
    let Expr::Path(expr_path) = expr else {
        return None;
    };
    if expr_path.qself.is_some() {
        return None;
    }
    expr_path.path.get_ident().cloned()
}

/// Recursively collect the `(binding, field-path)` pairs of a struct pattern,
/// descending into nested struct sub-patterns. `Outer { inner: Inner { v }, .. }`
/// yields `(v, [inner, v])` → `let v = recv.inner.v;`. Returns `None` if any
/// field member is unnamed (tuple struct) or any leaf is not a plain identifier.
fn collect_struct_bindings(
    pat_struct: &syn::PatStruct,
    prefix: &[Ident],
    out: &mut Vec<(Ident, Vec<Ident>)>,
) -> Option<()> {
    for field in &pat_struct.fields {
        let syn::Member::Named(field_ident) = &field.member else {
            return None; // tuple-struct members are not this shape
        };
        let mut path = prefix.to_vec();
        path.push(field_ident.clone());
        match &*field.pat {
            Pat::Ident(pat_ident) => {
                if pat_ident.by_ref.is_some()
                    || pat_ident.mutability.is_some()
                    || pat_ident.subpat.is_some()
                {
                    return None;
                }
                out.push((pat_ident.ident.clone(), path));
            }
            Pat::Struct(nested) => collect_struct_bindings(nested, &path, out)?,
            _ => return None, // tuple/slice/or/etc. subpattern → leave fail-closed
        }
    }
    Some(())
}

/// The `(binding, field-path)` pairs of a top-level `Pat::Struct`, flattening
/// nested struct sub-patterns. Fires ONLY when the extractor does not already
/// lower the pattern — i.e. it carries a rest `..` OR has a nested struct
/// sub-pattern; a FULL FLAT pattern (`S { a, b, c }`) already lowers and is left
/// alone. `None` if it does not qualify.
fn rest_struct_bindings(pat: &Pat) -> Option<Vec<(Ident, Vec<Ident>)>> {
    let Pat::Struct(pat_struct) = pat else {
        return None;
    };
    let has_nested_struct = pat_struct
        .fields
        .iter()
        .any(|field| matches!(&*field.pat, Pat::Struct(_)));
    if pat_struct.rest.is_none() && !has_nested_struct {
        return None; // full flat pattern — the extractor already lowers it
    }
    let mut bindings = Vec::new();
    collect_struct_bindings(pat_struct, &[], &mut bindings)?;
    if bindings.is_empty() {
        return None;
    }
    Some(bindings)
}

/// For a fixed-array pattern (`Pat::Slice`) WITHOUT a rest, the `(binding,
/// index)` pairs to bind. `_` elements are skipped. Returns `None` if any
/// element is not a plain identifier or `_` (a rest `..` shifts indices, and a
/// nested subpattern is not this shape).
fn slice_pattern_bindings(pat: &Pat) -> Option<Vec<(Ident, usize)>> {
    let Pat::Slice(pat_slice) = pat else {
        return None;
    };
    let mut bindings = Vec::new();
    for (index, elem) in pat_slice.elems.iter().enumerate() {
        match elem {
            Pat::Wild(_) => {}
            Pat::Ident(pat_ident) => {
                if pat_ident.by_ref.is_some()
                    || pat_ident.mutability.is_some()
                    || pat_ident.subpat.is_some()
                {
                    return None;
                }
                bindings.push((pat_ident.ident.clone(), index));
            }
            _ => return None, // Pat::Rest (index shift) or nested → fail-closed
        }
    }
    if bindings.is_empty() {
        return None;
    }
    Some(bindings)
}

/// For a tuple-struct pattern (`Pat::TupleStruct`, e.g. `TS(a, _)`) WITHOUT a
/// rest, the `(binding, position)` pairs to bind by numeric tuple index. `_`
/// elements are skipped. Returns `None` if any element is not a plain identifier
/// or `_` (a rest `..` shifts positions, and a nested subpattern is not this
/// shape).
fn tuple_struct_bindings(pat: &Pat) -> Option<Vec<(Ident, usize)>> {
    let Pat::TupleStruct(pat_ts) = pat else {
        return None;
    };
    let mut bindings = Vec::new();
    for (index, elem) in pat_ts.elems.iter().enumerate() {
        match elem {
            Pat::Wild(_) => {}
            Pat::Ident(pat_ident) => {
                if pat_ident.by_ref.is_some()
                    || pat_ident.mutability.is_some()
                    || pat_ident.subpat.is_some()
                {
                    return None;
                }
                bindings.push((pat_ident.ident.clone(), index));
            }
            _ => return None, // Pat::Rest (position shift) or nested → fail-closed
        }
    }
    if bindings.is_empty() {
        return None;
    }
    Some(bindings)
}

/// Expand a qualifying `let PAT = recv;` (struct-with-rest / nested, fixed-array,
/// or tuple-struct pattern) into per-element `let`s, preserving order. Returns
/// `None` if `local` does not qualify.
fn expand_local(local: &Local) -> Option<Vec<Stmt>> {
    // A `let ... else { .. }` (diverging) is a different shape — leave it.
    let init = local.init.as_ref()?;
    if init.diverge.is_some() {
        return None;
    }
    let receiver = simple_receiver(&init.expr)?;
    if let Some(bindings) = rest_struct_bindings(&local.pat) {
        return Some(
            bindings
                .into_iter()
                .map(|(binding, fields)| {
                    let mut access: Expr = syn::parse_quote! { #receiver };
                    for field in fields {
                        access = syn::parse_quote! { #access.#field };
                    }
                    syn::parse_quote! { let #binding = #access; }
                })
                .collect(),
        );
    }
    if let Some(bindings) = slice_pattern_bindings(&local.pat) {
        return Some(
            bindings
                .into_iter()
                .map(|(binding, index)| {
                    let idx = proc_macro2::Literal::usize_unsuffixed(index);
                    syn::parse_quote! { let #binding = #receiver[#idx]; }
                })
                .collect(),
        );
    }
    if let Some(bindings) = tuple_struct_bindings(&local.pat) {
        return Some(
            bindings
                .into_iter()
                .map(|(binding, index)| {
                    let member = syn::Index::from(index);
                    syn::parse_quote! { let #binding = #receiver.#member; }
                })
                .collect(),
        );
    }
    None
}

struct RestPatternRewriter {
    rewrote: bool,
}
impl VisitMut for RestPatternRewriter {
    fn visit_block_mut(&mut self, block: &mut Block) {
        // Recurse first so nested blocks are handled.
        syn::visit_mut::visit_block_mut(self, block);

        if !block
            .stmts
            .iter()
            .any(|stmt| matches!(stmt, Stmt::Local(local) if expand_local(local).is_some()))
        {
            return;
        }
        let mut new_stmts = Vec::with_capacity(block.stmts.len());
        for stmt in std::mem::take(&mut block.stmts) {
            match &stmt {
                Stmt::Local(local) => {
                    if let Some(expanded) = expand_local(local) {
                        new_stmts.extend(expanded);
                        self.rewrote = true;
                    } else {
                        new_stmts.push(stmt);
                    }
                }
                _ => new_stmts.push(stmt),
            }
        }
        block.stmts = new_stmts;
    }
}

/// Rewrite qualifying `let S { a, .. } = recv;` bindings in `func` into per-field
/// `let`s. Returns `Some(rewritten)` iff any binding was expanded.
pub(crate) fn desugar_struct_rest_pattern(func: &ItemFn) -> Option<ItemFn> {
    let mut rewritten = func.clone();
    let mut rewriter = RestPatternRewriter { rewrote: false };
    rewriter.visit_item_fn_mut(&mut rewritten);
    rewriter.rewrote.then_some(rewritten)
}
