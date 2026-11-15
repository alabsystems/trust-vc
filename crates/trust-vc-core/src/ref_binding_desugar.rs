//! Source-level desugaring of a binding-mode borrow in a `let`:
//!   · `let ref mut r = e;`    → `let r = &mut e;`
//!   · `let ref mut r: T = e;` → `let r: &mut T = &mut e;`
//!   · `let ref r = e;`        → `let r = &e;`
//!   · `let ref r: T = e;`     → `let r: &T = &e;`
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Rust reference, "Identifier patterns": a `ref` / `ref mut` identifier
//! pattern binds a reference to the matched place instead of moving or copying
//! it, so `let ref mut r = s;` is exactly `let r = &mut s;` (a value
//! initializer borrows a lifetime-extended temporary in both spellings).
//!
//! SOUNDNESS: the extractor read the
//! binding mode nowhere, so `let ref mut r = s;` bound `r` to an owned COPY of
//! `s`, and every write through `r` was modeled on the copy —
//! `let mut s = S64 { f: 5u64 }; let ref mut r = s; r.f += 1u64;
//! assert!(s.f == 5u64);` VERIFIED, as did the tuple form, `r.f = 6u64`, the
//! typed `let ref mut r: S64 = s;`, and an overflow split across `r.f += 50u8;
//! s.f += 50u8;`. The explicit `let r = &mut s;` spelling is modeled (or
//! fails closed) by the `&mut` alias machinery, so rewriting to it can only
//! replace the copy model with the reference model.
//!
//! SCOPE: only a plain `ref` / `ref mut` identifier pattern (optionally
//! type-ascribed) with no `@` subpattern and no `let ... else`, AND only over a
//! bare VARIABLE initializer. `ref` bindings inside tuple / struct / match /
//! `if let` patterns are untouched (they keep their existing fail-closed
//! rejections), and so is every non-variable initializer.
//!
//! The variable-initializer restriction is measured, not stylistic: the
//! explicit `&mut` machinery this rewrite hands the binding to carries a
//! pre-existing hole on an INDEX place — `let r = &mut x[5usize]; *r = 20u64;`
//! on `x: [u64; 3]` VERIFIES when nothing later reads the array (the bounds
//! obligation is only discharged when a later claim resolves the
//! `Seq::update`), and the same program with any later read of `x` IS refuted.
//! `let ref mut r = x[5usize];` fails closed today, so rewriting it would widen
//! that hole rather than narrow the copy model; it keeps its rejection until
//! the borrow itself pins the bound.

use proc_macro2::Span;
use syn::visit_mut::VisitMut;
use syn::{Expr, ItemFn, Local, Pat};

/// Whether `expr` is a bare variable — the only initializer this rewrite
/// accepts (see the SCOPE paragraph in the module docs).
fn is_bare_variable(expr: &Expr) -> bool {
    match expr {
        Expr::Paren(paren) => is_bare_variable(&paren.expr),
        Expr::Group(group) => is_bare_variable(&group.expr),
        Expr::Path(path) => path.qself.is_none() && path.path.get_ident().is_some(),
        _ => false,
    }
}

fn borrow_of(init: &Expr, mutable: bool) -> Expr {
    let place = match init {
        Expr::Path(_) | Expr::Field(_) | Expr::Index(_) | Expr::Paren(_) | Expr::Group(_) => {
            init.clone()
        }
        other => Expr::Paren(syn::ExprParen {
            attrs: Vec::new(),
            paren_token: syn::token::Paren::default(),
            expr: Box::new(other.clone()),
        }),
    };
    Expr::Reference(syn::ExprReference {
        attrs: Vec::new(),
        and_token: syn::Token![&](Span::call_site()),
        mutability: mutable.then(|| syn::Token![mut](Span::call_site())),
        expr: Box::new(place),
    })
}

/// Rewrites `local` in place when it is a qualifying binding-mode borrow.
fn desugar_local(local: &mut Local) -> bool {
    let Some(init) = local.init.as_mut() else {
        return false;
    };
    if init.diverge.is_some() {
        return false;
    }
    let (ident_pat, ty) = match &mut local.pat {
        Pat::Ident(ident) => (ident, None),
        Pat::Type(pat_type) => match pat_type.pat.as_mut() {
            Pat::Ident(ident) => (ident, Some(&mut pat_type.ty)),
            _ => return false,
        },
        _ => return false,
    };
    if ident_pat.by_ref.is_none() || ident_pat.subpat.is_some() {
        return false;
    }
    if !is_bare_variable(&init.expr) {
        return false;
    }
    let mutable = ident_pat.mutability.is_some();
    ident_pat.by_ref = None;
    ident_pat.mutability = None;
    if let Some(ty) = ty {
        let elem = std::mem::replace(
            ty.as_mut(),
            syn::Type::Verbatim(proc_macro2::TokenStream::new()),
        );
        **ty = syn::Type::Reference(syn::TypeReference {
            and_token: syn::Token![&](Span::call_site()),
            lifetime: None,
            mutability: mutable.then(|| syn::Token![mut](Span::call_site())),
            elem: Box::new(elem),
        });
    }
    *init.expr = borrow_of(&init.expr, mutable);
    true
}

struct RefBindingRewriter {
    rewrote: bool,
}

impl VisitMut for RefBindingRewriter {
    fn visit_local_mut(&mut self, local: &mut Local) {
        syn::visit_mut::visit_local_mut(self, local);
        if desugar_local(local) {
            self.rewrote = true;
        }
    }
}

/// Rewrite every qualifying `let ref [mut] r[: T] = e;` in `func` into the
/// explicit-borrow spelling. Returns `Some(rewritten)` iff any binding changed.
pub(crate) fn desugar_ref_bindings(func: &ItemFn) -> Option<ItemFn> {
    let mut rewritten = func.clone();
    let mut rewriter = RefBindingRewriter { rewrote: false };
    rewriter.visit_item_fn_mut(&mut rewritten);
    rewriter.rewrote.then_some(rewritten)
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::ToTokens;

    fn rewrite(src: &str) -> Option<String> {
        let func: ItemFn = syn::parse_str(src).expect("fn");
        desugar_ref_bindings(&func).map(|f| f.block.to_token_stream().to_string())
    }

    #[test]
    fn ref_mut_binding_becomes_explicit_mut_borrow() {
        let out = rewrite("fn f() { let mut s = 1u8; let ref mut r = s; *r += 1u8; }")
            .expect("rewritten");
        assert!(out.contains("let r = & mut s ;"), "{out}");
    }

    #[test]
    fn typed_and_shared_variable_initializers() {
        let out = rewrite("fn f() { let ref mut r: S = s; let ref q = b; }").expect("rewritten");
        assert!(out.contains("let r : & mut S = & mut s ;"), "{out}");
        assert!(out.contains("let q = & b ;"), "{out}");
    }

    #[test]
    fn non_ref_and_nested_patterns_are_untouched() {
        assert!(rewrite("fn f() { let mut r = s; let (ref mut a, b) = t; }").is_none());
        assert!(rewrite("fn f() { let ref mut r @ 1u8 = s; }").is_none());
    }

    #[test]
    fn non_variable_initializers_are_untouched() {
        // See the SCOPE paragraph: an index / field place would be handed to the
        // `&mut` machinery's pre-existing out-of-bounds-borrow hole.
        assert!(rewrite("fn f() { let ref mut r = x[5usize]; }").is_none());
        assert!(rewrite("fn f() { let ref mut r = t.0; }").is_none());
        assert!(rewrite("fn f() { let ref q = a + b; }").is_none());
        assert!(rewrite("fn f() { let ref mut r: S = mk(); }").is_none());
    }
}
