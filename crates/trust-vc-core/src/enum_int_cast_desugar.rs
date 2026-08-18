//! Source-level desugaring of `<fieldless-enum> as <int>` into an integer
//! expression equal to the variant's declaration-order discriminant.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Rust assigns a C-like (fieldless) enum the discriminants `0, 1, 2, …` in
//! declaration order WHEN no variant carries an explicit discriminant. Verus
//! lets `e as int` read that discriminant; the trust-vc cast encoder cannot
//! (a datatype value has no int view), so `e as u64` fail-closes at encoding.
//!
//! This pass rewrites ONLY the cast's OPERAND — the enum expression — into an
//! equal integer expression, leaving the `as TARGET` in place so the existing,
//! already-sound integer→TARGET cast handling performs the final conversion
//! uniformly for every target (`u64`, `int`, `nat`, …):
//!   · `Enum::Variant as T`   →  `<index> as T`                 (literal ctor)
//!   · `c as T` (c: Enum)     →  `(match c { V0 => 0, .. }) as T`
//! The `match` is exhaustive over the enum (one arm per variant), producing the
//! variant's index; the existing match-over-enum encoding is sound and the
//! arms are ordinary integer literals.
//!
//! SOUNDNESS (never a false `Verified`): a rewrite fires ONLY for an enum that
//! is (a) fieldless (every variant `Fields::Unit`) and (b) free of explicit
//! discriminants — exactly when declaration order IS Rust's discriminant. An
//! `enum E { A = 5, B }` (explicit) or any fielded enum is never collected, so
//! its cast is left untouched and stays fail-closed. The variable form fires
//! only for a bare parameter whose declared type is such an enum and that is
//! never re-bound in the body (shadowing would change what `c` denotes) — a
//! rewrite therefore only turns a previously-fail-closed cast into a soundly
//! modeled one. See enum_int_cast.rs for the cardinal tests.

use std::collections::{BTreeMap, BTreeSet};

use quote::{quote, ToTokens};
use syn::visit::Visit;
use syn::visit_mut::VisitMut;
use syn::{Attribute, Expr, File, FnArg, Ident, ItemFn, Meta, Pat, Stmt};

/// Integer target types whose `as` cast this pass may feed a discriminant into.
fn is_integer_target(ty: &syn::Type) -> bool {
    let rendered = ty.to_token_stream().to_string();
    matches!(
        rendered.as_str(),
        "u8" | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "int"
            | "nat"
    )
}

/// A fieldless enum's variants paired with their Rust-assigned integer
/// discriminant (`name → [(variant, discriminant)]`).
type CastableEnums = BTreeMap<String, Vec<(Ident, i128)>>;

/// Parse an explicit-discriminant expression as an `i128` — an integer literal
/// or its negation. Anything else (a const path, a computed expression) returns
/// `None`, which fail-closes the whole enum (its discriminants are not
/// statically known here).
fn eval_discriminant_expr(expr: &Expr) -> Option<i128> {
    match expr {
        Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit),
            ..
        }) => lit.base10_parse::<i128>().ok(),
        Expr::Unary(syn::ExprUnary {
            op: syn::UnOp::Neg(_),
            expr,
            ..
        }) => eval_discriminant_expr(expr).map(|v| -v),
        Expr::Group(g) => eval_discriminant_expr(&g.expr),
        Expr::Paren(p) => eval_discriminant_expr(&p.expr),
        _ => None,
    }
}

/// Collect the file's fieldless enums with each variant's Rust discriminant.
///
/// Rust assigns a fieldless enum's discriminants by: the explicit value where
/// given, else the previous discriminant + 1 (the first defaulting to 0). This
/// reproduces that rule EXACTLY, so `variant → value` is sound for both plain
/// (`{A,B,C}` → 0,1,2) and explicitly-numbered (`{A=5,B}` → 5,6) enums.
///
/// An enum is EXCLUDED (left fail-closed) if any variant is non-unit, any
/// explicit discriminant is not a statically-evaluable integer literal, or the
/// computed sequence contains a duplicate (which rustc itself rejects, but
/// excluding keeps the rewrite sound regardless).
fn collect_castable_enums(file: &File) -> CastableEnums {
    let mut enums = BTreeMap::new();
    for item in &file.items {
        let syn::Item::Enum(item_enum) = item else {
            continue;
        };
        if item_enum.variants.is_empty() {
            continue;
        }
        if !item_enum
            .variants
            .iter()
            .all(|v| matches!(v.fields, syn::Fields::Unit))
        {
            continue;
        }
        let mut variants: Vec<(Ident, i128)> = Vec::with_capacity(item_enum.variants.len());
        let mut next: i128 = 0;
        let mut ok = true;
        for variant in &item_enum.variants {
            let value = match &variant.discriminant {
                Some((_, expr)) => match eval_discriminant_expr(expr) {
                    Some(v) => v,
                    None => {
                        ok = false;
                        break;
                    }
                },
                None => next,
            };
            variants.push((variant.ident.clone(), value));
            next = match value.checked_add(1) {
                Some(n) => n,
                None => {
                    ok = false;
                    break;
                }
            };
        }
        if !ok {
            continue;
        }
        // Reject duplicate discriminants (rustc E0081) defensively — a duplicate
        // would let two variants share a value, so a `match`-based rewrite could
        // not distinguish them.
        let mut seen = BTreeSet::new();
        if variants.iter().any(|(_, v)| !seen.insert(*v)) {
            continue;
        }
        enums.insert(item_enum.ident.to_string(), variants);
    }
    enums
}

/// Every identifier bound by a pattern anywhere in the function body — used to
/// exclude a parameter whose name is re-bound (shadowed), since inside that
/// scope `c` would no longer denote the enum parameter.
struct PatternBindingCollector<'a> {
    names: &'a mut BTreeSet<String>,
}
impl<'a, 'ast> Visit<'ast> for PatternBindingCollector<'a> {
    fn visit_pat_ident(&mut self, pat_ident: &'ast syn::PatIdent) {
        self.names.insert(pat_ident.ident.to_string());
        syn::visit::visit_pat_ident(self, pat_ident);
    }
}

/// A parameter `c: Enum` where `Enum` is a collected decl-order enum and `c` is
/// a plain identifier (no `ref`/`mut`/subpattern), keyed name → enum name.
fn enum_typed_params(
    func: &ItemFn,
    enums: &CastableEnums,
    rebound: &BTreeSet<String>,
) -> BTreeMap<String, String> {
    let mut map = BTreeMap::new();
    for input in &func.sig.inputs {
        let FnArg::Typed(pat_type) = input else {
            continue;
        };
        let Pat::Ident(pat_ident) = &*pat_type.pat else {
            continue;
        };
        if pat_ident.by_ref.is_some()
            || pat_ident.mutability.is_some()
            || pat_ident.subpat.is_some()
        {
            continue;
        }
        let name = pat_ident.ident.to_string();
        if rebound.contains(&name) {
            continue; // shadowed somewhere → what `c` denotes is not stable
        }
        let syn::Type::Path(type_path) = &*pat_type.ty else {
            continue;
        };
        let Some(ident) = type_path.path.get_ident() else {
            continue;
        };
        if enums.contains_key(&ident.to_string()) {
            map.insert(name, ident.to_string());
        }
    }
    map
}

/// If `expr` is a path `Enum::Variant` naming a collected enum's variant, return
/// that variant's Rust discriminant value.
fn literal_variant_value(expr: &Expr, enums: &CastableEnums) -> Option<i128> {
    let Expr::Path(expr_path) = expr else {
        return None;
    };
    if expr_path.qself.is_some() {
        return None;
    }
    let segs = &expr_path.path.segments;
    if segs.len() < 2 {
        return None;
    }
    let variant = segs.last()?.ident.to_string();
    let enum_name = segs[segs.len() - 2].ident.to_string();
    let variants = enums.get(&enum_name)?;
    variants
        .iter()
        .find(|(ident, _)| *ident == variant)
        .map(|(_, value)| *value)
}

/// Build the integer literal expression `<value>` (unsuffixed — the retained
/// outer `as TARGET` fixes its type). A negative discriminant renders as a
/// unary negation so it parses.
fn int_literal(value: i128) -> Expr {
    if value < 0 {
        // `unsigned_abs` (not `-value`) so `i128::MIN` cannot overflow the negation.
        let lit: syn::LitInt = syn::parse_str(&value.unsigned_abs().to_string())
            // quality-audit: allow-expect — a plain decimal literal always parses as LitInt
            .expect("magnitude literal parses");
        return Expr::Unary(syn::ExprUnary {
            attrs: Vec::new(),
            op: syn::UnOp::Neg(syn::token::Minus::default()),
            expr: Box::new(Expr::Lit(syn::ExprLit {
                attrs: Vec::new(),
                lit: syn::Lit::Int(lit),
            })),
        });
    }
    // quality-audit: allow-expect — a plain decimal literal always parses as LitInt
    let lit: syn::LitInt = syn::parse_str(&value.to_string()).expect("value literal parses");
    Expr::Lit(syn::ExprLit {
        attrs: Vec::new(),
        lit: syn::Lit::Int(lit),
    })
}

/// Build `match <scrutinee> { Enum::V0 => <d0>, Enum::V1 => <d1>, … }` mapping
/// each variant to its Rust discriminant.
fn discriminant_match(scrutinee: Ident, enum_name: &str, variants: &[(Ident, i128)]) -> Expr {
    let arms = variants
        .iter()
        .map(|(variant, value)| {
            let enum_ident = syn::Ident::new(enum_name, variant.span());
            let pat: Pat = syn::parse_quote!(#enum_ident::#variant);
            syn::Arm {
                attrs: Vec::new(),
                pat,
                guard: None,
                fat_arrow_token: syn::token::FatArrow::default(),
                body: Box::new(int_literal(*value)),
                comma: Some(syn::token::Comma::default()),
            }
        })
        .collect();
    Expr::Match(syn::ExprMatch {
        attrs: Vec::new(),
        match_token: syn::token::Match::default(),
        expr: Box::new(Expr::Path(syn::ExprPath {
            attrs: Vec::new(),
            qself: None,
            path: scrutinee.into(),
        })),
        brace_token: syn::token::Brace::default(),
        arms,
    })
}

struct EnumCastRewriter<'a> {
    enums: &'a CastableEnums,
    params: &'a BTreeMap<String, String>,
    rewrote: bool,
}
impl<'a> EnumCastRewriter<'a> {
    /// Rewrite the enum-int casts inside a token stream that parses as a single
    /// `Expr` (an `assert!` body or a `requires`/`ensures` attribute argument),
    /// returning the new tokens iff a rewrite fired. syn's AST visitors never
    /// descend into macro/attribute token streams, so these must be handled by
    /// re-parsing.
    fn rewrite_tokens(
        &self,
        tokens: &proc_macro2::TokenStream,
    ) -> Option<proc_macro2::TokenStream> {
        let mut expr: Expr = syn::parse2(tokens.clone()).ok()?;
        let mut inner = EnumCastRewriter {
            enums: self.enums,
            params: self.params,
            rewrote: false,
        };
        inner.visit_expr_mut(&mut expr);
        inner.rewrote.then(|| quote!(#expr))
    }
}
impl<'a> VisitMut for EnumCastRewriter<'a> {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        // Recurse first so nested casts are handled bottom-up.
        syn::visit_mut::visit_expr_mut(self, expr);

        // A spec macro (`trust_vc::assert!(EXPR)`) hides its cast in an opaque
        // token stream. Re-parse, rewrite, re-emit.
        if let Expr::Macro(expr_macro) = expr {
            if let Some(new_tokens) = self.rewrite_tokens(&expr_macro.mac.tokens) {
                expr_macro.mac.tokens = new_tokens;
                self.rewrote = true;
            }
            return;
        }

        let Expr::Cast(cast) = expr else {
            return;
        };
        if !is_integer_target(&cast.ty) {
            return;
        }
        // Literal constructor: `Enum::Variant as T` → `<discriminant> as T`.
        if let Some(value) = literal_variant_value(&cast.expr, self.enums) {
            *cast.expr = int_literal(value);
            self.rewrote = true;
            return;
        }
        // Enum-typed parameter: `c as T` → `(match c { .. }) as T`.
        if let Expr::Path(expr_path) = &*cast.expr {
            if expr_path.qself.is_none() {
                if let Some(ident) = expr_path.path.get_ident() {
                    if let Some(enum_name) = self.params.get(&ident.to_string()) {
                        let variants = &self.enums[enum_name];
                        *cast.expr = discriminant_match(ident.clone(), enum_name, variants);
                        self.rewrote = true;
                    }
                }
            }
        }
    }

    fn visit_stmt_mut(&mut self, stmt: &mut Stmt) {
        syn::visit_mut::visit_stmt_mut(self, stmt);
        // A statement-position spec macro (`trust_vc::assert!(EXPR);`).
        if let Stmt::Macro(stmt_macro) = stmt {
            if let Some(new_tokens) = self.rewrite_tokens(&stmt_macro.mac.tokens) {
                stmt_macro.mac.tokens = new_tokens;
                self.rewrote = true;
            }
        }
    }
}

/// Rewrite the enum-int casts inside a function's `requires`/`ensures`/
/// `recommends`/`invariant` contract attributes (each carries its predicate as
/// an opaque `Meta::List` token stream that AST visitors do not descend into).
fn rewrite_contract_attrs(rewriter: &EnumCastRewriter<'_>, attrs: &mut [Attribute]) -> bool {
    let mut changed = false;
    for attr in attrs.iter_mut() {
        let Meta::List(meta_list) = &mut attr.meta else {
            continue;
        };
        let is_contract = meta_list.path.segments.last().is_some_and(|seg| {
            matches!(
                seg.ident.to_string().as_str(),
                "requires" | "ensures" | "recommends" | "invariant" | "assert"
            )
        });
        if !is_contract {
            continue;
        }
        if let Some(new_tokens) = rewriter.rewrite_tokens(&meta_list.tokens) {
            meta_list.tokens = new_tokens;
            changed = true;
        }
    }
    changed
}

/// Rewrite `<fieldless-decl-order-enum> as <int>` casts in `func`'s body into an
/// equivalent integer expression. Returns `Some(rewritten)` if any cast was
/// rewritten, else `None` (leaving the function — and its fail-closed cast —
/// untouched).
pub(crate) fn desugar_enum_int_cast(func: &ItemFn, file: Option<&File>) -> Option<ItemFn> {
    let enums = collect_castable_enums(file?);
    if enums.is_empty() {
        return None;
    }
    let mut rebound = BTreeSet::new();
    PatternBindingCollector {
        names: &mut rebound,
    }
    .visit_block(&func.block);
    let params = enum_typed_params(func, &enums, &rebound);

    let mut rewritten = func.clone();
    let mut rewriter = EnumCastRewriter {
        enums: &enums,
        params: &params,
        rewrote: false,
    };
    rewriter.visit_item_fn_mut(&mut rewritten);
    let body_changed = rewriter.rewrote;
    // Contract attributes (`#[trust_vc::ensures(..)]`) hold their predicate as an
    // opaque token stream the body visit above does not reach — rewrite them
    // separately with a fresh (non-mutating) rewriter view.
    let attr_rewriter = EnumCastRewriter {
        enums: &enums,
        params: &params,
        rewrote: false,
    };
    let attrs_changed = rewrite_contract_attrs(&attr_rewriter, &mut rewritten.attrs);
    if body_changed || attrs_changed {
        Some(rewritten)
    } else {
        None
    }
}
