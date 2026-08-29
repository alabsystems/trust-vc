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
//!
//! That argument is about WHICH ENUMS are castable. It says nothing about WHICH
//! ENUM a written path denotes, and that second question is where this pass was
//! actually unsound: the registry was keyed by BARE name from `file.items`
//! alone, so `m::E::C` and a top-level `E::C` were indistinguishable and the
//! top-level one won. See [`EnumPathScopes`] for the defect and the resolution
//! rules that replaced it, and enum_int_cast_scope_soundness.rs for the cardinal
//! tests. Resolving the path correctly is also what made module-declared enums
//! castable at all.

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

/// An enum declaration's identity: the inline-module path it is declared in,
/// plus its bare name. Keying by the BARE NAME ALONE was a cardinal false
/// verify — see [`EnumPathScopes`].
type EnumKey = (Vec<String>, String);

/// A fieldless enum's variants paired with their Rust-assigned integer
/// discriminant (`(module, name) → [(variant, discriminant)]`).
type CastableEnums = BTreeMap<EnumKey, Vec<(Ident, i128)>>;

/// Everything one walk over a file's items records about where enum names are
/// declared and what else could supply one.
///
/// `declarations` alone is not enough to resolve a use site: a name that is
/// declared NOWHERE the use site can see must not fall through to a same-named
/// declaration somewhere else, and a name that IS declared at the use site but
/// is not castable must shadow every other candidate rather than yield to one.
/// `all_enum_names` is what makes the second case decidable.
#[derive(Default)]
struct EnumScopeIndex {
    /// Enums this pass may rewrite, keyed by declaration site.
    declarations: CastableEnums,
    /// EVERY enum declared in the file, castable or not. A non-castable
    /// declaration still occupies its name and must fail the resolution closed.
    all_enum_names: BTreeSet<EnumKey>,
    /// `(module, in-scope name)` for every explicit `use` binding. A bound name
    /// may denote an item this file does not contain, so it is undecidable here.
    use_bound_names: BTreeSet<(Vec<String>, String)>,
    /// Modules holding a glob import, which can introduce a name from anywhere.
    glob_modules: BTreeSet<Vec<String>>,
}

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
fn collect_enum_scope_index(file: &File) -> EnumScopeIndex {
    let mut index = EnumScopeIndex::default();
    collect_enum_scope_items(&file.items, &mut Vec::new(), &mut index);
    index
}

/// Record every `use` binding and glob `tree` introduces into `module`.
fn collect_enum_use_tree(tree: &syn::UseTree, module: &[String], index: &mut EnumScopeIndex) {
    match tree {
        syn::UseTree::Path(path) => collect_enum_use_tree(&path.tree, module, index),
        syn::UseTree::Name(name) => {
            index
                .use_bound_names
                .insert((module.to_vec(), name.ident.to_string()));
        }
        syn::UseTree::Rename(rename) => {
            index
                .use_bound_names
                .insert((module.to_vec(), rename.rename.to_string()));
        }
        syn::UseTree::Glob(_) => {
            index.glob_modules.insert(module.to_vec());
        }
        syn::UseTree::Group(group) => {
            for item in &group.items {
                collect_enum_use_tree(item, module, index);
            }
        }
    }
}

fn collect_enum_scope_items(
    items: &[syn::Item],
    module: &mut Vec<String>,
    index: &mut EnumScopeIndex,
) {
    for item in items {
        if let syn::Item::Use(item_use) = item {
            collect_enum_use_tree(&item_use.tree, module, index);
            continue;
        }
        if let syn::Item::Mod(item_mod) = item {
            // An out-of-line `mod m;` has no content here; its enums are simply
            // absent from the index, which resolves as UNDECIDED rather than
            // falling through to a same-named enum in another module.
            if let Some((_, inner)) = &item_mod.content {
                module.push(item_mod.ident.to_string());
                collect_enum_scope_items(inner, module, index);
                module.pop();
            }
            continue;
        }
        let syn::Item::Enum(item_enum) = item else {
            continue;
        };
        // Claim the NAME first and unconditionally: a fielded or
        // explicitly-discriminated enum is still a declaration that occupies
        // this name at this module path.
        index
            .all_enum_names
            .insert((module.clone(), item_enum.ident.to_string()));
        collect_castable_enum(item_enum, module, &mut index.declarations);
    }
}

fn collect_castable_enum(item_enum: &syn::ItemEnum, module: &[String], enums: &mut CastableEnums) {
    if item_enum.variants.is_empty() {
        return;
    }
    if !item_enum
        .variants
        .iter()
        .all(|v| matches!(v.fields, syn::Fields::Unit))
    {
        return;
    }
    let mut variants: Vec<(Ident, i128)> = Vec::with_capacity(item_enum.variants.len());
    let mut next: i128 = 0;
    for variant in &item_enum.variants {
        let value = match &variant.discriminant {
            Some((_, expr)) => match eval_discriminant_expr(expr) {
                Some(v) => v,
                None => return,
            },
            None => next,
        };
        variants.push((variant.ident.clone(), value));
        next = match value.checked_add(1) {
            Some(n) => n,
            None => return,
        };
    }
    // Reject duplicate discriminants (rustc E0081) defensively — a duplicate
    // would let two variants share a value, so a `match`-based rewrite could
    // not distinguish them.
    let mut seen = BTreeSet::new();
    if variants.iter().any(|(_, v)| !seen.insert(*v)) {
        return;
    }
    enums.insert((module.to_vec(), item_enum.ident.to_string()), variants);
}

/// What a written enum path denotes at one use site.
enum EnumResolution<'a> {
    /// Settled: the path denotes exactly this castable enum.
    Castable(&'a [(Ident, i128)]),
    /// Deliberately UNDECIDED. The caller must leave the cast untouched, which
    /// leaves it fail-closed at encoding. This variant exists so that "this pass
    /// could not work out what the path means" is a value the caller has to
    /// handle, rather than a silent fall-through to some other declaration.
    Undecided,
}

/// The scopes an enum path is resolved through, and the ONLY way this pass may
/// turn a written path into a set of discriminants.
///
/// THE DEFECT THIS TYPE EXISTS TO PREVENT. The registry used to be keyed by the
/// BARE enum name and populated from `file.items` alone, while the use site's
/// path was read as "second-to-last segment = enum name" with every qualifier
/// discarded. Two declarations of one bare name were therefore indistinguishable
/// and the file-top-level one always won, so with
/// `mod m { enum E { A, B, C } }` beside a top-level `enum E { C, A, B }`:
///   · `m::E::C as u8` was rewritten to `0` — its real discriminant is 2, so
///     `assert!((m::E::C as u8) == 0)` VERIFIED and the TRUE `== 2` was REFUTED;
///   · the same held for a bare `E::C` written INSIDE `mod m`, where `E` denotes
///     `m::E` and the pass reached for the top-level `E` instead.
/// Both were cardinal false verifies on legal single-file Rust. Note the shape:
/// the resolver did not silently answer "nothing here", it silently answered
/// with a CONFIDENT WRONG VALUE, which is the same defect one step worse.
///
/// The struct is built by exhaustive literal and consumed by the exhaustive
/// destructure at the top of [`EnumPathScopes::resolve`], so adding a scope
/// cannot compile until someone writes down how it participates in resolution.
#[derive(Clone, Copy)]
struct EnumPathScopes<'a> {
    /// Inline-module path of the function being desugared. `None` means the
    /// function's own module could not be identified (an ambiguous or absent
    /// enclosing module), under which NOTHING resolves — a use site whose scope
    /// is unknown cannot have its paths resolved against any scope.
    use_site_module: Option<&'a [String]>,
    index: &'a EnumScopeIndex,
}

impl<'a> EnumPathScopes<'a> {
    /// Resolve `PREFIX::enum_name` written at this use site.
    ///
    /// Every step that cannot be settled from the file alone answers
    /// [`EnumResolution::Undecided`]; nothing here ever falls back to a
    /// same-named declaration in another scope.
    fn resolve(&self, prefix: &[String], enum_name: &str) -> EnumResolution<'a> {
        // Exhaustive destructure — see the type doc.
        let EnumPathScopes {
            use_site_module,
            index,
        } = self;
        let EnumScopeIndex {
            declarations,
            all_enum_names,
            use_bound_names,
            glob_modules,
        } = index;

        let Some(module) = use_site_module else {
            return EnumResolution::Undecided;
        };
        let module: &[String] = module;

        // The head of a relative path — or the bare enum name itself — may be a
        // `use` binding, which can denote an item this file does not contain.
        let head = prefix.first().map_or(enum_name, String::as_str);
        if use_bound_names.contains(&(module.to_vec(), head.to_string())) {
            return EnumResolution::Undecided;
        }

        // Normalise the written prefix to an absolute inline-module path. Items
        // in an ANCESTOR module are not in scope in a child, so a relative path
        // is rooted at the use site's own module and nowhere else.
        let absolute: Vec<String> = match prefix.split_first() {
            None => module.to_vec(),
            Some((head, rest)) if head == "crate" => rest.to_vec(),
            Some((head, rest)) if head == "self" => module.iter().chain(rest).cloned().collect(),
            // `super::` is resolvable in principle; it is declined rather than
            // guessed, and is a capability gap, not a soundness one.
            Some((head, _)) if head == "super" => return EnumResolution::Undecided,
            Some(_) => module.iter().chain(prefix).cloned().collect(),
        };

        // A glob in the use site's module can bind the head of the path to a
        // module this file never names. An EXPLICIT declaration of the enum at
        // the resolved path beats a glob, so the glob only matters when the head
        // is not the enum's own already-checked name.
        if !prefix.is_empty() && glob_modules.contains(module) {
            return EnumResolution::Undecided;
        }

        let key = (absolute, enum_name.to_string());
        if !all_enum_names.contains(&key) {
            // Declared nowhere the use site can see it: an out-of-line `mod m;`,
            // another crate, a glob, a type alias. Never fall through.
            return EnumResolution::Undecided;
        }
        match declarations.get(&key) {
            Some(variants) => EnumResolution::Castable(variants),
            // Declared HERE but not castable (fielded, non-literal explicit
            // discriminant, duplicate values). It occupies the name, so the cast
            // stays fail-closed instead of resolving to a same-named enum
            // somewhere else.
            None => EnumResolution::Undecided,
        }
    }
}

/// Split a `syn::Path` into its module prefix and trailing segments, rejecting
/// any path carrying generic arguments (`E::<T>::V`) or a qualified self type.
fn plain_path_segments(path: &syn::Path, qself: Option<&syn::QSelf>) -> Option<Vec<String>> {
    if qself.is_some() {
        return None;
    }
    path.segments
        .iter()
        .map(|seg| matches!(seg.arguments, syn::PathArguments::None).then(|| seg.ident.to_string()))
        .collect()
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
fn enum_typed_params<'a>(
    func: &ItemFn,
    scopes: EnumPathScopes<'a>,
    rebound: &BTreeSet<String>,
) -> BTreeMap<String, ResolvedEnumParam<'a>> {
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
        let Some(segments) = plain_path_segments(&type_path.path, type_path.qself.as_ref()) else {
            continue;
        };
        let Some((enum_name, prefix)) = segments.split_last() else {
            continue;
        };
        // The written type path is resolved through the use site's scope, not
        // looked up by bare name: `c: m::E` and a `c: E` written inside `mod m`
        // must both reach `m::E`, and neither may reach a top-level `E`.
        if let EnumResolution::Castable(variants) = scopes.resolve(prefix, enum_name) {
            map.insert(
                name,
                ResolvedEnumParam {
                    written_path: type_path.path.clone(),
                    variants,
                },
            );
        }
    }
    map
}

/// A parameter whose declared type RESOLVED to a castable enum, together with
/// the type path exactly as the use site spelled it — the generated `match` arms
/// must spell the variant the same way for the rewritten source to still name
/// the same enum.
struct ResolvedEnumParam<'a> {
    written_path: syn::Path,
    variants: &'a [(Ident, i128)],
}

/// If `expr` is a path `PREFIX::Enum::Variant` that RESOLVES to a castable enum
/// at this use site, return that variant's Rust discriminant value.
fn literal_variant_value(expr: &Expr, scopes: EnumPathScopes<'_>) -> Option<i128> {
    let Expr::Path(expr_path) = expr else {
        return None;
    };
    let segments = plain_path_segments(&expr_path.path, expr_path.qself.as_ref())?;
    if segments.len() < 2 {
        return None;
    }
    let (variant, head) = segments.split_last()?;
    let (enum_name, prefix) = head.split_last()?;
    let EnumResolution::Castable(variants) = scopes.resolve(prefix, enum_name) else {
        return None;
    };
    variants
        .iter()
        .find(|(ident, _)| ident == variant)
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
fn discriminant_match(scrutinee: Ident, enum_path: &syn::Path, variants: &[(Ident, i128)]) -> Expr {
    let arms = variants
        .iter()
        .map(|(variant, value)| {
            // Spell the arm with the path the USE SITE wrote (`m::E::V`, or a
            // bare `E::V` inside `mod m`). Re-spelling it as a bare name would
            // re-introduce exactly the ambiguity this pass now resolves.
            let pat: Pat = syn::parse_quote!(#enum_path::#variant);
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
    scopes: EnumPathScopes<'a>,
    params: &'a BTreeMap<String, ResolvedEnumParam<'a>>,
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
            scopes: self.scopes,
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
        if let Some(value) = literal_variant_value(&cast.expr, self.scopes) {
            *cast.expr = int_literal(value);
            self.rewrote = true;
            return;
        }
        // Enum-typed parameter: `c as T` → `(match c { .. }) as T`.
        if let Expr::Path(expr_path) = &*cast.expr {
            if expr_path.qself.is_none() {
                if let Some(ident) = expr_path.path.get_ident() {
                    if let Some(param) = self.params.get(&ident.to_string()) {
                        *cast.expr =
                            discriminant_match(ident.clone(), &param.written_path, param.variants);
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
pub(crate) fn desugar_enum_int_cast(
    func: &ItemFn,
    file: Option<&File>,
    enclosing_module: Option<&[String]>,
) -> Option<ItemFn> {
    let index = collect_enum_scope_index(file?);
    if index.declarations.is_empty() {
        return None;
    }
    // `enclosing_module` is `None` when the function's own inline module could
    // not be identified UNIQUELY. Resolution needs the use site's scope, so that
    // is carried into the scopes and declines every path — not dropped to an
    // implicit file-top-level reading, which is the very substitution that made
    // a nested `mod m`'s `E` resolve to the top-level `E`.
    let scopes = EnumPathScopes {
        use_site_module: enclosing_module,
        index: &index,
    };
    let mut rebound = BTreeSet::new();
    PatternBindingCollector {
        names: &mut rebound,
    }
    .visit_block(&func.block);
    let params = enum_typed_params(func, scopes, &rebound);

    let mut rewritten = func.clone();
    let mut rewriter = EnumCastRewriter {
        scopes,
        params: &params,
        rewrote: false,
    };
    rewriter.visit_item_fn_mut(&mut rewritten);
    let body_changed = rewriter.rewrote;
    // Contract attributes (`#[trust_vc::ensures(..)]`) hold their predicate as an
    // opaque token stream the body visit above does not reach — rewrite them
    // separately with a fresh (non-mutating) rewriter view.
    let attr_rewriter = EnumCastRewriter {
        scopes,
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
