//! Source-level desugaring of the `?` (Try) operator into a tail `match`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `let PAT = g()?; REST` is behaviorally `match g() { Some(PAT) => { REST },
//! None => None }` (and the `Ok`/`Err` analogue for a `Result`-returning fn) —
//! a TAIL match with no early return, which the extractor already handles
//! soundly (it checks the postcondition on BOTH arms). Rewriting `?` to that
//! form sidesteps the multi-path-return-in-let extraction that otherwise fails
//! closed, WITHOUT introducing any new control-flow semantics.
//!
//! Scope (everything else stays fail-closed by returning `None`): every `?` in
//! the body must be the direct initializer of a top-level `let IDENT = …` (or
//! wildcard) statement with no attributes or explicit type annotation, or be
//! in a reorder-safe final tail expression. File/module context must prove that
//! the function and every operand use the canonical built-in `Option`/`Result`;
//! a `Result` rewrite additionally requires the exact same error type so its
//! `FromResidual` conversion is the identity. Typed, attributed, refutable,
//! shadowed, and type-ambiguous shapes remain fail-closed: dropping source
//! semantics or trusting a trailing type identifier would be unsound without
//! rustc type checking. Generated tail binders are fresh against every source
//! identifier and generated constructors are absolute `::core` paths. The
//! rewrite can therefore only turn a previously-fail-closed function into a
//! soundly-verified (or soundly-refuted) one — never a false `Verified` (the
//! tail `match` is validated to check every arm; see try_operator.rs).

use proc_macro2::Span;
use quote::ToTokens;
use std::collections::BTreeSet;
use syn::visit::Visit;
use syn::visit_mut::VisitMut;
use syn::{
    Block, Expr, File, FnArg, GenericArgument, Ident, Item, ItemFn, Pat, PathArguments, ReturnType,
    Stmt, Type, UseTree,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TryReturnKind {
    Option,
    Result,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ProvenTryType {
    kind: TryReturnKind,
    /// `Result`'s error type, rendered from the authoritative source signature.
    /// Exact equality is deliberately required: Rust's `?` applies
    /// `FromResidual`/`From` on the failure path, and the desugaring below models
    /// only the identity `From<E> for E` conversion.
    error_type: Option<String>,
}

impl ProvenTryType {
    fn is_compatible_operand(&self, operand: &Self) -> bool {
        self.kind == operand.kind
            && (self.kind == TryReturnKind::Option || self.error_type == operand.error_type)
    }
}

struct FreshTryNames {
    used: BTreeSet<String>,
    next: usize,
}

impl FreshTryNames {
    fn for_function(func: &ItemFn) -> Self {
        #[derive(Default)]
        struct IdentCollector(BTreeSet<String>);

        impl<'ast> Visit<'ast> for IdentCollector {
            fn visit_ident(&mut self, ident: &'ast Ident) {
                self.0.insert(ident.to_string());
            }
        }

        let mut collector = IdentCollector::default();
        collector.visit_item_fn(func);
        Self {
            used: collector.0,
            next: 0,
        }
    }

    fn take(&mut self) -> Ident {
        loop {
            let name = format!("__trust_vc_try_{}", self.next);
            self.next += 1;
            if self.used.insert(name.clone()) {
                return Ident::new(&name, Span::call_site());
            }
        }
    }
}

/// Rewrites the `?` operators in `func`'s body into tail `match`es, returning the
/// rewritten function — or `None` when the body has no `?` or uses `?` in a shape
/// outside the supported scope (leaving the original to fail closed).
pub(crate) fn desugar_try_operator(
    func: &ItemFn,
    file: Option<&File>,
    enclosing_module: Option<&[String]>,
) -> Option<ItemFn> {
    let total = count_all_try(&func.block);
    if total == 0 {
        return None;
    }
    // `?` is a type-directed operation. The no-file extraction surface has no
    // authoritative namespace or callee-signature context, so it must retain
    // the existing fail-closed Expr::Try behavior.
    let file = file?;
    let enclosing_module = enclosing_module?;
    // Every generated constructor is rooted at `::core`; do not emit that path
    // when the source can bind a different crate/module under the same name.
    if source_may_shadow_namespace_name(file, func, "core") {
        return None;
    }
    let return_ty = try_return_type(&func.sig.output, func, file)?;
    let kind = return_ty.kind;
    if !all_try_operands_are_compatible(func, file, enclosing_module, &return_ty) {
        return None;
    }
    // Supported iff EVERY `?` in the body is either a top-level `let PAT = E?;`
    // statement OR appears (unconditionally) in the block's final tail expression.
    // Any other position (a `?` in a middle expression-statement, or nested inside
    // an `if`/`match`/loop/closure/short-circuit where it would be CONDITIONAL)
    // leaves the whole function to fail closed.
    let tail_count = tail_expr_try_count(&func.block);
    if total != top_level_let_try_count(&func.block) + tail_count {
        return None;
    }
    if !top_level_let_tries_are_plain(&func.block) {
        return None;
    }
    if tail_count > 0
        && (tail_expr_has_conditional(&func.block)
            || tail_expr_has_attrs(&func.block)
            || !tail_expr_rewrite_preserves_order(&func.block, func, file, enclosing_module))
    {
        return None;
    }
    let mut owned = func.clone();
    let mut fresh_names = FreshTryNames::for_function(func);
    owned.block = Box::new(desugar_stmts(
        &func.block.stmts,
        kind,
        func.block.brace_token,
        &mut fresh_names,
    ));
    Some(owned)
}

fn try_return_type(output: &ReturnType, func: &ItemFn, file: &File) -> Option<ProvenTryType> {
    let ReturnType::Type(_, ty) = output else {
        return None;
    };
    canonical_try_type(ty, func, file)
}

/// Recognize only a provenance-established standard-library `Option`/`Result`.
/// A trailing identifier is not enough: `foo::Option`, a local `enum Option`,
/// or an imported alias would otherwise grant custom source types the built-in
/// Try semantics without rustc type checking.
fn canonical_try_type(ty: &Type, func: &ItemFn, file: &File) -> Option<ProvenTryType> {
    let Type::Path(type_path) = ty else {
        return None;
    };
    if type_path.qself.is_some() {
        return None;
    }
    let path = &type_path.path;
    let names: Vec<_> = path
        .segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect();
    let (kind, expected_args, unqualified) = match names.as_slice() {
        [name] if name == "Option" => (TryReturnKind::Option, 1, true),
        [name] if name == "Result" => (TryReturnKind::Result, 2, true),
        [root, module, name]
            if (root == "core" || root == "std") && module == "option" && name == "Option" =>
        {
            if source_may_shadow_namespace_name(file, func, root) {
                return None;
            }
            (TryReturnKind::Option, 1, false)
        }
        [root, module, name]
            if (root == "core" || root == "std") && module == "result" && name == "Result" =>
        {
            if source_may_shadow_namespace_name(file, func, root) {
                return None;
            }
            (TryReturnKind::Result, 2, false)
        }
        _ => return None,
    };
    if unqualified {
        let name = match kind {
            TryReturnKind::Option => "Option",
            TryReturnKind::Result => "Result",
        };
        if source_may_shadow_namespace_name(file, func, name) {
            return None;
        }
    }
    if path
        .segments
        .iter()
        .take(path.segments.len().saturating_sub(1))
        .any(|segment| !matches!(segment.arguments, PathArguments::None))
    {
        return None;
    }
    let PathArguments::AngleBracketed(args) = &path.segments.last()?.arguments else {
        return None;
    };
    if args.args.len() != expected_args
        || args
            .args
            .iter()
            .any(|arg| !matches!(arg, GenericArgument::Type(_)))
    {
        return None;
    }
    let error_type = if kind == TryReturnKind::Result {
        match args.args.iter().nth(1)? {
            GenericArgument::Type(error) => Some(error.to_token_stream().to_string()),
            _ => return None,
        }
    } else {
        None
    };
    Some(ProvenTryType { kind, error_type })
}

/// Conservative namespace proof for unqualified built-ins and the generated
/// absolute `::core` constructor paths. Declarations/imports are scanned across
/// the whole parsed file; rejecting an unrelated collision is preferable to
/// attributing semantics to a shadowed name. The common prelude-only spelling
/// remains accepted.
pub(crate) fn source_may_shadow_namespace_name(file: &File, func: &ItemFn, target: &str) -> bool {
    if target == "Option" || target == "Result" {
        struct PreludeAttrFinder {
            found: bool,
        }
        impl<'ast> Visit<'ast> for PreludeAttrFinder {
            fn visit_attribute(&mut self, attr: &'ast syn::Attribute) {
                // `cfg_attr` is unevaluated here and may inject
                // `no_implicit_prelude`; a module-level inner attribute is just
                // as authoritative as the crate/file-level spelling.
                self.found |=
                    attr.path().is_ident("no_implicit_prelude") || attr.path().is_ident("cfg_attr");
            }
        }
        let mut attrs = PreludeAttrFinder { found: false };
        attrs.visit_file(file);
        if attrs.found {
            return true;
        }
    }

    struct ShadowFinder<'a> {
        target: &'a str,
        found: bool,
    }
    impl ShadowFinder<'_> {
        fn mark(&mut self, ident: &Ident) {
            self.found |= ident == self.target;
        }
    }
    impl<'ast> Visit<'ast> for ShadowFinder<'_> {
        fn visit_item(&mut self, item: &'ast Item) {
            match item {
                Item::Enum(item) => self.mark(&item.ident),
                Item::ExternCrate(item) => {
                    if let Some((_, rename)) = &item.rename {
                        self.mark(rename);
                    } else {
                        self.mark(&item.ident);
                    }
                }
                Item::Mod(item) => self.mark(&item.ident),
                Item::Struct(item) => self.mark(&item.ident),
                Item::Trait(item) => self.mark(&item.ident),
                Item::TraitAlias(item) => self.mark(&item.ident),
                Item::Type(item) => self.mark(&item.ident),
                Item::Union(item) => self.mark(&item.ident),
                Item::Use(item) => {
                    self.found |= use_tree_may_bind(&item.tree, self.target);
                }
                _ => {}
            }
            syn::visit::visit_item(self, item);
        }

        fn visit_type_param(&mut self, param: &'ast syn::TypeParam) {
            self.mark(&param.ident);
            syn::visit::visit_type_param(self, param);
        }

        fn visit_foreign_item_type(&mut self, item: &'ast syn::ForeignItemType) {
            self.mark(&item.ident);
            syn::visit::visit_foreign_item_type(self, item);
        }
    }

    let mut finder = ShadowFinder {
        target,
        found: false,
    };
    finder.visit_file(file);
    // The transformed function can contain inferred/substituted signature
    // material not present in the original file node. Scan its generics too.
    finder.visit_generics(&func.sig.generics);
    finder.found
}

fn use_tree_may_bind(tree: &UseTree, target: &str) -> bool {
    use_tree_may_bind_with_parent(tree, target, None)
}

fn use_tree_may_bind_with_parent(tree: &UseTree, target: &str, parent: Option<&Ident>) -> bool {
    match tree {
        UseTree::Path(path) => use_tree_may_bind_with_parent(&path.tree, target, Some(&path.ident)),
        // `use foo::{self}` binds `foo`, not the literal identifier `self`.
        UseTree::Name(name) if name.ident == "self" => parent.is_some_and(|name| name == target),
        UseTree::Name(name) => name.ident == target,
        UseTree::Rename(rename) => rename.rename == target,
        UseTree::Glob(_) => true,
        UseTree::Group(group) => group
            .items
            .iter()
            .any(|tree| use_tree_may_bind_with_parent(tree, target, parent)),
    }
}

fn all_try_operands_are_compatible(
    func: &ItemFn,
    file: &File,
    enclosing_module: &[String],
    return_ty: &ProvenTryType,
) -> bool {
    struct Checker<'a> {
        func: &'a ItemFn,
        file: &'a File,
        enclosing_module: &'a [String],
        return_ty: &'a ProvenTryType,
        valid: bool,
    }
    impl<'ast> Visit<'ast> for Checker<'_> {
        fn visit_expr_try(&mut self, node: &'ast syn::ExprTry) {
            let compatible =
                proven_operand_type(&node.expr, self.func, self.file, self.enclosing_module)
                    .is_some_and(|operand| self.return_ty.is_compatible_operand(&operand));
            self.valid &= compatible;
            syn::visit::visit_expr_try(self, node);
        }

        fn visit_expr_closure(&mut self, _node: &'ast syn::ExprClosure) {}
        fn visit_item(&mut self, _node: &'ast Item) {}
    }

    let mut checker = Checker {
        func,
        file,
        enclosing_module,
        return_ty,
        valid: true,
    };
    checker.visit_block(&func.block);
    checker.valid
}

fn proven_operand_type(
    expr: &Expr,
    func: &ItemFn,
    file: &File,
    enclosing_module: &[String],
) -> Option<ProvenTryType> {
    match expr {
        Expr::Paren(paren) if paren.attrs.is_empty() => {
            proven_operand_type(&paren.expr, func, file, enclosing_module)
        }
        Expr::Group(group) if group.attrs.is_empty() => {
            proven_operand_type(&group.expr, func, file, enclosing_module)
        }
        Expr::Path(path)
            if path.attrs.is_empty()
                && path.qself.is_none()
                && path.path.leading_colon.is_none()
                && path.path.segments.len() == 1
                && matches!(path.path.segments[0].arguments, PathArguments::None) =>
        {
            let name = &path.path.segments[0].ident;
            if block_may_shadow_value(&func.block, name) {
                return None;
            }
            func.sig.inputs.iter().find_map(|arg| match arg {
                FnArg::Typed(arg) => match &*arg.pat {
                    Pat::Ident(pat)
                        if arg.attrs.is_empty()
                            && pat.attrs.is_empty()
                            && pat.by_ref.is_none()
                            && pat.subpat.is_none()
                            && pat.ident == *name =>
                    {
                        canonical_try_type(&arg.ty, func, file)
                    }
                    _ => None,
                },
                FnArg::Receiver(_) => None,
            })
        }
        Expr::Call(call) if call.attrs.is_empty() => {
            let Expr::Path(callee) = &*call.func else {
                return None;
            };
            if !callee.attrs.is_empty()
                || callee.qself.is_some()
                || callee.path.leading_colon.is_some()
                || callee.path.segments.len() != 1
                || !matches!(callee.path.segments[0].arguments, PathArguments::None)
            {
                return None;
            }
            let name = &callee.path.segments[0].ident;
            if function_locally_shadows_value(func, name)
                || file_has_ambiguous_value_binding(file, name)
            {
                return None;
            }
            let mut matches = Vec::new();
            collect_named_functions(file, enclosing_module, name, &mut matches);
            if matches.len() != 1 {
                return None;
            }
            let helper = matches[0];
            if helper.sig.asyncness.is_some()
                || helper.sig.unsafety.is_some()
                || helper.sig.abi.is_some()
                || helper.sig.variadic.is_some()
                || !helper.attrs.is_empty()
                || !helper.sig.generics.params.is_empty()
                || helper.sig.generics.where_clause.is_some()
                || helper.sig.inputs.len() != call.args.len()
                || !helper_call_arguments_have_exact_types(call, helper, func)
            {
                return None;
            }
            try_return_type(&helper.sig.output, helper, file)
        }
        _ => None,
    }
}

fn items_in_inline_module<'a>(file: &'a File, module: &[String]) -> Option<&'a [Item]> {
    let mut items = file.items.as_slice();
    for component in module {
        let mut candidates = items.iter().filter_map(|item| match item {
            Item::Mod(item) if item.ident == component => {
                item.content.as_ref().map(|(_, items)| items)
            }
            _ => None,
        });
        let next = candidates.next()?;
        if candidates.next().is_some() {
            return None;
        }
        items = next;
    }
    Some(items)
}

fn collect_named_functions<'a>(
    file: &'a File,
    enclosing_module: &[String],
    name: &Ident,
    matches: &mut Vec<&'a ItemFn>,
) {
    let Some(items) = items_in_inline_module(file, enclosing_module) else {
        return;
    };
    matches.extend(items.iter().filter_map(|item| match item {
        Item::Fn(func) if func.sig.ident == *name => Some(func),
        _ => None,
    }));
}

fn helper_call_arguments_have_exact_types(
    call: &syn::ExprCall,
    helper: &ItemFn,
    caller: &ItemFn,
) -> bool {
    call.args
        .iter()
        .zip(&helper.sig.inputs)
        .all(|(actual, formal)| {
            let FnArg::Typed(formal) = formal else {
                return false;
            };
            if !formal.attrs.is_empty() {
                return false;
            }
            let Some(actual_ty) = simple_unshadowed_parameter_type(actual, caller) else {
                return false;
            };
            actual_ty.to_token_stream().to_string() == formal.ty.to_token_stream().to_string()
        })
}

fn simple_unshadowed_parameter_type<'a>(expr: &Expr, func: &'a ItemFn) -> Option<&'a Type> {
    let Expr::Path(path) = expr else {
        return None;
    };
    if !path.attrs.is_empty()
        || path.qself.is_some()
        || path.path.leading_colon.is_some()
        || path.path.segments.len() != 1
        || !matches!(path.path.segments[0].arguments, PathArguments::None)
    {
        return None;
    }
    let name = &path.path.segments[0].ident;
    if block_may_shadow_value(&func.block, name) {
        return None;
    }
    func.sig.inputs.iter().find_map(|arg| match arg {
        FnArg::Typed(arg) => match &*arg.pat {
            Pat::Ident(pat)
                if arg.attrs.is_empty()
                    && pat.attrs.is_empty()
                    && pat.by_ref.is_none()
                    && pat.subpat.is_none()
                    && pat.ident == *name =>
            {
                Some(arg.ty.as_ref())
            }
            _ => None,
        },
        FnArg::Receiver(_) => None,
    })
}

fn block_may_shadow_value(block: &Block, name: &Ident) -> bool {
    struct Finder<'a> {
        name: &'a Ident,
        found: bool,
    }
    impl<'ast> Visit<'ast> for Finder<'_> {
        fn visit_pat_ident(&mut self, pat: &'ast syn::PatIdent) {
            self.found |= pat.ident == *self.name;
            syn::visit::visit_pat_ident(self, pat);
        }
        fn visit_item_fn(&mut self, item: &'ast ItemFn) {
            self.found |= item.sig.ident == *self.name;
            syn::visit::visit_item_fn(self, item);
        }
        fn visit_item_const(&mut self, item: &'ast syn::ItemConst) {
            self.found |= item.ident == *self.name;
            syn::visit::visit_item_const(self, item);
        }
        fn visit_item_static(&mut self, item: &'ast syn::ItemStatic) {
            self.found |= item.ident == *self.name;
            syn::visit::visit_item_static(self, item);
        }
        fn visit_item_use(&mut self, item: &'ast syn::ItemUse) {
            self.found |= use_tree_may_bind(&item.tree, &self.name.to_string());
            syn::visit::visit_item_use(self, item);
        }
    }
    let mut finder = Finder { name, found: false };
    finder.visit_block(block);
    finder.found
}

fn function_locally_shadows_value(func: &ItemFn, name: &Ident) -> bool {
    struct Finder<'a> {
        name: &'a Ident,
        found: bool,
    }
    impl<'ast> Visit<'ast> for Finder<'_> {
        fn visit_pat_ident(&mut self, pat: &'ast syn::PatIdent) {
            self.found |= pat.ident == *self.name;
            syn::visit::visit_pat_ident(self, pat);
        }

        fn visit_item_fn(&mut self, item: &'ast ItemFn) {
            self.found |= item.sig.ident == *self.name;
            syn::visit::visit_item_fn(self, item);
        }

        fn visit_item_const(&mut self, item: &'ast syn::ItemConst) {
            self.found |= item.ident == *self.name;
            syn::visit::visit_item_const(self, item);
        }

        fn visit_item_static(&mut self, item: &'ast syn::ItemStatic) {
            self.found |= item.ident == *self.name;
            syn::visit::visit_item_static(self, item);
        }

        fn visit_item_use(&mut self, item: &'ast syn::ItemUse) {
            self.found |= use_tree_may_bind(&item.tree, &self.name.to_string());
            syn::visit::visit_item_use(self, item);
        }
    }
    let mut finder = Finder { name, found: false };
    finder.visit_signature(&func.sig);
    finder.visit_block(&func.block);
    finder.found
}

fn file_has_ambiguous_value_binding(file: &File, name: &Ident) -> bool {
    struct Finder<'a> {
        name: &'a Ident,
        found: bool,
    }
    impl<'ast> Visit<'ast> for Finder<'_> {
        fn visit_item(&mut self, item: &'ast Item) {
            match item {
                Item::Const(item) => self.found |= item.ident == *self.name,
                Item::Enum(item) => self.found |= item.ident == *self.name,
                Item::Mod(item) => self.found |= item.ident == *self.name,
                Item::Static(item) => self.found |= item.ident == *self.name,
                Item::Struct(item) => self.found |= item.ident == *self.name,
                Item::Union(item) => self.found |= item.ident == *self.name,
                Item::Use(item) => {
                    self.found |= use_tree_may_bind(&item.tree, &self.name.to_string());
                }
                _ => {}
            }
            syn::visit::visit_item(self, item);
        }
    }
    let mut finder = Finder { name, found: false };
    finder.visit_file(file);
    finder.found
}

/// Counts every `Expr::Try` reachable in `block`, NOT descending into nested
/// closures or items (their `?` binds to that inner control-flow scope).
fn count_all_try(block: &Block) -> usize {
    struct Counter {
        count: usize,
    }
    impl<'ast> Visit<'ast> for Counter {
        fn visit_expr_try(&mut self, node: &'ast syn::ExprTry) {
            self.count += 1;
            syn::visit::visit_expr_try(self, node);
        }
        fn visit_expr_closure(&mut self, _node: &'ast syn::ExprClosure) {}
        fn visit_item(&mut self, _node: &'ast syn::Item) {}
    }
    let mut counter = Counter { count: 0 };
    counter.visit_block(block);
    counter.count
}

/// A top-level statement of `block` that is `let PAT = <Expr::Try>;`.
fn stmt_let_try(stmt: &Stmt) -> Option<(&Pat, &Expr, bool)> {
    let Stmt::Local(local) = stmt else {
        return None;
    };
    // Local attributes can remove or transform the statement before execution.
    // The source-level verifier does not evaluate cfg/procedural attributes, so
    // consuming the statement here would silently grant it unconditional
    // control-flow and contract authority.
    if !local.attrs.is_empty() {
        return None;
    }
    let init = local.init.as_ref()?;
    let Expr::Try(try_expr) = &*init.expr else {
        return None;
    };
    if !try_expr.attrs.is_empty() {
        return None;
    }
    // A type ascription is illegal inside a constructor pattern. Silently
    // stripping it would be unsound: e.g. `let v: bool = Option<u64>?` would be
    // lowered as a `u64` binding and could verify. Keep every typed binding on
    // the existing Expr::Try fail-closed path until the annotation can be
    // preserved and checked exactly.
    let pat = match &local.pat {
        Pat::Type(_) => return None,
        other => other,
    };
    // A plain Rust `let` must be irrefutable. Without payload type-checking we
    // can establish that property only for a simple identifier or wildcard.
    // Rewriting `let Some(v) = o?` into a partial match would otherwise turn an
    // invalid source function into a Verified one.
    match pat {
        Pat::Ident(ident)
            if ident.attrs.is_empty() && ident.by_ref.is_none() && ident.subpat.is_none() => {}
        Pat::Wild(wild) if wild.attrs.is_empty() => {}
        _ => return None,
    }
    Some((pat, &try_expr.expr, init.diverge.is_some()))
}

fn top_level_let_try_count(block: &Block) -> usize {
    block
        .stmts
        .iter()
        .filter(|stmt| stmt_let_try(stmt).is_some())
        .count()
}

fn top_level_let_tries_are_plain(block: &Block) -> bool {
    block
        .stmts
        .iter()
        .all(|stmt| stmt_let_try(stmt).is_none_or(|(_, _, has_diverge)| !has_diverge))
}

/// Rewrites a statement sequence: the first `let PAT = E?;` becomes a tail
/// `match E { success(PAT) => { <rest> }, failure => <failure value> }`, with the
/// remaining statements recursively desugared inside the success arm.
fn desugar_stmts(
    stmts: &[Stmt],
    kind: TryReturnKind,
    brace: syn::token::Brace,
    fresh_names: &mut FreshTryNames,
) -> Block {
    for (index, stmt) in stmts.iter().enumerate() {
        if let Some((pat, inner, _)) = stmt_let_try(stmt) {
            let rest = desugar_stmts(&stmts[index + 1..], kind, brace, fresh_names);
            let match_expr = build_try_match(inner, pat, &rest, kind);
            let mut new_stmts: Vec<Stmt> = stmts[..index].to_vec();
            new_stmts.push(Stmt::Expr(match_expr, None));
            return Block {
                brace_token: brace,
                stmts: new_stmts,
            };
        }
    }
    // No top-level `let`-`?` remains; desugar any `?` in the tail expression
    // (guaranteed unconditional by the scope check).
    let mut new_stmts = stmts.to_vec();
    if let Some(Stmt::Expr(expr, None)) = new_stmts.last_mut() {
        if expr_try_count(expr) > 0 {
            *expr = desugar_expr_try(expr.clone(), kind, fresh_names);
        }
    }
    Block {
        brace_token: brace,
        stmts: new_stmts,
    }
}

/// Desugars an expression-level `?` (`Some(g()?)`, `f(g()?, h()?)`, …): replaces
/// the FIRST `?` with a fresh binder, wraps the whole expression in a `match` on
/// that `?`'s operand, and recurses for the remaining `?` inside the success arm.
/// The left-to-right order matches Rust's short-circuit: the first `?` is the
/// OUTERMOST match, so a failure there does not evaluate later ones.
fn desugar_expr_try(expr: Expr, kind: TryReturnKind, fresh_names: &mut FreshTryNames) -> Expr {
    struct FirstTry {
        inner: Option<Expr>,
        fresh: Ident,
    }
    impl VisitMut for FirstTry {
        fn visit_expr_mut(&mut self, node: &mut Expr) {
            if self.inner.is_some() {
                return;
            }
            if let Expr::Try(try_expr) = node {
                self.inner = Some((*try_expr.expr).clone());
                *node = Expr::Path(syn::ExprPath {
                    attrs: Vec::new(),
                    qself: None,
                    path: self.fresh.clone().into(),
                });
                return;
            }
            syn::visit_mut::visit_expr_mut(self, node);
        }
        // A `?` inside a nested closure belongs to that closure's scope.
        fn visit_expr_closure_mut(&mut self, _node: &mut syn::ExprClosure) {}
    }

    let fresh = fresh_names.take();
    let mut finder = FirstTry {
        inner: None,
        fresh: fresh.clone(),
    };
    let mut expr = expr;
    finder.visit_expr_mut(&mut expr);
    match finder.inner {
        None => expr,
        Some(inner) => {
            let rest = desugar_expr_try(expr, kind, fresh_names);
            build_try_match_expr(&inner, &fresh, &rest, kind)
        }
    }
}

fn build_try_match_expr(inner: &Expr, fresh: &Ident, rest: &Expr, kind: TryReturnKind) -> Expr {
    match kind {
        TryReturnKind::Option => syn::parse_quote! {
            match #inner {
                ::core::option::Option::Some(#fresh) => #rest,
                ::core::option::Option::None => ::core::option::Option::None,
            }
        },
        TryReturnKind::Result => syn::parse_quote! {
            match #inner {
                ::core::result::Result::Ok(#fresh) => #rest,
                ::core::result::Result::Err(__trust_vc_try_err) =>
                    ::core::result::Result::Err(__trust_vc_try_err),
            }
        },
    }
}

/// The block's final tail expression (`Stmt::Expr` with no trailing `;`), if any.
fn tail_expr(block: &Block) -> Option<&Expr> {
    match block.stmts.last() {
        Some(Stmt::Expr(expr, None)) => Some(expr),
        _ => None,
    }
}

/// Counts `Expr::Try` in an expression, NOT descending into closures.
fn expr_try_count(expr: &Expr) -> usize {
    struct Counter {
        count: usize,
    }
    impl<'ast> Visit<'ast> for Counter {
        fn visit_expr_try(&mut self, node: &'ast syn::ExprTry) {
            self.count += 1;
            syn::visit::visit_expr_try(self, node);
        }
        fn visit_expr_closure(&mut self, _node: &'ast syn::ExprClosure) {}
    }
    let mut counter = Counter { count: 0 };
    counter.visit_expr(expr);
    counter.count
}

fn tail_expr_try_count(block: &Block) -> usize {
    tail_expr(block).map_or(0, expr_try_count)
}

/// Checks the evaluation-order boundary of the expression-level rewrite.
///
/// Replacing the first `?` with a binder and wrapping the WHOLE tail expression
/// in a match hoists that `?` ahead of everything syntactically before it. That
/// is exact only when every preceding computation is reorder-inert. Paths,
/// literals, tuples, and already-processed `?` payloads meet that bar; calls,
/// arithmetic, indexing, assignments, and blocks do not. In particular,
/// `Some((1 / d, o?).1)` must remain fail-closed: Rust evaluates `1 / d`
/// before `o?`, and a None value must not make a real division-by-zero panic
/// disappear.
struct TryOrderContext<'a> {
    func: &'a ItemFn,
    file: &'a File,
    enclosing_module: &'a [String],
}

fn tail_expr_rewrite_preserves_order(
    block: &Block,
    func: &ItemFn,
    file: &File,
    enclosing_module: &[String],
) -> bool {
    let context = TryOrderContext {
        func,
        file,
        enclosing_module,
    };
    tail_expr(block).is_none_or(|expr| expr_try_rewrite_preserves_order(expr, &context))
}

fn expr_try_rewrite_preserves_order(expr: &Expr, context: &TryOrderContext<'_>) -> bool {
    if expr_try_count(expr) == 0 {
        return true;
    }

    match expr {
        Expr::Try(expr_try) => expr_try.attrs.is_empty() && expr_try_count(&expr_try.expr) == 0,
        Expr::Paren(paren) => expr_try_rewrite_preserves_order(&paren.expr, context),
        Expr::Group(group) => expr_try_rewrite_preserves_order(&group.expr, context),
        Expr::Field(field) => expr_try_rewrite_preserves_order(&field.base, context),
        Expr::Reference(reference) => expr_try_rewrite_preserves_order(&reference.expr, context),
        Expr::RawAddr(raw_addr) => expr_try_rewrite_preserves_order(&raw_addr.expr, context),
        Expr::Cast(cast) => expr_try_rewrite_preserves_order(&cast.expr, context),
        Expr::Unary(unary) => expr_try_rewrite_preserves_order(&unary.expr, context),
        Expr::Array(array) => sequence_preserves_try_order(array.elems.iter(), context),
        Expr::Tuple(tuple) => sequence_preserves_try_order(tuple.elems.iter(), context),
        // A proven free function/constructor path is name resolution, not value
        // evaluation. Ordinary argument paths are still evaluated below and are
        // deliberately non-inert: passing `&mut` can create an implicit move or
        // reborrow before a later `?`.
        Expr::Call(call) => {
            call_callee_is_name_only(&call.func, context)
                && sequence_preserves_try_order(call.args.iter(), context)
        }
        Expr::MethodCall(call) => sequence_preserves_try_order(
            std::iter::once(call.receiver.as_ref()).chain(call.args.iter()),
            context,
        ),
        Expr::Binary(binary) if !matches!(binary.op, syn::BinOp::And(_) | syn::BinOp::Or(_)) => {
            sequence_preserves_try_order([binary.left.as_ref(), binary.right.as_ref()], context)
        }
        Expr::Index(index) => {
            sequence_preserves_try_order([index.expr.as_ref(), index.index.as_ref()], context)
        }
        Expr::Range(range) => sequence_preserves_try_order(
            range
                .start
                .iter()
                .map(Box::as_ref)
                .chain(range.end.iter().map(Box::as_ref)),
            context,
        ),
        Expr::Struct(expr_struct) => sequence_preserves_try_order(
            expr_struct
                .fields
                .iter()
                .map(|field| &field.expr)
                .chain(expr_struct.rest.iter().map(|rest| rest.as_ref())),
            context,
        ),
        // Blocks/control flow, assignments, async/await/yield, macros, and
        // unknown future expression forms stay on the existing fail-closed
        // Expr::Try path. Their exact sequencing cannot be recovered by the
        // whole-tail wrapper.
        _ => false,
    }
}

fn sequence_preserves_try_order<'a>(
    children: impl IntoIterator<Item = &'a Expr>,
    context: &TryOrderContext<'_>,
) -> bool {
    let mut preceding_non_inert = false;
    for child in children {
        let has_try = expr_try_count(child) > 0;
        if has_try && preceding_non_inert {
            return false;
        }
        if has_try && !expr_try_rewrite_preserves_order(child, context) {
            return false;
        }
        if !expr_is_reorder_inert_modulo_try(child) {
            preceding_non_inert = true;
        }
    }
    true
}

/// Whether evaluating an expression before a later `?` is observably inert
/// after any `?` inside it has yielded its payload. This deliberately excludes
/// calls and potentially trapping operators even when the verifier currently
/// models a particular instance as pure/safe: the desugar boundary must be
/// correct from source shape alone.
fn expr_is_reorder_inert_modulo_try(expr: &Expr) -> bool {
    match expr {
        // A value path may perform an implicit move/reborrow when consumed by
        // its parent call. Without a full Copy/borrow proof it is not inert.
        Expr::Path(_) => false,
        Expr::Lit(_) | Expr::Infer(_) => true,
        Expr::Try(expr_try) => expr_try.attrs.is_empty() && expr_try_count(&expr_try.expr) == 0,
        Expr::Paren(paren) => expr_is_reorder_inert_modulo_try(&paren.expr),
        Expr::Group(group) => expr_is_reorder_inert_modulo_try(&group.expr),
        Expr::Field(field) => expr_is_reorder_inert_modulo_try(&field.base),
        Expr::Reference(reference) => expr_is_reorder_inert_modulo_try(&reference.expr),
        Expr::RawAddr(raw_addr) => expr_is_reorder_inert_modulo_try(&raw_addr.expr),
        Expr::Cast(cast) => expr_is_reorder_inert_modulo_try(&cast.expr),
        Expr::Array(array) => array.elems.iter().all(expr_is_reorder_inert_modulo_try),
        Expr::Tuple(tuple) => tuple.elems.iter().all(expr_is_reorder_inert_modulo_try),
        Expr::Range(range) => range
            .start
            .iter()
            .map(Box::as_ref)
            .chain(range.end.iter().map(Box::as_ref))
            .all(expr_is_reorder_inert_modulo_try),
        Expr::Struct(expr_struct) => {
            expr_struct
                .fields
                .iter()
                .map(|field| &field.expr)
                .all(expr_is_reorder_inert_modulo_try)
                && expr_struct
                    .rest
                    .iter()
                    .map(|rest| rest.as_ref())
                    .all(expr_is_reorder_inert_modulo_try)
        }
        _ => false,
    }
}

fn call_callee_is_name_only(callee: &Expr, context: &TryOrderContext<'_>) -> bool {
    let Expr::Path(path) = callee else {
        return false;
    };
    if !path.attrs.is_empty()
        || path.qself.is_some()
        || path.path.leading_colon.is_some()
        || path
            .path
            .segments
            .iter()
            .any(|segment| !matches!(segment.arguments, PathArguments::None))
    {
        return false;
    }

    let names: Vec<_> = path
        .path
        .segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect();
    if let [name] = names.as_slice() {
        let ident = &path.path.segments[0].ident;
        if function_locally_shadows_value(context.func, ident)
            || file_has_ambiguous_value_binding(context.file, ident)
        {
            return false;
        }
        let mut functions = Vec::new();
        collect_named_functions(
            context.file,
            context.enclosing_module,
            ident,
            &mut functions,
        );
        if !functions.is_empty() {
            return functions.len() == 1 && functions[0].attrs.is_empty();
        }
        return matches!(name.as_str(), "Some" | "None" | "Ok" | "Err")
            && !source_may_shadow_namespace_name(context.file, context.func, name);
    }

    matches!(
        names.as_slice(),
        [family, variant]
            if ((family == "Option" && matches!(variant.as_str(), "Some" | "None"))
                || (family == "Result" && matches!(variant.as_str(), "Ok" | "Err")))
                && !source_may_shadow_namespace_name(context.file, context.func, family)
    ) || matches!(
        names.as_slice(),
        [root, module, family, variant]
            if (root == "core" || root == "std")
                && ((module == "option"
                    && family == "Option"
                    && matches!(variant.as_str(), "Some" | "None"))
                    || (module == "result"
                        && family == "Result"
                        && matches!(variant.as_str(), "Ok" | "Err")))
                && !source_may_shadow_namespace_name(context.file, context.func, root)
    )
}

/// True when the tail expression contains a control-flow construct that would make
/// a nested `?` CONDITIONAL (`if`/`match`/loop/closure/`&&`/`||`). Conservative: it
/// flags the construct even if no `?` sits under it, so such a tail expression with
/// ANY `?` is left fail-closed rather than risk an unconditional-evaluation rewrite.
fn tail_expr_has_conditional(block: &Block) -> bool {
    let Some(expr) = tail_expr(block) else {
        return false;
    };
    struct Check {
        found: bool,
    }
    impl<'ast> Visit<'ast> for Check {
        fn visit_expr_if(&mut self, _node: &'ast syn::ExprIf) {
            self.found = true;
        }
        fn visit_expr_match(&mut self, _node: &'ast syn::ExprMatch) {
            self.found = true;
        }
        fn visit_expr_while(&mut self, _node: &'ast syn::ExprWhile) {
            self.found = true;
        }
        fn visit_expr_for_loop(&mut self, _node: &'ast syn::ExprForLoop) {
            self.found = true;
        }
        fn visit_expr_loop(&mut self, _node: &'ast syn::ExprLoop) {
            self.found = true;
        }
        fn visit_expr_closure(&mut self, _node: &'ast syn::ExprClosure) {
            self.found = true;
        }
        fn visit_expr_binary(&mut self, node: &'ast syn::ExprBinary) {
            if matches!(node.op, syn::BinOp::And(_) | syn::BinOp::Or(_)) {
                self.found = true;
            }
            syn::visit::visit_expr_binary(self, node);
        }
    }
    let mut check = Check { found: false };
    check.visit_expr(expr);
    check.found
}

/// Wrapping a tail expression in an outer `match` moves every expression-level
/// attribute relative to the `?` that triggers short-circuiting. Attributes can
/// conditionally remove or transform their target, and this verifier does not
/// evaluate them. Retain the original Expr::Try fail-close whenever one occurs
/// anywhere in the rewritten tail.
fn tail_expr_has_attrs(block: &Block) -> bool {
    let Some(expr) = tail_expr(block) else {
        return false;
    };
    struct Check {
        found: bool,
    }
    impl<'ast> Visit<'ast> for Check {
        fn visit_attribute(&mut self, _node: &'ast syn::Attribute) {
            self.found = true;
        }
    }
    let mut check = Check { found: false };
    check.visit_expr(expr);
    check.found
}

fn build_try_match(inner: &Expr, pat: &Pat, rest: &Block, kind: TryReturnKind) -> Expr {
    match kind {
        // `?` on an `Option`: `None` short-circuits to `None`.
        TryReturnKind::Option => syn::parse_quote! {
            match #inner {
                ::core::option::Option::Some(#pat) => #rest,
                ::core::option::Option::None => ::core::option::Option::None,
            }
        },
        // `?` on a `Result`: `Err(e)` short-circuits to `Err(e)`. Restricted to a
        // matching error type (no `.into()` conversion is modeled) — a differing
        // error type simply produces a fail-closed type mismatch downstream.
        TryReturnKind::Result => syn::parse_quote! {
            match #inner {
                ::core::result::Result::Ok(#pat) => #rest,
                ::core::result::Result::Err(__trust_vc_try_err) =>
                    ::core::result::Result::Err(__trust_vc_try_err),
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::ToTokens;
    use syn::parse_quote;

    fn only_fn(file: &File) -> ItemFn {
        file.items
            .iter()
            .find_map(|item| match item {
                Item::Fn(func) => Some(func.clone()),
                _ => None,
            })
            .expect("fixture function")
    }

    #[test]
    fn generated_option_constructors_are_capture_resistant() {
        let file: File = parse_quote! {
            fn f(o: Option<u64>) -> Option<u64> { let v = o?; Some(v) }
        };
        let rewritten =
            desugar_try_operator(&only_fn(&file), Some(&file), Some(&[])).expect("supported ?");
        let rendered = rewritten.to_token_stream().to_string();
        assert!(rendered.contains(":: core :: option :: Option :: Some"));
        assert!(rendered.contains(":: core :: option :: Option :: None"));
    }

    #[test]
    fn try_and_binding_pattern_attributes_stay_fail_closed() {
        let file: File = parse_quote! {
            fn f(o: Option<u64>) -> Option<u64> { let v = o?; Some(v) }
        };

        let mut try_attributed = only_fn(&file);
        let Stmt::Local(local) = &mut try_attributed.block.stmts[0] else {
            panic!("fixture local")
        };
        let Expr::Try(expr_try) = &mut *local.init.as_mut().expect("initializer").expr else {
            panic!("fixture try")
        };
        expr_try.attrs.push(parse_quote!(#[trust_vc_test_attr]));
        assert!(desugar_try_operator(&try_attributed, Some(&file), Some(&[])).is_none());

        let mut pat_attributed = only_fn(&file);
        let Stmt::Local(local) = &mut pat_attributed.block.stmts[0] else {
            panic!("fixture local")
        };
        let Pat::Ident(pat) = &mut local.pat else {
            panic!("fixture pattern")
        };
        pat.attrs.push(parse_quote!(#[trust_vc_test_attr]));
        assert!(desugar_try_operator(&pat_attributed, Some(&file), Some(&[])).is_none());

        let wildcard_file: File = parse_quote! {
            fn f(o: Option<u64>) -> Option<u64> { let _ = o?; Some(0u64) }
        };
        let mut wildcard_attributed = only_fn(&wildcard_file);
        let Stmt::Local(local) = &mut wildcard_attributed.block.stmts[0] else {
            panic!("fixture local")
        };
        let Pat::Wild(pat) = &mut local.pat else {
            panic!("fixture wildcard")
        };
        pat.attrs.push(parse_quote!(#[trust_vc_test_attr]));
        assert!(
            desugar_try_operator(&wildcard_attributed, Some(&wildcard_file), Some(&[])).is_none()
        );
    }

    #[test]
    fn any_attribute_in_rewritten_tail_stays_fail_closed() {
        let file: File = parse_quote! {
            fn f(o: Option<u64>) -> Option<u64> { Some(o?) }
        };
        let mut func = only_fn(&file);
        let Some(Stmt::Expr(Expr::Call(call), None)) = func.block.stmts.last_mut() else {
            panic!("fixture tail call")
        };
        call.attrs.push(parse_quote!(#[trust_vc_test_attr]));
        assert!(desugar_try_operator(&func, Some(&file), Some(&[])).is_none());
    }

    #[test]
    fn value_callee_and_method_receiver_paths_are_not_reorder_inert() {
        let method_file: File = parse_quote! {
            fn f(x: &mut u64, o: Option<u64>) -> Option<u64> {
                Some(x.take(o?))
            }
        };
        assert!(
            desugar_try_operator(&only_fn(&method_file), Some(&method_file), Some(&[])).is_none()
        );

        let value_callee_file: File = parse_quote! {
            fn f(call: fn(u64) -> u64, o: Option<u64>) -> Option<u64> {
                Some(call(o?))
            }
        };
        assert!(desugar_try_operator(
            &only_fn(&value_callee_file),
            Some(&value_callee_file),
            Some(&[]),
        )
        .is_none());
    }

    #[test]
    fn attributed_parameters_and_ambiguous_preludes_stay_fail_closed() {
        let file: File = parse_quote! {
            fn f(o: Option<u64>) -> Option<u64> { let v = o?; Some(v) }
        };
        let mut attributed_param = only_fn(&file);
        let FnArg::Typed(param) = &mut attributed_param.sig.inputs[0] else {
            panic!("fixture typed parameter")
        };
        param.attrs.push(parse_quote!(#[trust_vc_test_attr]));
        assert!(
            desugar_try_operator(&attributed_param, Some(&file), Some(&[])).is_none(),
            "an attributed caller parameter is not authoritative type evidence"
        );

        let module_file: File = parse_quote! {
            mod inner {
                #![no_implicit_prelude]
                fn f(o: Option<u64>) -> Option<u64> { let v = o?; Some(v) }
            }
        };
        let Item::Mod(module) = &module_file.items[0] else {
            panic!("fixture module")
        };
        let (_, items) = module.content.as_ref().expect("inline module");
        let Item::Fn(module_func) = &items[0] else {
            panic!("fixture module function")
        };
        assert!(desugar_try_operator(
            module_func,
            Some(&module_file),
            Some(&["inner".to_string()]),
        )
        .is_none());

        let cfg_attr_file: File = parse_quote! {
            #![cfg_attr(feature = "unconfigured-test-feature", no_implicit_prelude)]
            fn f(o: Option<u64>) -> Option<u64> { let v = o?; Some(v) }
        };
        assert!(
            desugar_try_operator(&only_fn(&cfg_attr_file), Some(&cfg_attr_file), Some(&[]))
                .is_none()
        );
    }
}
