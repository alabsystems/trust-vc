// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Binder-type inference for `assert forall|x| …` (untyped binders).
//!
//! Verus lets an `assert forall` binder omit its type and infers it from the
//! binder's USE (upstream `assert_forall_by.rs::test_forallstmt1` contains both
//! `assert forall|x: int| f1(x) > x` and the inference variant
//! `assert forall|x| f1(x) > x` in the SAME test case, so the case cannot
//! reproduce without this).
//!
//! trust-vc's quantifier encoding needs a concrete sort for every bound
//! variable, so this pass runs as a source-level pre-pass over the verified
//! function's body: it rewrites `|x|` into `|x: T|` wherever `T` is forced by
//! the program itself, and otherwise leaves the tokens ALONE so the downstream
//! parser keeps failing closed with "assert_forall_by! binders must be typed".
//!
//! ## Why this is sound
//!
//! The inferred type is never guessed. It is READ OFF the declared parameter
//! type of a spec function the binder is passed to, at the position it is passed
//! in: for `assert forall|x| f1(x) > x` with `spec fn f1(i: int) -> int`, `x`
//! must be `int` or the program would not typecheck in Rust/Verus either. Two
//! properties keep it fail-closed:
//!
//! 1. **Spec functions only.** A quantifier body is a spec-mode context, so a
//!    spec fn is the only thing callable inside it. Restricting resolution to
//!    `#[trust_vc::spec]` items means a local closure or an exec helper that
//!    happens to share a name can never supply a type.
//! 2. **Unanimity or nothing.** Every occurrence of the binder in an argument
//!    position must agree on the type. A binder used at two spec fns with
//!    different parameter types (or used at none) is left untyped, and the
//!    existing typed-binder error fires.
//!
//! Guessing WIDER than the truth (say `nat` where the program means `int`) is
//! the direction that would prove MORE than Verus — a `forall` over a smaller
//! domain is a weaker hypothesis to discharge. That is exactly why the type is
//! taken from the callee's signature rather than inferred from the body's
//! operators.

use std::collections::BTreeMap;

use proc_macro2::{Delimiter, Spacing, TokenStream, TokenTree};
use quote::quote;
use syn::visit_mut::VisitMut;
use syn::{File, Item, ItemFn, Type};

/// A spec function's identity: the inline-module path it is declared in, plus
/// its bare name. Keying by the BARE NAME ALONE was a cardinal false verify —
/// see [`SpecFnScopes`].
type SpecFnKey = (Vec<String>, String);

/// Spec-function declaration site -> declared parameter types, in order.
type SpecSignatures = BTreeMap<SpecFnKey, Vec<Type>>;

/// Where spec functions are declared, and what else could supply a name.
#[derive(Default)]
struct SpecFnIndex {
    declarations: SpecSignatures,
    /// `(module, in-scope name)` for every explicit `use` binding — a bound name
    /// may denote an item this file does not contain.
    use_bound_names: std::collections::BTreeSet<(Vec<String>, String)>,
    /// Modules holding a glob import, which can introduce a name from anywhere.
    glob_modules: std::collections::BTreeSet<Vec<String>>,
}

/// The scopes a written callee path is resolved through, and the ONLY way this
/// pass may turn a call into a parameter type.
///
/// THE DEFECT THIS TYPE EXISTS TO PREVENT. The signature registry was built from
/// `file.items` alone and keyed by the BARE function name, while the callee was
/// read as "the identifier token immediately before `(`" — so the `m::` in
/// `m::f1(x)` was discarded and the call matched a same-named TOP-LEVEL spec fn.
/// With `mod m { spec fn f1(i: int) -> int { i } }` beside a top-level
/// `spec fn f1(i: nat) -> int`, the binder in
/// `assert_forall_by!(|x| m::f1(x) >= 0, {})` was annotated `nat`, silently
/// narrowing the quantifier domain from `int`. `m::f1` is the identity, so the
/// claim is FALSE at `x = -1` — and it VERIFIED. `nat` and `int` share the SMT
/// Int sort, so no sort check downstream could catch it (a `u64`/`u8` mismatch
/// does fail closed, which is why this shape is the one that got through).
///
/// This is precisely the direction the module doc above calls out as unsound:
/// the type must be read off the callee the program actually names.
///
/// Built by exhaustive literal and consumed by the exhaustive destructure in
/// [`SpecFnScopes::resolve`], so adding a scope cannot compile until someone
/// writes down how it participates.
#[derive(Clone, Copy)]
struct SpecFnScopes<'a> {
    /// Inline-module path of the function whose body is being rewritten. `None`
    /// means it could not be identified, under which nothing resolves.
    use_site_module: Option<&'a [String]>,
    index: &'a SpecFnIndex,
}

impl<'a> SpecFnScopes<'a> {
    /// Resolve the written callee path `PREFIX::name` at this use site.
    /// Anything the file cannot settle answers `None`, which leaves the binder
    /// untyped and the downstream typed-binder error firing.
    fn resolve(&self, prefix: &[String], name: &str) -> Option<&'a Vec<Type>> {
        // Exhaustive destructure — see the type doc.
        let SpecFnScopes {
            use_site_module,
            index,
        } = self;
        let SpecFnIndex {
            declarations,
            use_bound_names,
            glob_modules,
        } = index;
        let module: &[String] = (*use_site_module)?;

        // The head of a relative path — or the bare callee name itself — may be
        // a `use` binding denoting an item this file does not contain.
        let head = prefix.first().map_or(name, String::as_str);
        if use_bound_names.contains(&(module.to_vec(), head.to_string())) {
            return None;
        }
        // A glob can bind the head of a qualified path to a module never named
        // here.
        if !prefix.is_empty() && glob_modules.contains(module) {
            return None;
        }

        // Items in an ANCESTOR module are not in scope in a child, so a relative
        // path is rooted at the use site's own module and nowhere else.
        let absolute: Vec<String> = match prefix.split_first() {
            None => module.to_vec(),
            Some((head, rest)) if head == "crate" => rest.to_vec(),
            Some((head, rest)) if head == "self" => module.iter().chain(rest).cloned().collect(),
            // Resolvable in principle; declined rather than guessed.
            Some((head, _)) if head == "super" => return None,
            Some(_) => module.iter().chain(prefix).cloned().collect(),
        };
        declarations.get(&(absolute, name.to_string()))
    }
}

/// Rewrites untyped `assert forall` binders in `func`'s body using the spec
/// functions declared in `file`. Returns `None` when nothing was inferred (the
/// caller then verifies the original, unmodified function).
pub(crate) fn infer_untyped_assert_forall_binders(
    file: &File,
    func: &ItemFn,
    enclosing_module: Option<&[String]>,
) -> Option<ItemFn> {
    let index = collect_spec_fn_index(file);
    if index.declarations.is_empty() {
        return None;
    }

    // `enclosing_module` is `None` when the function's own inline module could
    // not be identified UNIQUELY. Resolution needs the use site's scope, so that
    // is carried through and declines every callee — never dropped to an
    // implicit file-top-level reading, which is the substitution that let a
    // nested `m::f1` be typed by the top-level `f1`.
    let mut rewriter = BinderInference {
        scopes: SpecFnScopes {
            use_site_module: enclosing_module,
            index: &index,
        },
        changed: false,
    };
    let mut rewritten = func.clone();
    rewriter.visit_item_fn_mut(&mut rewritten);
    rewriter.changed.then_some(rewritten)
}

fn collect_spec_fn_index(file: &File) -> SpecFnIndex {
    let mut index = SpecFnIndex::default();
    collect_spec_fn_items(&file.items, &mut Vec::new(), &mut index);
    index
}

fn collect_spec_use_tree(tree: &syn::UseTree, module: &[String], index: &mut SpecFnIndex) {
    match tree {
        syn::UseTree::Path(path) => collect_spec_use_tree(&path.tree, module, index),
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
                collect_spec_use_tree(item, module, index);
            }
        }
    }
}

fn collect_spec_fn_items(items: &[Item], module: &mut Vec<String>, index: &mut SpecFnIndex) {
    for item in items {
        if let Item::Use(item_use) = item {
            collect_spec_use_tree(&item_use.tree, module, index);
            continue;
        }
        if let Item::Mod(item_mod) = item {
            // An out-of-line `mod m;` has no content here, so its spec fns are
            // simply absent and every path through it declines.
            if let Some((_, inner)) = &item_mod.content {
                module.push(item_mod.ident.to_string());
                collect_spec_fn_items(inner, module, index);
                module.pop();
            }
            continue;
        }
        let Item::Fn(item_fn) = item else {
            continue;
        };
        // Only SPEC functions participate: a quantifier body is a spec context.
        if !matches!(
            crate::mode_attrs::classify_item_fn(item_fn),
            crate::mode::FunctionMode::Spec
        ) {
            continue;
        }
        let mut params = Vec::new();
        let mut typed = true;
        for input in &item_fn.sig.inputs {
            match input {
                syn::FnArg::Typed(pat_type) => params.push((*pat_type.ty).clone()),
                syn::FnArg::Receiver(_) => {
                    typed = false;
                    break;
                }
            }
        }
        if typed {
            index
                .declarations
                .insert((module.clone(), item_fn.sig.ident.to_string()), params);
        }
    }
}

/// Recover the callee path written immediately before a parenthesised group at
/// `index`, walking BACKWARDS over `ident (:: ident)*`.
///
/// Reading only `trees[index - 1]` was the defect: it saw `f1` in `m::f1(x)` and
/// silently dropped the qualifier. Returns the segments in source order, or
/// `None` when the token before `(` is not an identifier at all (a method call's
/// `.f(x)`, an index, a nested group).
fn callee_path_segments(trees: &[TokenTree], index: usize) -> Option<Vec<String>> {
    let TokenTree::Ident(name) = &trees[index - 1] else {
        return None;
    };
    // A method call (`recv.f1(x)`) is not a free spec-fn call and must not be
    // resolved as one.
    let mut segments = vec![name.to_string()];
    let mut cursor = index - 1;
    loop {
        // Expect `:` `:` (a joint-then-alone pair) then an identifier.
        if cursor < 3 {
            break;
        }
        let (TokenTree::Punct(second), TokenTree::Punct(first)) =
            (&trees[cursor - 1], &trees[cursor - 2])
        else {
            break;
        };
        if first.as_char() != ':' || second.as_char() != ':' || first.spacing() != Spacing::Joint {
            break;
        }
        let TokenTree::Ident(seg) = &trees[cursor - 3] else {
            break;
        };
        segments.push(seg.to_string());
        cursor -= 3;
    }
    // A leading `.` means this was a method call, not a path.
    if cursor >= 1 {
        if let TokenTree::Punct(dot) = &trees[cursor - 1] {
            if dot.as_char() == '.' {
                return None;
            }
        }
    }
    segments.reverse();
    Some(segments)
}

struct BinderInference<'a> {
    scopes: SpecFnScopes<'a>,
    changed: bool,
}

impl VisitMut for BinderInference<'_> {
    fn visit_macro_mut(&mut self, mac: &mut syn::Macro) {
        let Some(name) = mac.path.segments.last().map(|seg| seg.ident.to_string()) else {
            return;
        };
        if !matches!(
            name.as_str(),
            "assert" | "trust_vc_assert" | "assert_forall_by"
        ) {
            return;
        }
        if let Some(rewritten) = annotate_binders(mac.tokens.clone(), self.scopes) {
            mac.tokens = rewritten;
            self.changed = true;
        }
    }

    fn visit_item_mut(&mut self, _: &mut Item) {
        // A nested item has its own scope and its own verification; do not
        // rewrite through it.
    }
}

/// Rewrites `|x| body` / `assert forall |x| body by { .. }` token streams,
/// annotating each untyped binder whose type the body forces. Returns `None` if
/// no binder was annotated.
fn annotate_binders(tokens: TokenStream, scopes: SpecFnScopes<'_>) -> Option<TokenStream> {
    let trees: Vec<TokenTree> = tokens.into_iter().collect();

    // Skip the leading `assert` / `forall` keywords of the Verus surface.
    let mut open = 0usize;
    while matches!(trees.get(open), Some(TokenTree::Ident(ident))
        if ident == "assert" || ident == "forall")
    {
        open += 1;
    }
    if !is_punct(trees.get(open)?, '|') {
        return None;
    }
    let close = (open + 1..trees.len()).find(|&idx| is_punct(&trees[idx], '|'))?;

    let binder_segments = split_top_level_commas(&trees[open + 1..close]);
    let body = &trees[close + 1..];

    let mut annotated: Vec<TokenStream> = Vec::new();
    let mut changed = false;
    for segment in &binder_segments {
        if let [TokenTree::Ident(ident)] = segment.as_slice() {
            if let Some(ty) = infer_binder_type(&ident.to_string(), body, scopes) {
                annotated.push(quote!(#ident: #ty));
                changed = true;
                continue;
            }
        }
        annotated.push(segment.iter().cloned().collect());
    }
    if !changed {
        return None;
    }

    let mut out: TokenStream = trees[..=open].iter().cloned().collect();
    for (index, segment) in annotated.iter().enumerate() {
        if index > 0 {
            out.extend(quote!(,));
        }
        out.extend(segment.clone());
    }
    out.extend(trees[close..].iter().cloned());
    Some(out)
}

/// The type every argument-position occurrence of `binder` agrees on, or `None`
/// (no occurrence, an unknown callee, or a disagreement — all fail closed).
fn infer_binder_type(binder: &str, body: &[TokenTree], scopes: SpecFnScopes<'_>) -> Option<Type> {
    let mut found: Option<Type> = None;
    collect_binder_arg_types(binder, body, scopes, &mut |ty| {
        match &found {
            // Disagreement between two call sites: poison the inference.
            Some(existing) if !types_match(existing, &ty) => found = Some(poison_type()),
            Some(_) => {}
            None => found = Some(ty),
        }
    });
    let ty = found?;
    (!types_match(&ty, &poison_type())).then_some(ty)
}

/// A type that can never be written in source, used as the "conflicting
/// inference" sentinel so a disagreement can never annotate a binder.
fn poison_type() -> Type {
    syn::parse_quote!(__trust_vc_conflicting_binder_type)
}

fn types_match(left: &Type, right: &Type) -> bool {
    use quote::ToTokens;
    left.to_token_stream().to_string() == right.to_token_stream().to_string()
}

/// Walks `trees` for `f( … )` calls on a known spec fn and reports the declared
/// parameter type at each position where `binder` is passed as a BARE argument.
fn collect_binder_arg_types(
    binder: &str,
    trees: &[TokenTree],
    scopes: SpecFnScopes<'_>,
    report: &mut impl FnMut(Type),
) {
    for (index, tree) in trees.iter().enumerate() {
        if let TokenTree::Group(group) = tree {
            // Recurse into every group so nested calls are seen too.
            let inner: Vec<TokenTree> = group.stream().into_iter().collect();
            collect_binder_arg_types(binder, &inner, scopes, report);

            if group.delimiter() != Delimiter::Parenthesis || index == 0 {
                continue;
            }
            // A parenthesized group directly after a PATH is a call. The whole
            // path is recovered and resolved through the use site's scope; the
            // trailing identifier alone is what used to let `m::f1(x)` be typed
            // by a top-level `f1`.
            let Some(segments) = callee_path_segments(trees, index) else {
                continue;
            };
            let Some((name, prefix)) = segments.split_last() else {
                continue;
            };
            let Some(params) = scopes.resolve(prefix, name) else {
                continue;
            };
            let args = split_top_level_commas(&inner);
            for (position, arg) in args.iter().enumerate() {
                // Only a BARE `x` argument pins the binder's type. `x + 1` or
                // `x as int` says nothing about `x`'s own type.
                let [TokenTree::Ident(ident)] = arg.as_slice() else {
                    continue;
                };
                if ident != binder {
                    continue;
                }
                if let Some(ty) = params.get(position) {
                    report(ty.clone());
                }
            }
        }
    }
}

fn split_top_level_commas(trees: &[TokenTree]) -> Vec<Vec<TokenTree>> {
    let mut segments = Vec::new();
    let mut current = Vec::new();
    for tree in trees {
        if is_punct(tree, ',') {
            segments.push(std::mem::take(&mut current));
        } else {
            current.push(tree.clone());
        }
    }
    if !current.is_empty() {
        segments.push(current);
    }
    segments
}

fn is_punct(tree: &TokenTree, ch: char) -> bool {
    matches!(tree, TokenTree::Punct(punct)
        if punct.as_char() == ch && punct.spacing() == Spacing::Alone)
}

#[cfg(test)]
#[path = "assert_forall_binder_inference_tests.rs"]
mod tests;
