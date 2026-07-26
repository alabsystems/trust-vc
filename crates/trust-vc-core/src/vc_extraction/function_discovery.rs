// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use quote::ToTokens;
use syn::{File, Item, ItemFn};

/// Extracts the last segment name from a syn::Path.
/// Handles both simple identifiers (`assert`) and qualified paths (`trust_vc::assert`).
pub(super) fn path_last_segment(path: &syn::Path) -> Option<String> {
    path.segments.last().map(|seg| seg.ident.to_string())
}

/// Finds a function by name in the AST.
///
/// Searches top-level functions first, then walks into `impl` blocks,
/// inline `mod` blocks, and `trait` blocks so that methods annotated with
/// trust_vc attributes are discoverable by `cargo trust_vc check --function`.
pub(super) fn find_function<'a>(file: &'a File, name: &str) -> Option<&'a ItemFn> {
    // A crate-root free function keeps historical precedence over methods with
    // the same name. Its lexical provenance is exact.
    for item in &file.items {
        if let Item::Fn(func) = item {
            if func.sig.ident == name {
                return Some(func);
            }
        }
    }

    // Every non-root candidate has the same CLI spelling. Resolve only a unique
    // candidate; source order must never select one of several methods.
    let mut matches = Vec::new();
    collect_named_functions(&file.items, name, &mut matches);
    if matches.len() == 1 {
        matches.pop()
    } else {
        None
    }
}

fn collect_named_functions<'a>(items: &'a [Item], name: &str, matches: &mut Vec<&'a ItemFn>) {
    for item in items {
        match item {
            Item::Fn(func) => {
                if func.sig.ident == name {
                    matches.push(func);
                }
            }
            Item::Impl(impl_block) => {
                for impl_item in &impl_block.items {
                    if let syn::ImplItem::Fn(method) = impl_item {
                        if method.sig.ident == name {
                            matches.push(impl_fn_to_item_fn_leak(method));
                        }
                    }
                }
            }
            Item::Mod(module) => {
                if let Some((_, ref inner_items)) = module.content {
                    collect_named_functions(inner_items, name, matches);
                }
            }
            Item::Trait(trait_block) => {
                for trait_item in &trait_block.items {
                    if let syn::TraitItem::Fn(method) = trait_item {
                        if method.sig.ident == name {
                            if let Some(ref block) = method.default {
                                matches.push(trait_fn_to_item_fn_leak(method, block));
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

/// Converts an `ImplItemFn` to an `ItemFn` reference by leaking a Box.
///
/// The AST lives for the duration of verification, so the leaked allocation
/// is cleaned up when the process (or thread) ends. This avoids changing the
/// public `extract_verification_conditions(&ItemFn)` signature.
///
/// `Self` is NOT resolved here — that happens once, at the common extraction
/// entry (`vc_extraction::apply_enclosing_self_substitution`), so every caller
/// of the extraction (the `verify_function_from_file` gate path AND the
/// file-context test harness, which lifts impl methods with its own copy of
/// this logic) resolves `Self` identically.
fn impl_fn_to_item_fn_leak(method: &syn::ImplItemFn) -> &'static ItemFn {
    Box::leak(Box::new(ItemFn {
        attrs: method.attrs.clone(),
        vis: method.vis.clone(),
        sig: method.sig.clone(),
        block: Box::new(method.block.clone()),
    }))
}

/// Provenance-preserving result of locating a lifted [`ItemFn`] in its source
/// file. Any collision or same-name mismatch must fail closed.
pub(super) enum EnclosingImplResolution<'a> {
    NotImpl,
    Unique(&'a syn::Type),
    Ambiguous,
}

/// Lexical inline-module path containing a discovered/lifted function.
/// `Ambiguous` includes a missing exact source identity: alias resolution must
/// never guess a module from a bare function name.
pub(super) enum EnclosingModuleResolution {
    Unique(Vec<String>),
    Ambiguous,
}

pub(super) fn enclosing_inline_module_path(
    file: &File,
    func: &ItemFn,
) -> EnclosingModuleResolution {
    // `find_function` gives a crate/file-root free function precedence. Mirror
    // that rule so an identical nested definition cannot steal its provenance.
    for item in &file.items {
        if let Item::Fn(candidate) = item {
            if candidate.sig.ident == func.sig.ident && item_fn_matches_item_fn(candidate, func) {
                return EnclosingModuleResolution::Unique(Vec::new());
            }
        }
    }

    let mut candidates = Vec::new();
    collect_enclosing_module_candidates(&file.items, func, &mut Vec::new(), &mut candidates);
    if candidates.len() == 1 {
        EnclosingModuleResolution::Unique(candidates.pop().expect("one candidate"))
    } else {
        EnclosingModuleResolution::Ambiguous
    }
}

fn collect_enclosing_module_candidates(
    items: &[Item],
    func: &ItemFn,
    module_path: &mut Vec<String>,
    candidates: &mut Vec<Vec<String>>,
) {
    for item in items {
        match item {
            Item::Fn(candidate) => {
                if candidate.sig.ident == func.sig.ident && item_fn_matches_item_fn(candidate, func)
                {
                    candidates.push(module_path.clone());
                }
            }
            Item::Impl(impl_block) => {
                for impl_item in &impl_block.items {
                    if let syn::ImplItem::Fn(method) = impl_item {
                        if method.sig.ident == func.sig.ident
                            && impl_method_matches_item_fn(method, func)
                        {
                            candidates.push(module_path.clone());
                        }
                    }
                }
            }
            Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    module_path.push(module.ident.to_string());
                    collect_enclosing_module_candidates(inner_items, func, module_path, candidates);
                    module_path.pop();
                }
            }
            Item::Trait(trait_block) => {
                for trait_item in &trait_block.items {
                    if let syn::TraitItem::Fn(method) = trait_item {
                        if method.sig.ident == func.sig.ident {
                            if let Some(block) = &method.default {
                                if trait_method_matches_item_fn(method, block, func) {
                                    candidates.push(module_path.clone());
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

/// Resolves the enclosing impl by complete source-item identity, never by name
/// or source order alone. Attributes, visibility, signature, and body are all
/// part of the identity witness.
pub(super) fn enclosing_impl_self_ty<'a>(
    file: &'a File,
    func: &ItemFn,
) -> EnclosingImplResolution<'a> {
    let name = &func.sig.ident;

    // A matching crate-root function has the same precedence as `find_function`.
    // Merely sharing its name is not sufficient provenance.
    for item in &file.items {
        if let Item::Fn(f) = item {
            if &f.sig.ident == name && item_fn_matches_item_fn(f, func) {
                return EnclosingImplResolution::NotImpl;
            }
        }
    }

    let mut exact_impls = Vec::new();
    let mut same_name_impls = 0usize;
    let mut exact_non_impls = 0usize;
    collect_enclosing_candidates(
        &file.items,
        func,
        &mut exact_impls,
        &mut same_name_impls,
        &mut exact_non_impls,
    );

    match (exact_impls.len(), exact_non_impls) {
        (1, 0) => EnclosingImplResolution::Unique(exact_impls[0]),
        (0, n) if n > 0 => EnclosingImplResolution::NotImpl,
        (0, 0) if same_name_impls == 0 => EnclosingImplResolution::NotImpl,
        _ => EnclosingImplResolution::Ambiguous,
    }
}

fn collect_enclosing_candidates<'a>(
    items: &'a [Item],
    func: &ItemFn,
    exact_impls: &mut Vec<&'a syn::Type>,
    same_name_impls: &mut usize,
    exact_non_impls: &mut usize,
) {
    for item in items {
        match item {
            Item::Fn(candidate) => {
                if candidate.sig.ident == func.sig.ident && item_fn_matches_item_fn(candidate, func)
                {
                    *exact_non_impls += 1;
                }
            }
            Item::Impl(impl_block) => {
                for impl_item in &impl_block.items {
                    if let syn::ImplItem::Fn(method) = impl_item {
                        if method.sig.ident == func.sig.ident {
                            *same_name_impls += 1;
                            if impl_method_matches_item_fn(method, func) {
                                exact_impls.push(impl_block.self_ty.as_ref());
                            }
                        }
                    }
                }
            }
            Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    collect_enclosing_candidates(
                        inner_items,
                        func,
                        exact_impls,
                        same_name_impls,
                        exact_non_impls,
                    );
                }
            }
            Item::Trait(trait_block) => {
                for trait_item in &trait_block.items {
                    if let syn::TraitItem::Fn(method) = trait_item {
                        if method.sig.ident == func.sig.ident {
                            if let Some(block) = &method.default {
                                if trait_method_matches_item_fn(method, block, func) {
                                    *exact_non_impls += 1;
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

fn token_string(value: &impl ToTokens) -> String {
    value.to_token_stream().to_string()
}

fn attrs_match(left: &[syn::Attribute], right: &[syn::Attribute]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| token_string(left) == token_string(right))
}

fn item_fn_matches_item_fn(left: &ItemFn, right: &ItemFn) -> bool {
    attrs_match(&left.attrs, &right.attrs)
        && token_string(&left.vis) == token_string(&right.vis)
        && token_string(&left.sig) == token_string(&right.sig)
        && token_string(left.block.as_ref()) == token_string(right.block.as_ref())
}

pub(super) fn impl_method_matches_item_fn(method: &syn::ImplItemFn, func: &ItemFn) -> bool {
    attrs_match(&method.attrs, &func.attrs)
        && token_string(&method.vis) == token_string(&func.vis)
        && token_string(&method.sig) == token_string(&func.sig)
        && token_string(&method.block) == token_string(func.block.as_ref())
}

fn trait_method_matches_item_fn(
    method: &syn::TraitItemFn,
    block: &syn::Block,
    func: &ItemFn,
) -> bool {
    attrs_match(&method.attrs, &func.attrs)
        && matches!(&func.vis, syn::Visibility::Inherited)
        && token_string(&method.sig) == token_string(&func.sig)
        && token_string(block) == token_string(func.block.as_ref())
}

/// Replaces the keyword `Self` with the enclosing impl's concrete self type in
/// both type position (`self`, `&self`, `-> Self`, `x: Self`) and the leading
/// segment of an associated path (`Self::method` → `Concrete::method`).
///
/// It deliberately does NOT descend into nested item definitions (`visit_item_mut`
/// is a no-op): a nested `fn`/`impl`/`struct` inside the body carries its own
/// `Self` scope, and rewriting it would be incorrect. Attributes are also left
/// untouched here — contract token streams are re-parsed downstream with their
/// own type context; no current case needs `Self` inside a contract, and
/// rewriting raw tokens blindly would be unsound.
pub(super) struct SelfTypeSubstituter {
    /// The concrete self type substituted for `Self` in type position.
    concrete: syn::Type,
    /// The concrete type's leading path segment (base ident only, args dropped),
    /// substituted for a leading `Self` segment in an associated path. `None`
    /// when the self type is not a plain path (then `Self::` paths are left as
    /// is and fail closed downstream).
    base_segment: Option<syn::PathSegment>,
}

impl SelfTypeSubstituter {
    pub(super) fn new(self_ty: &syn::Type) -> Self {
        let base_segment = match self_ty {
            syn::Type::Path(tp) if tp.qself.is_none() => {
                tp.path.segments.last().map(|seg| syn::PathSegment {
                    ident: seg.ident.clone(),
                    arguments: syn::PathArguments::None,
                })
            }
            _ => None,
        };
        Self {
            concrete: self_ty.clone(),
            base_segment,
        }
    }
}

/// True for the bare keyword type `Self` (single segment, no path qualifier,
/// no generic arguments). `&Self`, `Self::Assoc`, and `Self<..>` are NOT bare
/// and are handled by ordinary recursion / path substitution.
fn is_bare_self_type(ty: &syn::Type) -> bool {
    if let syn::Type::Path(tp) = ty {
        if tp.qself.is_none() && tp.path.segments.len() == 1 {
            let seg = &tp.path.segments[0];
            return seg.ident == "Self" && matches!(seg.arguments, syn::PathArguments::None);
        }
    }
    false
}

impl syn::visit_mut::VisitMut for SelfTypeSubstituter {
    fn visit_type_mut(&mut self, ty: &mut syn::Type) {
        if is_bare_self_type(ty) {
            *ty = self.concrete.clone();
            return;
        }
        syn::visit_mut::visit_type_mut(self, ty);
    }

    fn visit_path_mut(&mut self, path: &mut syn::Path) {
        // `Self::method` / `Self::CONST` → `Concrete::method`. A lone `Self`
        // path (len == 1) is a type and is handled by `visit_type_mut`.
        if path.segments.len() > 1 {
            if let Some(first) = path.segments.first() {
                if first.ident == "Self" && matches!(first.arguments, syn::PathArguments::None) {
                    if let Some(seg) = &self.base_segment {
                        path.segments[0] = seg.clone();
                    }
                }
            }
        }
        syn::visit_mut::visit_path_mut(self, path);
    }

    // Nested item definitions carry their own `Self` scope — do not rewrite them.
    fn visit_item_mut(&mut self, _item: &mut syn::Item) {}
}

/// A resolvable associated-type projection harvested from a file's
/// `#[trust_vc::trait_impl]` blocks: `<concrete as trait>::assoc = bound`
/// (Phase A3).
///
/// `concrete_key` is the whitespace-stripped token rendering of the impl's self
/// type, matched against the same rendering of a projection's qualified self so
/// incidental spacing never blocks a match.
pub(super) struct AssocProjectionBinding {
    trait_name: String,
    concrete_key: String,
    assoc_name: String,
    bound: syn::Type,
}

/// Whitespace-stripped token rendering of a type, used as a structural key.
fn projection_type_key(ty: &syn::Type) -> String {
    ty.to_token_stream()
        .to_string()
        .replace(char::is_whitespace, "")
}

/// True iff `attrs` carries `#[trust_vc::trait_impl]` (or the post-expansion
/// bare `#[trait_impl]`): the marker that admits an impl into the trait-impl
/// registry the projection resolver reads.
fn is_trait_impl_attr(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|seg| seg.ident == "trait_impl")
    })
}

/// Collects every associated-type binding declared by the file's
/// `#[trust_vc::trait_impl] impl Trait for Concrete { type Assoc = Bound; }`
/// blocks (recursing inline modules), keyed for resolving fully-qualified
/// projections `<Concrete as Trait>::Assoc` in type position (Phase A3).
///
/// Best-effort: a non-trait impl, or a trait path with no final segment, is
/// skipped — the projection then stays unresolved and fails closed downstream,
/// never silently mis-resolved.
pub(super) fn collect_assoc_projection_bindings(file: &File) -> Vec<AssocProjectionBinding> {
    let mut bindings = Vec::new();
    collect_assoc_projection_bindings_in_items(&file.items, &mut bindings);
    bindings
}

fn collect_assoc_projection_bindings_in_items(
    items: &[Item],
    bindings: &mut Vec<AssocProjectionBinding>,
) {
    for item in items {
        match item {
            Item::Impl(item_impl) if is_trait_impl_attr(&item_impl.attrs) => {
                let Some((_, trait_path, _)) = &item_impl.trait_ else {
                    continue;
                };
                let Some(trait_name) = trait_path.segments.last().map(|seg| seg.ident.to_string())
                else {
                    continue;
                };
                let concrete_key = projection_type_key(&item_impl.self_ty);
                for impl_item in &item_impl.items {
                    if let syn::ImplItem::Type(assoc) = impl_item {
                        bindings.push(AssocProjectionBinding {
                            trait_name: trait_name.clone(),
                            concrete_key: concrete_key.clone(),
                            assoc_name: assoc.ident.to_string(),
                            bound: assoc.ty.clone(),
                        });
                    }
                }
            }
            Item::Mod(module) => {
                if let Some((_, inner)) = &module.content {
                    collect_assoc_projection_bindings_in_items(inner, bindings);
                }
            }
            _ => {}
        }
    }
}

/// Rewrites fully-qualified associated-type projections
/// `<Concrete as Trait>::Assoc` in TYPE position to the concrete type the file's
/// matching `#[trust_vc::trait_impl]` binds (`type Assoc = Bound;`), using
/// bindings harvested by [`collect_assoc_projection_bindings`] (Phase A3).
///
/// Only a projection naming a concrete self type with a matching in-file impl
/// resolves. A bare-generic projection (`T::X`, whose self is a type parameter),
/// or one naming a type/trait/assoc with no matching binding, is left as-is and
/// fails closed downstream. SOUND: the rewrite only makes a type MORE concrete,
/// and only to the type the impl actually binds; the resolved type lands in the
/// lifted variable's OWN sort (a fresh parameter/return slot), never a shared
/// per-trait UF slot, so the sort-divergence that keeps the trait-side bridged
/// path fail-closed cannot arise here.
pub(super) struct AssocProjectionResolver<'a> {
    bindings: &'a [AssocProjectionBinding],
}

impl<'a> AssocProjectionResolver<'a> {
    pub(super) fn new(bindings: &'a [AssocProjectionBinding]) -> Self {
        Self { bindings }
    }

    /// Returns the bound type for a qualified projection `<C as Tr>::X` iff the
    /// file binds it, else `None`.
    fn resolve(&self, ty: &syn::Type) -> Option<&syn::Type> {
        let syn::Type::Path(type_path) = ty else {
            return None;
        };
        let qself = type_path.qself.as_ref()?;
        let position = qself.position;
        // `<C as Tr>::X`: the trait segment is immediately before the associated
        // segment, and the associated segment must be the LAST one (a single
        // projected assoc; nested `::Y::Z` is not resolved here). `position == 0`
        // is `<C>::X` (inherent, no trait) — left unresolved.
        if position == 0 || type_path.path.segments.len() != position + 1 {
            return None;
        }
        let trait_name = type_path.path.segments[position - 1].ident.to_string();
        let assoc_name = type_path.path.segments[position].ident.to_string();
        let concrete_key = projection_type_key(&qself.ty);
        self.bindings
            .iter()
            .find(|binding| {
                binding.trait_name == trait_name
                    && binding.assoc_name == assoc_name
                    && binding.concrete_key == concrete_key
            })
            .map(|binding| &binding.bound)
    }
}

impl syn::visit_mut::VisitMut for AssocProjectionResolver<'_> {
    fn visit_type_mut(&mut self, ty: &mut syn::Type) {
        if let Some(bound) = self.resolve(ty).cloned() {
            // Substitute once; do NOT recurse into the substituted node (a bound
            // that itself named a projection would otherwise risk an
            // infinitely-sized rewrite). A projection NESTED in a container
            // (`Vec<<C as Tr>::X>`) still resolves via the default recursion on
            // the non-matching outer type below.
            *ty = bound;
            return;
        }
        syn::visit_mut::visit_type_mut(self, ty);
    }
}

/// Converts a `TraitItemFn` with a default body to an `ItemFn` reference.
fn trait_fn_to_item_fn_leak(method: &syn::TraitItemFn, block: &syn::Block) -> &'static ItemFn {
    Box::leak(Box::new(ItemFn {
        attrs: method.attrs.clone(),
        vis: syn::Visibility::Inherited,
        sig: method.sig.clone(),
        block: Box::new(block.clone()),
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use syn::parse_quote;

    fn impl_method(file: &File, impl_index: usize) -> &syn::ImplItemFn {
        let item_impl = file
            .items
            .iter()
            .filter_map(|item| match item {
                Item::Impl(item_impl) => Some(item_impl),
                _ => None,
            })
            .nth(impl_index)
            .expect("impl");
        item_impl
            .items
            .iter()
            .find_map(|item| match item {
                syn::ImplItem::Fn(method) => Some(method),
                _ => None,
            })
            .expect("method")
    }

    #[test]
    fn enclosing_impl_uses_full_method_identity() {
        let file: File = parse_quote! {
            struct A;
            struct B;
            impl A { fn same(&self) -> u32 { 1 } }
            impl B { fn same(&self) -> u32 { 2 } }
        };
        let lifted = impl_fn_to_item_fn_leak(impl_method(&file, 1));
        match enclosing_impl_self_ty(&file, lifted) {
            EnclosingImplResolution::Unique(ty) => assert_eq!(token_string(ty), "B"),
            _ => panic!("the exact B method should resolve uniquely"),
        }
    }

    #[test]
    fn token_identical_methods_are_ambiguous() {
        let file: File = parse_quote! {
            struct A;
            struct B;
            impl A { fn same(&self) -> u32 { 1 } }
            impl B { fn same(&self) -> u32 { 1 } }
        };
        let lifted = impl_fn_to_item_fn_leak(impl_method(&file, 0));
        assert!(matches!(
            enclosing_impl_self_ty(&file, lifted),
            EnclosingImplResolution::Ambiguous
        ));
    }
}
