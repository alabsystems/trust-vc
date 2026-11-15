// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Impl-group census: which impls implement ONE trait for ONE self type.
//!
//! SOUNDNESS-CRITICAL. The engine identifies an impl by (trait name, erased
//! self type): the per-trait UF `Tr__m` carries no trait arguments, the `Box_S`
//! bridge and the concrete-receiver method metadata are keyed by the self type
//! with references erased, and the concrete symbol `S__m` and the
//! `ImplMethodKey (trait, S__m)` registries omit the trait arguments. Two impls
//! of one trait for one self type — `impl Wc<bool> for S` beside
//! `impl Wc<u32> for S`, `impl Wc<u8> for S` beside `impl<'x> Wc<&'x u8> for S`,
//! `impl Tm for S` beside `impl<'a> Tm for &'a S` — are therefore one function
//! to every consumer, and whichever registered first answered for both.
//!
//! The decl list cannot be trusted to show such a pair. `register_trait_impl`
//! merges decls that compare equal, and equality runs over the ERASED fields,
//! so `Wc<u8>` / `Wc<&'x u8>` (both arguments lower to `u8`),
//! `Wc<HashSet<u8>>` / `Wc<BTreeSet<u8>>` (one `Set` sort), const arguments
//! (one `Opaque` placeholder) and `impl Tm for S` / `impl Tm for &S` collapse
//! into ONE decl before any consumer counts. [`impl_group_census`] therefore
//! counts from SOURCE, and the result rides on the decl as merged metadata
//! ([`ImplGroupCensus`]) that the dedup unions rather than compares.
//! [`collided_group_members`] combines it with the decl-level view (two decls
//! that survived dedup with the same trait and erased self type) for the
//! consumers.
//!
//! The source walk covers the WHOLE syntax tree of the file, not the module
//! item list the registering producers walk (`trait_catalog::collect_traits`,
//! `vc_extraction::collect_source_trait_declarations`): an impl inside a
//! function body, a `const`/`static` initializer block, a module nested in a
//! function body, another impl's method or a closure is never registered and
//! never conformance-checked, yet Rust applies it crate-wide — rustc says so
//! itself while compiling those shapes ("an `impl` is never scoped, even when
//! it is nested inside an item"). Before the walk was widened, each of those
//! left the file FULLY GREEN with `Wc::<u32>::wc(&s) == 1u8` verified against a
//! hidden body returning 2.
//!
//! RESIDUALS, measured and open (not closable here):
//! * an impl produced by expanding a `macro_rules!` invocation — `syn` does not
//!   expand macros, so its tokens are opaque to this walk and to every producer;
//!   such a sibling is still uncounted and its file still reports green;
//! * a group split across FILES of one crate (`mod m;` with no inline body) —
//!   the per-file lane sees one file;
//! * an impl the walk DOES see but no producer registers is counted only as a
//!   sibling. When it is the file's ONLY impl there is no row to refuse, so it
//!   is neither registered nor checked (the separately-keyed "impl in a fn body
//!   is never conformance-checked" hole).

use std::collections::BTreeSet;

use crate::ir::{ImplGroupCensus, TraitImplDecl};
use crate::trait_path_resolution::TraitScopeIndex;

/// The source census of `item_impl` (whose parsed, trait-resolved decl is
/// `impl_decl`) against every OTHER trait impl in `root_file`, including impls
/// nested in inline `mod` bodies and impls NOT marked `#[trust_vc::trait_impl]`
/// (an unmarked sibling is exactly as invisible to the registries, and its body
/// is never checked).
///
/// Two impls are grouped when their traits resolve to the same name and their
/// self types share ANY of the keys the engine itself erases to: the leaf
/// type (`S`, `&S`, `super::S` → `S`; see `self_type_leaf`), the erased
/// `TrustVcType` rendering, or the concrete-symbol prefix. Grouping more than
/// the engine conflates only over-rejects; grouping less is the false verify.
///
/// `item_impl` must be a reference INTO `root_file` (both lanes walk the same
/// `File`); it is excluded from its own census by address.
pub(crate) fn impl_group_census(
    root_file: &syn::File,
    scope_index: &TraitScopeIndex,
    impl_decl: &TraitImplDecl,
    item_impl: &syn::ItemImpl,
) -> ImplGroupCensus {
    let own_keys = SelfTypeKeys::of(item_impl, &impl_decl.concrete_type);
    let own_methods = impl_fn_names(item_impl);
    let mut census = ImplGroupCensus::default();
    let mut module = Vec::new();
    visit_trait_impls(&root_file.items, &mut module, &mut |module, other| {
        if std::ptr::eq(other, item_impl) {
            return;
        }
        // Self type first: it is cheap and rules out almost every impl.
        let other_keys = SelfTypeKeys::of(other, &crate::trait_expand::impl_concrete_type(other));
        if !own_keys.overlaps(&other_keys) {
            return;
        }
        // The lanes key a decl by its RESOLVED trait name. An undecidable header
        // fails a MARKED impl's file closed in the lanes; for an unmarked one it
        // keeps the last-segment spelling `parse_trait_impl_decl` records.
        let other_trait = match crate::trait_path_resolution::resolved_impl_trait_name(
            scope_index,
            module,
            other,
        ) {
            Ok(Some(resolved)) => Some(resolved),
            _ => other.trait_.as_ref().and_then(|(_, path, _)| {
                path.segments
                    .last()
                    .map(|segment| segment.ident.to_string())
            }),
        };
        if other_trait.as_deref() != Some(impl_decl.trait_name.as_str()) {
            return;
        }
        // A method is SHARED only where the per-impl registries actually
        // collide: the captured bodies, impl `ensures`, function contexts and
        // exempt set are keyed by the concrete symbol `{prefix}__{method}`, so
        // only a sibling minting the same prefix can answer for this impl's
        // conformance check. (`impl Wc<u32> for self::S` beside
        // `impl Wc<bool> for S` mints `self_P__P_S__wc` vs `S__wc`: its rows are
        // checked on the merits, while the CALLER lane — keyed by the erased
        // self type — still treats the pair as a group.)
        let sibling_shared = if own_keys.symbol_prefix == other_keys.symbol_prefix {
            impl_fn_names(other)
        } else {
            BTreeSet::new()
        };
        census.record_sibling(own_methods.iter().map(String::as_str), &sibling_shared);
    });
    census
}

/// For each entry of `impl_decls` (same order): whether it belongs to a group
/// of two or more impls of one trait for one self type — by the source census
/// carried on the decl, or because another decl that survived dedup names the
/// same trait and the same erased self type. Every consumer that publishes a
/// per-impl fact about the (trait, self type) key must treat a `true` entry as
/// unresolvable and publish nothing.
pub(crate) fn collided_group_members(impl_decls: &[TraitImplDecl]) -> Vec<bool> {
    impl_decls
        .iter()
        .enumerate()
        .map(|(index, impl_decl)| {
            impl_decl.impl_group.has_sibling_impl
                || impl_decls.iter().enumerate().any(|(other_index, other)| {
                    other_index != index && decls_share_group_key(impl_decl, other)
                })
        })
        .collect()
}

fn decls_share_group_key(left: &TraitImplDecl, right: &TraitImplDecl) -> bool {
    if left.trait_name != right.trait_name {
        return false;
    }
    if left.concrete_type.to_type_string() == right.concrete_type.to_type_string() {
        return true;
    }
    let left_prefixes = binding_prefixes(left);
    binding_prefixes(right)
        .iter()
        .any(|prefix| left_prefixes.contains(prefix))
}

/// The `Type` half of every `Type__method` symbol the decl binds.
fn binding_prefixes(decl: &TraitImplDecl) -> BTreeSet<String> {
    decl.method_bindings
        .iter()
        .filter_map(|(method, symbol)| {
            symbol
                .strip_suffix(&format!("__{method}"))
                .map(str::to_owned)
        })
        .collect()
}

/// The keys under which the engine may conflate two self types.
struct SelfTypeKeys {
    leaf: Option<String>,
    erased: String,
    symbol_prefix: String,
}

impl SelfTypeKeys {
    fn of(item_impl: &syn::ItemImpl, concrete_type: &crate::ir::TrustVcType) -> Self {
        Self {
            leaf: self_type_leaf(&item_impl.self_ty),
            erased: concrete_type.to_type_string(),
            symbol_prefix: crate::trait_expand::encode_type_component(&item_impl.self_ty),
        }
    }

    fn overlaps(&self, other: &Self) -> bool {
        matches!((&self.leaf, &other.leaf), (Some(a), Some(b)) if a == b)
            || self.erased == other.erased
            || self.symbol_prefix == other.symbol_prefix
    }
}

/// The nominal leaf of an impl self type: its LAST path segment with that
/// segment's generic arguments — `S` for `S`, `&'a S`, `&mut S` and
/// `super::S`; `G<u8>` for `G<u8>` and `crate::m::G<u8>`. The path qualifier is
/// dropped because `S` and `self::S` name one type while the engine keys them
/// apart (their impls would otherwise not be grouped, and one impl's axioms
/// would answer calls to the other); the arguments are kept so `Vec<u8>` and
/// `Vec<u16>` stay distinct (an argument the engine erases is caught by the
/// erased-type key instead). `None` for a non-path self type (tuple, array,
/// slice, pointer, trait object), which is grouped by its erased rendering and
/// symbol prefix only.
fn self_type_leaf(ty: &syn::Type) -> Option<String> {
    match ty {
        syn::Type::Path(type_path) => type_path.path.segments.last().map(|segment| {
            quote::ToTokens::to_token_stream(segment)
                .to_string()
                .split_whitespace()
                .collect::<String>()
        }),
        syn::Type::Reference(reference) => self_type_leaf(&reference.elem),
        syn::Type::Group(group) => self_type_leaf(&group.elem),
        syn::Type::Paren(paren) => self_type_leaf(&paren.elem),
        _ => None,
    }
}

fn impl_fn_names(item_impl: &syn::ItemImpl) -> BTreeSet<String> {
    item_impl
        .items
        .iter()
        .filter_map(|item| match item {
            syn::ImplItem::Fn(method) => Some(method.sig.ident.to_string()),
            _ => None,
        })
        .collect()
}

/// Every trait impl written ANYWHERE in `items`, with the inline-module path it
/// sits under.
///
/// The walk descends through the whole syntax tree, not just module items: an
/// impl written inside a function body, inside a `const _: () = { .. };` or
/// `static` initializer, inside a module nested in a function body, or inside
/// another impl's method is still a sibling to the registries, because a trait
/// impl anywhere in the crate applies everywhere — while `collect_traits` and
/// `collect_source_trait_declarations` walk module items only, so such an impl
/// is never registered and never conformance-checked. Counting it here is what
/// keeps the VISIBLE impl of the pair from answering calls meant for it
/// (measured: a sibling in a fn body, in a `const` block and in a fn-local
/// module each left the file fully green with `Wc::<u32>::wc(&s) == 1u8`
/// verified against a body returning 2).
///
/// NOT reachable this way: an impl produced by expanding a `macro_rules!`
/// invocation — `syn` does not expand macros, so those tokens are opaque to
/// every producer here. See the module docs' residual list.
fn visit_trait_impls<'file>(
    items: &'file [syn::Item],
    module: &mut Vec<String>,
    visit: &mut dyn FnMut(&[String], &'file syn::ItemImpl),
) {
    let mut walk = TraitImplWalk {
        module: std::mem::take(module),
        visit,
    };
    for item in items {
        syn::visit::Visit::visit_item(&mut walk, item);
    }
    *module = walk.module;
}

struct TraitImplWalk<'file, 'visit> {
    module: Vec<String>,
    visit: &'visit mut dyn FnMut(&[String], &'file syn::ItemImpl),
}

impl<'file> syn::visit::Visit<'file> for TraitImplWalk<'file, '_> {
    fn visit_item_mod(&mut self, item_mod: &'file syn::ItemMod) {
        // `mod m;` (no inline body) is another file: outside this lane, and
        // recorded as a residual.
        let Some((_, inner)) = &item_mod.content else {
            return;
        };
        self.module.push(item_mod.ident.to_string());
        for item in inner {
            syn::visit::Visit::visit_item(self, item);
        }
        self.module.pop();
    }

    fn visit_item_impl(&mut self, item_impl: &'file syn::ItemImpl) {
        if item_impl.trait_.is_some() {
            (self.visit)(&self.module, item_impl);
        }
        // Keep descending: a method body may itself hold an impl.
        syn::visit::visit_item_impl(self, item_impl);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn census_of(src: &str, index: usize) -> ImplGroupCensus {
        let file = syn::parse_file(src).expect("parse");
        let scope_index = TraitScopeIndex::build(&file);
        let mut impls = Vec::new();
        visit_trait_impls(&file.items, &mut Vec::new(), &mut |module, item_impl| {
            impls.push((module.to_vec(), item_impl));
        });
        let (module, item_impl) = impls[index].clone();
        let mut decl = crate::trait_expand::parse_trait_impl_decl(item_impl).expect("decl");
        if let Ok(Some(resolved)) =
            crate::trait_path_resolution::resolved_impl_trait_name(&scope_index, &module, item_impl)
        {
            decl.trait_name = resolved;
        }
        impl_group_census(&file, &scope_index, &decl, item_impl)
    }

    #[test]
    fn erased_trait_arguments_are_siblings() {
        let src = "struct S; trait Wc<B> { fn wc(&self) -> u8; }
            impl Wc<u8> for S { fn wc(&self) -> u8 { 1 } }
            impl<'x> Wc<&'x u8> for S { fn wc(&self) -> u8 { 2 } }";
        let census = census_of(src, 0);
        assert!(census.has_sibling_impl);
        assert!(census.shared_method_names.contains("wc"));
    }

    #[test]
    fn reference_self_type_is_a_sibling_and_default_inheritor_shares_nothing() {
        let src = "struct S; trait Tm { fn m(&self) -> u8 { 0 } }
            impl Tm for S {}
            mod e { use super::*; impl<'a> Tm for &'a S { fn m(&self) -> u8 { 2 } } }";
        let census = census_of(src, 0);
        assert!(census.has_sibling_impl);
        assert!(census.shared_method_names.is_empty());
        let census = census_of(src, 1);
        assert!(census.has_sibling_impl);
        assert!(census.shared_method_names.is_empty());
    }

    #[test]
    fn path_qualified_spelling_of_one_self_type_is_a_sibling_but_other_arguments_are_not() {
        let src = "struct S; struct G<P>(P); trait Wc<B> { fn wc(&self) -> u8; }
            impl Wc<bool> for S { fn wc(&self) -> u8 { 1 } }
            impl Wc<u32> for self::S { fn wc(&self) -> u8 { 2 } }
            impl Wc<bool> for G<u8> { fn wc(&self) -> u8 { 3 } }
            impl Wc<bool> for G<u16> { fn wc(&self) -> u8 { 4 } }";
        let census = census_of(src, 0);
        assert!(census.has_sibling_impl);
        // Different concrete-symbol prefixes: the registries do not collide.
        assert!(census.shared_method_names.is_empty());
        assert_eq!(census_of(src, 2), ImplGroupCensus::default());
        assert_eq!(census_of(src, 3), ImplGroupCensus::default());
    }

    #[test]
    fn siblings_outside_the_module_item_list_are_counted() {
        // rustc: "an `impl` is never scoped, even when it is nested inside an
        // item". Each hidden impl below applies crate-wide, and none of them is
        // registered or conformance-checked, so the VISIBLE impl must see it.
        for hidden in [
            "fn h() { impl Wc<u32> for S { fn wc(&self) -> u8 { 2 } } }",
            "const _: () = { impl Wc<u32> for S { fn wc(&self) -> u8 { 2 } } };",
            "static _X: () = { impl Wc<u32> for S { fn wc(&self) -> u8 { 2 } } };",
            "fn h() { mod inner { use super::*; impl Wc<u32> for S { fn wc(&self) -> u8 { 2 } } } }",
            "impl S { fn h() { impl Wc<u32> for S { fn wc(&self) -> u8 { 2 } } } }",
            "fn h() { let _ = || { impl Wc<u32> for S { fn wc(&self) -> u8 { 2 } } }; }",
        ] {
            let src = format!(
                "struct S; trait Wc<B> {{ fn wc(&self) -> u8; }}
                 impl Wc<bool> for S {{ fn wc(&self) -> u8 {{ 1 }} }}
                 {hidden}"
            );
            let census = census_of(&src, 0);
            assert!(census.has_sibling_impl, "hidden in `{hidden}`");
            assert!(
                census.shared_method_names.contains("wc"),
                "hidden in `{hidden}`"
            );
        }
    }

    #[test]
    fn a_nested_impl_of_another_trait_or_self_type_is_still_not_a_sibling() {
        // The deeper walk must not group by nesting: only (trait, self type).
        let src = "struct S; struct T; trait Wc<B> { fn wc(&self) -> u8; }
            trait Other { fn wc(&self) -> u8; }
            impl Wc<bool> for S { fn wc(&self) -> u8 { 1 } }
            fn h() {
                impl Wc<bool> for T { fn wc(&self) -> u8 { 2 } }
                impl Other for S { fn wc(&self) -> u8 { 3 } }
            }";
        assert_eq!(census_of(src, 0), ImplGroupCensus::default());
    }

    #[test]
    fn different_traits_and_different_self_types_are_not_siblings() {
        let src =
            "struct S; struct T; trait A { fn v(&self) -> u8; } trait B { fn v(&self) -> u8; }
            impl A for S { fn v(&self) -> u8 { 1 } }
            impl B for S { fn v(&self) -> u8 { 2 } }
            impl A for T { fn v(&self) -> u8 { 3 } }";
        for index in 0..3 {
            assert_eq!(
                census_of(src, index),
                ImplGroupCensus::default(),
                "impl {index}"
            );
        }
    }

    #[test]
    fn decl_level_group_needs_the_same_trait_and_self_type() {
        let a = TraitImplDecl::new("Tr", crate::ir::TrustVcType::Bool, Vec::new());
        let b = TraitImplDecl::new("Tr", crate::ir::TrustVcType::Bool, Vec::new())
            .with_trait_type_args(vec![crate::ir::TrustVcType::Bool]);
        let c = TraitImplDecl::new("Other", crate::ir::TrustVcType::Bool, Vec::new());
        assert_eq!(collided_group_members(&[a.clone(), b]), vec![true, true]);
        assert_eq!(collided_group_members(&[a, c]), vec![false, false]);
    }
}
