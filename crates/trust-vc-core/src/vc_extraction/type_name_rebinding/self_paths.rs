// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Spellings `Self::Name` that need not name an enum variant.
//!
//! The type-name rules read `Self::Name` as a variant where `Name` is one, and
//! otherwise as a spelling of `Name` through a path they cannot follow. Rust
//! reads it as a variant only where `Self` is an enum with that variant, which
//! is inside an `impl` of that enum, and only in a value or a pattern. In a
//! type position `Self::Name` is an associated type: of the impl's trait, of a
//! trait the type implements, or inside a trait, of the trait or of any of its
//! supertraits, which the file need not declare (`trait Tr: Iterator<Item =
//! u8>` gives `Self::Item`, the byte). Inside a trait, a `struct`, `enum` or
//! `union` definition, or an `impl` of anything but an enum, `Self` is not an
//! enum whose variants a path can name.
//!
//! [`self_path_not_variant`] finds the first `Self::Name` that need not be a
//! variant. A path written in the tokens of a macro or an attribute has no
//! known position, so it is read as a variant only inside an `impl` of an enum
//! with that variant, and only when the tokens declare no item of their own
//! (a nested `trait` or `impl` gives `Self` another meaning).

use std::collections::{BTreeMap, BTreeSet};

use proc_macro2::{TokenStream, TokenTree};
use syn::visit::Visit;
use syn::{File, ItemFn};

use super::declared_names::file_holds;
use super::{is_path_sep, unraw};

/// The enums and associated types that decide what `Self::Name` names.
pub(super) struct SelfVariants<'a> {
    /// Every enum's variant names, by the enum's name.
    pub(super) enums: &'a BTreeMap<String, BTreeSet<String>>,
    /// Every name a trait or an impl declares as an associated type, which
    /// `Self::` names before a variant.
    pub(super) associated: &'a BTreeSet<String>,
}

/// The `Name` of the first spelling `Self::Name` in `file` and `func`, with
/// `Name` in `wanted`, that need not name a variant (see the module
/// documentation). `func` is read at file scope when `file` does not hold it,
/// so outside any `impl`.
pub(super) fn self_path_not_variant(
    file: Option<&File>,
    func: Option<&ItemFn>,
    variants: &SelfVariants<'_>,
    wanted: &dyn Fn(&str) -> bool,
) -> Option<String> {
    let mut scan = SelfPathScan {
        variants,
        wanted,
        selves: Vec::new(),
        value: false,
        found: None,
    };
    if let Some(file) = file {
        scan.visit_file(file);
    }
    if let Some(func) = func {
        if scan.found.is_none() && !file.is_some_and(|file| file_holds(file, func)) {
            scan.visit_item_fn(func);
        }
    }
    scan.found
}

struct SelfPathScan<'a> {
    variants: &'a SelfVariants<'a>,
    wanted: &'a dyn Fn(&str) -> bool,
    /// For each item around the walk that gives `Self` a meaning, outermost
    /// first, the enum it is an `impl` of, if it is one.
    selves: Vec<Option<String>>,
    /// Whether the path being walked is a value or a pattern.
    value: bool,
    found: Option<String>,
}

impl SelfPathScan<'_> {
    /// Whether `Self::name` names a variant: the innermost item that gives
    /// `Self` a meaning is an `impl` of an enum with a variant `name`, and no
    /// associated type of that name is declared.
    fn names_variant(&self, name: &str) -> bool {
        !self.variants.associated.contains(name)
            && self
                .selves
                .last()
                .and_then(Option::as_ref)
                .and_then(|owner| self.variants.enums.get(owner))
                .is_some_and(|variants| variants.contains(name))
    }

    fn found(&mut self, name: String) {
        if self.found.is_none() {
            self.found = Some(name);
        }
    }

    fn check_path(&mut self, path: &syn::Path) {
        let mut segments = path.segments.iter();
        let (Some(first), Some(second)) = (segments.next(), segments.next()) else {
            return;
        };
        if path.leading_colon.is_some() || first.ident != "Self" {
            return;
        }
        let name = unraw(&second.ident);
        if !(self.wanted)(&name) {
            return;
        }
        let variant = self.value
            && path.segments.len() == 2
            && first.arguments.is_none()
            && self.names_variant(&name);
        if !variant {
            self.found(name);
        }
    }

    fn check_tokens(&mut self, tokens: TokenStream) {
        let declares_items = holds_item_keyword(tokens.clone());
        self.check_token_paths(tokens, declares_items);
    }

    fn check_token_paths(&mut self, tokens: TokenStream, declares_items: bool) {
        let flat: Vec<TokenTree> = tokens.into_iter().collect();
        for (index, tree) in flat.iter().enumerate() {
            match tree {
                TokenTree::Group(group) => self.check_token_paths(group.stream(), declares_items),
                TokenTree::Ident(ident) if ident == "Self" => {
                    let (Some(sep_a), Some(sep_b), Some(TokenTree::Ident(next))) = (
                        flat.get(index + 1),
                        flat.get(index + 2),
                        flat.get(index + 3),
                    ) else {
                        continue;
                    };
                    if !is_path_sep(sep_a, sep_b) {
                        continue;
                    }
                    let name = unraw(next);
                    if !(self.wanted)(&name) {
                        continue;
                    }
                    let continues = matches!(
                        (flat.get(index + 4), flat.get(index + 5)),
                        (Some(a), Some(b)) if is_path_sep(a, b)
                    );
                    if declares_items || continues || !self.names_variant(&name) {
                        self.found(name);
                    }
                }
                _ => {}
            }
        }
    }

    fn with_self<T>(&mut self, owner: Option<String>, visit: impl FnOnce(&mut Self) -> T) -> T {
        self.selves.push(owner);
        let out = visit(self);
        self.selves.pop();
        out
    }

    fn with_value<T>(&mut self, value: bool, visit: impl FnOnce(&mut Self) -> T) -> T {
        let saved = std::mem::replace(&mut self.value, value);
        let out = visit(self);
        self.value = saved;
        out
    }
}

impl<'ast> Visit<'ast> for SelfPathScan<'_> {
    fn visit_item_impl(&mut self, item: &'ast syn::ItemImpl) {
        let owner = match &*item.self_ty {
            syn::Type::Path(path) if path.qself.is_none() => path
                .path
                .segments
                .last()
                .map(|segment| unraw(&segment.ident))
                .filter(|name| self.variants.enums.contains_key(name)),
            _ => None,
        };
        self.with_self(owner, |scan| syn::visit::visit_item_impl(scan, item));
    }

    fn visit_item_trait(&mut self, item: &'ast syn::ItemTrait) {
        self.with_self(None, |scan| syn::visit::visit_item_trait(scan, item));
    }

    fn visit_item_trait_alias(&mut self, item: &'ast syn::ItemTraitAlias) {
        self.with_self(None, |scan| syn::visit::visit_item_trait_alias(scan, item));
    }

    fn visit_item_struct(&mut self, item: &'ast syn::ItemStruct) {
        self.with_self(None, |scan| syn::visit::visit_item_struct(scan, item));
    }

    fn visit_item_enum(&mut self, item: &'ast syn::ItemEnum) {
        self.with_self(None, |scan| syn::visit::visit_item_enum(scan, item));
    }

    fn visit_item_union(&mut self, item: &'ast syn::ItemUnion) {
        self.with_self(None, |scan| syn::visit::visit_item_union(scan, item));
    }

    fn visit_type_path(&mut self, path: &'ast syn::TypePath) {
        self.with_value(false, |scan| syn::visit::visit_type_path(scan, path));
    }

    fn visit_expr_path(&mut self, path: &'ast syn::ExprPath) {
        self.with_value(true, |scan| syn::visit::visit_expr_path(scan, path));
    }

    fn visit_expr_struct(&mut self, expr: &'ast syn::ExprStruct) {
        self.with_value(true, |scan| syn::visit::visit_expr_struct(scan, expr));
    }

    fn visit_pat_struct(&mut self, pat: &'ast syn::PatStruct) {
        self.with_value(true, |scan| syn::visit::visit_pat_struct(scan, pat));
    }

    fn visit_pat_tuple_struct(&mut self, pat: &'ast syn::PatTupleStruct) {
        self.with_value(true, |scan| syn::visit::visit_pat_tuple_struct(scan, pat));
    }

    fn visit_path(&mut self, path: &'ast syn::Path) {
        self.check_path(path);
        syn::visit::visit_path(self, path);
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        syn::visit::visit_macro(self, mac);
        self.check_tokens(mac.tokens.clone());
    }

    fn visit_meta_list(&mut self, list: &'ast syn::MetaList) {
        syn::visit::visit_meta_list(self, list);
        self.check_tokens(list.tokens.clone());
    }
}

/// Whether `tokens` hold, at any group depth, a keyword that declares an item
/// in which `Self` means something else.
fn holds_item_keyword(tokens: TokenStream) -> bool {
    tokens.into_iter().any(|tree| match tree {
        TokenTree::Group(group) => holds_item_keyword(group.stream()),
        TokenTree::Ident(ident) => ["trait", "impl", "struct", "enum", "union"]
            .iter()
            .any(|keyword| ident == *keyword),
        _ => false,
    })
}
