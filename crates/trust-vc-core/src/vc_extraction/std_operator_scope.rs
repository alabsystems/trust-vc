// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Which one-argument operator methods (`x.add(e)`, `x.shl(n)`, `x.shr(n)`)
//! the file calls only where the std trait that supplies them is in scope.
//!
//! None of these traits is in the prelude, so on a primitive integer the
//! method resolves to the std impl only where a `use` brings `Add`, `Shl` or
//! `Shr` from `std::ops` or `core::ops` into scope. There, method resolution
//! tries the by-value receiver first and finds the std method, which takes
//! `self` by value and cannot change the caller's binding. Anywhere else the
//! call resolves to some other trait's method, which may take `&mut self`.
//!
//! A method counts as covered only when every call of it written in the file
//! is: the file's top level imports the trait and so does every inline module
//! that holds a call, or the function body under extraction imports it in its
//! own top-level statements. A file (or function) that binds the name `std`
//! or `core` itself covers nothing, since the `use` path may then name a
//! module of the file.
//!
//! The lowering asks more ([`methods_read_as_std_operator`]): it reads the
//! contracts and bodies of other functions of the file too, so a function
//! body's import covers only the calls in that body, and every call in the
//! file must be covered.

use std::collections::BTreeSet;

use proc_macro2::{TokenStream, TokenTree};
use quote::ToTokens;
use syn::visit::Visit;
use syn::{File, ItemFn};

/// Each operator method the lowering reads as the std operator on a primitive
/// integer, with the `std::ops` trait that supplies it.
const OPERATOR_METHODS: &[(&str, &str)] = &[("add", "Add"), ("shl", "Shl"), ("shr", "Shr")];

/// The methods of [`OPERATOR_METHODS`] whose every call the file (or `func`,
/// when there is no file) makes where the std trait is in scope. See the
/// module documentation.
pub(super) fn methods_with_std_trait_in_scope(
    file: Option<&File>,
    func: &ItemFn,
) -> BTreeSet<&'static str> {
    let mut out = BTreeSet::new();
    if binds_std_root(file, func) {
        return out;
    }
    for &(method, trait_name) in OPERATOR_METHODS {
        let body_imports = func.block.stmts.iter().any(|stmt| {
            matches!(stmt, syn::Stmt::Item(syn::Item::Use(item)) if use_imports_std_trait(&item.tree, trait_name, &[]))
        });
        let file_imports = file.is_some_and(|file| {
            items_import_std_trait(&file.items, trait_name)
                && inline_modules_cover(&file.items, method, trait_name)
        });
        if body_imports || file_imports {
            out.insert(method);
        }
    }
    out
}

/// The methods of [`OPERATOR_METHODS`] the lowering may read as the std
/// operator on a primitive integer: every call of the method written anywhere
/// in the file sits where the std trait is in scope. The lowering reads more
/// than the function under extraction (the contracts and bodies of the file
/// functions it calls, trait and impl methods), so one uncovered call in the
/// file uncovers the method for all of them. A call is covered when the
/// module holding it (the file or an inline module) imports the trait at its
/// top level, or when it sits in the body of a function whose top-level
/// statements import it; a call in a function's attributes or signature is
/// covered only by its module. Without a file only `func` is read.
pub(crate) fn methods_read_as_std_operator(
    file: Option<&File>,
    func: &ItemFn,
) -> BTreeSet<&'static str> {
    let mut out = BTreeSet::new();
    if binds_std_root(file, func) {
        return out;
    }
    for &(method, trait_name) in OPERATOR_METHODS {
        let covered = match file {
            Some(file) => module_calls_covered(&file.items, method, trait_name),
            None => fn_calls_covered(
                &func.attrs,
                &func.sig,
                Some(&func.block),
                method,
                trait_name,
            ),
        };
        if covered {
            out.insert(method);
        }
    }
    out
}

/// Whether every `.method` call among `items` (at any depth) is covered by an
/// import of the std trait: the module's own, or a function body's. A nested
/// module does not see its parent's imports.
fn module_calls_covered(items: &[syn::Item], method: &str, trait_name: &str) -> bool {
    let module_imports = items_import_std_trait(items, trait_name);
    items.iter().all(|item| match item {
        syn::Item::Mod(module) => {
            !module
                .attrs
                .iter()
                .any(|attr| calls_method(attr.to_token_stream(), method))
                && module
                    .content
                    .as_ref()
                    .is_none_or(|(_, inner)| module_calls_covered(inner, method, trait_name))
        }
        _ if module_imports || !calls_method(item.to_token_stream(), method) => true,
        syn::Item::Fn(func) => fn_calls_covered(
            &func.attrs,
            &func.sig,
            Some(&func.block),
            method,
            trait_name,
        ),
        syn::Item::Impl(item_impl) => {
            let mut header = item_impl.clone();
            header.items.clear();
            !calls_method(header.to_token_stream(), method)
                && item_impl.items.iter().all(|impl_item| match impl_item {
                    syn::ImplItem::Fn(func) => fn_calls_covered(
                        &func.attrs,
                        &func.sig,
                        Some(&func.block),
                        method,
                        trait_name,
                    ),
                    other => !calls_method(other.to_token_stream(), method),
                })
        }
        syn::Item::Trait(item_trait) => {
            let mut header = item_trait.clone();
            header.items.clear();
            !calls_method(header.to_token_stream(), method)
                && item_trait.items.iter().all(|trait_item| match trait_item {
                    syn::TraitItem::Fn(func) => fn_calls_covered(
                        &func.attrs,
                        &func.sig,
                        func.default.as_ref(),
                        method,
                        trait_name,
                    ),
                    other => !calls_method(other.to_token_stream(), method),
                })
        }
        _ => false,
    })
}

/// Whether every `.method` call in one function is covered by an import of
/// the std trait among its body's top-level statements. A call in its
/// attributes or signature, or in a module nested in its body, is not.
fn fn_calls_covered(
    attrs: &[syn::Attribute],
    sig: &syn::Signature,
    body: Option<&syn::Block>,
    method: &str,
    trait_name: &str,
) -> bool {
    struct NestedModules<'m> {
        method: &'m str,
        calls: bool,
    }
    impl<'ast> Visit<'ast> for NestedModules<'_> {
        fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
            self.calls |= calls_method(item.to_token_stream(), self.method);
        }
    }
    if attrs
        .iter()
        .any(|attr| calls_method(attr.to_token_stream(), method))
        || calls_method(sig.to_token_stream(), method)
    {
        return false;
    }
    let Some(body) = body else {
        return true;
    };
    if !calls_method(body.to_token_stream(), method) {
        return true;
    }
    let body_items: Vec<syn::Item> = body
        .stmts
        .iter()
        .filter_map(|stmt| match stmt {
            syn::Stmt::Item(item) => Some(item.clone()),
            _ => None,
        })
        .collect();
    let mut nested = NestedModules {
        method,
        calls: false,
    };
    nested.visit_block(body);
    items_import_std_trait(&body_items, trait_name) && !nested.calls
}

/// Whether one of `items` is a `use` that brings the std trait `trait_name`
/// into scope.
fn items_import_std_trait(items: &[syn::Item], trait_name: &str) -> bool {
    items.iter().any(|item| {
        matches!(item, syn::Item::Use(item) if use_imports_std_trait(&item.tree, trait_name, &[]))
    })
}

/// Whether `tree`, under the path segments `prefix`, imports `trait_name`
/// from `std::ops` or `core::ops`: by name, renamed (`as _` included), or
/// through a glob over that module.
fn use_imports_std_trait(tree: &syn::UseTree, trait_name: &str, prefix: &[String]) -> bool {
    let in_std_ops =
        || matches!(prefix, [root, ops] if (root == "std" || root == "core") && ops == "ops");
    match tree {
        syn::UseTree::Path(path) => {
            let mut prefix = prefix.to_vec();
            prefix.push(syn::ext::IdentExt::unraw(&path.ident).to_string());
            use_imports_std_trait(&path.tree, trait_name, &prefix)
        }
        syn::UseTree::Group(group) => group
            .items
            .iter()
            .any(|item| use_imports_std_trait(item, trait_name, prefix)),
        syn::UseTree::Name(name) => in_std_ops() && name.ident == trait_name,
        syn::UseTree::Rename(rename) => in_std_ops() && rename.ident == trait_name,
        syn::UseTree::Glob(_) => in_std_ops(),
    }
}

/// Whether every inline module among `items` (at any depth) that itself holds
/// a `.method` call imports the std trait at its own top level. A module does
/// not see its parent's imports.
fn inline_modules_cover(items: &[syn::Item], method: &str, trait_name: &str) -> bool {
    items.iter().all(|item| match item {
        syn::Item::Mod(module) => match &module.content {
            Some((_, inner)) => {
                let calls_here = inner.iter().any(|item| {
                    !matches!(item, syn::Item::Mod(_))
                        && calls_method(item.to_token_stream(), method)
                });
                (!calls_here || items_import_std_trait(inner, trait_name))
                    && inline_modules_cover(inner, method, trait_name)
            }
            None => true,
        },
        _ => true,
    })
}

/// Whether `tokens` (at any group depth) hold `.method`, the start of a call
/// of `method` in method-call syntax.
fn calls_method(tokens: TokenStream, method: &str) -> bool {
    let flat: Vec<TokenTree> = tokens.into_iter().collect();
    flat.iter().enumerate().any(|(index, tree)| match tree {
        TokenTree::Group(group) => calls_method(group.stream(), method),
        TokenTree::Ident(ident) => {
            syn::ext::IdentExt::unraw(ident) == method
                && index > 0
                && matches!(&flat[index - 1], TokenTree::Punct(p) if p.as_char() == '.')
        }
        _ => false,
    })
}

/// Whether the file or `func` binds `std` or `core` with a `mod`, an
/// `extern crate` under another name, or a `use`.
fn binds_std_root(file: Option<&File>, func: &ItemFn) -> bool {
    struct RootBinding(bool);
    fn is_root(ident: &syn::Ident) -> bool {
        let name = syn::ext::IdentExt::unraw(ident).to_string();
        name == "std" || name == "core"
    }
    fn use_binds_root(tree: &syn::UseTree, top: bool) -> bool {
        match tree {
            syn::UseTree::Path(path) => use_binds_root(&path.tree, false),
            syn::UseTree::Group(group) => group.items.iter().any(|item| use_binds_root(item, top)),
            // `use std;` binds the crate to its own name.
            syn::UseTree::Name(name) => !top && is_root(&name.ident),
            syn::UseTree::Rename(rename) => {
                is_root(&rename.rename) && !(top && rename.ident == rename.rename)
            }
            syn::UseTree::Glob(_) => false,
        }
    }
    impl<'ast> Visit<'ast> for RootBinding {
        fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
            self.0 |= is_root(&item.ident);
            syn::visit::visit_item_mod(self, item);
        }
        fn visit_item_extern_crate(&mut self, item: &'ast syn::ItemExternCrate) {
            let bound = item
                .rename
                .as_ref()
                .map_or(&item.ident, |(_, rename)| rename);
            self.0 |= is_root(bound) && *bound != item.ident;
        }
        fn visit_item_use(&mut self, item: &'ast syn::ItemUse) {
            self.0 |= use_binds_root(&item.tree, true);
        }
    }
    let mut visitor = RootBinding(false);
    if let Some(file) = file {
        visitor.visit_file(file);
    }
    visitor.visit_item_fn(func);
    visitor.0
}

#[cfg(test)]
mod tests {
    use super::*;

    fn covered(src: &str) -> BTreeSet<&'static str> {
        let file = syn::parse_file(src).expect("fixture parses");
        let func = file
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "f" => Some(func.clone()),
                _ => None,
            })
            .expect("fixture has `fn f`");
        methods_with_std_trait_in_scope(Some(&file), &func)
    }

    #[test]
    fn an_import_of_the_std_trait_covers_its_method() {
        for src in [
            "use std::ops::Add; fn f(x: u64) -> u64 { x.add(1) }",
            "use core::ops::Add; fn f(x: u64) -> u64 { x.add(1) }",
            "use ::std::ops::Add; fn f(x: u64) -> u64 { x.add(1) }",
            "use std::ops::{Add, Sub}; fn f(x: u64) -> u64 { x.add(1) }",
            "use std::{fmt, ops::Add}; fn f(x: u64) -> u64 { x.add(1) }",
            "use std::ops::Add as _; fn f(x: u64) -> u64 { x.add(1) }",
            "use std::ops::Add as Plus; fn f(x: u64) -> u64 { x.add(1) }",
            "use std::ops::*; fn f(x: u64) -> u64 { x.add(1) }",
            "fn f(x: u64) -> u64 { use std::ops::Add; x.add(1) }",
            "use std::ops::Add; mod m { use std::ops::Add; fn g(x: u64) -> u64 { x.add(1) } } \
             fn f(x: u64) -> u64 { x.add(1) }",
            "use std::ops::Add; mod m { fn g(x: u64) -> u64 { x } } \
             fn f(x: u64) -> u64 { x.add(1) }",
            "use std::ops::Add; extern crate core; fn f(x: u64) -> u64 { x.add(1) }",
        ] {
            assert!(covered(src).contains("add"), "{src}");
        }
        assert!(
            covered("use std::ops::{Shl, Shr}; fn f(x: u64) -> u64 { x.shl(1u32) }")
                .is_superset(&BTreeSet::from(["shl", "shr"]))
        );
    }

    #[test]
    fn a_call_the_std_trait_does_not_reach_is_not_covered() {
        for src in [
            // No import: the call resolves to some other trait's method.
            "fn f(x: u64) -> u64 { x.add(1) }",
            "trait MyAdd { fn add(&mut self, y: u64); } fn f(x: u64) { x.add(1) }",
            "use other::*; fn f(x: u64) -> u64 { x.add(1) }",
            "use std::ops; fn f(x: u64) -> u64 { x.add(1) }",
            "use std::ops::Sub; fn f(x: u64) -> u64 { x.add(1) }",
            "use std::ops::Add::{self}; fn f(x: u64) -> u64 { x.add(1) }",
            "use other::ops::Add; fn f(x: u64) -> u64 { x.add(1) }",
            // A module does not see its parent's import.
            "use std::ops::Add; mod m { fn g(x: u64) -> u64 { x.add(1) } } \
             fn f(x: u64) -> u64 { x.add(1) }",
            "use std::ops::Add; mod m { mod n { fn g(x: u64) -> u64 { x.add(1) } } } \
             fn f(x: u64) -> u64 { x.add(1) }",
            // An import in a nested block reaches only that block.
            "fn f(x: u64) -> u64 { { use std::ops::Add; } x.add(1) }",
            // `std` or `core` may name a module of the file.
            "use std::ops::Add; mod std { pub mod ops { pub trait Add {} } } \
             fn f(x: u64) -> u64 { x.add(1) }",
            "use core::ops::Add; extern crate other as core; fn f(x: u64) -> u64 { x.add(1) }",
            "use std::ops::Add; use other as std; fn f(x: u64) -> u64 { x.add(1) }",
            "use std::ops::Add; use a::std; fn f(x: u64) -> u64 { x.add(1) }",
            "fn f(x: u64) -> u64 { use std::ops::Add; mod core {} x.add(1) }",
        ] {
            assert!(!covered(src).contains("add"), "{src}");
        }
        assert!(!covered("use std::ops::Add; fn f(x: u64) -> u64 { x.shl(1u32) }").contains("shl"));
    }

    fn read_as_std(src: &str) -> BTreeSet<&'static str> {
        let file = syn::parse_file(src).expect("fixture parses");
        let func = file
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "f" => Some(func.clone()),
                _ => None,
            })
            .expect("fixture has `fn f`");
        methods_read_as_std_operator(Some(&file), &func)
    }

    #[test]
    fn every_call_in_the_file_under_the_std_trait_is_read_as_std() {
        for src in [
            "fn f(x: u64) -> u64 { x }",
            "use std::ops::Add; fn f(x: u64) -> u64 { x.add(1) }",
            "use std::ops::Add; fn g(x: u64) -> u64 { x.add(1) } fn f(x: u64) -> u64 { g(x) }",
            "use std::ops::Add; #[ensures(result == x.add(1))] fn f(x: u64) -> u64 { x + 1 }",
            "use std::ops::Add; impl S { fn m(&self, x: u64) -> u64 { x.add(1) } } \
             fn f(x: u64) -> u64 { x }",
            "use std::ops::Add; trait T { fn m(x: u64) -> u64 { x.add(1) } } \
             fn f(x: u64) -> u64 { x }",
            "use std::ops::Add; mod m { use std::ops::Add; fn g(x: u64) -> u64 { x.add(1) } } \
             fn f(x: u64) -> u64 { x.add(1) }",
            "fn f(x: u64) -> u64 { use std::ops::Add; x.add(1) } \
             fn g(x: u64) -> u64 { use core::ops::Add; x.add(2) }",
            "impl S { fn m(&self, x: u64) -> u64 { use std::ops::Add; x.add(1) } } \
             fn f(x: u64) -> u64 { x }",
            "trait T { fn m(x: u64) -> u64 { use std::ops::*; x.add(1) } } \
             fn f(x: u64) -> u64 { x }",
            // A function nested in a body sees the body's imports.
            "fn f(x: u64) -> u64 { use std::ops::Add; fn g(y: u64) -> u64 { y.add(1) } g(x) }",
            "use std::ops::Add; const C: u64 = 1u64.add(2); fn f(x: u64) -> u64 { x }",
        ] {
            assert!(read_as_std(src).contains("add"), "{src}");
        }
    }

    #[test]
    fn one_call_outside_the_std_trait_is_not_read_as_std() {
        for src in [
            "fn f(x: u64) -> u64 { x.add(1) }",
            "use other::*; fn f(x: u64) -> u64 { x.add(1) }",
            "use other::MyAdd; fn f(x: u64) -> u64 { x.add(1) }",
            // Another function's call reaches the lowering too.
            "fn f(x: u64) -> u64 { use std::ops::Add; x.add(1) } \
             fn g(x: u64) -> u64 { x.add(1) }",
            "fn f(x: u64) -> u64 { x } fn g(x: u64) -> u64 { x.add(1) }",
            // A body's import does not reach the function's attributes.
            "#[ensures(result == x.add(1))] fn f(x: u64) -> u64 { use std::ops::Add; x + 1 }",
            "fn f(x: u64) -> u64 { x } \
             #[ensures(result == x.add(1))] fn g(x: u64) -> u64 { use std::ops::Add; x + 1 }",
            // A module does not see its parent's imports, nor a body's.
            "use std::ops::Add; mod m { fn g(x: u64) -> u64 { x.add(1) } } \
             fn f(x: u64) -> u64 { x }",
            "fn f(x: u64) -> u64 { use std::ops::Add; \
             mod inner { fn g(y: u64) -> u64 { y.add(1) } } x.add(1) }",
            "impl S { fn m(&self, x: u64) -> u64 { x.add(1) } } \
             fn f(x: u64) -> u64 { use std::ops::Add; x }",
            "trait T { fn m(x: u64) -> u64 { x.add(1) } } fn f(x: u64) -> u64 { x }",
            "trait T { #[ensures(result == x.add(1))] fn m(x: u64) -> u64; } \
             fn f(x: u64) -> u64 { x }",
            "macro_rules! m { ($x:expr) => { $x.add(1) } } fn f(x: u64) -> u64 { x }",
            "const C: u64 = 1u64.add(2); fn f(x: u64) -> u64 { x }",
            // An import in a nested block reaches only that block.
            "fn f(x: u64) -> u64 { { use std::ops::Add; } x.add(1) }",
            // `std` may name a module of the file.
            "use std::ops::Add; mod std { pub mod ops { pub trait Add {} } } \
             fn f(x: u64) -> u64 { x.add(1) }",
        ] {
            assert!(!read_as_std(src).contains("add"), "{src}");
        }
        assert!(
            !read_as_std("use std::ops::Add; fn f(x: u64) -> u64 { x.shl(1u32) }").contains("shl")
        );
        assert!(
            read_as_std("use std::ops::Add; fn f(x: u64) -> u64 { x.shl(1u32) }").contains("add")
        );
    }

    #[test]
    fn no_file_reads_the_function_body_alone() {
        let func: ItemFn = syn::parse_str("fn f(x: u64) -> u64 { x.add(1) }").unwrap();
        assert!(methods_with_std_trait_in_scope(None, &func).is_empty());
        let func: ItemFn =
            syn::parse_str("fn f(x: u64) -> u64 { use std::ops::Add; x.add(1) }").unwrap();
        assert!(methods_with_std_trait_in_scope(None, &func).contains("add"));
        assert!(methods_read_as_std_operator(None, &func).contains("add"));
        let func: ItemFn = syn::parse_str("fn f(x: u64) -> u64 { x.add(1) }").unwrap();
        assert!(!methods_read_as_std_operator(None, &func).contains("add"));
    }
}
