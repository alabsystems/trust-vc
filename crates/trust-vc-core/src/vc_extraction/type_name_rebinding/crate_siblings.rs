// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The type names a crate's other files bring into the file the crate lane
//! verifies, and when the copy that brings them can be misread.
//!
//! The crate lane copies the `struct`, `enum` and `type` items of the crate's
//! other files, from any inline module, to the top level of the file it
//! verifies, so the lane reads a type another file declares by its name. The
//! copy drops the scope each item was written in: the `use` items that give
//! its spellings their meaning, and the module whose path names it. So `b.rs`
//! holding `use core::primitive::u8 as u64; pub type W = u64;` reaches the
//! verified file as `type W = u64;`, the primitive, and `use c::V as W;` in
//! the verified file is read as the `W` some other file declares.
//!
//! [`crate_sibling_view`] refuses a `Verified` answer for every function of
//! the verified file when
//!
//! 0. the files it was given need not be all the files of the crate: a file
//!    could not be read or parsed, or a `mod` carries a `path` attribute,
//!    which can put its file anywhere (`#[path = "../gen/b.rs"] mod b;`,
//!    also spelled `r#path`);
//! 1. another file that has items to copy holds a construct the type-name rule
//!    refuses, read over its `use` and `extern crate` items and the items
//!    copied from it (a primitive rename, a glob from outside the file where a
//!    primitive is spelled, a `use` that binds a name it declares from
//!    elsewhere); or, when any file has items to copy, any file of the crate,
//!    the verified one included, holds anywhere a construct the unread-item
//!    rule refuses (a macro invocation, a derive or an attribute that can emit
//!    an item), or a macro whose expansion declares a `struct`, `enum` or
//!    `union` of any name. An item such a construct emits is neither copied
//!    nor counted by rule 3: `use core::primitive::u8 as u64;` from `rn!();`
//!    in the scope of the copied items, or a second `W` that `use c::W;`
//!    imports;
//! 2. a `use` in any file of the crate binds a name another file declares (in
//!    another file, a name any file declares) other than by importing that
//!    name under its own name through a path that stays in the crate (see
//!    [`Routes::stays`]);
//! 3. a type name is declared more than once across the files, another file
//!    among them: the copies all land at the top level, where their name no
//!    longer tells them apart;
//! 4. a file of the crate has a glob import whose source is outside the crate
//!    (`std`, `core` and this toolchain's crates included) or a path that does
//!    not stay in it, and a file spells a name another file declares that it
//!    does not declare itself: that glob, or a module that re-exports what it
//!    brings, can bind the name (`use core::ffi::*;` binds `c_uchar`);
//! 5. a file spells a name another file declares after a path that does not
//!    stay in the crate, or as `Self::Name` where `Self` need not be an enum
//!    with a variant `Name` (see `self_paths`: in a trait, `Self::Item` can be
//!    an associated type of a supertrait no file declares);
//! 6. a file binds the name of one of this toolchain's crates to something
//!    else (`mod vstd;`), or has a glob import from another crate while a
//!    file spells `int`, `nat` or `real`: a path through that name need not
//!    reach that crate; or
//! 7. another file spells an identifier outside ASCII (see
//!    `identifier_spelling`): rustc reads identifiers in Unicode
//!    normalization form C, so `pub type K = u8;` spelled with the Kelvin
//!    sign in `z.rs` is the `K` that `use z::K;` imports, while the lane
//!    compares the strings as written and reads the `K` another file
//!    declares.
//!
//! A path stays in the crate when it starts at `crate`, `self`, `super` or a
//! module declared in the scope it is written in, and every later segment
//! names a module some file declares. No segment may be a name that a `use` or
//! an `extern crate` binds anywhere in the crate, and no segment after the
//! first may follow a glob from outside the crate anywhere in it: either can
//! bind a segment to a module outside the crate (`pub use core::ffi;` makes
//! `c::ffi::c_uchar` core's). A module of the crate binds a name by declaring
//! it, by a `use` that rule 2 checks, or by a glob that rule 4 checks, so such
//! a path reaches the crate's one declaration of that name or a `use` of it.
//!
//! The names the verified file declares itself are the type-name rule's, which
//! reads that file with its scopes and leaves the copied names to this module
//! (`verified_refusal_with_outside_types`). Rule 3 keeps the two sets apart.

use std::collections::{BTreeMap, BTreeSet};

use proc_macro2::{TokenStream, TokenTree};
use quote::ToTokens;
use syn::visit::Visit;
use syn::{File, ItemFn};

use super::declared_names::declared_type_names;
use super::self_paths::{self_path_not_variant, SelfVariants};
use super::{
    is_path_sep, path_segments, unraw, DeclaredIdentMasker, Frame, UseItemRemover,
    TYPE_NAME_REBINDING_TAG,
};

/// What the crate lane needs to know about the crate's other files when it
/// verifies a file with their type items copied in.
#[derive(Clone, Debug, Default)]
pub struct CrateSiblingView {
    /// The names the copied items declare.
    pub(in crate::vc_extraction) outside_types: BTreeSet<String>,
    /// Why no function of the verified file may be answered `Verified`.
    pub(in crate::vc_extraction) refusal: Option<String>,
}

impl CrateSiblingView {
    /// The refusal this view carries, if any.
    pub fn refusal(&self) -> Option<&str> {
        self.refusal.as_deref()
    }
}

/// Reads `target`, the file the crate lane verifies, beside `siblings`, the
/// crate's other files as `(path for messages, parsed file)`, and `unread`,
/// a description of each file of the crate the lane could not read or parse.
/// See the module documentation.
pub fn crate_sibling_view(
    target: &File,
    siblings: &[(String, File)],
    unread: &[String],
) -> CrateSiblingView {
    let probe: ItemFn = syn::parse_quote! {
        fn __trust_vc_crate_sibling_probe() {}
    };
    let surfaces: Vec<(String, File)> = siblings
        .iter()
        .map(|(path, file)| (path.clone(), surface(&file.items)))
        .collect();
    let mut sibling_counts: BTreeMap<String, usize> = BTreeMap::new();
    let mut sibling_declared: Vec<BTreeSet<String>> = Vec::new();
    for (_, surface) in &surfaces {
        let mut names = BTreeSet::new();
        for_each_copied_item(&surface.items, &mut |item| {
            if let Some(name) = copied_item_name(item) {
                *sibling_counts.entry(name.clone()).or_default() += 1;
                names.insert(name);
            }
        });
        sibling_declared.push(names);
    }
    let outside_types: BTreeSet<String> = sibling_counts.keys().cloned().collect();
    let refusal = unread
        .first()
        .map(|why| format!("{why}, so the files it reads need not be all the files of the crate"))
        .or_else(|| {
            refusal(
                target,
                siblings,
                &surfaces,
                &sibling_counts,
                &sibling_declared,
                &outside_types,
                &probe,
            )
        })
        .map(|why| {
            format!(
                "{TYPE_NAME_REBINDING_TAG}: this crate lane copies the type items of the crate's \
                 other files into this file, and {why}, so a type spelling in this file need not \
                 denote the type this extraction reads it as. A `Verified` answer is refused; a \
                 refutation would be kept"
            )
        });
    CrateSiblingView {
        outside_types,
        refusal,
    }
}

fn refusal(
    target: &File,
    siblings: &[(String, File)],
    surfaces: &[(String, File)],
    sibling_counts: &BTreeMap<String, usize>,
    sibling_declared: &[BTreeSet<String>],
    outside_types: &BTreeSet<String>,
    probe: &ItemFn,
) -> Option<String> {
    if surfaces.is_empty() {
        return None;
    }
    let target_declared = declared_type_names(Some(target), probe);
    let crate_declared: BTreeSet<String> = outside_types.union(&target_declared).cloned().collect();
    let crate_enums = crate_enum_variants(target, surfaces);
    let whole: Vec<(&str, &File)> = std::iter::once(("this file", target))
        .chain(siblings.iter().map(|(path, file)| (path.as_str(), file)))
        .collect();

    // Rule 0: a module whose file the `path` attribute places.
    for (path, file) in &whole {
        if let Some(module) = module_with_path_attribute(file) {
            return Some(format!(
                "`{path}` declares `mod {module}` with a `path` attribute, whose file the lane \
                 need not have read"
            ));
        }
    }

    // Rule 7. The verified file's own spellings are the identifier rule's.
    for (path, file) in whole.iter().skip(1) {
        if let Some(hazard) = super::super::identifier_spelling::file_hazard(file) {
            return Some(format!(
                "in `{path}`, {hazard}, where it can be a name another file spells otherwise"
            ));
        }
    }

    // Rule 6.
    for (path, file) in &whole {
        if let Some(binding) = super::declared_names::rebound_toolchain_root(Some(file), probe) {
            return Some(format!("`{path}` binds {binding}"));
        }
    }

    // Rule 1.
    for ((path, surface), declared) in surfaces.iter().zip(sibling_declared) {
        if declared.is_empty() {
            continue;
        }
        if let Some(hazard) = super::file_hazard(surface) {
            return Some(format!("in `{path}`, {hazard}"));
        }
    }
    if !outside_types.is_empty() {
        for (index, (path, file)) in whole.iter().enumerate() {
            // The unread-item rule refuses the verified file's own constructs
            // with its own message; only what it admits there is read here.
            if index == 0 && super::super::unread_items::file_hazard(file).is_some() {
                continue;
            }
            if let Some(hazard) = super::super::unread_items::crate_file_hazard(file) {
                return Some(format!(
                    "in `{path}`, {hazard}, and an item it emits can declare a type name \
                     another file declares, or bind a name the items copied from a file spell"
                ));
            }
        }
    }

    // Rule 3.
    let target_counts = declaration_counts(target);
    for (name, count) in sibling_counts {
        let total = count + target_counts.get(name).copied().unwrap_or(0);
        if total > 1 {
            return Some(format!(
                "the crate declares the type name `{name}` {total} times, in this file or \
                 another, and the copies no longer tell those declarations apart"
            ));
        }
    }

    // The files to read: this one in full, and the others as copied.
    let mut files: Vec<(&str, &File, &BTreeSet<String>, BTreeSet<String>)> =
        vec![("this file", target, outside_types, target_declared.clone())];
    for ((path, surface), declared) in surfaces.iter().zip(sibling_declared) {
        files.push((path.as_str(), surface, &crate_declared, declared.clone()));
    }
    let mut routes = Routes {
        modules: whole
            .iter()
            .flat_map(|(_, file)| module_names(file))
            .collect(),
        imported: whole
            .iter()
            .flat_map(|(_, file)| imported_names(file))
            .collect(),
        outside_glob: false,
        associated_types: whole
            .iter()
            .flat_map(|(_, file)| associated_type_names(file))
            .collect(),
    };
    let crate_glob = files
        .iter()
        .find_map(|(path, file, _, _)| outside_glob(file, &routes, &[]).map(|glob| (*path, glob)));
    routes.outside_glob = crate_glob.is_some();

    // Rule 6, through a glob: a module of another crate can be named like a
    // crate of this toolchain, and a glob binds it where a 2015-edition `use
    // vstd::int;` starts, at the crate root.
    let roots: Vec<&str> = super::declared_names::TOOLCHAIN_ROOTS
        .iter()
        .chain(&["std", "core", "alloc"])
        .copied()
        .collect();
    let foreign_glob = files.iter().find_map(|(path, file, _, _)| {
        outside_glob(file, &routes, &roots).map(|glob| (*path, glob))
    });
    if let Some((glob_path, glob)) = foreign_glob {
        let spelled = whole.iter().find_map(|(path, file)| {
            let tokens = file.to_token_stream();
            super::GHOST_SCALAR_NAMES
                .iter()
                .find(|name| spells_anywhere(tokens.clone(), name))
                .map(|name| (*path, *name))
        });
        if let Some((path, name)) = spelled {
            return Some(format!(
                "`{glob_path}` has the glob import `use {glob};`, which can bind a module named \
                 like a crate of this toolchain, and `{path}` spells `{name}`"
            ));
        }
    }

    // Rule 2.
    for (path, file, interest, _) in &files {
        if let Some(hazard) = use_hazard(file, interest, &routes) {
            return Some(format!("in `{path}`, {hazard}"));
        }
    }

    // Rule 4.
    if let Some((glob_path, glob)) = crate_glob {
        for (path, file, interest, own) in &files {
            let tokens = reading_tokens(file);
            let spelled = interest
                .iter()
                .filter(|name| !own.contains(*name))
                .find(|name| spells_anywhere(tokens.clone(), name));
            if let Some(name) = spelled {
                return Some(format!(
                    "`{glob_path}` has the glob import `use {glob};` from outside the crate, \
                     and `{path}` spells `{name}`, a type name of another file of the crate, \
                     which that glob can bind"
                ));
            }
        }
    }

    // Rule 5.
    for (path, file, interest, _) in &files {
        for (in_scope, tokens) in module_scopes(file) {
            if let Some(spelling) =
                path_leaving_crate(tokens, interest, &in_scope, &routes, &crate_enums)
            {
                return Some(format!(
                    "`{path}` spells `{spelling}`, a type name of another file of the crate, \
                     through a path that does not stay in the crate"
                ));
            }
        }
    }
    let variants = SelfVariants {
        enums: &crate_enums,
        associated: &routes.associated_types,
    };
    for (path, file, interest, _) in &files {
        if let Some(name) = self_path_not_variant(Some(*file), None, &variants, &|name| {
            interest.contains(name)
        }) {
            return Some(format!(
                "`{path}` spells `Self::{name}`, a type name of another file of the crate, \
                 where `Self` need not be an enum with a variant `{name}`"
            ));
        }
    }
    None
}

/// The items of a file the crate lane reads: its `use` and `extern crate`
/// items, the items it copies (`struct`, `enum` and `type` items, and the headers of `impl Drop`,
/// `impl PartialEq` and `impl PartialOrd`), and its modules with the same
/// items of their own. A copied item keeps its place, so its spellings are
/// read in the scope they were written in.
fn surface(items: &[syn::Item]) -> File {
    fn keep(items: &[syn::Item]) -> Vec<syn::Item> {
        let mut out = Vec::new();
        for item in items {
            match item {
                syn::Item::Use(_)
                | syn::Item::ExternCrate(_)
                | syn::Item::Enum(_)
                | syn::Item::Struct(_)
                | syn::Item::Type(_) => out.push(item.clone()),
                syn::Item::Impl(impl_block) if is_copied_impl(impl_block) => {
                    let mut header = impl_block.clone();
                    header.attrs.clear();
                    header.items.clear();
                    out.push(syn::Item::Impl(header));
                }
                syn::Item::Mod(module) => {
                    let mut module = module.clone();
                    if let Some((_, inner)) = &mut module.content {
                        *inner = keep(inner);
                    }
                    out.push(syn::Item::Mod(module));
                }
                _ => {}
            }
        }
        out
    }
    File {
        shebang: None,
        attrs: Vec::new(),
        items: keep(items),
    }
}

/// Whether the crate lane copies the header of `impl_block`.
fn is_copied_impl(impl_block: &syn::ItemImpl) -> bool {
    impl_block
        .trait_
        .as_ref()
        .and_then(|(_, path, _)| path.segments.last())
        .is_some_and(|segment| {
            segment.ident == "Drop" || segment.ident == "PartialEq" || segment.ident == "PartialOrd"
        })
}

/// Calls `visit` on each item of `items` the crate lane copies, in any inline
/// module.
fn for_each_copied_item(items: &[syn::Item], visit: &mut impl FnMut(&syn::Item)) {
    for item in items {
        match item {
            syn::Item::Mod(module) => {
                if let Some((_, inner)) = &module.content {
                    for_each_copied_item(inner, visit);
                }
            }
            syn::Item::Use(_) => {}
            item => visit(item),
        }
    }
}

/// The type name a copied item declares.
fn copied_item_name(item: &syn::Item) -> Option<String> {
    match item {
        syn::Item::Enum(it) => Some(unraw(&it.ident)),
        syn::Item::Struct(it) => Some(unraw(&it.ident)),
        syn::Item::Type(it) => Some(unraw(&it.ident)),
        _ => None,
    }
}

/// How many `struct`, `enum`, `union` and `type` items declare each name in
/// `file`, at any depth.
fn declaration_counts(file: &File) -> BTreeMap<String, usize> {
    #[derive(Default)]
    struct Count(BTreeMap<String, usize>);
    impl<'ast> Visit<'ast> for Count {
        fn visit_item(&mut self, item: &'ast syn::Item) {
            let ident = match item {
                syn::Item::Struct(it) => Some(&it.ident),
                syn::Item::Enum(it) => Some(&it.ident),
                syn::Item::Union(it) => Some(&it.ident),
                syn::Item::Type(it) => Some(&it.ident),
                _ => None,
            };
            if let Some(ident) = ident {
                *self.0.entry(unraw(ident)).or_default() += 1;
            }
            syn::visit::visit_item(self, item);
        }
    }
    let mut count = Count::default();
    count.visit_file(file);
    count.0
}

/// The names of the enums the files declare, with their variant names.
fn crate_enum_variants(
    target: &File,
    surfaces: &[(String, File)],
) -> BTreeMap<String, BTreeSet<String>> {
    #[derive(Default)]
    struct Collect(BTreeMap<String, BTreeSet<String>>);
    impl<'ast> Visit<'ast> for Collect {
        fn visit_item_enum(&mut self, item: &'ast syn::ItemEnum) {
            self.0
                .entry(unraw(&item.ident))
                .or_default()
                .extend(item.variants.iter().map(|variant| unraw(&variant.ident)));
            syn::visit::visit_item_enum(self, item);
        }
    }
    let mut collect = Collect::default();
    collect.visit_file(target);
    for (_, surface) in surfaces {
        collect.visit_file(surface);
    }
    collect.0
}

/// The names of the modules `file` declares, inline or not, at any depth.
fn module_names(file: &File) -> BTreeSet<String> {
    #[derive(Default)]
    struct Collect(BTreeSet<String>);
    impl<'ast> Visit<'ast> for Collect {
        fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
            self.0.insert(unraw(&item.ident));
            syn::visit::visit_item_mod(self, item);
        }
    }
    let mut collect = Collect::default();
    collect.visit_file(file);
    collect.0
}

/// Whether a `mod` named `name` is declared in the innermost module of
/// `frames` or in a block around the `use`.
fn module_in_scope(frames: &[Frame<'_>], name: &str) -> bool {
    for frame in frames.iter().rev() {
        let declares =
            |item: &syn::Item| matches!(item, syn::Item::Mod(it) if unraw(&it.ident) == name);
        match frame {
            Frame::Block(block) => {
                if super::block_items(block).any(declares) {
                    return true;
                }
            }
            Frame::Module(items) => return items.iter().any(declares),
        }
    }
    false
}

/// Where a path of the crate can lead. See the module documentation.
struct Routes {
    /// The names of the modules the files declare, inline or not, at any
    /// depth.
    modules: BTreeSet<String>,
    /// Every name a `use` or an `extern crate` binds anywhere in the files.
    imported: BTreeSet<String>,
    /// Whether a file has a glob import from outside the crate.
    outside_glob: bool,
    /// Every name a trait or an impl of the files declares as an associated
    /// type, which `Self::` and `E::` name before an enum variant.
    associated_types: BTreeSet<String>,
}

impl Routes {
    /// Whether a path whose segments before the named item are `prefix`
    /// stays in the crate. `in_scope` says whether a first segment other than
    /// `crate`, `self` and `super` names a module declared in the scope the
    /// path is written in.
    fn stays(
        &self,
        leading_colon: bool,
        prefix: &[String],
        in_scope: impl Fn(&str) -> bool,
    ) -> bool {
        let Some((first, rest)) = prefix.split_first() else {
            return false;
        };
        if leading_colon {
            return false;
        }
        let rest = match first.as_str() {
            "crate" | "self" | "super" => {
                let supers = rest
                    .iter()
                    .take_while(|segment| *segment == "super")
                    .count();
                &rest[supers..]
            }
            first if in_scope(first) && !self.imported.contains(first) => rest,
            _ => return false,
        };
        rest.is_empty()
            || (!self.outside_glob
                && rest.iter().all(|segment| {
                    self.modules.contains(segment) && !self.imported.contains(segment)
                }))
    }
}

/// Every name a `use` (a `self` leaf included) or an `extern crate` binds in
/// `file`, at any depth.
fn imported_names(file: &File) -> BTreeSet<String> {
    fn walk(tree: &syn::UseTree, prefix: &mut Vec<String>, out: &mut BTreeSet<String>) {
        match tree {
            syn::UseTree::Path(path) => {
                prefix.push(unraw(&path.ident));
                walk(&path.tree, prefix, out);
                prefix.pop();
            }
            syn::UseTree::Group(group) => {
                for item in &group.items {
                    walk(item, prefix, out);
                }
            }
            syn::UseTree::Name(leaf) => {
                let name = unraw(&leaf.ident);
                if name == "self" {
                    out.extend(prefix.last().cloned());
                } else {
                    out.insert(name);
                }
            }
            syn::UseTree::Rename(rename) if rename.rename != "_" => {
                out.insert(unraw(&rename.rename));
            }
            syn::UseTree::Rename(_) | syn::UseTree::Glob(_) => {}
        }
    }
    #[derive(Default)]
    struct Collect(BTreeSet<String>);
    impl<'ast> Visit<'ast> for Collect {
        fn visit_item_use(&mut self, item: &'ast syn::ItemUse) {
            walk(&item.tree, &mut Vec::new(), &mut self.0);
        }
        fn visit_item_extern_crate(&mut self, item: &'ast syn::ItemExternCrate) {
            let bound = item
                .rename
                .as_ref()
                .map_or(&item.ident, |(_, rename)| rename);
            if bound != "_" {
                self.0.insert(unraw(bound));
            }
        }
    }
    let mut collect = Collect::default();
    collect.visit_file(file);
    collect.0
}

/// Every name a trait or an impl in `file` declares as an associated type.
fn associated_type_names(file: &File) -> BTreeSet<String> {
    #[derive(Default)]
    struct Collect(BTreeSet<String>);
    impl<'ast> Visit<'ast> for Collect {
        fn visit_impl_item_type(&mut self, item: &'ast syn::ImplItemType) {
            self.0.insert(unraw(&item.ident));
            syn::visit::visit_impl_item_type(self, item);
        }
        fn visit_trait_item_type(&mut self, item: &'ast syn::TraitItemType) {
            self.0.insert(unraw(&item.ident));
            syn::visit::visit_trait_item_type(self, item);
        }
    }
    let mut collect = Collect::default();
    collect.visit_file(file);
    collect.0
}

/// The name of the first `mod` in `file` that carries a `path` attribute,
/// written directly or under `cfg_attr`, as `path` or `r#path`.
fn module_with_path_attribute(file: &File) -> Option<String> {
    fn names_path(tokens: TokenStream) -> bool {
        tokens.into_iter().any(|tree| match tree {
            TokenTree::Group(group) => names_path(group.stream()),
            TokenTree::Ident(ident) => unraw(&ident) == "path",
            _ => false,
        })
    }
    #[derive(Default)]
    struct Find(Option<String>);
    impl<'ast> Visit<'ast> for Find {
        fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
            if self.0.is_none()
                && item
                    .attrs
                    .iter()
                    .any(|attr| names_path(attr.meta.to_token_stream()))
            {
                self.0 = Some(unraw(&item.ident));
            }
            syn::visit::visit_item_mod(self, item);
        }
    }
    let mut find = Find::default();
    find.visit_file(file);
    find.0
}

/// The first `use` in `file` that binds a name in `interest` other than under
/// its own name through a path that stays in the crate, described.
fn use_hazard(file: &File, interest: &BTreeSet<String>, routes: &Routes) -> Option<String> {
    struct Scan<'a, 'ast> {
        frames: Vec<Frame<'ast>>,
        interest: &'a BTreeSet<String>,
        routes: &'a Routes,
        hazard: Option<String>,
    }
    impl<'ast> Visit<'ast> for Scan<'_, 'ast> {
        fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
            if let Some((_, items)) = &item.content {
                self.frames.push(Frame::Module(items));
                syn::visit::visit_item_mod(self, item);
                self.frames.pop();
            }
        }

        fn visit_block(&mut self, block: &'ast syn::Block) {
            self.frames.push(Frame::Block(block));
            syn::visit::visit_block(self, block);
            self.frames.pop();
        }

        fn visit_item_use(&mut self, item: &'ast syn::ItemUse) {
            let leading_colon = item.leading_colon.is_some();
            let mut bindings = Vec::new();
            super::declared_names::use_bindings(&item.tree, &mut Vec::new(), &mut bindings);
            for binding in bindings {
                if self.hazard.is_some() || !self.interest.contains(&binding.bound) {
                    continue;
                }
                let rendered = format!(
                    "{}{}::{}",
                    if leading_colon { "::" } else { "" },
                    binding.prefix.join("::"),
                    binding.leaf
                );
                if binding.leaf != binding.bound {
                    self.hazard = Some(format!(
                        "the `use` of `{rendered}` binds `{}`, a type name a file of the crate \
                         declares, to an item of another name",
                        binding.bound
                    ));
                } else if !self.routes.stays(leading_colon, &binding.prefix, |first| {
                    module_in_scope(&self.frames, first)
                }) {
                    self.hazard = Some(format!(
                        "the `use` of `{rendered}` binds `{}`, a type name a file of the crate \
                         declares, from a path that does not stay in the crate",
                        binding.bound
                    ));
                }
            }
        }
    }
    let mut scan = Scan {
        frames: vec![Frame::Module(&file.items)],
        interest,
        routes,
        hazard: None,
    };
    scan.visit_file(file);
    scan.hazard
}

/// The first glob import in `file` whose source is not a path that stays in
/// the crate (by `routes`, before any glob is known) and does not start at
/// one of `exempt`, as written after `use`. With no root exempt, a glob from
/// `std`, `core` or this toolchain's crates counts: their modules export
/// names a file of the crate can declare too (`core::ffi::c_uchar`).
fn outside_glob(file: &File, routes: &Routes, exempt: &[&str]) -> Option<String> {
    struct Scan<'a, 'ast> {
        frames: Vec<Frame<'ast>>,
        routes: &'a Routes,
        exempt: &'a [&'a str],
        found: Option<String>,
    }
    impl<'ast> Visit<'ast> for Scan<'_, 'ast> {
        fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
            if let Some((_, items)) = &item.content {
                self.frames.push(Frame::Module(items));
                syn::visit::visit_item_mod(self, item);
                self.frames.pop();
            }
        }

        fn visit_block(&mut self, block: &'ast syn::Block) {
            self.frames.push(Frame::Block(block));
            syn::visit::visit_block(self, block);
            self.frames.pop();
        }

        fn visit_item_use(&mut self, item: &'ast syn::ItemUse) {
            let leading_colon = item.leading_colon.is_some();
            let mut prefixes = Vec::new();
            super::glob_prefixes(&item.tree, &mut Vec::new(), &mut prefixes);
            for prefix in prefixes {
                let exempt = prefix
                    .first()
                    .is_some_and(|root| self.exempt.contains(&root.as_str()));
                if self.found.is_none()
                    && !exempt
                    && !self.routes.stays(leading_colon, &prefix, |first| {
                        module_in_scope(&self.frames, first)
                    })
                {
                    self.found = Some(format!(
                        "{}{}::*",
                        if leading_colon { "::" } else { "" },
                        prefix.join("::")
                    ));
                }
            }
        }

        fn visit_macro(&mut self, mac: &'ast syn::Macro) {
            syn::visit::visit_macro(self, mac);
            // A glob written in macro tokens is not read with its scopes.
            if self.found.is_none() && holds_glob_use(mac.tokens.clone()) {
                self.found = Some(mac.tokens.to_string());
            }
        }
    }
    let mut scan = Scan {
        frames: vec![Frame::Module(&file.items)],
        routes,
        exempt,
        found: None,
    };
    scan.visit_file(file);
    scan.found
}

/// Whether `tokens` hold a `use` and a `*` at any group depth: a glob import
/// the parser did not read as one.
fn holds_glob_use(tokens: TokenStream) -> bool {
    fn walk(tokens: TokenStream, saw_use: &mut bool, saw_star: &mut bool) {
        for tree in tokens {
            match tree {
                TokenTree::Group(group) => walk(group.stream(), saw_use, saw_star),
                TokenTree::Ident(ident) if ident == "use" => *saw_use = true,
                TokenTree::Punct(punct) if punct.as_char() == '*' => *saw_star = true,
                _ => {}
            }
        }
    }
    let (mut saw_use, mut saw_star) = (false, false);
    walk(tokens, &mut saw_use, &mut saw_star);
    saw_use && saw_star
}

/// The tokens of `file` that read names: every item but `use` items, with the
/// names that items and variants declare left out.
fn reading_tokens(file: &File) -> TokenStream {
    let mut file = file.clone();
    syn::visit_mut::VisitMut::visit_file_mut(&mut UseItemRemover, &mut file);
    syn::visit_mut::VisitMut::visit_file_mut(&mut DeclaredIdentMasker, &mut file);
    file.to_token_stream()
}

/// Whether `tokens` hold the identifier `name` at any group depth.
fn spells_anywhere(tokens: TokenStream, name: &str) -> bool {
    tokens.into_iter().any(|tree| match tree {
        TokenTree::Group(group) => spells_anywhere(group.stream(), name),
        TokenTree::Ident(ident) => unraw(&ident) == name,
        _ => false,
    })
}

/// The tokens of each module scope of `file` that read names, as
/// [`reading_tokens`] keeps them, each with the names of the modules that
/// scope declares. A module's attributes are read in the scope around it.
fn module_scopes(file: &File) -> Vec<(BTreeSet<String>, TokenStream)> {
    fn walk(items: &[syn::Item], out: &mut Vec<(BTreeSet<String>, TokenStream)>) {
        let modules = items
            .iter()
            .filter_map(|item| match item {
                syn::Item::Mod(module) => Some(unraw(&module.ident)),
                _ => None,
            })
            .collect();
        let mut tokens = TokenStream::new();
        for item in items {
            match item {
                syn::Item::Use(_) => {}
                syn::Item::Mod(module) => {
                    for attr in &module.attrs {
                        attr.to_tokens(&mut tokens);
                    }
                    if let Some((_, inner)) = &module.content {
                        walk(inner, out);
                    }
                }
                item => {
                    let mut item = item.clone();
                    syn::visit_mut::VisitMut::visit_item_mut(&mut UseItemRemover, &mut item);
                    syn::visit_mut::VisitMut::visit_item_mut(&mut DeclaredIdentMasker, &mut item);
                    item.to_tokens(&mut tokens);
                }
            }
        }
        out.push((modules, tokens));
    }
    let mut out = Vec::new();
    walk(&file.items, &mut out);
    if let Some((_, tokens)) = out.last_mut() {
        for attr in &file.attrs {
            attr.to_tokens(tokens);
        }
    }
    out
}

/// The first spelling in `tokens`, the tokens of one module scope, of a name
/// in `interest` after a path that does not stay in the crate (by `routes`,
/// with `in_scope` the modules that scope declares) and does not name a
/// variant of a crate enum, rendered. A `Self::` path is left to
/// `self_paths`.
fn path_leaving_crate(
    tokens: TokenStream,
    interest: &BTreeSet<String>,
    in_scope: &BTreeSet<String>,
    routes: &Routes,
    enums: &BTreeMap<String, BTreeSet<String>>,
) -> Option<String> {
    let flat: Vec<TokenTree> = tokens.into_iter().collect();
    for (index, tree) in flat.iter().enumerate() {
        match tree {
            TokenTree::Group(group) => {
                if let Some(found) =
                    path_leaving_crate(group.stream(), interest, in_scope, routes, enums)
                {
                    return Some(found);
                }
            }
            TokenTree::Ident(ident) => {
                let name = unraw(ident);
                if !interest.contains(&name)
                    || index < 2
                    || !is_path_sep(&flat[index - 2], &flat[index - 1])
                {
                    continue;
                }
                let before = &flat[..index];
                let stays = path_segments(before).is_some_and(|prefix| {
                    let start = before.len() - 3 * prefix.len();
                    let leading_colon =
                        start >= 2 && is_path_sep(&before[start - 2], &before[start - 1]);
                    let route_stays = |route: &[String]| {
                        routes.stays(leading_colon, route, |first| in_scope.contains(first))
                    };
                    let variant = prefix.split_last().is_some_and(|(owner, route)| {
                        // `Self::W` is left to `self_paths`, which knows what
                        // `Self` is where the path is written.
                        let names_variant = owner == "Self"
                            || (!routes.associated_types.contains(&name)
                                && enums
                                    .get(owner)
                                    .is_some_and(|variants| variants.contains(&name)));
                        names_variant
                            && if route.is_empty() {
                                !leading_colon
                            } else {
                                route_stays(route)
                            }
                    });
                    variant || route_stays(&prefix)
                });
                if !stays {
                    let prefix = path_segments(before)
                        .map_or_else(|| "..".to_string(), |prefix| prefix.join("::"));
                    return Some(format!("{prefix}::{name}"));
                }
            }
            _ => {}
        }
    }
    None
}
